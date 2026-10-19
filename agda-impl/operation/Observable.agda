{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  The shared machine (`operation.AbstractObservable`'s
-- `Machine`), driven by the world: user-written colds that may perform
-- IO feed it their emissions, and the effects it asks for are performed
-- for real.  Every transition is the one the pure runtime takes; only the
-- driver is unproven, and it is checked against the TypeScript by the
-- oracle.
--
-- Asynchrony is JavaScript's, not threads': a cold sets timers with
-- `after`, and the loop runs the earliest, ties in the order they were
-- set.  Time is the loop's own counter, so a run takes no wall-clock
-- time and two runs of one program agree.
--
-- DELIVERY IS ATOMIC PER SUBSCRIPTION.  A cold may `produce` from any
-- thread, and any interleaving of emissions is legal; a state no
-- interleaving produces is not.  So every entry into the engine — the
-- subscribe burst, a `produce`, a `complete`, a timer — runs whole under
-- one lock per `subscribe`, re-entrant on its own thread, since a
-- cascade emits again synchronously.  A thread arriving mid-cascade
-- blocks in `produce`, first come first served, and delivers after: as
-- a JavaScript `next` returns only once delivered, nothing is dropped.
-- The subscribing thread holds the lock through its burst, so a forked
-- thread's emissions always land after it.  Code that blocks INSIDE a
-- cascade waiting on another producer thread — a `subscription` awaiting
-- its own fork, a subscriber awaiting a producer — deadlocks.
--
-- The driver's recursion — running the machine until it holds, the
-- loop's next turn — is closed with `fixIO`.  Every fixpoint it takes is
-- an IO action: one may run forever, but none is a value of any other
-- type, so nothing here proves anything.
module operation.Observable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)
open import Level using (Lift; lift; lower; 0ℓ) renaming (suc to lsuc)

open import Tree using (Obs)
open import operation.AbstractObservable using (Prims; prims; module Heap; module Run; module Machine)
open import denotation.MonotonicList.Events using (From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline)

------------------------------------------------------------------------
-- Haskell's refs

postulate
  IORef      : Set → Set
  newIORef   : ∀ {A} → A → IO (IORef A)
  readIORef  : ∀ {A} → IORef A → IO A
  writeIORef : ∀ {A} → IORef A → A → IO ⊤

-- A lock, re-entrant on the thread holding it, released on any exit.
postulate
  Lock     : Set
  newLock  : IO Lock
  withLock : ∀ {a} {A : Set a} → Lock → IO A → IO A

-- Haskell's `fix` is untyped at the FFI, so it is bound at a simple
-- type — and is unsound at most of them.  Its scope is this module, whose
-- one export takes fixpoints of IO actions only.
private
  module FixIO where
    private
      postulate
        fixᴴ : ∀ {a} {A : Set a} → (A → A) → A
    {-# COMPILE GHC fixᴴ = \ _ _ -> Data.Function.fix #-}

    fixIO : ∀ {a b} {X : Set a} {Y : X → Set b} → ((∀ x → IO (Y x)) → ∀ x → IO (Y x)) → ∀ x → IO (Y x)
    fixIO = fixᴴ

open FixIO using (fixIO)

{-# FOREIGN GHC import qualified Data.IORef #-}
{-# FOREIGN GHC import qualified Data.Function #-}
{-# FOREIGN GHC import qualified Unsafe.Coerce #-}
{-# COMPILE GHC IORef = type Data.IORef.IORef #-}
{-# COMPILE GHC newIORef = \ _ -> Data.IORef.newIORef #-}
{-# COMPILE GHC readIORef = \ _ -> Data.IORef.readIORef #-}
{-# COMPILE GHC writeIORef = \ _ -> Data.IORef.writeIORef #-}
{-# FOREIGN GHC
import qualified Control.Concurrent
import qualified Control.Concurrent.MVar
import qualified Control.Exception

data RxLock = RxLock (Control.Concurrent.MVar.MVar ()) (Data.IORef.IORef (Maybe Control.Concurrent.ThreadId))

rxLockNew :: IO RxLock
rxLockNew = do
  m <- Control.Concurrent.MVar.newMVar ()
  o <- Data.IORef.newIORef Nothing
  return (RxLock m o)

rxLockWith :: RxLock -> IO a -> IO a
rxLockWith (RxLock m o) act = do
  me  <- Control.Concurrent.myThreadId
  cur <- Data.IORef.readIORef o
  if cur == Just me then act else
    Control.Exception.mask (\restore -> do
      Control.Concurrent.MVar.takeMVar m
      Data.IORef.writeIORef o (Just me)
      restore act `Control.Exception.finally`
        (Data.IORef.writeIORef o Nothing >> Control.Concurrent.MVar.putMVar m ()))
#-}
{-# COMPILE GHC Lock = type RxLock #-}
{-# COMPILE GHC newLock = rxLockNew #-}
{-# COMPILE GHC withLock = \ _ _ -> rxLockWith #-}

private
  infixl 1 _>>_
  _>>_ : ∀ {A : Set} → IO ⊤ → IO A → IO A
  m >> n = m >>= λ _ → n

  unless : IORef Bool → IO ⊤ → IO ⊤
  unless r m = readIORef r >>= λ b → if b then pure tt else m

  fixIO′ : ∀ {a b} {X : Set a} {Y : Set b} → ((X → IO Y) → X → IO Y) → X → IO Y
  fixIO′ {Y = Y} = fixIO {Y = λ _ → Y}

------------------------------------------------------------------------
-- Colds

-- A cold, as the user writes it.  `subscription` runs when the cold is
-- subscribed; every `produce` it makes before returning is the
-- synchronous burst.  A `produce` from a timer it set is an async
-- emission.  `teardown` runs once, on completion or unsubscribe; after
-- it, `produce` and `complete` are ignored.
record Started (Internal : Set) : Set where
  field
    subscription : IO Internal
    teardown     : Internal → IO ⊤

-- What a cold is handed: how to emit, and how to set a timer.
-- `closed` is rxjs's `subscriber.closed`, for a producer to poll.
record Emit (A : Set) : Set where
  field
    produce  : A → IO ⊤
    complete : IO ⊤
    closed   : IO Bool
    after    : ℕ → IO ⊤ → IO ⊤

-- `create` takes an `Emit`, not its fields curried: with `Internal`
-- erased MAlonzo compiles this record to a `newtype`, and GHC rejects a
-- newtype whose field mentions `IO` bare — its kind-polymorphic
-- arguments become existentials.
record IOCold (A : Set) : Set₁ where
  field
    Internal : Set
    create   : Emit A → Started Internal

-- A started cold, as the IO driver tracks it: whether it is spent, and
-- its teardown once known — not before its `subscription` has returned.
record Slot : Set where
  field
    spent    : IORef Bool
    tearDown : IORef (Maybe (IO ⊤))

-- The IO runtime's primitives: the shared heap, user-written colds, IO.
IOᴾ : Prims
IOᴾ = prims IOCold IO

open Heap using (World; _⊑_; _∋_; here; there; _⨾_; wk∋; Sink; Handle)
open Run IOᴾ
open Machine IOCold IO

Observable : Set → Set₁
Observable = Obs IOCold []

------------------------------------------------------------------------
-- The driver's state

-- The machine's configuration lives in `Set₁`, so its ref is one level up.
postulate
  IORef₁      : Set₁ → Set
  newIORef₁   : ∀ {A} → A → IO (IORef₁ A)
  readIORef₁  : ∀ {A} → IORef₁ A → IO A
  writeIORef₁ : ∀ {A} → IORef₁ A → A → IO ⊤

{-# COMPILE GHC IORef₁ = type Data.IORef.IORef #-}
{-# COMPILE GHC newIORef₁ = \ _ -> Data.IORef.newIORef #-}
{-# COMPILE GHC readIORef₁ = \ _ -> Data.IORef.readIORef #-}
{-# COMPILE GHC writeIORef₁ = \ _ -> Data.IORef.writeIORef #-}

-- A started cold's entry in the driver: the world its sink and handle
-- were made in, how that world has grown since, and its slot.  A cold's
-- `produce` names its entry by index, since a closure cannot follow the
-- world as it grows.
record Ticket (v : World) : Set₁ where
  field
    {made}  : World
    {A}     : Set
    sink    : Sink made A
    handle  : Handle made
    grown   : made ⊑ v
    slot    : Slot

record Live : Set₁ where
  field
    conf    : Conf
    tickets : List (Ticket (Conf.world conf))

record Loop : Set where
  field
    clock  : IORef ℕ
    timers : IORef (List (ℕ × IO ⊤))
    lock   : Lock
    live   : IORef₁ Live

-- The IO driver's one unchecked step: a value the machine awaits, or a
-- sink a cold names by index, read at the type the configuration has
-- now.  The machine's types are not followed across a real effect.
postulate
  coerce : ∀ {a} {A B : Set a} → A → B
{-# COMPILE GHC coerce = \ _ _ _ -> Unsafe.Coerce.unsafeCoerce #-}

private
  atomically : ∀ {a} {X : Set a} → Loop → IO X → IO X
  atomically lp = withLock (Loop.lock lp)

  -- After every timer due no later: two timers due together fire in the
  -- order they were set.
  insert : ℕ → IO ⊤ → List (ℕ × IO ⊤) → List (ℕ × IO ⊤)
  insert d a []              = (d , a) ∷ []
  insert d a ((e , b) ∷ ts) = if e ≤ᵇ d then (e , b) ∷ insert d a ts else (d , a) ∷ (e , b) ∷ ts

  setTimer : Loop → ℕ → IO ⊤ → IO ⊤
  setTimer lp d a = readIORef (Loop.clock lp) >>= λ now → readIORef (Loop.timers lp) >>= λ ts →
                    writeIORef (Loop.timers lp) (insert (now + d) a ts)

  runTeardown : Slot → IO ⊤
  runTeardown sl = readIORef (Slot.tearDown sl) >>= λ where
    nothing  → pure tt
    (just t) → writeIORef (Slot.tearDown sl) nothing >> t

  nextTimer : Loop → IO Bool
  nextTimer lp = readIORef (Loop.timers lp) >>= λ where
    []             → pure false
    ((t , a) ∷ ts) → writeIORef (Loop.timers lp) ts >> writeIORef (Loop.clock lp) t >> atomically lp a >> pure true

  mapList : ∀ {a b} {X : Set a} {Y : Set b} → (X → Y) → List X → List Y
  mapList f []       = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  nth : ∀ {a} {X : Set a} → ℕ → List X → Maybe X
  nth n       []       = nothing
  nth zero    (x ∷ xs) = just x
  nth (suc n) (x ∷ xs) = nth n xs

  len : ∀ {a} {X : Set a} → List X → ℕ
  len []       = 0
  len (_ ∷ xs) = suc (len xs)

  -- Two names in one world, the same entry.
  _≡ₙ_ : ∀ {w j k} → w ∋ j → w ∋ k → Bool
  here    ≡ₙ here    = true
  there i ≡ₙ there j = i ≡ₙ j
  _       ≡ₙ _       = false

  -- Whether the machine is mid-computation, rather than holding.
  running : Conf → Bool
  running c with Conf.ctl c
  ... | run _ _ _      = true
  ... | ret _ _ _      = true
  ... | held _ _       = false
  ... | asking _ _ _ _ = false

------------------------------------------------------------------------
-- THE IO DRIVER: the shared machine, fed by the world

module Drive (lp : Loop) where
  -- What the driver does, as one recursion closed with `fixIO`: feed one
  -- input chosen against the configuration as it stands, or run the
  -- machine until it holds.
  data Call : Set₁ where
    feeding  : ((l : Live) → Input (Live.conf l)) → Call
    settling : Call

  private
    _>>′_ : ∀ {A : Set} → IO Bool → IO A → IO A
    m >>′ n = m >>= λ _ → n

  -- The entry a cold names by index, read in the current world.
  named : (l : Live) → ℕ → (∀ {A} → Sink (Conf.world (Live.conf l)) A → Handle (Conf.world (Live.conf l)) → Input (Live.conf l)) → Input (Live.conf l)
  named l idx k with nth idx (Live.tickets l)
  ... | just t  = k (wk∋ (Ticket.grown t) (Ticket.sink t)) (wk∋ (Ticket.grown t) (Ticket.handle t))
  ... | nothing = go

  module Body (self : Call → IO Bool) where
    feed : ((l : Live) → Input (Live.conf l)) → IO Bool
    feed i = self (feeding i)

    settle : IO Bool
    settle = self settling

    -- A cold started: its ticket filed, its `subscription` run — each
    -- `produce` fed as a delivery — then the machine resumed.
    started : ∀ {h A} → IOCold A → Sink h A → Handle h → IO ⊤
    started {A = A} c s hd =
      newIORef false >>= λ sp → newIORef nothing >>= λ td →
      readIORef₁ (Loop.live lp) >>= λ l →
      let sl  = record { spent = sp ; tearDown = td }
          idx = len (Live.tickets l)
          st  = IOCold.create c (record
            { produce  = λ a → atomically lp (unless sp (feed (λ l′ → named l′ idx λ s′ hd′ → deliver s′ (coerce a) []) >>′ pure tt))
            ; complete = atomically lp (unless sp (feed (λ l′ → named l′ idx λ s′ hd′ → end hd′ s′ []) >>′ runTeardown sl))
            ; closed   = atomically lp (readIORef sp >>= λ x → if x then pure true else feed (λ l′ → named l′ idx λ s′ hd′ → poll s′))
            ; after    = setTimer lp })
      in writeIORef₁ (Loop.live lp) (record l { tickets = Live.tickets l ++ (record { made = _ ; A = A ; sink = s ; handle = hd ; grown = coerce (Heap.same {w = Conf.world (Live.conf l)}) ; slot = sl } ∷ []) }) >>
         Started.subscription st >>= λ i →
         writeIORef td (just (Started.teardown st i)) >>
         readIORef sp >>= λ x → (if x then runTeardown sl else pure tt) >>
         feed (λ _ → go) >>′ pure tt

    -- A teardown: the started cold whose handle this is, spent and torn down.
    stopping : ∀ {h v} → Handle h → List (Ticket v) → IO ⊤
    stopping hd []       = pure tt
    stopping hd (t ∷ ts) = if coerce {B = Handle _} (wk∋ (Ticket.grown t) (Ticket.handle t)) ≡ₙ hd
                           then (writeIORef (Slot.spent (Ticket.slot t)) true >> runTeardown (Ticket.slot t)) else stopping hd ts

    -- What the machine asks: an effect performed and answered; a cold
    -- started, its burst fed now; a teardown run; a poll answered.
    obey : ∀ {h} → List (Output h) → IO Bool
    obey []                    = pure false
    obey (perform e ∷ _)       = e >>= λ x → feed (λ _ → answer (coerce x))
    obey (start c s hd ∷ _)    = started c s hd >> pure false
    obey (stopped hd ∷ _)      = readIORef₁ (Loop.live lp) >>= λ l → stopping hd (Live.tickets l) >> pure false
    obey (closedIs b ∷ _)      = pure b

    -- One transition taken: the tickets carried into the grown world, the
    -- outputs obeyed, the machine run until it holds.  A poll's answer is
    -- returned.
    taken : (l : Live) → Next (Conf.world (Live.conf l)) → IO Bool
    taken l (next c ρ os) =
      writeIORef₁ (Loop.live lp) (record { conf = c ; tickets = mapList (λ t → record { sink = Ticket.sink t ; handle = Ticket.handle t ; grown = Ticket.grown t ⨾ ρ ; slot = Ticket.slot t }) (Live.tickets l) }) >>
      obey os >>= λ b → settle >>′ pure b

    call : Call → IO Bool
    call (feeding i) = readIORef₁ (Loop.live lp) >>= λ l → taken l (transition (Live.conf l) (i l))
    call settling    = readIORef₁ (Loop.live lp) >>= λ l → if running (Live.conf l) then feed (λ _ → go) >>′ settle else pure false

  drive : Call → IO Bool
  drive = fixIO′ Body.call


------------------------------------------------------------------------
-- A timeline, played

-- Frame 0 inline, then each later frame on a timer set where the burst
-- before it ends.  A closed subscriber or a teardown stops the playing.
fromTimeline : ∀ {A} → Timeline A → IOCold A
fromTimeline {A} c = record
  { Internal = IORef Bool
  ; create   = λ e → record
      { subscription = newIORef false >>= λ off → first e off (lower c) >> pure off
      ; teardown     = λ off → writeIORef off true }
  }
  where
    -- `self` plays the frames after this burst.
    burst : Emit A → IORef Bool → (∀ t → From A (suc t) → IO ⊤) → ∀ t → Frame A t → IO ⊤
    burst e off self t = fixIO′ λ next′ b → Emit.closed e >>= λ c → if c then pure tt else step next′ b
      where
        step : (Frame A t → IO ⊤) → Frame A t → IO ⊤
        step next′ (emit a k) = Emit.produce e a >> unless off (next′ (Frame∞.force k))
        step next′ (stall k)  = next′ (Frame∞.force k)
        step next′ (close k)  = self t (From∞.force k)

    play : Emit A → IORef Bool → Time → ∀ {u} → From A u → IO ⊤
    play e off now m = fixIO′ step (now , _ , m)
      where
        step : (Time × Σ Time (From A) → IO ⊤) → Time × Σ Time (From A) → IO ⊤
        step self (now , _ , done)     = Emit.complete e
        step self (now , _ , quiet)    = pure tt
        step self (now , _ , at t _ b) = Emit.after e (t ∸ now) (unless off (burst e off (λ t′ m′ → self (t′ , suc t′ , m′)) t b))

    first : Emit A → IORef Bool → From A 0 → IO ⊤
    first e off (at 0 _ b) = burst e off (λ t′ m′ → play e off t′ m′) 0 b
    first e off m        = play e off 0 m

------------------------------------------------------------------------
-- The entry point

-- THE ENTRY POINT: the program loaded into the shared machine, run until
-- it holds, then the loop, each timer under the lock, until none is
-- left.  Each value is handed the loop's time at its arrival; the last
-- argument runs on completion.
subscribe : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → IO ⊤
subscribe {A} o f c =
  newLock >>= λ lk → newIORef 0 >>= λ cl → newIORef [] >>= λ ts →
  newIORef₁ (record { conf = load (compile o []) (observer cl) ; tickets = [] }) >>= λ lv →
  let lp = record { clock = cl ; timers = ts ; lock = lk ; live = lv } in
  atomically lp (Drive.drive lp Drive.settling >>= λ _ → pure tt) >> fixIO′ (λ again _ → nextTimer lp >>= λ more → if more then again tt else pure tt) tt
  where
    observer : IORef ℕ → Observer A []
    observer cl = record
      { next     = λ a → eff (readIORef cl >>= λ t → f t a) λ _ → done tt
      ; complete = eff c λ _ → done tt
      ; closed   = done false
      }
