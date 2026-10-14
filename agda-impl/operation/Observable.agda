{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  The shared engine, run in IO: real refs, user-written
-- colds that may perform IO.  Nothing here is proven; it is checked
-- against the TypeScript by the oracle.
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
-- The pure runtime closes the engine's recursion by unfolding it n
-- times; a real program needs every unfolding, and IO cannot re-run to
-- take the limit, so here it is closed with `fixIO`.  Every fixpoint it
-- takes is an IO action: one may run forever, but none is a value of any
-- other type, so nothing here proves anything.
module operation.Observable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)
open import Level using (Lift; lift; lower; 0ℓ) renaming (suc to lsuc)

open import Tree using (Obs)
open import operation.AbstractObservable using (Prims; module Run)
open import denotation.MonotonicList using (From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline)

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

-- A registered observer, as the IO it runs.
record SinkSlot (A : Set) : Set where
  field
    onNext     : A → IO ⊤
    onComplete : IO ⊤
    isClosed   : IO Bool

-- A started cold: whether it is spent, and its teardown once known —
-- not before its `subscription` has returned.
record Slot : Set where
  field
    spent    : IORef Bool
    tearDown : IORef (Maybe (IO ⊤))

-- IO has one world, so every name is valid everywhere.  A record with no
-- fields, so any two worlds are equal by eta and weakening is the identity.
record One : Set₁ where

IOᴾ : Prims
IOᴾ = record
  { World = One ; _⊑_ = λ _ _ → ⊤ ; ⊑-refl = tt ; _⨾_ = λ _ _ → tt
  ; RefOf = λ _ _ → IORef ; Sink = λ _ → SinkSlot ; Handle = λ _ → Slot
  ; wkRef = λ _ _ r → r ; wkSink = λ _ s → s ; wkHandle = λ _ h → h
  ; Cold = IOCold ; Eff = IO }

open Run IOᴾ

Observable : Set → Set₁
Observable = Obs IOCold []

------------------------------------------------------------------------
-- The runtime

-- The engine's monad: IO, lifted to the universe its tables live in.
M : One → Set → Set₁
M _ A = IO (Lift (lsuc 0ℓ) A)

private
  ret : ∀ {w A} → IO A → M w A
  ret m = m >>= λ a → pure (lift a)

  low : ∀ {w A} → M w A → IO A
  low m = m >>= λ a → pure (lower a)

-- The loop's state: the clock, the timers in the order they fire, and
-- the subscription's lock.
record Loop : Set where
  field
    clock  : IORef ℕ
    timers : IORef (List (ℕ × IO ⊤))
    lock   : Lock

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

  -- Spends the slot, once.
  spend : Slot → IO ⊤ → IO ⊤
  spend sl m = unless (Slot.spent sl) (writeIORef (Slot.spent sl) true >> m >> runTeardown sl)

  -- Runs the user's `subscription`, delivering each `produce` as it is
  -- made.  A cold spent during its own subscription is torn down the
  -- moment its teardown exists.
  playCold : Loop → ∀ {A} → IOCold A → SinkSlot A → IO Slot
  playCold lp {A} c sk =
    newIORef false >>= λ sp → newIORef nothing >>= λ td →
    let sl = record { spent = sp ; tearDown = td }
        st = IOCold.create c (record
          { produce  = λ a → atomically lp (unless sp (SinkSlot.onNext sk a))
          ; complete = atomically lp (spend sl (SinkSlot.onComplete sk))
          ; closed   = atomically lp (readIORef sp >>= λ s → if s then pure true else SinkSlot.isClosed sk)
          ; after    = setTimer lp })
    in Started.subscription st >>= λ i →
       writeIORef td (just (Started.teardown st i)) >>
       readIORef sp >>= λ s → (if s then runTeardown sl else pure tt) >> pure sl

  nextTimer : Loop → IO Bool
  nextTimer lp = readIORef (Loop.timers lp) >>= λ where
    []             → pure false
    ((t , a) ∷ ts) → writeIORef (Loop.timers lp) ts >> writeIORef (Loop.clock lp) t >> atomically lp a >> pure true

IOᴿ : Loop → Runtime
IOᴿ lp = record
  { M          = M
  ; return     = λ a → pure (lift a)
  ; _>>=_      = λ m f → m >>= λ a → f (lower a)
  ; newRefᴿ    = λ _ a k → newIORef a >>= k tt
  ; readRefᴿ   = λ r k → readIORef r >>= k tt
  ; writeRefᴿ  = λ r a → ret (writeIORef r a)
  ; registerᴿ  = λ run n c x k → k tt (record { onNext = λ a → low (run (n a)) ; onComplete = low (run c) ; isClosed = low (run x) })
  ; sendᴿ      = λ _ sk a → ret (SinkSlot.onNext sk a)
  ; finishᴿ    = λ _ sk → ret (SinkSlot.onComplete sk)
  ; startColdᴿ = λ _ c sk k → playCold lp c sk >>= k tt
  ; stopᴿ      = λ sl → ret (spend sl (pure tt))
  ; effᴿ       = ret
  ; hereᴿ      = λ k → k []
  ; gotoᴿ      = λ _ → pure (lift tt)
  ; divergeᴿ   = fixIO′ (λ d _ → d tt) tt
  ; nextᴿ      = λ _ → ret (nextTimer lp)
  }

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
    burst e off self t = fixIO′ λ go b → Emit.closed e >>= λ c → if c then pure tt else step go b
      where
        step : (Frame A t → IO ⊤) → Frame A t → IO ⊤
        step go (emit a k) = Emit.produce e a >> unless off (go (Frame∞.force k))
        step go (stall k)  = go (Frame∞.force k)
        step go (close k)  = self t (From∞.force k)

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

-- One `Act` to run, its world and result packed, so that `fixIO` can
-- close the interpreter's recursion over every one of them.
private
  record Job : Set₁ where
    constructor job
    field
      {w}  : One
      {B}  : Set
      act  : Act w B

module _ (lp : Loop) where
  open Engine (IOᴿ lp)

  private
    run∞ : RunAct
    run∞ a = fixIO {Y = λ j → Lift (lsuc 0ℓ) (Job.B j)} (λ self j → interpret (λ a′ → self (job a′)) (Job.act j)) (job a)

    loop∞ : M _ ⊤
    loop∞ = fixIO′ (λ again _ → loopStep run∞ (again tt)) tt

  running : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → IO ⊤
  -- The subscribe burst under the lock; then the loop, whose timers
  -- each take it.
  running {A} o f c = atomically lp (low (run∞ (compile o [] tt observer λ _ _ → done tt))) >>= λ _ → low loop∞
    where
      observer : Observer A _
      observer = record
        { next     = λ a → eff (readIORef (Loop.clock lp) >>= λ t → f t a) λ _ → done tt
        ; complete = eff c λ _ → done tt
        ; closed   = done false
        }

-- THE ENTRY POINT: runs until no timer is left.  Each value is handed
-- the loop's time at its arrival; the last argument runs on completion.
subscribe : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → IO ⊤
subscribe o f c = newLock >>= λ lk → newIORef 0 >>= λ cl → newIORef [] >>= λ ts → running (record { clock = cl ; timers = ts ; lock = lk }) o f c
