{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  `operation.StateTree`'s machine, driven by the world:
-- user-written colds that may perform IO feed it their emissions, and
-- what it shows and tears down is done for real.  Every transition is the
-- one the pure runtime (`operation.StateTree.Pure`) takes; only the
-- driver is unproven, and it is checked against the TypeScript by the
-- oracle.
--
-- Nothing is coerced.  The driver keeps no typed state of its own: a
-- cold's emissions wait in its own leaf's inbox, and the cold names its
-- leaf by path, so each is read at the leaf's type.
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
-- its own fork, a subscriber awaiting a producer — deadlocks.  An
-- emission made while the machine is mid-step, from a teardown, waits in
-- its inbox for the cold's next.
--
-- The driver's recursion — running the machine until it is calm, the
-- loop's next turn — is closed with `fixIO`.  Every fixpoint it takes is
-- an IO action: one may run forever, but none is a value of any other
-- type, so nothing here proves anything.
module operation.Observable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; fixed; fresh; timelineAt; Pos; ix)

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

-- A wake-up for the loop: raised any number of times, it is taken once.
postulate
  Signal    : Set
  newSignal : IO Signal
  raise     : Signal → IO ⊤
  await     : Signal → IO ⊤

{-# COMPILE GHC Signal = type Control.Concurrent.MVar.MVar () #-}
{-# COMPILE GHC newSignal = Control.Concurrent.MVar.newEmptyMVar #-}
{-# COMPILE GHC raise = \ s -> () <$ Control.Concurrent.MVar.tryPutMVar s () #-}
{-# COMPILE GHC await = Control.Concurrent.MVar.takeMVar #-}

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

Observable : Set → Set₁
Observable = Obs IOCold []

-- What the driver keeps at a started cold: what it has made and the
-- machine not yet taken in, oldest first — a value, or `nothing` for its
-- completion — and its slot.  A cold's `produce` reaches its leaf by
-- path, and reads the leaf's own inbox there, so every value goes in at
-- the type the machine has at that leaf.
record Leaf (A : Set) : Set₁ where
  field
    inbox : IORef (List (Maybe A))
    slot  : Slot

import operation.StateTree
module Machine = operation.StateTree IOCold Leaf
open Machine using (Conf; Stepped; moved; starting; Shown; Torn; Ev; nx; cp; load; Poke; gone; leaf; poke; spot; calm; depth)
  renaming (step to stepᴹ)

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

record Loop (R : Set) : Set where
  field
    clock  : IORef ℕ
    timers : IORef (List (ℕ × IO ⊤))
    lock   : Lock
    wake   : Signal
    conf   : IORef₁ (Conf R)

private
  atomically : ∀ {R a} {X : Set a} → Loop R → IO X → IO X
  atomically lp = withLock (Loop.lock lp)

  -- After every timer due no later: two timers due together fire in the
  -- order they were set.
  insert : ℕ → IO ⊤ → List (ℕ × IO ⊤) → List (ℕ × IO ⊤)
  insert d a []              = (d , a) ∷ []
  insert d a ((e , b) ∷ ts) = if e ≤ᵇ d then (e , b) ∷ insert d a ts else (d , a) ∷ (e , b) ∷ ts

  -- A cold may set a timer from its own thread, so the queue is touched
  -- only under the lock, and the loop is woken.
  setTimer : ∀ {R} → Loop R → ℕ → IO ⊤ → IO ⊤
  setTimer lp d a = atomically lp (readIORef (Loop.clock lp) >>= λ now → readIORef (Loop.timers lp) >>= λ ts →
                    writeIORef (Loop.timers lp) (insert (now + d) a ts)) >> raise (Loop.wake lp)

  runTeardown : Slot → IO ⊤
  runTeardown sl = readIORef (Slot.tearDown sl) >>= λ where
    nothing  → pure tt
    (just t) → writeIORef (Slot.tearDown sl) nothing >> t

  nextTimer : ∀ {R} → Loop R → IO Bool
  nextTimer lp = atomically lp (readIORef (Loop.timers lp) >>= λ where
    []             → pure false
    ((t , a) ∷ ts) → writeIORef (Loop.timers lp) ts >> writeIORef (Loop.clock lp) t >> a >> pure true)

------------------------------------------------------------------------
-- THE IO DRIVER: the shared machine, fed by the world

module Drive {R : Set} (lp : Loop R) (f : Time → R → IO ⊤) (c : IO ⊤) where
  -- What the driver does, as one recursion closed with `fixIO`: run the
  -- machine until it is calm with no more than `d` jobs owed; or take in
  -- what the cold at a path has made.
  data Call : Set where
    settling : ℕ → Call
    pulse    : List ℕ → Call

  -- rxjs's `closed`, for the cold at a path: gone, ended, or its
  -- observer closed.
  asked : Poke R → Bool
  asked gone              = true
  asked (leaf b _ cl _ _) = not b ∨ cl

  ask : List ℕ → IO Bool
  ask π = readIORef₁ (Loop.conf lp) >>= λ k → pure (asked (poke π k))

  shown : Shown R → IO ⊤
  shown []               = pure tt
  shown ((_ , nx a) ∷ s) = readIORef (Loop.clock lp) >>= λ t → f t a >> shown s
  shown ((_ , cp) ∷ s)   = c >> shown s

  -- The colds an unsubscribe reached: spent, then torn down.
  tear : Torn → IO ⊤
  tear []             = pure tt
  tear ((_ , l) ∷ ls) = writeIORef (Slot.spent (Leaf.slot l)) true >> runTeardown (Leaf.slot l) >> tear ls

  push : ∀ {A} → Leaf A → Maybe A → IO ⊤
  push l e = readIORef (Leaf.inbox l) >>= λ es → writeIORef (Leaf.inbox l) (es ++ e ∷ [])

  -- What a cold made, as the machine takes it: IO knows no positions.
  delivered : ∀ {A} → (Ev A → Leaf A → Bool → Pos → Conf R) → Leaf A → Maybe A → Conf R
  delivered dv l (just a) = dv (nx a) l true []
  delivered dv l nothing  = dv cp l false []

  module Body (self : Call → IO ⊤) where
    settle : ℕ → IO ⊤
    settle d = self (settling d)

    -- A cold subscribed: its leaf made and the machine resumed at it,
    -- then its `subscription` run, each `produce` taken in as it is made.
    started : ∀ {A} → IOCold A → (Leaf A → Conf R) → ℕ → IO ⊤
    started x k d =
      newIORef [] >>= λ ib → newIORef false >>= λ sp → newIORef nothing >>= λ td →
      let sl = record { spent = sp ; tearDown = td }
          l  = record { inbox = ib ; slot = sl }
          k′ = k l
          π  = spot k′
          st = IOCold.create x (record
            { produce  = λ a → atomically lp (unless sp (push l (just a) >> self (pulse π)))
            ; complete = atomically lp (unless sp (push l nothing >> self (pulse π) >> runTeardown sl))
            ; closed   = atomically lp (readIORef sp >>= λ b → if b then pure true else ask π)
            ; after    = setTimer lp })
      in writeIORef₁ (Loop.conf lp) k′ >>
         Started.subscription st >>= λ i →
         writeIORef td (just (Started.teardown st i)) >>
         readIORef sp >>= λ b → (if b then runTeardown sl else pure tt) >>
         settle d

    taken : Stepped R → ℕ → IO ⊤
    taken (moved k s t)    d = writeIORef₁ (Loop.conf lp) k >> shown s >> tear t >> settle d
    taken (starting x _ k) d = started x k d

    -- The oldest thing a cold made, delivered if the cold is still live;
    -- the machine then run back down to the jobs owed before it.
    pulsed : ℕ → Poke R → IO ⊤
    pulsed d gone                = pure tt
    pulsed d (leaf b l cl dv st) = readIORef (Leaf.inbox l) >>= λ where
      []       → pure tt
      (e ∷ es) → writeIORef (Leaf.inbox l) es >>
                 (if b then writeIORef₁ (Loop.conf lp) (delivered dv l e) >> settle d else pure tt)

    call : Call → IO ⊤
    call (settling d) = readIORef₁ (Loop.conf lp) >>= λ k →
      if calm k ∧ (depth k ≤ᵇ d) then pure tt else taken (stepᴹ k) d
    call (pulse π)    = readIORef₁ (Loop.conf lp) >>= λ k → if calm k then pulsed (depth k) (poke π k) else pure tt

  drive : Call → IO ⊤
  drive = fixIO′ Body.call

------------------------------------------------------------------------
-- A timeline, played

-- Frame 0 inline, then each later frame on a timer set where the burst
-- before it ends.  A closed subscriber or a teardown stops the playing.
-- IO knows no positions, so a `fresh` leaf's name is drawn from `names`,
-- a supply shared by the run: a position no other draw returns, which is
-- all a name is read for.
fromTimeline : ∀ {A} → IORef ℕ → Timeline A → IOCold A
fromTimeline {A} names c = record
  { Internal = IORef Bool
  ; create   = λ e → record
      { subscription = newIORef false >>= λ off → named c >>= λ q → first e off (timelineAt c q) >> pure off
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

    named : Timeline A → IO Pos
    named (fixed _) = pure []
    named fresh     = readIORef names >>= λ n → writeIORef names (suc n) >> pure (ix n ∷ [])

    first : Emit A → IORef Bool → From A 0 → IO ⊤
    first e off (at 0 _ b) = burst e off (λ t′ m′ → play e off t′ m′) 0 b
    first e off m        = play e off 0 m

------------------------------------------------------------------------
-- The entry point

private
  -- The program loaded into the machine and run until it is calm; then
  -- the loop, each timer under the lock, until none is left and `stop`
  -- says so.  Each value is handed the loop's time at its arrival; `c`
  -- runs on completion.
  launch : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → (Signal → IO Bool) → IO ⊤
  launch o f c stop =
    newLock >>= λ lk → newSignal >>= λ wk → newIORef 0 >>= λ cl → newIORef [] >>= λ ts → newIORef₁ (load o) >>= λ k →
    let lp = record { clock = cl ; timers = ts ; lock = lk ; wake = wk ; conf = k } in
    atomically lp (Drive.drive lp f (c >> raise wk) (Drive.settling 0)) >>
    fixIO′ (λ again _ → nextTimer lp >>= λ more → if more then again tt else stop wk >>= λ s → if s then pure tt else again tt) tt

-- THE ENTRY POINT, as rxjs's `subscribe()`: what the program does is done
-- by its colds; its values are dropped.  It returns once the program has
-- completed — until then a cold's thread may still emit or set a timer,
-- which wakes the loop.
subscribe : ∀ {A} → Observable A → IO ⊤
subscribe o = newIORef false >>= λ fin →
  launch o (λ _ _ → pure tt) (writeIORef fin true)
    (λ wk → readIORef fin >>= λ d → if d then pure true else await wk >> pure false)

-- THE HARNESS'S ENTRY POINT: each value with the loop's time, and the
-- completion, handed out; returns once no timer is left, completed or
-- not, so a program that goes quiet can be read.
subscribeLogged : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → IO ⊤
subscribeLogged o f c = launch o f c (λ _ → pure true)
