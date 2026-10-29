{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  `operation.AbstractObservable`'s machine, driven by
-- the world: user-written colds that may perform IO feed it their
-- emissions, and what it shows and tears down is done for real.  Every
-- transition is the one the pure runtime (`operation.PureObservable`)
-- takes; only the driver is unproven, and it is checked against the
-- TypeScript by the oracle.
--
-- Nothing is coerced.  The driver keeps no typed state of its own: a
-- cold's emissions wait in its own leaf's inbox, and the cold names its
-- leaf by path, so each is read at the leaf's type.
--
-- The runtime keeps no clock and no timers.  What happens later is a
-- cold's own business — its own thread, its own delays — and it reaches
-- the machine only through what it is handed: `produce`, `complete`,
-- `closed`.
--
-- DELIVERY IS ATOMIC PER SUBSCRIPTION.  A cold may `produce` from any
-- thread, and any interleaving of emissions is legal; a state no
-- interleaving produces is not.  So every entry into the engine — the
-- subscribe burst, a `produce`, a `complete` — runs whole under
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
-- The driver's recursion — running the machine until it is calm — is
-- closed with `fixIO`, exported for colds that loop.  Every fixpoint it
-- takes is an IO action: one may run forever, but none is a value of any
-- other type, so nothing proves anything with it.
--
-- Before a delivery the driver runs the machine while the least mark is
-- earlier than the least mark before the delivery.
--
-- The driver MAKES the positions IO does not have.  A cold delivering
-- during its own `subscription`, begun at `u`, delivers its i-th at
-- `u ++ [ix i]`, as a pure cold's subscribe burst does.  Any other
-- delivery comes when the machine has nothing owed, so it starts a fresh
-- root of its own, past every one before it.  Its leaves are never due:
-- what a cold makes is pushed, never scheduled.
module operation.Observable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; _∷_; []; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)

open import denotation.Events using (Pos; ix)
open import operation.Key using (Key; _<ᴷ_)
open import Tree using (Obs)

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
-- one export, `fixIO`, takes fixpoints of IO actions only.
private
  module FixIO where
    private
      postulate
        fixᴴ : ∀ {a} {A : Set a} → (A → A) → A
    {-# COMPILE GHC fixᴴ = \ _ _ -> Data.Function.fix #-}

    fixIO : ∀ {a b} {X : Set a} {Y : X → Set b} → ((∀ x → IO (Y x)) → ∀ x → IO (Y x)) → ∀ x → IO (Y x)
    fixIO = fixᴴ

open FixIO public using (fixIO)

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

-- A wake-up: raised any number of times, it is taken once.
postulate
  Signal    : Set
  newSignal : IO Signal
  raise     : Signal → IO ⊤
  await     : Signal → IO ⊤

{-# COMPILE GHC Signal = type Control.Concurrent.MVar.MVar () #-}
{-# COMPILE GHC newSignal = Control.Concurrent.MVar.newEmptyMVar #-}
{-# COMPILE GHC raise = \ s -> () <$ Control.Concurrent.MVar.tryPutMVar s () #-}
{-# COMPILE GHC await = Control.Concurrent.MVar.takeMVar #-}

-- A thread of its own, for a cold whose emissions come later.
postulate
  forkIO : IO ⊤ → IO ⊤

{-# COMPILE GHC forkIO = \ a -> () <$ Control.Concurrent.forkIO a #-}

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
-- synchronous burst.  A `produce` from a thread it started is an async
-- emission.  `teardown` runs once, on completion or unsubscribe; after
-- it, `produce` and `complete` are ignored.
record Started (Internal : Set) : Set where
  field
    subscription : IO Internal
    teardown     : Internal → IO ⊤

-- What a cold is handed: rxjs's subscriber.  `closed` is
-- `subscriber.closed`, for a producer that would otherwise loop forever.
record Emit (A : Set) : Set where
  field
    produce  : A → IO ⊤
    complete : IO ⊤
    closed   : IO Bool

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

-- What the driver keeps at a started cold: what it has made and the
-- machine not yet taken in, oldest first — a value, or `nothing` for its
-- completion — its slot, and, while its `subscription` runs, where it
-- was begun and its next value's index.
record Leaf (A : Set) : Set₁ where
  field
    inbox : IORef (List (Maybe A))
    slot  : Slot
    burst : IORef (Maybe (Pos × ℕ))

never : ∀ {A} → Leaf A → Maybe Key
never _ = nothing

unseen : ∀ {A} → Leaf A → Maybe (Maybe A)
unseen _ = nothing

import operation.AbstractObservable
module Machine = operation.AbstractObservable IOCold Leaf never unseen
open Machine using (Conf; Stepped; moved; starting; turn; quiet; Shown; Torn; Ev; nx; cp; load; Poke; gone; leaf; poke; spot; calm; next)
  renaming (step to stepᴹ)

record Loop (R : Set) : Set where
  field
    lock  : Lock
    conf  : IORef₁ (Conf R)
    roots : IORef ℕ

private
  atomically : ∀ {R a} {X : Set a} → Loop R → IO X → IO X
  atomically lp = withLock (Loop.lock lp)

  runTeardown : Slot → IO ⊤
  runTeardown sl = readIORef (Slot.tearDown sl) >>= λ where
    nothing  → pure tt
    (just t) → writeIORef (Slot.tearDown sl) nothing >> t

-- Whether the least mark still runs under a bound: under none, while any
-- is owed; else while it is earlier than the bound.
below : Maybe Key → Maybe Key → Bool
below _        nothing  = false
below nothing  (just _) = true
below (just b) (just k) = k <ᴷ b

module Drive {R : Set} (lp : Loop R) (c : IO ⊤) where
  data Call : Set where
    settling : Maybe Key → Call
    pulse    : List ℕ → Call

  asked : Poke R → Bool
  asked gone              = true
  asked (leaf b _ cl _ _) = not b ∨ cl

  ask : List ℕ → IO Bool
  ask π = readIORef₁ (Loop.conf lp) >>= λ k → pure (asked (poke π k))

  shown : Shown R → IO ⊤
  shown []               = pure tt
  shown ((_ , nx a) ∷ s) = shown s
  shown ((_ , cp) ∷ s)   = c >> shown s

  tear : Torn → IO ⊤
  tear []             = pure tt
  tear ((_ , l) ∷ ls) = writeIORef (Slot.spent (Leaf.slot l)) true >> runTeardown (Leaf.slot l) >> tear ls

  push : ∀ {A} → Leaf A → Maybe A → IO ⊤
  push l e = readIORef (Leaf.inbox l) >>= λ es → writeIORef (Leaf.inbox l) (es ++ e ∷ [])

  -- Where a delivery goes: in its cold's subscribe burst, or a fresh root.
  placed : ∀ {A} → Leaf A → IO Pos
  placed l = readIORef (Leaf.burst l) >>= λ where
    (just (u , i)) → writeIORef (Leaf.burst l) (just (u , suc i)) >> pure (u ++ [ ix i ])
    nothing        → readIORef (Loop.roots lp) >>= λ n → writeIORef (Loop.roots lp) (suc n) >> pure [ ix (suc n) ]

  delivered : ∀ {A} → (Ev A → Leaf A → Bool → Pos → Conf R) → Leaf A → Maybe A → Pos → Conf R
  delivered dv l (just a) p = dv (nx a) l true p
  delivered dv l nothing  p = dv cp l false p

  module Body (self : Call → IO ⊤) where
    settle : Maybe Key → IO ⊤
    settle b = self (settling b)

    started : ∀ {A} → IOCold A → Pos → (Leaf A → Conf R) → Maybe Key → IO ⊤
    started x u k b =
      newIORef [] >>= λ ib → newIORef false >>= λ sp → newIORef nothing >>= λ td → newIORef (just (u , 0)) >>= λ bs →
      let sl = record { spent = sp ; tearDown = td }
          l  = record { inbox = ib ; slot = sl ; burst = bs }
          k′ = k l
          π  = spot k′
          st = IOCold.create x (record
            { produce  = λ a → atomically lp (unless sp (push l (just a) >> self (pulse π)))
            ; complete = atomically lp (unless sp (push l nothing >> self (pulse π) >> runTeardown sl))
            ; closed   = atomically lp (readIORef sp >>= λ d → if d then pure true else ask π) })
      in writeIORef₁ (Loop.conf lp) k′ >>
         Started.subscription st >>= λ i →
         writeIORef bs nothing >>
         writeIORef td (just (Started.teardown st i)) >>
         readIORef sp >>= λ d → (if d then runTeardown sl else pure tt) >>
         settle b

    taken : Stepped R → Maybe Key → IO ⊤
    taken (moved k s t)    b = writeIORef₁ (Loop.conf lp) k >> shown s >> tear t >> settle b
    taken (starting x u k) b = started x u k b
    taken (turn _)         b = pure tt
    taken quiet            b = pure tt

    -- The oldest thing a cold made, delivered if the cold is still live;
    -- the machine then run while what it owes is earlier than what it
    -- owed before.
    pulsed : Maybe Key → Poke R → IO ⊤
    pulsed b gone                = pure tt
    pulsed b (leaf v l cl dv st) = readIORef (Leaf.inbox l) >>= λ where
      []       → pure tt
      (e ∷ es) → writeIORef (Leaf.inbox l) es >>
                 (if v then placed l >>= (λ p → writeIORef₁ (Loop.conf lp) (delivered dv l e p) >> settle b) else pure tt)

    call : Call → IO ⊤
    call (settling b) = readIORef₁ (Loop.conf lp) >>= λ k →
      if calm k ∧ not (below b (next k)) then pure tt else taken (stepᴹ k) b
    call (pulse π)    = readIORef₁ (Loop.conf lp) >>= λ k → if calm k then pulsed (next k) (poke π k) else pure tt

  drive : Call → IO ⊤
  drive = fixIO′ Body.call

-- THE ENTRY POINT, as `operation.Observable.subscribe`.
subscribe : ∀ {A} → Observable A → IO ⊤
subscribe o =
  newLock >>= λ lk → newSignal >>= λ wk → newIORef false >>= λ fin → newIORef₁ (load o) >>= λ k → newIORef 0 >>= λ rs →
  let lp = record { lock = lk ; conf = k ; roots = rs } in
  withLock lk (Drive.drive lp (writeIORef fin true >> raise wk) (Drive.settling nothing)) >>
  readIORef fin >>= λ d → if d then pure tt else await wk
