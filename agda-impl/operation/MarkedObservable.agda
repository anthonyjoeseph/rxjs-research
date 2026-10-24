{-# OPTIONS --guardedness #-}

-- SPIKE: THE IO RUNTIME OVER `operation.Marked`.  `operation.Observable`'s
-- driver, its colds, lock and refs reused, with the machine's job depth
-- replaced by keys.  Nothing in it knows a depth: where today's driver
-- runs the machine back down to the jobs owed before a delivery, this one
-- runs it while the least mark is earlier than the least mark before the
-- delivery.
--
-- The driver MAKES the positions IO does not have.  A cold delivering
-- during its own `subscription`, begun at `u`, delivers its i-th at
-- `u ++ [ix i]`, as a pure cold's subscribe burst does.  Any other
-- delivery comes when the machine has nothing owed, so it starts a fresh
-- root of its own, past every one before it.  Its leaves are never due:
-- what a cold makes is pushed, never scheduled.
module operation.MarkedObservable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; _∷_; []; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Pos; ix)
open import operation.Key using (Key; _<ᴷ_)
open import operation.Observable using (IORef; newIORef; readIORef; writeIORef; Lock; newLock; withLock; Signal; newSignal; raise; await; fixIO′; Started; Emit; IOCold; Slot; Observable; IORef₁; newIORef₁; readIORef₁; writeIORef₁)

private
  infixl 1 _>>_
  _>>_ : ∀ {A : Set} → IO ⊤ → IO A → IO A
  m >> n = m >>= λ _ → n

  unless : IORef Bool → IO ⊤ → IO ⊤
  unless r m = readIORef r >>= λ b → if b then pure tt else m

-- What the driver keeps at a started cold: as today's, and, while its
-- `subscription` runs, where it was begun and its next value's index.
record Leaf (A : Set) : Set₁ where
  field
    inbox : IORef (List (Maybe A))
    slot  : Slot
    burst : IORef (Maybe (Pos × ℕ))

never : ∀ {A} → Leaf A → Maybe Key
never _ = nothing

unseen : ∀ {A} → Leaf A → Maybe (Maybe A)
unseen _ = nothing

import operation.Marked
module Machine = operation.Marked IOCold Leaf never unseen
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
