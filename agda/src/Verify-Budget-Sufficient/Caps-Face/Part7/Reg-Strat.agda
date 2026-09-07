-- Verify-Budget-Sufficient.Caps-Face.Part7.Reg-Strat
-- entStrat? … registry-entStrat
module Verify-Budget-Sufficient.Caps-Face.Part7.Reg-Strat where

open import Data.Bool using (Bool; true; _∧_; _∨_)
open import Data.Nat using (_≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Prim using (Source)
open import Rx.Evaluator using (Sched; EvalSt; Path)
open import Verify-Budget-Sufficient.Caps using (Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; pathFloor; pathStrat?)
open import Verify-Budget-Sufficient.Delivery-Walk using (regQ?)

-- THE ONE READING BOTH ENTRY FACES WANT OF THE REGISTRY, and it is
-- stated at an entry rather than at a path because half of it is about
-- the REGISTRATION.  A chain is either charged at the whole context --
-- the free half, which `pathStrat-top` settles without spending
-- anything -- or it is stratified AND its floor is at or above the
-- source it listens to.  The two travel together because the second is
-- what makes the first usable at a fan: values leaving a slot are
-- known below that slot's index, and raising a floor only weakens
-- that, so a continuation whose floor is at or above the source
-- inherits them.
entStrat? : ∀ {n} {Γ : Ctx n} {u t} → Source → Path Γ u t → Bool
entStrat? {n = n} s p =
  (n ≤ᵇ pathFloor p) ∨ (pathStrat? p ∧ (s ≤ᵇ pathFloor p))

-- WHAT IS OPEN, AND IT IS THE WHOLE OF WHAT THE TWO SITES USED TO ASK
-- SEPARATELY.  The telescope is what should supply this: a
-- sink-floored chain is registered by the CONNECT, which subscribes
-- the slot's def under `share-sink i`, so a frame the descent pushes
-- is a subterm of that def -- and `Rx.Slots.shared` admits a def only
-- with its inputs below the slot's own index, which is definitionally
-- what `frameStrat?` asks at the floor such a chain reports.  That
-- covers four of the five registration sites; the fifth subscribes an
-- observable that arrived as a VALUE, and `Val Γ (obs t)` is arbitrary
-- closed syntax the telescope never checked.
--
-- AND THE RECEIPT IS THE SUSPECT PART OF THE STATEMENT, NOT THE
-- PREDICATE.  `capsOK?` carries a length ledger over the registry and
-- nothing about stratification, so what is being asserted is that a
-- state satisfying the cap reading is one the evaluator could have
-- BUILT -- which no conjunct of that reading says.  If it turns out
-- false, the repair is a conjunct on the state predicate rather than a
-- weaker statement here: a producer obligation, cascading through
-- every site that builds a state, is the cost of the fact being true.
--
-- DEAD ROUTE: a free path quantified after the receipt cannot be
--   asked for at all, and the refutation of that form is recorded at
--   `cascade-admit-sink`'s own site -- which is why the subject here
--   is the registry the receipt is already about.
postulate
  registry-entStrat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    regQ? {t = t} (λ {u} → entStrat? {u = u}) (EvalSt.registry st) ≡ true
