-- ══════════════════════════════════════════════════════════════════
-- THE WALK'S STORE DOES NOT GROW BY ONE `nestSyn` PER DELIVERY EITHER,
-- and the ingredient is the one that hid it: a bounded limit crossed
-- with a hot slot.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  One arrival's chain walk leaves the store
-- measure no deeper than it found it plus ONE `nestSyn` per DELIVERY on
-- the evaluator's own ledger — the tight half of the width-denominated
-- growth its consumer spends, split out so that the counting question
-- could be settled statically.
--
-- WHY IT LOOKED RIGHT.  `nestSyn` is a SYNTACTIC ceiling on nesting, so
-- a delivery that stores deeper deepens the ceiling by the same step,
-- and a charge in that currency cannot be outrun by depth.  Every
-- family the store face had been read on agrees, and reads TIGHT — the
-- overshoot is a constant per delivery on both axes — which is what the
-- row was ranked on.
--
-- WHERE IT BREAKS.  A BOUNDED mergeAll parks its overflow, and the
-- DRAIN that releases it stores each released inner in turn, so ONE
-- delivery stores as many times as the drain releases while the charge
-- pays for one.  The witness reads ONE delivery and no cancellation.
--
-- WHY NO EARLIER ROW SAW IT, which is the part worth keeping.  The
-- store face's own sweep runs on two families and BOTH leave their
-- mergeAll unbounded, so nothing parks and no delivery enters a drain
-- at all; the families that bound it script a COLD slot and schedule no
-- arrival.  Neither half can reach the shape.  Crossing them is the
-- whole ingredient, and it is the same gap that hid the depth face's
-- refutation from three series at once.
--
-- THE WITNESS is `progU 2 2` — a limit-1 mergeAll over three inners, so
-- the drain fires — at the two-slot vocabulary `insF 1 2 2`, whose
-- second slot is HOT, which is what makes the program cascade at all.
-- Read at the SECOND cascade, where the drain has something to release.
-- Across the fold parameter the store after the walk reads 6, 12, 18,
-- 24, 30, 36 against a charge of 8, 10, 12, 14, 16, 18: six per fold
-- layer against two, clearing at depth one and crossing at two.
--
-- WHAT IS PINNED HERE AND WHAT IS NOT.  The slots premise is discharged
-- by construction — the statement's vocabulary is the one the run
-- carries — and the payload's nesting premise by computation, pinned
-- below.  The other two are not.  `nestOK?` does not REDUCE in the
-- typechecker though it computes fine in native code, which is the
-- ordinary consequence of a family being sealed for cost.  `capsOK?`
-- computes NOWHERE, since `capsAt` does not terminate even natively, so
-- no witness will ever discharge it.  The escape left to the statement
-- is therefore that one of those two excludes a state a real run
-- reaches.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here touches the WIDTH form the
-- consumer actually states, which this same instant clears by better
-- than an order of magnitude.  What dies is the plan to prove a
-- per-delivery form and widen it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Cascade-Nest-PerDeliv where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; cascadeGo; chainsOf; arrTy; arrVal)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ)

open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; progU; insF; sucGU)
open import Verify-Budget-Sufficient.Deliveries using (delivN)
open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; nestSyn; nestOK?; nestCapAt)

prog : Closed Γ₂ natᵗ
prog = progU 2 2

slots : Slots Γ₂
slots = insF 1 2 2

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE (gasPad (sucGU 1 2 2 2 2) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the state the FIRST cascade leaves, which is where the drain has
-- something parked
after1 : Sched Γ₂ × EvalSt prog
after1 with sched-next (proj₁ sub)
... | inj₁ _        = sub
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ sub)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the second cascade's two sides, and the two premises that compute
row : ℕ × ℕ × Bool × Bool
row with sched-next (proj₁ after1)
... | inj₁ _        = 0 , 0 , false , false
... | inj₂ (a , sd) =
  let st  = proj₂ after1
      sl  = Sched.slots sd
      stL = cascadeLatch a st
      ch  = chainsOf a st
      g   = cascadeGo a 2 ch sd stL
  in storeNestMax (proj₁ (proj₂ g)) (proj₂ (proj₂ g))
   , (storeNestMax sd stL + delivN stL (proj₂ (proj₂ g)) * nestSyn prog sl)
   , nestOK? prog sl 2 sd stL
   , (nestDᵛ (arrTy a) (arrVal a) ≤ᵇ nestCapAt prog sl 2)

-- THE FIGURES, PINNED.  Spelled out rather than left inline so that any
-- repair moving either measure fails here, naming the number, instead
-- of quietly turning the crossing into an equality
grown≡12 : proj₁ row ≡ 12
grown≡12 = refl

perDeliv≡10 : proj₁ (proj₂ row) ≡ 10
perDeliv≡10 = refl

store-val-hyp : proj₂ (proj₂ (proj₂ row)) ≡ true
store-val-hyp = refl

cascade-nest-perDeliv-absurd : proj₁ row ≤ proj₁ (proj₂ row) → ⊥
-- `12 ≤ᵇ 10` reduces to `false`, so `T` of it IS the empty type
cascade-nest-perDeliv-absurd h = ≤⇒≤ᵇ h
