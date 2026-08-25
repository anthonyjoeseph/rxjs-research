-- ══════════════════════════════════════════════════════════════════
-- THE PER-FRAME CHARGE DOES NOT SURVIVE A STEP FUNCTION THAT NAMES ITS
-- PAYLOAD TWICE, and this is the consumer-level half of the finding
-- `Refuted.Apply-Fn-Nest` states at the substitution.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  One frame moves its node and the values it
-- hands on together, by its own wrap: the pair after the step is under
-- the pair before it, plus `frameNestD` -- which at a map frame is the
-- step function's own nesting, and is what `pathNestD` telescopes.
--
-- WHY IT LOOKED RIGHT.  A variable weighs nothing, so a map frame
-- appears to hand on exactly what it was given, wrapped by whatever the
-- step function wraps around it; and the walk above needs precisely
-- that shape to telescope with nothing left over at either end.
--
-- WHERE IT BREAKS.  `nestDᵉ` is additive at `mapᵉ`, so a step function
-- naming its payload on both sides of one -- as the source list and as
-- the mapped result -- emits a value the measure reads at TWICE the
-- payload's own nesting, against a `frameNestD` of zero.  Nothing about
-- the node arm is involved: the map frame touches no node, and the
-- emission half alone is over.
--
-- THE WITNESS is that step function at a payload forty `*All` layers
-- deep: eighty against forty.  Doubling is the whole content, so the
-- gap grows without bound in the payload and no constant charge can
-- close it.
--
-- WHAT DIES AND WHAT DOES NOT.  The additive per-frame charge dies at
-- the map arm, and the telescope above it with it.  The dynamics are
-- untouched -- the value really emitted is forty layers deep, not
-- eighty -- so what is refuted is the MEASURE's additivity under
-- duplication, and the repair the numbers point at is a per-frame
-- FACTOR the syntax can see rather than a summand.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Step-Frame-Nest-Dup where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Fn; Val; natᵗ; obs; applyFn;
         ofᵉ; mapᵉ; switchAllᵉ; varᵗ; nat̂; strmᵗ)
open import Rx.Evaluator using (map-f)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; frameNestD)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

-- a payload k `*All` layers deep
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the step function names its payload TWICE: once as the list its
-- source emits, once as the value the map returns
dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dupFn = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

row : ℕ × ℕ
row = let v = deepV 40
      in nestDᵛˢ (map (applyFn dupFn) (v ∷ []))
       , nestDᵛˢ (v ∷ []) + frameNestD (map-f dupFn)

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
dup≡80 : proj₁ row ≡ 80
dup≡80 = refl

perFrame≡40 : proj₂ row ≡ 40
perFrame≡40 = refl

stepFrame-nest-dup-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `80 ≤ᵇ 40` reduces to `false`, so `T` of it IS the empty type
stepFrame-nest-dup-absurd h = ≤⇒≤ᵇ h
