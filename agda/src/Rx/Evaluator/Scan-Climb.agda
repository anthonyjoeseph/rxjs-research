------------------------------------------------------------------
-- WHAT A FOLD COSTS, PRICED IN THE ONE QUANTITY THE SYNTAX DOES NOT
-- CARRY: THE LENGTH OF THE BURST IT IS HANDED.
--
-- A fold re-enters its own template with the accumulator it last
-- produced, so the reading climbs once per delivery rather than once
-- per frame, and no figure computed from the template and the incoming
-- bound alone can dominate the outputs.  What that argument leaves
-- standing is the RATE: one delivery costs the template's own reading
-- plus the one wrap `reify` writes when the accumulator goes back into
-- the environment, and that is a constant.  So the outputs of a burst
-- of `k` deliveries sit `k` rates above where the fold started, and
-- this module proves exactly that and nothing about whether any rank
-- can afford it.
--
-- AND IT IS DENOMINATED THROUGH `reify` ON BOTH SIDES, WHICH IS WHAT
-- MAKES THE INDUCTION CLOSE.  The accumulator a step hands back is the
-- environment the next step is evaluated at, so a statement whose
-- premise reads an environment and whose conclusion reads a value
-- cannot be iterated -- the two readings differ by a wrap, and a lemma
-- that spends the wrap on the way out cannot re-supply it on the way
-- in.  Reading both ends through `reify` closes the loop and pays the
-- wrap exactly once, inside the rate.
--
-- AND THE RATE IS THE TEMPLATE'S CLOSED READING, WHICH IS EXACTLY WHAT
-- THE TEMPLATE WRITES.  A template that merely passes its accumulator
-- through reads nought at the closed bound and so costs nothing per
-- delivery, which is right: the fold does not deepen what it does not
-- wrap.  What makes that sayable is that the bound is a PARAMETER of
-- the reading, so the part a template contributes and the part it
-- inherits from its argument are two different numbers rather than one
-- sum, and only the first is a rate.
--
-- REFUTED: `Refuted.Scan-Deepens` — that no such length-free figure
--   exists, which is why the bound below carries one.
module Rx.Evaluator.Scan-Climb where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; _≤_; _+_; _*_; z≤n)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Nat.Properties using (≤-trans; +-assoc; +-monoʳ-≤;
  ⊔-lub; m≤m+n; +-identityʳ; ≤-reflexive)
open import Data.Product using (_,_; proj₁)
open import Rx.Exp using (Ctx; Val; Fn; _×ᵗ_; reify; applyFn)
open import Rx.Obs-Depth using (depᵗ)
open import Rx.Obs-Depth.Substitution using (dep-eval; dep-shiftᵗ; dep-monoᵗ)
open import Rx.Evaluator using (scanVals)

-- the rate: one delivery's worth of climb, read off the template at
-- the CLOSED bound, which is what the template writes on its own
-- account rather than what it passes through from its argument
Rate : ∀ {n} {Γ : Ctx n} {s u} → (Fin n → ℕ) → Fn Γ [] [] [] (u ×ᵗ s) u → ℕ
Rate η fn = depᵗ η 0 fn

-- ONE DELIVERY, AND THE WHOLE MECHANISM IS HERE.  The step evaluates
-- the template at an environment holding the accumulator beside the
-- input, so the evaluation lemma prices it at the template READ AT the
-- bound those two satisfy — and the shift lemma is what turns that
-- nested reading into the incoming bound plus a constant.
step-climbs : ∀ {n} {Γ : Ctx n} {s u} (η : Fin n → ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (v : Val Γ s) (a : ℕ)
  → depᵗ η 0 (reify ac) ≤ a → depᵗ η 0 (reify v) ≤ a
  → depᵗ η 0 (reify (applyFn fn (ac , v))) ≤ a + Rate η fn
step-climbs {u = u} η fn ac v a ac≤ v≤ =
  ≤-trans (dep-eval η fn ((ac , v) ∷ᵃ []ᵃ) a (⊔-lub (⊔-lub ac≤ v≤) z≤n))
          (≤-trans (dep-monoᵗ η (≤-reflexive (sym (+-identityʳ a))) fn)
                   (dep-shiftᵗ η a 0 fn))

-- THE BURST.  Every output is one of the accumulators the fold wrote,
-- so a bound climbing with the length bounds the list.
scan-climbs : ∀ {n} {Γ : Ctx n} {s u} (η : Fin n → ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) (a : ℕ)
  → depᵗ η 0 (reify ac) ≤ a
  → All (λ v → depᵗ η 0 (reify v) ≤ a) vs
  → All (λ o → depᵗ η 0 (reify o) ≤ a + length vs * Rate η fn)
        (proj₁ (scanVals fn ac vs))
scan-climbs η fn ac []       a ac≤ []ᵃ       = []ᵃ
scan-climbs η fn ac (v ∷ vs) a ac≤ (p ∷ᵃ ps) =
    ≤-trans (step-climbs η fn ac v a ac≤ p)
            (+-monoʳ-≤ a (m≤m+n (Rate η fn) (length vs * Rate η fn)))
  ∷ᵃ allClimb (scan-climbs η fn (applyFn fn (ac , v)) vs (a + Rate η fn)
                 (step-climbs η fn ac v a ac≤ p)
                 (widen ps))
  where
  -- the inputs were read under `a`, and the tail is taken under the
  -- rank one delivery further along
  widen : ∀ {ws : List _} → All (λ w → depᵗ η 0 (reify w) ≤ a) ws
        → All (λ w → depᵗ η 0 (reify w) ≤ a + Rate η fn) ws
  widen []ᵃ       = []ᵃ
  widen (q ∷ᵃ qs) = ≤-trans q (m≤m+n a (Rate η fn)) ∷ᵃ widen qs

  -- the tail's bound is stated from its own starting rank; reassociating
  -- is what turns it into one delivery's worth more of this one's
  allClimb : ∀ {os : List _}
    → All (λ o → depᵗ η 0 (reify o) ≤ (a + Rate η fn) + length vs * Rate η fn) os
    → All (λ o → depᵗ η 0 (reify o) ≤ a + length (v ∷ vs) * Rate η fn) os
  allClimb []ᵃ       = []ᵃ
  allClimb (q ∷ᵃ qs) =
    ≤-trans q (≤-reflexive (+-assoc a (Rate η fn) (length vs * Rate η fn)))
      ∷ᵃ allClimb qs
