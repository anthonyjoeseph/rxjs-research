------------------------------------------------------------------
-- THE CEILING AN ARRIVAL CANNOT LEAVE, AND WHY THE NEST FACE NEEDS
-- ONE SEPARATE FROM ITS CAP.
--
-- The nest walk reads every arrival at the head's own written cap,
-- and that reading is false: an arrival is the head's syntax with the
-- payload SUBSTITUTED IN, so a step function naming its payload twice
-- hands back about twice the payload while contributing a constant to
-- the head.  One substitution is the caps face's own size step, and a
-- descent performs at most the head's size of them, so a ceiling that
-- steps the cap that many times dominates everything the run can
-- reach -- including an arrival's own arrivals, because the hops are
-- counted against the head and not against the ceiling.
--
-- THAT IS WHAT MAKES IT FLAT.  The alternative device is a LEVEL, an
-- index stepped at each substituting frame, which is what the caps
-- face carries and what costs an existential in every conclusion.
-- Here the count is bounded once, at the head, so the walk threads a
-- plain number that never moves: the cap keeps bounding the head and
-- the ceiling bounds everything the head can produce.
--
-- AND IT IS SEALED, because it lands in premises the walk carries
-- through every recursive call.  The two lemmas below are the whole
-- interface: the ceiling is above the cap, and it is above one
-- descent's worth of steps from the cap.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Sub where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤ᵇ⇒≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Decide using (∧-trueˡ; ∧-trueʳ; T-to)

open import Rx.Evaluator using (iterSize)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; iterSize-infl)

-- THE ARRIVAL-SIDE CAP, which is the walk's own cap with its size
-- field replaced.  The width and the registration count are the
-- state's business and an arrival changes neither, so only the size
-- moves -- and a widened width would weaken the queue conjunct the
-- room record owes upward.
subCaps : ℕ → Caps → Caps
subCaps Ŝ c = caps Ŝ (Caps.cWid c) (Caps.cReg c)

abstract
  -- one substituting frame's worth of growth, at the size it is
  -- growing from: the frame's own syntax is inside that size, so the
  -- count and the base are the same quantity
  towStep : ℕ → ℕ
  towStep s = iterSize s s s

  -- and the ceiling after `j` more of them, which is the shape the
  -- walk threads: one hop is spent at every substituting frame, and
  -- what the premise says is that the hops still to come fit under
  -- the ceiling the entry chose.
  tow : ℕ → ℕ → ℕ
  tow zero    s = s
  tow (suc k) s = tow k (towStep s)

  tow-step : ∀ (j s : ℕ) → tow (suc j) s ≡ tow j (towStep s)
  tow-step j s = refl

  1≤towStep : ∀ (s : ℕ) → 1 ≤ s → 1 ≤ towStep s
  1≤towStep s h = ≤-trans h (iterSize-infl s h s s)

  s≤towStep : ∀ (s : ℕ) → 1 ≤ s → s ≤ towStep s
  s≤towStep s h = iterSize-infl s h s s

  tow-infl : ∀ (j s : ℕ) → 1 ≤ s → s ≤ tow j s
  tow-infl zero    s h = ≤-refl
  tow-infl (suc j) s h =
    ≤-trans (s≤towStep s h) (tow-infl j (towStep s) (1≤towStep s h))

-- THE WALK'S OWN CLOSURE PREMISE: the cap the head is read at, and the
-- ceiling everything the head can reach is read at.  Both conjuncts
-- are spent -- the first widens a frame's key from the head's cap to
-- the ceiling, the second is what makes the arrival statements true --
-- and the first is kept rather than derived because deriving it wants
-- the cap to be positive, which is a premise the walk does not carry.
nestSubOK? : ℕ → Caps → Caps → Bool
nestSubOK? j c₀ c =
  (Caps.cSize c₀ ≤ᵇ Caps.cSize c) ∧ (tow j (Caps.cSize c₀) ≤ᵇ Caps.cSize c)

abstract
  nestSubOK?-cap : ∀ (j : ℕ) (c₀ c : Caps) → nestSubOK? j c₀ c ≡ true →
    Caps.cSize c₀ ≤ Caps.cSize c
  nestSubOK?-cap j c₀ c h = ≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ h))

  nestSubOK?-tow : ∀ (j : ℕ) (c₀ c : Caps) → nestSubOK? j c₀ c ≡ true →
    tow j (Caps.cSize c₀) ≤ Caps.cSize c
  nestSubOK?-tow j c₀ c h = ≤ᵇ⇒≤ _ _ (T-to (∧-trueʳ h))
