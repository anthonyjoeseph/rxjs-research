{-# OPTIONS --guardedness #-}

-- SPIKE: A GAP BETWEEN WHEN A STEP RUNS AND WHERE ITS EVENT SITS IS
-- WHAT NEEDS PAIRS.  The engine runs a step at its key
-- (`operation.Marked`); the stepper `denotation.Unfold.step` races steps
-- by the position of the event each makes.  Where the two differ, the
-- engine and the stepper agree only if no other node holds a key in the
-- gap, which is a fact about pairs of nodes.  A failing inclusive
-- takeWhile has one: it runs at its source's key `k` and shows at
-- `k ⊕ ix 0`.
--
-- Two lanes, both keyed `q ⊕ ix 0`, the first under a takeWhile its value
-- fails.  Every node maps to its ghost (`spike.MarkedGhost.gh`), so no
-- per-node relation excludes the configuration; the engine shows the
-- first lane's value first (`engine-first`), the stepper the second's
-- (`stepper-first`), and the engine's run goes backwards in position.
-- With a value that passes, both take the older lane (`passing-agree`):
-- the tie alone is not what diverges.
module spike.MarkedGap where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (empty; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; ix; root)
open import denotation.Unfold using (outˢ) renaming (Step to Stepᵁ; step to stepᵁ)
open import operation.MarkedPure using (module Machine; module Driver)
open Machine using (St; ofS; doneS; lnS; takeS; flatS; free; top; Conf; ⟨_,_,_,_⟩; absorbed)
open import spike.MarkedGhost using (gh)
open Driver ℕ using (silent; value; complete; drained; step)

private
  q : Pos
  q = root

  -- Two lanes subscribed at `q`, the first under a takeWhile of `ok`.
  lanes : (ℕ → Bool) → St [] ℕ
  lanes ok = flatS (mergeᶠ nothing) (λ (_ : ℕ) → empty) false 2 [] doneS
    (lnS true (takeS true ok free (ofS 0 q (1 ∷ []))) ∷ lnS true (ofS 0 q (2 ∷ [])) ∷ [])

  -- The engine's first value, within `n` steps.
  firstᴱ : ℕ → Conf ℕ → Maybe ℕ
  firstᴱ zero    k = nothing
  firstᴱ (suc n) k with step k
  ... | silent t k′    = firstᴱ n k′
  ... | value t p a k′ = just a
  ... | complete p     = nothing
  ... | drained        = nothing

  -- The stepper's first step, if it shows a value.
  firstᵁ : Stepᵁ [] ℕ → Maybe ℕ
  firstᵁ (outˢ k a n) = just a
  firstᵁ _            = nothing

  at₀ : (ℕ → Bool) → Conf ℕ
  at₀ ok = ⟨ top , lanes ok , absorbed , q ⟩

engine-first : firstᴱ 10 (at₀ (λ _ → false)) ≡ just 1
engine-first = refl

stepper-first : firstᵁ (stepᵁ (gh (lanes (λ _ → false)))) ≡ just 2
stepper-first = refl

passing-agree : firstᴱ 10 (at₀ (λ _ → true)) ≡ firstᵁ (stepᵁ (gh (lanes (λ _ → true))))
passing-agree = refl
