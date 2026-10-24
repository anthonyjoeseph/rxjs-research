{-# OPTIONS --guardedness #-}

-- SPIKE: A TIE IS BROKEN BY WHERE THE EVENT SITS.  A failing inclusive
-- takeWhile runs at its source's key `k` and shows at `k ⊕ ix 0`, and
-- nothing lies strictly between, so it differs from the stepper
-- (`denotation.Unfold.step`) only against another node keyed at `k`.
-- Two lanes keyed `q ⊕ ix 0`, the first under a takeWhile its value
-- fails, every node mapping to its ghost (`spike.MarkedGhost.gh`): the
-- engine keys each candidate where its event sits as its parent sees it
-- (`operation.Marked.seek`), so it shows the second lane's value first,
-- as the stepper does (`failing-agree`); with a value that passes, both
-- take the older lane (`passing-agree`).
module spike.MarkedGap where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (empty; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; root)
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

failing-agree : firstᴱ 10 (at₀ (λ _ → false)) ≡ firstᵁ (stepᵁ (gh (lanes (λ _ → false))))
failing-agree = refl

passing-agree : firstᴱ 10 (at₀ (λ _ → true)) ≡ firstᵁ (stepᵁ (gh (lanes (λ _ → true))))
passing-agree = refl
