{-# OPTIONS --guardedness #-}

-- Witness: a steady source stepping and then emitting at one position,
-- cut at that value, showing it just inside the step.
module adequacy.Refute-Tie where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; _≢_)

open import Tree using (Obs; takeWhile; connected)
open import denotation.MonotonicList using (Events; Events∞; Timeline; ix; skip; out; hush)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Placed using (Sorted; Alienᴱ; Steady; steady; ordered; every; ext)

open Events∞

-- A skip and then a value at `[ ix 1 ]`: in order, and steady, a skip
-- being apart from what sits at its own position.
S : Events ℕ
S = skip (ix 1 ∷ []) λ where .force → out (ix 1 ∷ []) 0 λ where .force → hush

ρ : NEnv (ℕ ∷ [])
ρ = S ∷ᴬ []ᴬ

sorted : Sorted ρ
sorted = (record { ordered = refl , record { ordered = tt , record { ordered = tt } } }
         , record { steady = (λ ()) , record { steady = tt , record { steady = tt } } }) , tt

alien : Alienᴱ (ix 0 ∷ []) ρ
alien = record { every = no , record { every = no , record { every = tt } } } , tt
  where no = λ { (inj₁ (() , _)) ; (inj₂ ()) }

steady-refuted : (∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
                   → Steady (U.meaning (U.subscribe o p) ρ)) → ⊥
steady-refuted h = proj₁ (steady (h (takeWhile true (λ _ → false) (connected (here refl))) (ix 0 ∷ []) ρ (λ ()) sorted alien)) (ext (ix 0) [])
