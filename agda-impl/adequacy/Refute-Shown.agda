{-# OPTIONS --guardedness #-}

-- Witness: a connect's cut, at its source's first step, pins the
-- source's next burst step `q`, which the connect then shows at
-- `q ++ [ ix 0 ]`.
module adequacy.Refute-Shown where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; connect; of; connected)
open import denotation.MonotonicList.Events using (Timeline; ix)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Finite using (Finite; connect-f; connected-f; of-f)
open import adequacy.Placed.Order using (Alienᴱ; Every; Every∞; Headed; Owned; Sorted; every; everyᵀ)

o : Obs Timeline [] ℕ
o = connect (of (0 ∷ 1 ∷ [])) (connected (here refl))

shown-refuted : (∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                  → Every (λ k → Every∞ (λ q → ¬ Owned (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe o p) ρ)) (U.meaning (U.subscribe o p) ρ))
              → ⊥
shown-refuted h = proj₁ (everyᵀ (proj₂ (proj₂ (every (proj₁ third))))) (inj₁ (refl , refl , refl , refl , tt))
  where
    E     = h o (connect-f (of-f _) (connected-f _)) (ix 0 ∷ []) []ᴬ tt tt tt
    E₂    = proj₁ (proj₂ (every E))
    E₃    = proj₁ (proj₂ (every E₂))
    third = proj₁ (every E₃)
