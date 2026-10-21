{-# OPTIONS --guardedness #-}
module adequacy.Refute.ShyApart where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList.Events using (end; last)
import denotation.Unfold as U
open import adequacy.Placed.Order using (Ordered; ordered)
open import adequacy.Stepper using (shy-apart)

-- A body and its source both ending at the one position, `[ last ]`.
ord : Ordered {ℕ} (end (last ∷ []))
ord .ordered = tt

refuted : ⊥
refuted = proj₁ (shy-apart {ν = []ᴬ} (U.ofᶜ [] 0 []) (U.ofᶜ [] 0 []) []ᴬ tt tt (ord , tt) (ord , tt) refl (last ∷ []) refl (last ∷ []) refl) refl
