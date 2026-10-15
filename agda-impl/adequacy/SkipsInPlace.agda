{-# OPTIONS --guardedness #-}

-- `≃` with a matched skip kept in place is not transitive: two runs of
-- skips at disjoint positions are each alike their interleaving.
module adequacy.SkipsInPlace where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤)

open import denotation.MonotonicList using (Events; Events∞; skip; ix)
open import adequacy.Content using (_≃_; _≃∞_; skip≃; skipˡ; skipʳ)

open Events∞
open _≃∞_

xs zs : ℕ → Events ⊤
xs n = skip (ix n ∷ ix 0 ∷ []) λ where .force → xs (suc n)
zs n = skip (ix n ∷ ix 1 ∷ []) λ where .force → zs (suc n)

mutual
  ya yb : ℕ → Events ⊤
  ya n = skip (ix n ∷ ix 0 ∷ []) λ where .force → yb n
  yb n = skip (ix n ∷ ix 1 ∷ []) λ where .force → ya (suc n)

xy : ∀ n → xs n ≃ ya n
xy n = skip≃ λ where .≃force → skipʳ (xy (suc n))

yz : ∀ n → ya n ≃ zs n
yz n = skipˡ (skip≃ λ where .≃force → yz (suc n))

apart : ∀ m n → xs m ≃ zs n → ⊥
apart m n (skipˡ r) = apart (suc m) n r
apart m n (skipʳ r) = apart m (suc n) r

refuted : (∀ {x y z : Events ⊤} → x ≃ y → y ≃ z → x ≃ z) → ⊥
refuted trans = apart 0 0 (trans (xy 0) (yz 0))
