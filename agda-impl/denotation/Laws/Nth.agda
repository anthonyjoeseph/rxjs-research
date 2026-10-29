-- AN OUTER'S VALUES IN ORDER.  The i-th value is a value of the outer,
-- one position has one index, and the value at an indexed position can be
-- any value there.
module denotation.Laws.Nth where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (<-cmp; m<1+n⇒m<n∨m≡n)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.EmissionSet using (EmissionSet; out; _≺_; module Values)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≼-antisym)

module Nths {A : Set} (O : EmissionSet A) where
  open Values O using (Nth; first; next)

  nth-val : ∀ {i q a} → Nth i q a → O q (out a)
  nth-val (first x _)    = x
  nth-val (next _ x _ _) = x

  nth-at : ∀ {i q a a′} → Nth i q a′ → O q (out a) → Nth i q a
  nth-at (first _ m)       x = first x m
  nth-at (next N _ lt nx)  x = next N x lt nx

  nth-fun : ∀ {i q q′ a a′} → Nth i q a → Nth i q′ a′ → q ≡ q′
  nth-fun {q = q} {q′} (first x m) (first x′ m′) = ≼-antisym {q} {q′} (m x′) (m′ x)
  nth-fun {q = q} {q′} (next nq x lt nx) (next nq′ x′ lt′ nx′) with nth-fun nq nq′
  ... | refl = ≼-antisym {q} {q′} (nx x′ lt′) (nx′ x lt)

  nth-lt : ∀ {i i′ q q′ a a′} → i < i′ → Nth i q a → Nth i′ q′ a′ → q ≺ q′
  nth-lt {q = q} {q′} lt nq (next {q = q₀} nq′ _ lt′ _) with m<1+n⇒m<n∨m≡n lt
  ... | inj₁ lt″ = ≺-trans {q} {q₀} {q′} (nth-lt lt″ nq nq′) lt′
  ... | inj₂ refl with nth-fun nq nq′
  ...   | refl = lt′

  nth-inj : ∀ {i i′ q a a′} → Nth i q a → Nth i′ q a′ → i ≡ i′
  nth-inj {i} {i′} {q} nq nq′ with <-cmp i i′
  ... | tri< lt _ _ = ⊥-elim (≺-irrefl {q} (nth-lt lt nq nq′))
  ... | tri≈ _ eq _ = eq
  ... | tri> _ _ gt = ⊥-elim (≺-irrefl {q} (nth-lt gt nq′ nq))
