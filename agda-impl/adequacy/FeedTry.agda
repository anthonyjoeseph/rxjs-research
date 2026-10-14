{-# OPTIONS --guardedness --large-indices #-}
module adequacy.FeedTry where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_++_; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym)

open import denotation.MonotonicList using (Pos; ix; _<ᵖ_) renaming (sub to subᴾ)
open import denotation.Unfold using (Node; Step; step; outˢ; skipˢ; joinᶜ)
open import adequacy.Carrier using (module Carrying)

module _ (R : Set) where
  open Carrying R using (Lags; stay; skip; drop)

  -- A node reaches a step after silent steps of its own.
  data Reach {A} : Node A → Step A → Set₁ where
    now   : ∀ {c} → Reach c (step c)
    later : ∀ {c c′ k s} → step c ≡ skipˢ k c′ → Reach c′ s → Reach c s

  joinSkip : ∀ {A} j i {cp : Node A} {k c′} → step cp ≡ skipˢ k c′ → Σ Pos λ k′ → Σ ℕ λ i′ → step (joinᶜ j i cp) ≡ skipˢ k′ (joinᶜ j i′ c′)
  joinSkip j i {k = k} e rewrite e with j <ᵖ k
  ... | true  = _ , i , refl
  ... | false = _ , suc i , refl

  joinDrop : ∀ {A} j i {cp : Node A} {k a c′} → step cp ≡ outˢ k a c′ → j <ᵖ k ≡ false
           → step (joinᶜ j i cp) ≡ skipˢ (j ++ [ ix i ]) (joinᶜ j (suc i) c′)
  joinDrop j i e nl rewrite e | nl = refl

  joinOut : ∀ {A} j i {cp : Node A} {q x n} → step cp ≡ outˢ q x n → j <ᵖ q ≡ true
          → step (joinᶜ j i cp) ≡ outˢ (q ++ [ subᴾ j ]) x (joinᶜ j i n)
  joinOut j i e lt rewrite e | lt = refl

  -- A joiner whose copy is owed the value `x` at `q` shows it at
  -- `q ++ [ sub j ]`, after the silent steps its lag costs.
  joiner-delivers : ∀ {A} {j : Pos} {cp cp′ q x n} (i : ℕ) → Lags j cp cp′ → step cp′ ≡ outˢ {A} q x n → j <ᵖ q ≡ true
                  → Σ ℕ λ i′ → Reach (joinᶜ j i cp) (outˢ (q ++ [ subᴾ j ]) x (joinᶜ j i′ n))
  joiner-delivers {j = j} {cp} i stay e lt = i , subst (Reach (joinᶜ j i cp)) (joinOut j i {cp} e lt) now
  joiner-delivers {j = j} {cp} i (skip e′ l) e lt with joinSkip j i {cp} e′
  ... | k′ , i₁ , st with joiner-delivers i₁ l e lt
  ...   | i′ , r = i′ , later st r
  joiner-delivers {j = j} {cp} i (drop e′ nl l) e lt with joiner-delivers (suc i) l e lt
  ... | i′ , r = i′ , later (joinDrop j i {cp} e′ nl) r

  open import denotation.MonotonicList using (<ᵖ-trans)
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  -- A lag behind `p` is a lag behind any position at or past it: a
  -- joiner subscribed now drops the whole history.
  lags-later : ∀ {A} {p j : Pos} {c n : Node A} → p ≡ j ⊎ p <ᵖ j ≡ true → Lags p c n → Lags j c n
  lags-later le stay           = stay
  lags-later le (skip e l)     = skip e (lags-later le l)
  lags-later {p = p} {j} le (drop {q = q} e nl l) = drop e (past le nl) (lags-later le l)
    where past : p ≡ j ⊎ p <ᵖ j ≡ true → p <ᵖ q ≡ false → j <ᵖ q ≡ false
          past (inj₁ refl) nl = nl
          past (inj₂ pj)   nl with j <ᵖ q in jq
          ... | false = refl
          ... | true  with trans (sym (<ᵖ-trans p j q pj jq)) nl
          ...   | ()
