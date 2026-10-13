{-# OPTIONS --guardedness #-}

-- A PROGRAM TREE'S MEANING: each node replaced by its `MonotonicList`
-- function.  This exists for `Adequacy`; nobody computing with timelines
-- needs it.
--
-- The tree has no fixpoint node — its recursion is Agda's own, through
-- `defer` — so there is no `λ x → …` to hand `fixᴰ`.  Instead the meaning
-- is built the way `fixᴰ` builds one: a chain of approximants, joined by
-- `lub`.
module Denote where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (lower)

open import AbstractObservable using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; concatᶠ;
  cold; of; map; scan; takeWhile; merge; flatMap; share; shared; defer)
open import MonotonicList

-- A share in scope means the handle `shareᴰ` passed its body.
DenEnv : List Set → Set₁
DenEnv = All MonotonicList

flatMapᴰ : ∀ {A B} → FlatOp → (A → MonotonicList B) → MonotonicList A → MonotonicList B
flatMapᴰ mergeᶠ   = mergeMapᴰ
flatMapᴰ switchᶠ  = switchMapᴰ
flatMapᴰ exhaustᶠ = exhaustMapᴰ
flatMapᴰ concatᶠ  = concatMapᴰ

-- APPROXIMANT n: the meaning with every path of more than n nested
-- `defer`s cut off at ⊥ᴰ — `iterate`, for a tree.  Lexicographic on
-- (n , tree): `defer` drops n, everything else is structural.
⟦_⟧[_] : ∀ {Γ A} → Obs Timeline Γ A → ℕ → DenEnv Γ → MonotonicList A
⟦ o ⟧[ n ] = approx n o
  where
    approx : ∀ {Γ A} → ℕ → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
    approx n       (cold c)         ρ = cold (lower c)
    approx n       (of xs)          ρ = ofᴰ xs
    approx n       (map f s)        ρ = mapᴰ f (approx n s ρ)
    approx n       (scan f z s)     ρ = scanᴰ f z (approx n s ρ)
    approx n       (takeWhile p s)  ρ = takeWhileᴰ p (approx n s ρ)
    approx n       (merge s t)      ρ = mergeᴰ (approx n s ρ) (approx n t ρ)
    approx n       (flatMap op f s) ρ = flatMapᴰ op (λ a → approx n (f a) ρ) (approx n s ρ)
    approx n       (share s b)      ρ = shareᴰ (approx n s ρ) λ r → approx n b (r ∷ ρ)
    approx n       (shared i)       ρ = lookup ρ i
    approx zero    (defer l)        ρ = ⊥ᴰ
    approx (suc n) (defer l)        ρ = deferᴰ (approx n (Later.force l) ρ)

-- THE meaning of a program.
⟦_⟧ : ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
⟦ o ⟧ ρ = lub λ n → ⟦ o ⟧[ n ] ρ
