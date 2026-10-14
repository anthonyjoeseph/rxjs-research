{-# OPTIONS --guardedness #-}

-- A PROGRAM TREE'S APPROXIMANTS: each node replaced by its
-- `MonotonicList` function, every path through more than n `defer`s cut
-- off at ⊥ᴰ.  The meaning itself is `denotation.Unfold`'s; these are the
-- tests' per-node reference (`quickcheck.Ghost`, `quickcheck.Chain`).
module denotation.Denote where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (lower)

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (MonotonicList; coldᴰ; Timeline; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flatMapᴰ; deferᴰ; connectᴰ; ⊥ᴰ)

-- A connect in scope means the handle `connectᴰ` passed its body.
DenEnv : List Set → Set₁
DenEnv = All MonotonicList

-- The tree and the library each declare the same policies.
flatOp : T.FlatOp → FlatOp
flatOp (T.mergeᶠ k) = mergeᶠ k
flatOp T.switchᶠ    = switchᶠ
flatOp T.exhaustᶠ   = exhaustᶠ

-- APPROXIMANT n: the meaning with every path of more than n nested
-- `defer`s cut off at ⊥ᴰ — `iterate`, for a tree.  Lexicographic on
-- (n , tree): `defer` drops n, everything else is structural.
mutual
  approx : ∀ {Γ A} → ℕ → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
  approx n       (cold c)         ρ = coldᴰ (lower c)
  approx n       empty            ρ = emptyᴰ
  approx n       (of xs)          ρ = ofᴰ xs
  approx n       (map f s)        ρ = mapᴰ f (approx n s ρ)
  approx n       (scan f z s)     ρ = scanᴰ f z (approx n s ρ)
  approx n       (takeWhile i p s) ρ = takeWhileᴰ i p (approx n s ρ)
  approx n       (flatMap op f s) ρ = flatMapᴰ (flatOp op) (λ a → approx n (f a) ρ) (approx n s ρ)
  approx n       (connect s b)    ρ = connectᴰ (approx n s ρ) λ r → approx n b (r ∷ ρ)
  approx n       (connected i)    ρ = lookup ρ i
  approx zero    (defer l)        ρ = ⊥ᴰ
  approx (suc n) (defer l)        ρ = deferᴰ (approx n (Later.force l) ρ)

⟦_⟧[_] : ∀ {Γ A} → Obs Timeline Γ A → ℕ → DenEnv Γ → MonotonicList A
⟦ o ⟧[ n ] = approx n o
