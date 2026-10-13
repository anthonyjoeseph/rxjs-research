{-# OPTIONS --guardedness #-}

-- A PROGRAM TREE'S MEANING: each node replaced by its `MonotonicList`
-- function.  This exists for `Adequacy`; nobody computing with timelines
-- needs it.
--
-- The tree has no fixpoint node — its recursion is Agda's own, through
-- `defer` — so there is no `λ x → …` to hand `fixᴰ`.  Instead the meaning
-- is built the way `fixᴰ` builds one: a chain of approximants, joined by
-- `lub`.
module denotation.Denote where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Level using (lower)

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatten; connect; connected; defer)
open import denotation.MonotonicList using (MonotonicList; cold; Timeline; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flattenᴰ; deferᴰ; connectᴰ; ⊥ᴰ; lub)

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
  approx n       (cold c)         ρ = cold (lower c)
  approx n       empty            ρ = emptyᴰ
  approx n       (of xs)          ρ = ofᴰ xs
  approx n       (map f s)        ρ = mapᴰ f (approx n s ρ)
  approx n       (scan f z s)     ρ = scanᴰ f z (approx n s ρ)
  approx n       (takeWhile p s)  ρ = takeWhileᴰ p (approx n s ρ)
  approx n       (flatten op f s) ρ = flattenᴰ (flatOp op) (mapᴰ (λ a → laneᴰ n (f a) ρ) (approx n s ρ))
  approx n       (connect s b)    ρ = connectᴰ (approx n s ρ) λ r → approx n b (r ∷ ρ)
  approx n       (connected i)    ρ = lookup ρ i
  approx zero    (defer l)        ρ = ⊥ᴰ
  approx (suc n) (defer l)        ρ = deferᴰ (approx n (Later.force l) ρ)

  -- a separate function, so Agda can see the lane is a subterm
  laneᴰ : ∀ {Γ B} → ℕ → Maybe B × Maybe (Obs Timeline Γ B) → DenEnv Γ → Maybe B × Maybe (MonotonicList B)
  laneᴰ n (e , nothing) ρ = e , nothing
  laneᴰ n (e , just l)  ρ = e , just (approx n l ρ)

⟦_⟧[_] : ∀ {Γ A} → Obs Timeline Γ A → ℕ → DenEnv Γ → MonotonicList A
⟦ o ⟧[ n ] = approx n o

-- THE meaning of a program.
⟦_⟧ : ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
⟦ o ⟧ ρ = lub λ n → ⟦ o ⟧[ n ] ρ
