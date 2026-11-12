{-# OPTIONS --guardedness #-}

-- EVERY PROGRAM IS CARRIED, by induction on it: each former carries when
-- its children do (`simultaneous.Carry`, `simultaneous.CarryScan`), a
-- `defer` by its unfolding depth: each approximant is carried, never the
-- meaning.
module simultaneous.Carried where

import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Carry using (Carry; carry-cold; carry-map; carry-flatMap; carry-connect)
open import simultaneous.CarryReader using (carry-connected)
open import simultaneous.CarryLeaves using (carry-empty; carry-of)
open import simultaneous.CarryDefer using (carry-⊥; carry-next)
open import simultaneous.CarryScan using (carry-scan)
open import simultaneous.CarryTake using (carry-takeWhile)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE)

carry-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → Carry n ρ o
carry-approx n       ρ (cold c)          = carry-cold n ρ c
carry-approx n       ρ empty             = carry-empty n ρ
carry-approx n       ρ (of xs)           = carry-of n ρ xs
carry-approx n       ρ (map f s)         = carry-map n ρ f s (carry-approx n ρ s)
carry-approx n       ρ (scan f z s)      = carry-scan n ρ f z s (carry-approx n ρ s)
carry-approx n       ρ (takeWhile i p s) = carry-takeWhile n ρ i p s (carry-approx n ρ s)
carry-approx n       ρ (flatMap op f s)  = carry-flatMap n ρ op f s (carry-approx n ρ s) λ a ρ′ → carry-approx n ρ′ (f a)
carry-approx n       ρ (connect s b)     = carry-connect n ρ s b (carry-approx n ρ s) λ ρ′ → carry-approx n ρ′ b
carry-approx n       ρ (connected i)     = carry-connected n ρ i
carry-approx zero    ρ (defer l)         = carry-⊥ ρ l
carry-approx (suc n) ρ (defer l)         = carry-next n ρ l (carry-approx n ρ (Later.force l))
