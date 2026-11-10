{-# OPTIONS --guardedness #-}

-- EVERY PROGRAM IS CARRIED, by induction on it: each former carries when
-- its children do (`simultaneous.Carry`, `simultaneous.CarryScan`), a
-- `defer` through its approximants.
module simultaneous.Carried where

import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Carry using (Carry; carry-cold; carry-empty; carry-of; carry-map; carry-takeWhile; carry-flatMap; carry-connect;
  carry-connected; carry-⊥; carry-next; carry-lim)
open import simultaneous.CarryScan using (carry-scan)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (AIE)

carry-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → Carry (just n) ρ o
carry-approx n       ρ (cold c)          = carry-cold (just n) ρ c
carry-approx n       ρ empty             = carry-empty (just n) ρ
carry-approx n       ρ (of xs)           = carry-of (just n) ρ xs
carry-approx n       ρ (map f s)         = carry-map (just n) ρ f s (carry-approx n ρ s)
carry-approx n       ρ (scan f z s)      = carry-scan (just n) ρ f z s (carry-approx n ρ s)
carry-approx n       ρ (takeWhile i p s) = carry-takeWhile (just n) ρ i p s (carry-approx n ρ s)
carry-approx n       ρ (flatMap op f s)  = carry-flatMap (just n) ρ op f s (carry-approx n ρ s) λ a ρ′ → carry-approx n ρ′ (f a)
carry-approx n       ρ (connect s b)     = carry-connect (just n) ρ s b (carry-approx n ρ s) λ ρ′ → carry-approx n ρ′ b
carry-approx n       ρ (connected i)     = carry-connected (just n) ρ i
carry-approx zero    ρ (defer l)         = carry-⊥ ρ l
carry-approx (suc n) ρ (defer l)         = carry-next n ρ l (carry-approx n ρ (Later.force l))

carry-⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → Carry nothing ρ o
carry-⟦⟧ ρ (cold c)          = carry-cold nothing ρ c
carry-⟦⟧ ρ empty             = carry-empty nothing ρ
carry-⟦⟧ ρ (of xs)           = carry-of nothing ρ xs
carry-⟦⟧ ρ (map f s)         = carry-map nothing ρ f s (carry-⟦⟧ ρ s)
carry-⟦⟧ ρ (scan f z s)      = carry-scan nothing ρ f z s (carry-⟦⟧ ρ s)
carry-⟦⟧ ρ (takeWhile i p s) = carry-takeWhile nothing ρ i p s (carry-⟦⟧ ρ s)
carry-⟦⟧ ρ (flatMap op f s)  = carry-flatMap nothing ρ op f s (carry-⟦⟧ ρ s) λ a ρ′ → carry-⟦⟧ ρ′ (f a)
carry-⟦⟧ ρ (connect s b)     = carry-connect nothing ρ s b (carry-⟦⟧ ρ s) λ ρ′ → carry-⟦⟧ ρ′ b
carry-⟦⟧ ρ (connected i)     = carry-connected nothing ρ i
carry-⟦⟧ ρ (defer l)         = carry-lim ρ l λ n → carry-approx n ρ (defer l)
