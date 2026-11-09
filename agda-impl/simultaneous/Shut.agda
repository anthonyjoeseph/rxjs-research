{-# OPTIONS --guardedness #-}

-- A DEAD INSTANT STAYS DEAD, read off a stream's rows.  Every stream's
-- emits are counted alike (`count`): a begin adds a route, a stop takes
-- one, an over ends them all, a begin of a new name starts afresh.  Once
-- a run's count holds no route of the instant it last began, no value of
-- that instant follows: every route of a live instant reaches the stream
-- as a begin, and leaves it as a stop only once nothing below can carry
-- the instant on.
module simultaneous.Shut where

open import Data.List using (_++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Events using (Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; out)
open import simultaneous.InstEmit using (instEmit; value; mark; begin)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Met; values)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count)

-- No route yet.
r₀ : Routes
r₀ = root , 0

-- Past a point where the run's count holds no route of the instant it
-- last began, no value of that instant.
Shut : ∀ {A : Set} → EmissionSet (IE A) → Set
Shut t = ∀ {rs} → Met t rs → ∀ r₁ r₂ → rs ≡ r₁ ++ r₂ → proj₂ (L.foldl count r₀ (values r₁)) ≡ 0
       → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (L.foldl count r₀ (values r₁))))) ∈ r₁
       → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → instantOf y ≡ instantOf q → ⊥

