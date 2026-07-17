module Rx.Provenance-Theorems where

open import Data.List    using (List)
open import Data.Product using (_×_)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Tick; Fuel; Ordinal; Id; freshId)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Slots)

------------------------------------------------------------------
-- Id discipline: the bridge premise.  formal-verification says the
-- partition matches the ids; THIS says the ids mean provenance.
------------------------------------------------------------------

postulate
  _⊆ᵢ_ : List Id → List Id → Set

  -- every id in the output stream is the id of some arrival's cascade;
  -- sync-spawned inners inherit, never mint
  id-inheritance :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    ⊤   -- state as: ids(evaluate fuel e ins) ⊆ᵢ freshId-image of arrivals

  -- distinct arrivals never share an id (freshId injective on (tick,ordinal))
  id-fresh : ∀ (t₁ t₂ : Tick) (o₁ o₂ : Ordinal) →
             freshId t₁ o₁ ≡ freshId t₂ o₂ → (t₁ ≡ t₂) × (o₁ ≡ o₂)

