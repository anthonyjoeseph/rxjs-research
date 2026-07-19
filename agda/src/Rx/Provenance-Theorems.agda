module Rx.Provenance-Theorems where

open import Data.List    using (List)
open import Data.Unit    using (⊤)

open import Rx.Prim      using (Fuel; Id)
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
    ⊤   -- state as: ids(evaluate fuel e ins) ⊆ᵢ {0 … fuel}

-- id-fresh became structural: instants mint from ARRIVAL POSITION
-- (0 the subscribe frame, then the drain counter), so distinct
-- cascades carry distinct, strictly increasing ids by construction —
-- the Protocol's horizon check consumes exactly this.

