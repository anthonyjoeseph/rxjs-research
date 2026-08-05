module Rx.Provenance-Theorems where

open import Data.List                            using (List; map; upTo)
open import Data.List.Membership.Propositional    using (_∈_)
open import Data.List.Relation.Unary.All          using (All)
open import Data.Nat                              using (suc)

open import Rx.Prim      using (Fuel; Id; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Slots; Stream; evaluate)

------------------------------------------------------------------
-- Id discipline: the bridge premise.  formal-verification says the
-- partition matches the ids; THIS says the ids mean provenance.
------------------------------------------------------------------

-- ordinary list inclusion on Id, spelled out over stdlib membership
-- rather than hand-rolled
_⊆ᵢ_ : List Id → List Id → Set
xs ⊆ᵢ ys = All (λ x → x ∈ ys) xs

-- every id an emit carries, in stream order
ids : ∀ {n} {Γ : Ctx n} {t} → Stream Γ t → List Id
ids = map InstEmit.instant

-- {0 … fuel}: Fuel is ℕ (Rx.Prim:10-11) and Id is ℕ too (Rx.Prim:55-56),
-- so the horizon is the literal enumeration — 0 is the subscribe
-- frame's instant, 1 … fuel the drain counter's (Rx.Evaluator.evaluate,
-- Rx.Evaluator.drain: nextId starts at 1 and increments once per
-- arrival, fuel arrivals at most)
horizon : Fuel → List Id
horizon fuel = upTo (suc fuel)

postulate
  -- every id in the output stream is the id of some arrival's cascade;
  -- sync-spawned inners inherit, never mint
  id-inheritance :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    ids (evaluate fuel e ins) ⊆ᵢ horizon fuel

-- id-fresh became structural: instants mint from ARRIVAL POSITION
-- (0 the subscribe frame, then the drain counter), so distinct
-- cascades carry distinct, strictly increasing ids by construction —
-- the Protocol's horizon check consumes exactly this.

