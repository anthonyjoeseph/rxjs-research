------------------------------------------------------------------
-- TIMED-FAITHFUL: the timed run, packets and END items dropped, is the
-- plain run.
--
-- THIS IS THE TRANSLATION'S OWN OBLIGATION, not the impl's: a
-- translation to `empty` would make `Timing-Correct` say nothing.
------------------------------------------------------------------
module Timed.Faithful where

open import Data.Bool    using (T)
open import Data.List    using ([]; concat; map)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx; isData)
open import Rx.SExp      using (SExp; Kinds)
open import Rx.Simul-Slots using (SimulSlots; plainSlots)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Plain     using (plainExp; plainValues)
open import Rx.Timed     using (timed; timedSlots; valuesᵀ; untimedᵈ)

Timed-Faithful : Set
Timed-Faithful =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  map (untimedᵈ t ok)
      (valuesᵀ {t = t} (plainValues (concat (evaluate↓ fuel (plainExp (timed κ e))
                                                         (plainSlots (timedSlots ins))))))
    ≡ plainValues (concat (evaluate↓ fuel (plainExp e) (plainSlots ins)))

postulate
  timed-faithful : Timed-Faithful
