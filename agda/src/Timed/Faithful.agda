------------------------------------------------------------------
-- TIMED-FAITHFUL: the timed run, packets and END items dropped, is the
-- plain run.
--
-- THIS IS THE TRANSLATION'S OWN OBLIGATION, not the impl's: a
-- translation to `empty` would make `Timing-Correct` say nothing.
------------------------------------------------------------------
module Timed.Faithful where

open import Data.Bool    using (T)
open import Data.List    using (List; []; map)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx; Val; isData)
open import SExp.Syntax      using (SExp; Kinds)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.Pipeline using (runᴾ)
open import Timed.Translation     using (timed; timedSlots; valuesᵀ; untimedᵈ)

-- the timed program's plain run, packets and END items dropped
untimedᵀ : ∀ {n} {Γ : Ctx n} {t} → T (isData t) → (κ : Kinds n) → Fuel
         → SExp Γ [] [] [] t → SimulSlots Γ κ → List (Val Γ t)
untimedᵀ {t = t} ok κ fuel e ins =
  map (untimedᵈ t ok) (valuesᵀ {t = t} (runᴾ fuel (timed κ e) (timedSlots ins)))

Timed-Faithful : Set
Timed-Faithful =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  untimedᵀ ok κ fuel e ins ≡ runᴾ fuel e ins

postulate
  timed-faithful : Timed-Faithful
