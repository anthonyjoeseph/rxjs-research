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
  -- THE COMPILED SWEEP REACHES THE FLATTENERS, AND FOUND NOTHING.
  -- `make qc-timed-faithful` decides this statement itself; at depth 3,
  -- fuel one, seeds 12..17 gave no red, and seed 17 alone had 107
  -- cases with values on two plain arrivals under an author flattener,
  -- every one agreeing.  Those counts are read at fuel one only.
  --
  -- PROBED: `Probed.Timed-Faithful` -- by `refl` at fuel 30 over three first-order
  --   programs: a scripted slot taken to one of two arrivals, the script's
  --   two arrivals kept (two instants), and a literal of two values (one
  --   instant).  Not a flattener, a share, a `μ` nor a cold slot: a
  --   flattener's run does not reduce in the typechecker inside 8 GB at fuel
  --   30 or 3, so those shapes are `make quickcheck`'s alone.
  timed-faithful : Timed-Faithful
