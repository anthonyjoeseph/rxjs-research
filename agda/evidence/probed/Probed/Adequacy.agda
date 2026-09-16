----------------------------------------------------------------------
-- THE ONE ROW ON THE ADEQUACY FACE A PROGRAM CAN DECIDE.
----------------------------------------------------------------------

-- WHY THIS FILE HOLDS EXACTLY ONE TARGET AND NOT THREE.  The face
-- carries three claims and the other two are stated over `meaning`,
-- which is `observe` of `denote` — two postulates, so neither side
-- reduces at any program whatever and no row can be written.  The
-- finding is recorded where it constrains something, in the domain's
-- own header; here it is why the file is small.
--
-- WHAT THE ROWS DECIDE.  `run-monotone` says more fuel EXTENDS a run
-- and never rewrites what a shorter one emitted, which is two
-- properties in one equation: the existence of a remainder, and the
-- shorter run being an honest prefix rather than merely shorter.  A row
-- where the remainder is EMPTY decides only the second, and a row where
-- it is non-empty decides both — so the set below carries one of each
-- at a program that can grow, plus a saturated program where growth is
-- impossible and rewriting is the only way to fail.
--
-- NOT REACHED: any program whose evaluation enters a flattening node,
-- for the reason the sibling probes record; a source firing past the
-- one tick scripted here, so no row spans two deliveries; a cold
-- source, so every arrival is scheduled at tick zero; and any fuel gap
-- wider than the program's own horizon, so nothing decides a run that
-- has already saturated and is then given far more fuel.

-- TARGET: run-monotone @b08aea
module Probed.Adequacy where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (_,_)
open import Data.Vec using ([]; _∷_)   -- contexts are Vecs; ∷/[] overload per type
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (natᵗ; Closed; nat̂; pairᵗ; primᵗ; varᵗ; add;
                          input; mapᵉ; ofᵉ)
open import Rx.Slots using (Slots)
open import Readme-Theorems using (hotOnce; oneSlot)
open import Verify-Adequacy using (run-monotone)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE TWO PROGRAMS, AND THE CONTEXT IS THE SAME ONE SO THE SLOT TABLE
-- CAN BE SHARED.  `const₀` never reads its input, so its whole run is
-- the subscribe frame and no fuel can add to it; `mapped₀` carries a
-- scripted arrival onward, so its run genuinely grows with fuel.
----------------------------------------------------------------------

const₀ : Closed (natᵗ ∷ []) natᵗ
const₀ = ofᵉ (nat̂ 7 ∷ nat̂ 8 ∷ [])

mapped₀ : Closed (natᵗ ∷ []) natᵗ
mapped₀ = mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 100))) (input zero)

ins₀ : Slots (natᵗ ∷ [])
ins₀ = oneSlot (hotOnce 3)

----------------------------------------------------------------------
-- 1.  A SATURATED PROGRAM: THE REMAINDER IS EMPTY AND REWRITING IS THE
--     ONLY AVAILABLE FAILURE.
--
-- LOAD-BEARING on the prefix half alone.  `const₀` emits its whole
-- content in the subscribe frame, so both runs are the same list and
-- what the row decides is that the extra fuel did not renumber an
-- instant, re-mint a provenance or re-order the burst — every one of
-- which leaves the equation false with the remainder still empty.  It
-- cannot decide the existence half, and is paired with the rows below
-- for exactly that reason.
----------------------------------------------------------------------

row-saturated : Confirms (run-monotone 0 2 const₀ ins₀ z≤n)
row-saturated = [] , refl

----------------------------------------------------------------------
-- 2.  A PROGRAM THAT GROWS: THE REMAINDER IS NON-EMPTY.
--
-- LOAD-BEARING on both halves.  At fuel zero the drain spends nothing,
-- so the run is the subscribe frame; at fuel one the scripted arrival
-- is delivered through the mapped leg and the run is strictly longer.
-- A machine that re-emitted the frame's own envelopes under the larger
-- fuel, or that delivered the arrival in place of part of the burst,
-- fails here rather than degenerating.
----------------------------------------------------------------------

row-grows : Confirms (run-monotone 0 1 mapped₀ ins₀ z≤n)
row-grows = _ , refl

----------------------------------------------------------------------
-- 3.  THE SAME PROGRAM PAST ITS OWN HORIZON.
--
-- LOAD-BEARING on the prefix half at a run the drain has actually
-- stepped, which the saturated row cannot reach: there the shorter run
-- is a burst and nothing was drained, so no drain counter was carried
-- across the two runs.  Here the shorter run already contains a
-- delivery, so a drain that resumed from a different arrival ordinal
-- under the larger fuel is what this row refuses.
----------------------------------------------------------------------

row-past-horizon : Confirms (run-monotone 1 3 mapped₀ ins₀ (s≤s z≤n))
row-past-horizon = [] , refl
