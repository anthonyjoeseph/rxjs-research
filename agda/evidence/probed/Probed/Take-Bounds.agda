----------------------------------------------------------------------
-- THE TAKE FACE, INSTANTIATED — AND IT IS THE GUINEA PIG A SATURATION
-- RESTRICTION IS MEASURED AGAINST, SO IT IS THE ONE STATEMENT HERE
-- THAT MUST NOT BE TAKEN ON TRUST.
----------------------------------------------------------------------

-- WHAT THE ROWS DECIDE.  `take-bounds-values` bounds a run's VALUE
-- count by the take's own budget, uniformly in fuel, so a row fails
-- exactly when the budget is spent at one point and the cut emitted
-- from another: a take that delivers before it decrements, or one that
-- lets the drain resume past its own zero, over-emits and no
-- constructor inhabits the row.  The set below walks k across the
-- burst it is cutting — under it, inside it, and exactly at it —
-- because an off-by-one is invisible at every k but the boundary.
--
-- AND ONE ROW PAST THE SUBSCRIBE FRAME, which the source-free rows
-- cannot reach: there the whole run is the burst and the drain never
-- steps, so a budget the drain fails to carry across a delivery is
-- decided only by a program with a slot in it.
--
-- NOT REACHED: any flattening program, which is where the budget's
-- remaining risk lives, since a take above a flattener has to hold its
-- grant across an inner subscribe; any cold source, so every arrival
-- is scheduled at tick zero; a source firing at more than one tick;
-- and any type other than `natᵗ`.

-- TARGET: take-bounds-values @189781
module Probed.Take-Bounds where

open import Data.Fin using (zero)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (s≤s; z≤n)
open import Data.Vec using ([]; _∷_)   -- contexts are Vecs; ∷/[] overload per type
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; ofᵉ; mapᵉ; input;
                          primᵗ; pairᵗ; varᵗ; add)
open import Rx.Slots using (Slots)
open import Readme-Theorems using (noSlots; hotOnce; oneSlot)
open import Verify-Take-Bounds using (take-bounds-values)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- TWO VALUES IN ONE SUBSCRIBE BURST, which is the smallest shape whose
-- cut can land inside an instant rather than between two of them.
pair₀ : Closed Γ₀ natᵗ
pair₀ = ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])

-- A PROGRAM WHOSE VALUES ARRIVE AT THE DRAIN instead of at subscribe.
mapped₀ : Closed (natᵗ ∷ []) natᵗ
mapped₀ = mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 100))) (input zero)

ins₀ : Slots (natᵗ ∷ [])
ins₀ = oneSlot (hotOnce 3)

----------------------------------------------------------------------
-- 1.  k = 0: THE BUDGET IS SPENT BEFORE ANYTHING IS EMITTED.
--
-- LOAD-BEARING, and the row an off-by-one at the dispatch fails first:
-- the program underneath emits two values at the subscribe frame, so
-- `≤ 0` is inhabited only if the take swallowed the whole burst.  A
-- take decrementing after delivery leaks the first value and leaves
-- `1 ≤ 0` with no constructor.
----------------------------------------------------------------------

row-zero : Confirms (take-bounds-values 0 0 pair₀ noSlots)
row-zero = z≤n

----------------------------------------------------------------------
-- 2.  k = 1: THE CUT LANDS INSIDE AN INSTANT.
--
-- LOAD-BEARING on the part a batch-counting take would get wrong: both
-- values sit in ONE burst, so keeping whole instants keeps both and
-- leaves `2 ≤ 1` uninhabited.
----------------------------------------------------------------------

row-cuts-instant : Confirms (take-bounds-values 0 1 pair₀ noSlots)
row-cuts-instant = s≤s z≤n

----------------------------------------------------------------------
-- 3.  k = 2: THE BUDGET IS EXACTLY THE BURST.
--
-- LOAD-BEARING on the other side of the boundary: the take must not
-- stop one short of its grant and must not let a third envelope
-- through, and at the exact fit those are the only two failures left.
----------------------------------------------------------------------

row-exact : Confirms (take-bounds-values 0 2 pair₀ noSlots)
row-exact = s≤s (s≤s z≤n)

----------------------------------------------------------------------
-- 4.  THE BUDGET ACROSS A DELIVERY.
--
-- LOAD-BEARING at the one point the source-free rows cannot reach: the
-- run has a drain step in it, so the grant has to survive being carried
-- from the subscribe frame into a delivery.  A take whose budget resets
-- when the drain resumes emits the arrival on top of its grant.
----------------------------------------------------------------------

row-past-frame : Confirms (take-bounds-values 2 1 mapped₀ ins₀)
row-past-frame = s≤s z≤n
