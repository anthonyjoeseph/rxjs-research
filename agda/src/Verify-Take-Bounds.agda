-- TAKE BOUNDS THE STREAM.  A program whose outermost node is `take k`
-- emits at most k values, whatever sits underneath it and whatever the
-- slots deliver.  It is the smallest claim in this repo that is about
-- the EVALUATOR's own bookkeeping rather than about a correspondence:
-- no spec, no batching, no second run to compare against.
module Verify-Take-Bounds where

open import Data.List using (length)
open import Data.Nat using (ℕ; _≤_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; takeᵉ; nat̂)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Readme-Theorems using (emitValues)

-- IT IS THE INSTANCE A SATURATION RESTRICTION IS MEASURED AGAINST
-- (Anthony).  Any claim that a program's whole emission is bounded is
-- false over this language unrestricted -- an unguarded fixpoint emits
-- one envelope per unit of fuel, so no finite list bounds it -- and the
-- repair is a predicate confining such a claim to programs that
-- saturate.  This is the ONLY emission bound
-- the repo states UNIFORMLY IN FUEL, which is exactly the shape such a
-- predicate has to deliver, so a candidate is judged by whether a
-- `take`-headed program satisfies it and whether the machinery below
-- proves that it does -- not by how the predicate reads.  The
-- consequence worth knowing before writing one: this is stated at an
-- OUTERMOST `take`, so a candidate that only admits programs of that
-- shape has been tested by nothing, since the face cannot tell it
-- apart from one admitting every saturating program.
--
-- IT IS A BARE POSTULATE AND MINTS NO LEAVES, WHICH IS WHY.  Its
-- previous leaves were denominated in the take node's own budget --
-- the registry's path condition, the node counter's guard, a drain
-- induction over chains -- and a restriction stated in the denotation
-- is what decides which of those is still the right currency.  Minting
-- them ahead of the predicate is a hypothesis about the route.
--
-- AND IT IS THE CHEAPEST THING HERE THAT CAN BE FALSE.  The budget is
-- decremented at the dispatch and the cut is emitted from the frame, so
-- an off-by-one between those two points, or a path that delivers
-- before it spends, is a counterexample rather than a hard proof -- and
-- it is reachable at a scripted slot with two entries and a take at one.
--
-- PROBED: `Probed.Take-Bounds` walks k across the burst it cuts — under
--   it, inside it, and exactly at it — and carries one row past the
--   subscribe frame, where the grant has to survive a drain step.  Not
--   reached: any flattening program, which is where the remaining risk
--   lives, since a take above a flattener holds its grant across an
--   inner subscribe; and any source firing at more than one tick.
--
-- RECOVERY: git show 9f5e3339:agda/src/Verify-Take-Bounds.agda restores
--   the drain induction over registered chains, the budget's split
--   across the root burst and the drain, and the registry's path
--   condition; git show 9f5e3339:agda/evidence/probed/Probed/Take-Bounds.agda
--   restores the rows that instantiated them.
postulate
  take-bounds-values :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ)
      (e : Closed Γ t) (ins : Slots Γ) →
    length (emitValues (evaluate↓ fuel (takeᵉ (nat̂ k) e) ins)) ≤ k
