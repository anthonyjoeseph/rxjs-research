-- TAKE BOUNDS THE STREAM.  A program whose outermost node is `take k`
-- emits at most k values, whatever sits underneath it and whatever the
-- slots deliver.  It is the smallest claim in this repo that is about
-- the EVALUATOR's own bookkeeping rather than about a correspondence:
-- no spec, no batching, no second run to compare against.
--
-- WHICH IS WHY IT IS THE REHEARSAL (Anthony).  Every other claim on
-- this face needs the run relation to be a function before a statement
-- about "the" output means anything; this one does not, because it is
-- an inequality about the one output the builder produces and holds of
-- any output at all.  So it exercises the take node's budget --
-- `take-st`, the frame, the dispatch split -- with none of the
-- determinacy apparatus in the way, and what it rehearses is the
-- induction over the drain that every well-formedness leaf also owes.
--
-- AND IT IS THE CHEAPEST THING HERE THAT CAN BE FALSE.  The budget is
-- decremented at the dispatch and the cut is emitted from the frame, so
-- an off-by-one between those two points, or a path that delivers
-- before it spends, is a counterexample rather than a hard proof -- and
-- it is reachable at a scripted slot with two entries and a take at one.
module Verify-Take-Bounds where

open import Data.List using (length)
open import Data.Nat using (ℕ; _≤_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; nat̂; takeᵉ)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Slots using (Slots)
open import Readme-Theorems using (emitValues)

postulate
  -- The bound, stated over the flat value stream rather than over
  -- batches, because `take` counts values: a batch-level statement
  -- would be weaker exactly where the node is interesting, since the
  -- cut can land mid-batch.
  -- PROBED: `Probed.Take-Bounds`, at the two points where the node has
  --   something to get wrong and at the one where it has nothing: a cut
  --   INSIDE a subscribe burst, a cut ACROSS two arrivals so the budget
  --   is carried into the drain and spent there, and a take at zero.
  --   Both cutting rows are TIGHT and pinned beside the same program
  --   with the take removed, so neither is met by a node that emits
  --   nothing and neither stands at a program that was short anyway.
  --   Not reached: every flattening program, a take nested under another
  --   take, and a budget that is not a literal.
  take-bounds-values :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ)
      (e : Closed Γ t) (ins : Slots Γ) →
    length (emitValues (evaluate↓ fuel (takeᵉ (nat̂ k) e) ins)) ≤ k
