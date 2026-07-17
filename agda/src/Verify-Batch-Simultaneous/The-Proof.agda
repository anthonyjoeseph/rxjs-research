module Verify-Batch-Simultaneous.The-Proof where

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim               using (InstEmit; Fuel)
open import Rx.Exp                using (Ctx; Closed)
open import Rx.Evaluator          using (Slots; evaluate)
open import Rx.Protocol           using (WellFormed)
open import Rx.Evaluator-Theorems using (evaluate-well-formed)
open import Spec                  using (spec-batchSimultaneous)
open import Implementation        using (impl-batchSimultaneous)

------------------------------------------------------------------
-- The sandwich.  batch-agreement: on any protocol-respecting stream
-- the counting machine matches the clairvoyant spec.  Quantified
-- over WellFormed streams, NOT arbitrary ones — an adversarial
-- stream confuses the counter (one registration emitting twice in
-- an instant closes the batch early).  evaluate-well-formed
-- (Rx.Evaluator-Theorems) supplies the hypothesis for every
-- actual program.
------------------------------------------------------------------

postulate
  batch-agreement :
    ∀ {A} (xs : List (InstEmit A)) → WellFormed xs →
    spec-batchSimultaneous xs ≡ impl-batchSimultaneous xs

-- THE verified object, end to end: for every program, batching its
-- rendered stream is spec-correct.  Already a real definition —
-- the proof IS the composition of the two lemmas.
formal-verification-batchSimultaneous :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  spec-batchSimultaneous (evaluate fuel e ins)
    ≡ impl-batchSimultaneous (evaluate fuel e ins)
formal-verification-batchSimultaneous fuel e ins =
  batch-agreement (evaluate fuel e ins) (evaluate-well-formed fuel e ins)
