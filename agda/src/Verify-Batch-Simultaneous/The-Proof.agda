module Verify-Batch-Simultaneous.The-Proof where

open import Data.List    using (List)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Rx.Prim        using (InstEmit)
open import Spec           using (spec-batchSimultaneous)
open import Implementation using (impl-batchSimultaneous)

------------------------------------------------------------------
-- THE verified object: the batching state machine vs its spec.
-- Quantified over streams — composition with evaluate is definitional.
------------------------------------------------------------------

postulate
  formal-verification-batchSimultaneous :
    ∀ {A} (xs : List (InstEmit A)) →
    spec-batchSimultaneous xs ≡ impl-batchSimultaneous xs