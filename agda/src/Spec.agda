module Spec where

open import Data.List using (List)
open import Rx.Prim   using (InstEmit)

postulate
  spec-batchSimultaneous : ∀ {A : Set} → List (InstEmit A) → List (InstEmit (List A))
    -- clairvoyant: whole stream in view — group emits by instant id,
    -- concat their values in stream order, drop valueless instants;
    -- each batch keeps its instant id (a batched stream re-batches)