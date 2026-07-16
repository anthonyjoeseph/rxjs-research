module Implementation where

open import Data.List using (List)
open import Rx.Prim   using (InstEmit)

postulate
  impl-batchSimultaneous : ∀ {A} → List (InstEmit A) → List (InstEmit (List A))
    -- ≡ fold step-batch, ++ flushBatch — definitional once written
