module Implementation where

postulate
  spec-batchSimultaneous : ∀ {A : Set} → List (InstEmit A) → List (List (InstEmit A))
    -- clairvoyant: whole stream in view, groups by shared id

  impl-batchSimultaneous : ∀ {A} → List (InstEmit A) → List (List (InstEmit A))
    -- ≡ fold step-batch, ++ flushBatch — definitional once written