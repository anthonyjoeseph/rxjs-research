module Spec where


postulate
  spec-batchSimultaneous : ∀ {A : Set} → List (InstEmit A) → List (List (InstEmit A))
    -- clairvoyant: whole stream in view, groups by shared id