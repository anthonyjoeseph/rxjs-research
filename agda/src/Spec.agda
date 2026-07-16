module Spec where

open import Data.List using (List)
open import Rx.Prim   using (InstEmit)

postulate
  spec-batchSimultaneous : ∀ {A : Set} → List (InstEmit A) → List (InstEmit (List A))
    -- clairvoyant: whole stream in view, groups by shared id;
    -- one record per instant: its id + the values in emission order