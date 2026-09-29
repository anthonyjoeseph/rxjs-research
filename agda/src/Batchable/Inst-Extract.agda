------------------------------------------------------------------
-- WHAT THE SPEC IS HANDED: every value a stream carries, tagged with
-- its emit's instant.  A valueless emit contributes nothing, which is
-- what a subscriber would see of it.
------------------------------------------------------------------
module Batchable.Inst-Extract where

open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)

open import Rx.Prim      using (Id; InstEvent; value; InstEmit)

private
  valuesᴱ : ∀ {A : Set} → List (InstEvent A) → List A
  valuesᴱ []             = []
  valuesᴱ (value v ∷ es) = v ∷ valuesᴱ es
  valuesᴱ (_       ∷ es) = valuesᴱ es

instExtract : ∀ {A : Set} → List (InstEmit A) → List (Id × A)
instExtract []       = []
instExtract (x ∷ xs) = map (InstEmit.instant x ,_) (valuesᴱ (InstEmit.events x)) ++ instExtract xs
