module Spec where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat  using (_≡ᵇ_)

open import Rx.Prim using (Id; Source; InstEvent; value; InstEmit; _at_from_)

------------------------------------------------------------------
-- Clairvoyant batching: whole stream in view — group emits by
-- instant id, concat their values in stream order, drop valueless
-- instants; each batch keeps its instant id (a batched stream
-- re-batches).  Batches appear in first-occurrence order of their
-- instant; a batch's source is its first emit's source (in a
-- WellFormed stream every emit of an instant carries the arrival's
-- source, so the choice is forced there).
------------------------------------------------------------------

valuesOf : ∀ {A : Set} → List (InstEvent A) → List A
valuesOf []             = []
valuesOf (value v ∷ es) = v ∷ valuesOf es
valuesOf (_       ∷ es) = valuesOf es

-- every value the stream assigns to instant i, in stream order
valuesAt : ∀ {A : Set} → Id → List (InstEmit A) → List A
valuesAt i [] = []
valuesAt i ((es at j from _) ∷ xs) =
  (if i ≡ᵇ j then valuesOf es else []) ++ valuesAt i xs

seenBefore : Id → List Id → Bool
seenBefore i []       = false
seenBefore i (j ∷ js) = if i ≡ᵇ j then true else seenBefore i js

-- one instant's batch: a single value event carrying the instant's
-- list of values, under the instant's own id — dropped when valueless
batchOf : ∀ {A : Set} → Id → Source → List A → List (InstEmit (List A))
batchOf i s []       = []
batchOf i s (v ∷ vs) = ((value (v ∷ vs) ∷ []) at i from s) ∷ []

specGo : ∀ {A : Set} → List Id → List (InstEmit A) → List (InstEmit (List A))
specGo seen [] = []
specGo seen ((es at i from s) ∷ xs) =
  if seenBefore i seen
  then specGo seen xs
  else batchOf i s (valuesOf es ++ valuesAt i xs) ++ specGo (i ∷ seen) xs

spec-batchSimultaneous : ∀ {A : Set} → List (InstEmit A) → List (InstEmit (List A))
spec-batchSimultaneous = specGo []
