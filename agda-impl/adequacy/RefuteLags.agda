{-# OPTIONS --guardedness #-}

-- `lags` refuted: a joiner untold of an ended source, under no running
-- source, has nothing bounding it, yet shows its end at once.
module adequacy.RefuteLags where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (ix)
import denotation.Unfold as U
open import adequacy.Stepper using (Env; []; _∷_; lags)

joiner : U.Node (⊤ ∷ []) ⊤
joiner = U.joinᶜ (here refl) (ix 0 ∷ []) [] nothing

env : Env (⊤ ∷ [])
env = U.ended (ix 0 ∷ []) ∷ []

refuted : ⊥
refuted with lags joiner env tt (record { ordered = tt } , tt) (ix 1 ∷ []) refl tt
... | ()
