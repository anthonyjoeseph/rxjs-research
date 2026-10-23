{-# OPTIONS --guardedness #-}

-- A TAKEWHILE RESTAGED in the world grown by its cut.
module port.Taken where

open import Data.List using (_∷_; _++_; [_]; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (tick; ix; sub; last)

-- A value under a position keeps its tick.
tick-ix0 : ∀ r → tick (r ++ [ ix 0 ]) ≡ tick r
tick-ix0 []           = refl
tick-ix0 (ix _ ∷ _)   = refl
tick-ix0 (sub _ ∷ _)  = refl
tick-ix0 (last ∷ _)   = refl
