{-# OPTIONS --guardedness #-}

-- `fed-≃` refuted: a joiner already told its end is fed all the same,
-- and shows the value its unfed self never does.
module adequacy.RefuteFed where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (Events∞; ix; last; out; end)
import denotation.Unfold as U
open import adequacy.Placed using (ordered)
open import adequacy.Stepper using (_≃_; ≃-refl; fed-≃)
open Events∞
open _≃_

q = ix 1 ∷ []

rest : Events∞ ⊤
force rest = end (ix 1 ∷ last ∷ [])

joiner : U.Node (⊤ ∷ []) ⊤
joiner = U.joinᶜ (here refl) (ix 0 ∷ []) [] (just (ix 2 ∷ []))

refuted : ⊥
refuted with alike (fed-≃ joiner []ᴬ q tt rest (≃-refl _)
                      (record { ordered = refl , record { ordered = tt } })
                      (record { ordered = refl , record { ordered = tt } })
                      refl (record { ordered = tt } , tt)
                      (record { ordered = refl , record { ordered = tt } } , tt))
... | ()
