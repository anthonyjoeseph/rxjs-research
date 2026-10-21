{-# OPTIONS --guardedness #-}

-- `body-sides` refuted: a body `of` whose second value lands where its
-- source's first does.  Nothing in `Placed` keeps a body's later
-- positions apart from its source's.
module adequacy.RefuteBodySides where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList.Events using (ix)
import denotation.Unfold as U
open import adequacy.Placed.Order using (ordered)
open import adequacy.Stepper.Within using (body-sides)

source : U.Node [] ⊤
source = U.ofᶜ [] 1 (tt ∷ [])

body : U.Node (⊤ ∷ []) ⊤
body = U.ofᶜ [] 0 (tt ∷ tt ∷ [])

refuted : ⊥
refuted = proj₁ (body-sides {ν = []ᴬ} [] body source []ᴬ (tt , tt) placed refl tt (ix 1 ∷ []) (ix 1 ∷ []) refl refl) refl
  where
    placed = record { ordered = refl , record { ordered = refl , record { ordered = refl , record { ordered = tt } } } }
           , (record { ordered = refl , record { ordered = refl , record { ordered = tt } } } , tt)
           , (record { ordered = refl , record { ordered = tt } } , tt)
           , λ { _ _ refl refl → (λ ()) , (λ ()) }
