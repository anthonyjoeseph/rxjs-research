{-# OPTIONS --guardedness #-}

-- `placed-after` refuted over a placing with each live joiner joined
-- before its source: a flatMap's lane admitted past its source's next
-- event joins after it.
module adequacy.RefutePlacedAfter where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (mergeᶠ)
open import denotation.MonotonicList using (ix)
import denotation.Unfold as U
open import adequacy.Placed using (Ordered; ordered)
open import adequacy.Stepper using (Env; []; _∷_; os; placed-after)

source : U.Node [] ⊤
source = U.ofᶜ (ix 0 ∷ []) 0 (tt ∷ [])

lanes : U.Node (⊤ ∷ []) ⊤
lanes = U.flatMapᶜ (mergeᶠ nothing) (λ _ q → U.joinᶜ (here refl) q [] nothing) (just (U.ofᶜ (ix 1 ∷ []) 0 (tt ∷ []))) [] []

src-placed : Ordered (U.meaning source []ᴬ)
ordered src-placed = refl , record { ordered = tt }

env : Env (⊤ ∷ [])
env = U.live source ∷ []

refuted : ⊥
refuted with placed-after lanes env (os source [] tt tt (src-placed , tt) , (src-placed , tt) , tt)
                   (tt , tt , λ _ _ → tt)
                   (record { ordered = refl , record { ordered = refl , record { ordered = refl , record { ordered = tt } } } }
                   , (record { ordered = refl , record { ordered = tt } } , tt) , tt)
... | _ , _ , _ , (_ , ()) , _
