{-# OPTIONS --guardedness #-}

-- `leads` refuted: a joiner placed at its source's next step shows a
-- pre-join skip there, at the very position the step comes first at.
module adequacy.RefuteLeads where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (ix)
import denotation.Unfold as U
open import adequacy.Placed using (Ordered; ordered)
open import adequacy.Stepper using (Env; []; _∷_; os; leads)

source : U.Node [] ⊤
source = U.ofᶜ (ix 0 ∷ []) 0 (tt ∷ [])

joiner : U.Node (⊤ ∷ []) ⊤
joiner = U.joinᶜ (here refl) (ix 0 ∷ ix 0 ∷ []) [] nothing

src-placed : Ordered (U.meaning source []ᴬ)
ordered src-placed = refl , record { ordered = tt }

env : Env (⊤ ∷ [])
env = U.live source ∷ []

refuted : ⊥
refuted with leads joiner env (os source [] tt tt (src-placed , tt) , (src-placed , tt) , tt)
                   (record { ordered = refl , record { ordered = tt } } , tt)
                   (ix 0 ∷ ix 0 ∷ ix 0 ∷ []) refl (refl , tt)
... | ()
