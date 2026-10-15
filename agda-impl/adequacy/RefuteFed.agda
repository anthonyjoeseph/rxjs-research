{-# OPTIONS --guardedness #-}

-- `fed-≃` refuted: a body that joins its source only later, at a position
-- before the value fed, reads the value from the source but is never fed
-- it.
module adequacy.RefuteFed where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Later; connected)
open import denotation.MonotonicList using (Events; Events∞; Pos; Timeline; out; skip; end; ix)
import denotation.Unfold as U
open import adequacy.Placed using (Ordered; ordered)
open import adequacy.Stepper using (_≃_; _∼_; skip∼; skipˡ; skipʳ; _∼∞_; ≃-refl; fed-≃)

open Events∞
open _≃_
open _∼∞_

joins : Later Timeline (⊤ ∷ []) ⊤
Later.force joins = connected (here refl)

body : U.Node (⊤ ∷ []) ⊤
body = U.deferᶜ joins (ix 0 ∷ [])

rest : Events∞ ⊤
force rest = end (ix 2 ∷ [])

ord-src : Ordered (out (ix 1 ∷ []) tt rest)
ordered ord-src = refl , record { ordered = tt }

oe : ∀ {k a l c} → out {A = ⊤} k a l ∼ end c → ⊥
oe ()

refuted : ⊥
refuted with alike (fed-≃ body []ᴬ (ix 1 ∷ []) tt rest (≃-refl _) ord-src ord-src
                       (record { ordered = refl , record { ordered = refl , record { ordered = tt } } } , tt)
                       (record { ordered = refl , record { ordered = tt } } , tt))
... | skip∼ r            = oe (∼force r)
... | skipˡ (skipʳ r)    = oe r
... | skipʳ (skipˡ r)    = oe r
