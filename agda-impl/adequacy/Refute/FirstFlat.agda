{-# OPTIONS --guardedness #-}
module adequacy.Refute.FirstFlat where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)

open import Tree using (Later; empty; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; ix)
import denotation.Unfold as U
open import adequacy.Placed.Order using (Ordered; ordered)
open import adequacy.Stepper using (first-flat)

-- A pool that is no rest: a defer, whose step skips while its cut is idle.
l : Later Timeline [] ℕ
l .Later.force = empty

pool : U.Node [] ℕ
pool = U.deferᶜ l (ix 0 ∷ []) []

g : ℕ → Pos → U.Node [] ℕ
g _ _ = U.idleᶜ

c : U.Node [] ℕ
c = U.flatMapᶜ (mergeᶠ nothing) g nothing [] [] pool

ord : Ordered (U.meaning c []ᴬ)
ord .ordered = tt

refuted : ⊥
refuted with first-flat {ν = []ᴬ} (mergeᶠ nothing) g nothing [] [] pool []ᴬ (tt , tt , λ _ _ → tt) (ord , tt , tt , λ _ _ ())
... | inj₁ ()
... | inj₂ ()
