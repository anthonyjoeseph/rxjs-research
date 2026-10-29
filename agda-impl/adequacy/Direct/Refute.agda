{-# OPTIONS --guardedness #-}

-- found-lead over Good alone: a merge whose outer and lane are each an
-- empty of at one position.  The keys tie, the lane wins the race, and
-- the outer's end sits at the found of's own position, not past it.
module adequacy.Direct.Refute where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (mergeᶠ; of)
open import denotation.EmissionSet using (at-end)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; ofS; cutS; lnS; flatS; attached; top; inCut; inLn; inLanes)
open import adequacy.Direct.AbsOf using (found-lead)

o : St [] ℕ
o = ofS 0 [] []

refuted : ⊥
refuted = proj₁ (found-lead c {0} {[]} {[]} refl g refl) at-end
  where
    c : Ctx ℕ [] ℕ
    c = inCut true attached (inLn true (inLanes (mergeᶠ nothing) (λ _ → of []) false 1 [] o [] [] top))
    g = tt , ((refl , tt , λ { at-end at-end () }) , tt) , refl , (λ { at-end at-end → refl }) , (λ { at-end at-end () }) , refl , λ ()
