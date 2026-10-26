{-# OPTIONS --guardedness #-}

-- `adequacy.Engine.Pick.limited-sides` over the fragment and the lane's
-- win alone is false: a switch under a connect whose source is running,
-- its outer a joiner of that source fed nothing.  The joiner has no
-- candidate, so the lane wins; its meaning shows the source under
-- `[ix 0]`, before `[ix 9]`.
module adequacy.Engine.LimitedSidesRefuted where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; empty; switchᶠ)
open import denotation.MonotonicList.Events using (ix; Timeline)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; CS; cs; St; top; inBody; ofS; lnS; cutS; joinS; attached)
open import operation.Key using (at)
open import adequacy.Engine.Race using (First)
open import adequacy.Engine.Pick using (limited-sides; lane-won)

k : CS
k = cs false true false nothing nothing nothing [] []

src : St [] ℕ
src = ofS 0 (ix 0 ∷ []) (0 ∷ [])

c : Ctx ℕ (ℕ ∷ []) ℕ
c = inBody k src top

y : ℕ ∈ (ℕ ∷ [])
y = here refl

f : ℕ → Obs Timeline (ℕ ∷ []) ℕ
f _ = empty

o : St (ℕ ∷ []) ℕ
o = joinS [] true y []

s : St (ℕ ∷ []) ℕ
s = lnS true (cutS true attached (joinS [] true y []))

refuted : ⊥
refuted with First.outerN (limited-sides (ix 9 ∷ []) c switchᶠ f false 1 [] o [] [] s (λ ()) refl
                             (lane-won tt tt tt)
                             (tt , (tt , ((tt , tt) , refl , (λ ()))) , (λ ()) , (λ ())))
... | ()
