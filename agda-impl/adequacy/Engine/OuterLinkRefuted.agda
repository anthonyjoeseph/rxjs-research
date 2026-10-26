{-# OPTIONS --guardedness #-}

-- `adequacy.Engine.Pick.outer-link` over the fragment and the stepper's
-- heads alone is false: a merge whose outer is done, under a connect whose
-- source is running, with one lane joined to that source and fed nothing.
-- The lane's step hushes, so every stepper head is after any position;
-- its meaning rejoins the source, which shows under `[ix 0]`, not after
-- `[ix 9]`.  `sides-link` falls to the same lane, newer than the one that
-- won: its step hushes, so the race reads it no earlier than `[ix 9]`,
-- while its meaning shows under `[ix 0]`.
module adequacy.Engine.OuterLinkRefuted where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; empty; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; ix; Timeline)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; CS; cs; St; top; inBody; ofS; doneS; flatS; lnS; cutS; joinS; attached)
open import adequacy.Engine.Pick using (outer-link; sides-link; step-sides)
open import adequacy.Engine.Race using (First)

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

ls : List (St (ℕ ∷ []) ℕ)
ls = lnS true (cutS true attached (joinS [] true y [])) ∷ []

refuted : ⊥
refuted with proj₁ (outer-link c (ix 9 ∷ []) (mergeᶠ nothing) f 1 [] doneS ls
                     (tt , (tt , ((tt , tt) , refl , (λ ()))) , (λ ()) , (λ ())) (tt ∷ []) refl)
... | () ∷ []

j : St (ℕ ∷ []) ℕ
j = lnS true (cutS true attached (joinS [] true y []))

sides-refuted : ⊥
sides-refuted with First.before (sides-link c (ix 9 ∷ []) f false 2 doneS [] (j ∷ []) j
                     (tt , (tt , ((tt , tt , tt) , refl , (λ ()))) , (λ ()) , (λ ()))
                     (step-sides (tt ∷ []) [] (λ _ → tt) refl))
... | () ∷ []
