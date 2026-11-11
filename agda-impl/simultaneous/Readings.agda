{-# OPTIONS --guardedness #-}

-- READING A RUN THE WAY THE SPEC DOES.
--
-- AN INSTANT IS A COMPONENT OF THE POSITION (`denotation.Position`): the
-- subscribe frame, or one async emission.  Two rows are simultaneous
-- exactly when their instants are equal, and nothing about a row has to
-- be proven for that reading to be right.
module simultaneous.Readings where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import denotation.Position using (Pos; Instant; _∙_; _⊕_) renaming (instant to instantᵖ)
open import simultaneous.InstEmit using (InstEmit; valuesOf)

open InstEmit using (instant)

instantOf : Pos → Instant
instantOf = instantᵖ

-- The root of a row's instant.  Every row of one synchronous burst has
-- the same root: the elaboration names and closes routes per instant.
rootOf : Pos → Pos
rootOf p = instantOf p ∙ []

------------------------------------------------------------------------
-- InstEmit streams

-- Each value an emit carries, with the emit's provenance.
stamped : ∀ {N A} → List (InstEmit N A) → List (N × A)
stamped []       = []
stamped (x ∷ xs) = map (λ a → instant x , a) (valuesOf x) ++ stamped xs

-- A grouping read off a prefix, its last group kept only once its
-- instant is over: until then it may still grow.
closed : ∀ {X : Set} → Bool → List X → List X
closed true  xs           = xs
closed false []           = []
closed false (x ∷ [])     = []
closed false (x ∷ y ∷ xs) = x ∷ closed false (y ∷ xs)

closed-snoc : ∀ {X : Set} (xs : List X) a → closed false (xs ++ a ∷ []) ≡ xs
closed-snoc []           a = refl
closed-snoc (x ∷ [])     a = refl
closed-snoc (x ∷ y ∷ xs) a = cong (x ∷_) (closed-snoc (y ∷ xs) a)

-- A position's parent, one label up.
parent : Pos → Pos
parent (i ∙ ps) = i ∙ closed false ps

parent-snoc : ∀ (y : Pos) l → parent (y ⊕ (l ∷ [])) ≡ y
parent-snoc (i ∙ ps) l = cong (i ∙_) (closed-snoc ps l)
