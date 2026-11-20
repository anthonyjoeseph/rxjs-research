{-# OPTIONS --guardedness #-}

-- WHERE A PROGRAM'S BOUNDARIES LIE (`Placing.Placed`).  A boundary is the
-- program's own, or its scope's: a hot's it reads.
--
-- An OWN boundary lies in the subscription's world at its cut, led by no
-- position of the world of a plain child of one of that cut's rows, and
-- a held one waits on a connect in that world (`Placing.Own`).  A
-- SCOPE'S boundary is named by the scope, and placed by it.
--
-- Not every boundary in the subscription's world: a reader's are its
-- hot's, in the source's world, apart from the body the reader is in.
module simultaneous.Placed where

open import Data.List using ([_])
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; _⊕_)
open import denotation.EmissionSet using (EmissionSet)
open import denotation.Laws.Worlds using (W; W⁼; Plain; _⊑_)
open import simultaneous.Horizon using (Tag; held)

-- A program subscribed at `p`, its cuts `c`, each under hot rows `H`,
-- and its scope's boundaries `Env`.
module Placing {A : Set} (H : ℕ → Pos → Set) (Env : ℕ → Pos → Tag → Set) (p : Pos) (c : ℕ → EmissionSet A) where

  record Own (N : ℕ) (b : Pos) (g : Tag) : Set where
    field
      world  : W (H N) p b
      under  : ∀ {x e l w} → c N x e → Plain l → W⁼ (H N) (x ⊕ [ l ]) w → ¬ w ⊑ b
      holder : ∀ {q} → g ≡ held q → W⁼ (H N) p q

  Placed : (ℕ → Pos → Tag → Set) → Set
  Placed Bd = ∀ {N b g} → Bd N b g → Own N b g ⊎ Env N b g
