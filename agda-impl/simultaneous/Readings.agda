{-# OPTIONS --guardedness #-}

-- READING A RUN THE WAY THE SPEC DOES.
--
-- AN INSTANT IS A FRAME, READ OFF THE POSITION.  The subscribe frame
-- sits under `root`.  After it, a cold's every async emission is a frame
-- of its own, with everything it causes synchronously: a timer firing at
-- tick t sits under `ix t ∷ sub e ∷ []`, `e` where its timer was created,
-- its tick never 0, and its i-th emission under `ix i` below that, its
-- completion under `last`.  The tick alone is too coarse, since two
-- timers firing at one tick are two frames; the whole position is too
-- fine, since every event of one frame has its own.
module simultaneous.Readings where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (suc)

open import denotation.Events using (Pos; Label; ix; sub; last; root)
open import simultaneous.InstEmit using (InstEmit; valuesOf)

open InstEmit using (instant)

-- Every position lies under one of the two: the subscribe frame, whose
-- first step is never a `sub`, or one step of a timer cascade, never at
-- tick 0.  This is what makes `instantOf` read the instant, and nothing
-- else does.
data NotSub : Label → Set where
  ix-ns   : ∀ {i} → NotSub (ix i)
  last-ns : NotSub last

data Rooted : Pos → Set where
  in-frame   : ∀ {l p} → NotSub l → Rooted (ix 0 ∷ l ∷ p)
  in-cascade : ∀ {t e l p} → Rooted (ix (suc t) ∷ sub e ∷ l ∷ p)

instantOf : Pos → Pos
instantOf (ix t ∷ sub e ∷ l ∷ _) = ix t ∷ sub e ∷ l ∷ []
instantOf _                      = root

------------------------------------------------------------------------
-- InstEmit streams

-- Each value an emit carries, with the emit's provenance.
stamped : ∀ {N A} → List (InstEmit N A) → List (N × A)
stamped []       = []
stamped (x ∷ xs) = map (λ a → instant x , a) (valuesOf x) ++ stamped xs

-- A grouping read off a prefix, its last group kept only once the run is
-- over: until then that instant may still be running.
closed : ∀ {X : Set} → Bool → List X → List X
closed true  xs           = xs
closed false []           = []
closed false (x ∷ [])     = []
closed false (x ∷ y ∷ xs) = x ∷ closed false (y ∷ xs)
