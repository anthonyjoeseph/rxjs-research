{-# OPTIONS --guardedness #-}

-- READING A RUN THE WAY THE SPEC DOES.  A run is coinductive and may
-- never end, so every claim is read off its first n events and quantified
-- over n.
--
-- AN INSTANT IS A CASCADE'S ROOT, READ OFF THE POSITION.  The subscribe
-- frame sits under `root`; a timer cascade at tick t sits under
-- `ix t ∷ sub e ∷ []`, `e` where its timer was created, and its tick is
-- never 0.  The tick alone is too coarse, since two timers firing at one
-- tick are two cascades; the whole position is too fine, since every
-- event of one cascade has its own.
module simultaneous.Readings where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Label; ix; sub; last; root; out; skip; end; hush)
open import simultaneous.InstEmit using (InstEmit; Provenance; valuesOf)

open Events∞ using (force)
open InstEmit using (instant)

-- Every position lies under one of the two: the subscribe frame, whose
-- first step is never a `sub`, or a timer cascade, never at tick 0.
-- This is what makes `instantOf` read the instant, and nothing else does.
data NotSub : Label → Set where
  ix-ns   : ∀ {i} → NotSub (ix i)
  last-ns : NotSub last

data Rooted : Pos → Set where
  in-frame   : ∀ {l p} → NotSub l → Rooted (ix 0 ∷ l ∷ p)
  in-cascade : ∀ {t e p} → Rooted (ix (suc t) ∷ sub e ∷ p)

instantOf : Pos → Pos
instantOf (ix t ∷ sub e ∷ _) = ix t ∷ sub e ∷ []
instantOf _                  = root

-- The run past its first n events.
after : ∀ {A} → ℕ → Events A → Events A
after zero    e           = e
after (suc n) (out _ _ k) = after n (force k)
after (suc n) (skip _ k)  = after n (force k)
after (suc n) (end c)     = end c
after (suc n) hush        = hush

-- The values among the first n events, each at its position.
outs : ∀ {A} → ℕ → Events A → List (Pos × A)
outs zero    _           = []
outs (suc n) (out p a k) = (p , a) ∷ outs n (force k)
outs (suc n) (skip _ k)  = outs n (force k)
outs (suc n) (end _)     = []
outs (suc n) hush        = []

-- The values among the first n events.
values : ∀ {A} → ℕ → Events A → List A
values n e = map proj₂ (outs n e)

-- Where each of the first n events sits, its silent steps and its
-- completion too.
positions : ∀ {A} → ℕ → Events A → List Pos
positions zero    _           = []
positions (suc n) (out p _ k) = p ∷ positions n (force k)
positions (suc n) (skip p k)  = p ∷ positions n (force k)
positions (suc n) (end c)     = c ∷ []
positions (suc n) hush        = []

-- Whether the first n events reach the run's end: its completion, or
-- the silence that never completes.  Either way no instant is left open.
over : ∀ {A} → ℕ → Events A → Bool
over zero    _           = false
over (suc n) (out _ _ k) = over n (force k)
over (suc n) (skip _ k)  = over n (force k)
over (suc n) (end _)     = true
over (suc n) hush        = true

------------------------------------------------------------------------
-- Finite instants

-- The run leaves instant `i` after finitely many events: an event of
-- another instant, or the run's end.
data Exits {A} (i : Pos) : Events A → Set where
  ends     : ∀ {c} → Exits i (end c)
  hushes   : Exits i hush
  out-to   : ∀ {p a k} → instantOf p ≢ i → Exits i (out p a k)
  skip-to  : ∀ {p k} → instantOf p ≢ i → Exits i (skip p k)
  out-on   : ∀ {p a k} → Exits i (force k) → Exits i (out p a k)
  skip-on  : ∀ {p k} → Exits i (force k) → Exits i (skip p k)

Settles : ∀ {A} → Events A → Set
Settles (out p _ k) = Exits (instantOf p) (force k)
Settles (skip p k)  = Exits (instantOf p) (force k)
Settles (end _)     = ⊤
Settles hush        = ⊤

-- Every instant of the run is over after finitely many events.  `ones`
-- is not: its instant never ends, so its batch never leaves.
FiniteInstants : ∀ {A} → Events A → Set
FiniteInstants e = ∀ n → Settles (after n e)

------------------------------------------------------------------------
-- InstEmit streams

-- Each value an emit carries, with the emit's provenance.
stamped : ∀ {A} → List (InstEmit A) → List (Provenance × A)
stamped []       = []
stamped (x ∷ xs) = map (λ a → instant x , a) (valuesOf x) ++ stamped xs

-- A grouping read off a prefix, its last group kept only once the run is
-- over: until then that instant may still be running.
closed : ∀ {X : Set} → Bool → List X → List X
closed true  xs           = xs
closed false []           = []
closed false (x ∷ [])     = []
closed false (x ∷ y ∷ xs) = x ∷ closed false (y ∷ xs)
