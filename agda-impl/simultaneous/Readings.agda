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
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; ix; sub; root; out; skip; end; hush)
open import simultaneous.InstEmit using (InstEmit; Provenance; valuesOf)

open Events∞ using (force)
open InstEmit using (instant)

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
stamped : ∀ {A} → List (Pos × InstEmit A) → List (Provenance × A)
stamped []             = []
stamped ((_ , x) ∷ xs) = map (λ a → instant x , a) (valuesOf x) ++ stamped xs

-- The emits carrying a value: where each sits, and its provenance.
valued : ∀ {A} → List (Pos × InstEmit A) → List (Pos × Provenance)
valued []             = []
valued ((p , x) ∷ xs) with valuesOf x
... | []    = valued xs
... | _ ∷ _ = (p , instant x) ∷ valued xs

-- A grouping read off a prefix, its last group kept only once the run is
-- over: until then that instant may still be running.
closed : ∀ {X : Set} → Bool → List X → List X
closed true  xs           = xs
closed false []           = []
closed false (x ∷ [])     = []
closed false (x ∷ y ∷ xs) = x ∷ closed false (y ∷ xs)
