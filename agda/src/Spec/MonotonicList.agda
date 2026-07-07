-- Time, and lists that are sorted BY CONSTRUCTION.
--
-- The spec's whole authority comes from timestamps, so a "timed
-- observable" whose sortedness is a separate theorem is a weaker
-- statement than one whose type guarantees it. A MonotonicList bundles
-- the list with its sortedness evidence: spec-level functions traffic in
-- MonotonicList, so `batchSpec` (group equal adjacent times) is
-- meaningful on every input it can receive.
module Spec.MonotonicList where

open import Prelude

------------------------------------------------------------------------
-- Time = (tick, origin), lexicographic. Tick 0 is the subscription
-- frame; tick k+1 is the k-th async emission. The origin coordinate
-- orders feedback: a reentrant .next() lands strictly after the batch
-- that caused it.

Time : Set
Time = ℕ × ℕ

t₀ : Time
t₀ = (zero , zero)

timeLeq : Time → Time → Bool
timeLeq (a , b) (c , d) =
  if ltℕ a c then true else (if eqℕ a c then leqℕ b d else false)

------------------------------------------------------------------------
-- sortedness as an inductive predicate mirroring list structure

data Sorted {A : Set} : List (Time × A) → Set where
  sorted-[]   : Sorted []
  sorted-one  : {t : Time} {a : A} → Sorted ((t , a) ∷ [])
  sorted-cons : {t u : Time} {a b : A} {xs : List (Time × A)}
              → timeLeq t u ≡ true
              → Sorted ((u , b) ∷ xs)
              → Sorted ((t , a) ∷ (u , b) ∷ xs)

------------------------------------------------------------------------
-- the verified-at-compile-time timed list

record MonotonicList (A : Set) : Set where
  constructor mono
  field
    list   : List (Time × A)
    sorted : Sorted list
open MonotonicList public

emptyM : {A : Set} → MonotonicList A
emptyM = mono [] sorted-[]
