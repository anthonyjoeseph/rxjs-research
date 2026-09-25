------------------------------------------------------------------
-- DECIDING TWO BATCHINGS EQUAL AS A BOOLEAN, for the two compiled
-- binaries that have to compare them without a typechecker underneath.
-- What is compared is the top line's currency: per burst, the batches'
-- raw values, with no envelope left on either side.
--
-- WHY A BOOLEAN AND NOT A DECISION PROCEDURE.  Nothing here is used in
-- a proof: both consumers are `main`s that print a verdict, so what is
-- wanted is a comparison the GHC backend runs, not a witness.  A
-- `Dec (xs ≡ ys)` would oblige every constructor along the way to
-- carry an injectivity argument for a value that is thrown away at the
-- moment it is printed.
--
-- THE VALUE TYPE IS FIXED AT `ℕ` RATHER THAN GENERALISED.
-- Generalising over the payload would need an equality on it passed
-- in, and there is exactly one payload either caller ever compares.
--
-- IT IS A SEPARATE MODULE BECAUSE IT HAS TWO ROOTS.  The QuickCheck
-- binary and the bug cache's runner are each compiled entry points
-- reachable from neither the other nor Main, so a family living in
-- one of them cannot be spent by the other -- and the duplicate that
-- would otherwise be written is precisely what `make dup-check`
-- exists to refuse.  It sits directly above the protocol's own
-- vocabulary so that the cone either caller pays for is that
-- vocabulary and nothing else.
------------------------------------------------------------------
module Rx.Emit-Eq where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≡ᵇ_)

eqListℕ : List ℕ → List ℕ → Bool
eqListℕ []       []       = true
eqListℕ (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqListℕ xs ys
eqListℕ _        _        = false

-- one burst: its batches, in order
eqBatches : List (List ℕ) → List (List ℕ) → Bool
eqBatches []       []       = true
eqBatches (x ∷ xs) (y ∷ ys) = eqListℕ x y ∧ eqBatches xs ys
eqBatches _        _        = false

eqBursts : List (List (List ℕ)) → List (List (List ℕ)) → Bool
eqBursts []       []       = true
eqBursts (x ∷ xs) (y ∷ ys) = eqBatches x y ∧ eqBursts xs ys
eqBursts _        _        = false
