{-# OPTIONS --guardedness #-}

-- MAIN IS THE TOP-LINE PROOF (Anthony).  Whatever it imports sticks
-- around; it names individual definitions, never a bare `open import`;
-- it is never touched without Anthony's explicit approval.  It is the
-- root `make wiring` traces from, and Agda checks exactly what it
-- reaches, so it is the build's coverage as well as its claim set.
module Main where

-- THE THEOREM: the pure runtime's run is the denotation's, observed at
-- time 0.  The IO runtime is the same engine over a different monad.
open import adequacy.Adequacy using (adequacy)

-- THE MEANING IS A FOLD: the theorem's denotation is the limit of each
-- operator's `MonotonicList` function applied to its children's.
open import denotation.Denote using (folded)

-- THE MEANING IS COMPOSITIONAL: a node's meaning is its operator applied
-- to its children's meanings, so proofs over it go one operator at a time.
open import denotation.Compositional using (compositional)

-- THE LIBRARY: what a user writes programs with, beyond the primitives
-- the theorem's statement already reaches.
open import Tree using (merge; flatMap; ones)
open import denotation.MonotonicList using (mergeᴰ; flatMapᴰ; fixᴰ; iterate; fix-unfold)

-- THE TESTS: the property the theorem asserts, sampled — and the oracle
-- that renders one program's run on each of the three runtimes.
open import quickcheck.Quickcheck using (quickcheck)
open import quickcheck.Oracle using (oracle)
