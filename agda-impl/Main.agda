{-# OPTIONS --guardedness #-}

-- MAIN IS THE TOP-LINE PROOF (Anthony).  Whatever it imports sticks
-- around; it names individual definitions, never a bare `open import`;
-- it is never touched without Anthony's explicit approval.  It is the
-- root `make wiring` traces from, and Agda checks exactly what it
-- reaches, so it is the build's coverage as well as its claim set.
module Main where

-- THE THEOREM: what the pure semantics shows is exactly what a reader of
-- the program's emission set meets, row by row in position order.
open import adequacy.Adequacy using (adequacy)

-- THE MEANING IS COMPOSITIONAL: each operator's emission set is its
-- operator's rows over its children's emission sets.
-- MAP FUSES: `map (f ∘ g)` and `map f ∘ map g` mean the same, and so,
-- through adequacy, run the same.
open import denotation.Laws using (compositional; map-fusion)

-- THE SIMULTANEOUS SPEC: an author's program, elaborated with
-- `batchSimultaneous` on top, groups what plain rxjs delivers by instant,
-- in order, releasing each batch the moment its instant is over.
open import simultaneous.Statement using (left-to-right; coherent; batchable; positioned)

-- THE LIBRARY: what a user writes programs with, beyond the primitives
-- the theorem's statement already reaches.
open import Tree using (merge; flatMap; ones)

-- THE TESTS: the property the theorem asserts, sampled — and the oracle
-- that renders one program's run on each runtime.
open import quickcheck.Quickcheck using (quickcheck)
open import quickcheck.Oracle using (oracle)

-- THE EMISSION SET'S LISTING: an uncut listing lists the emission set's
-- rows exactly, so the oracle comparing it with rxjs is testing the
-- emission set itself.
open import quickcheck.Tabled.Exact using (tabled-exact)
