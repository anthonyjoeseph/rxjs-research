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
-- `batchSimultaneous` on top, batches the way the stamps batch — each
-- batch stamped with the instant it leaves in is the spec's grouping of
-- the plain run's values stamped the same way.
open import simultaneous.Statement using (spec)

-- THE INSTANT IS THE TIMESTAMP: the subscribe frame is one instant, and
-- each async emission is its own.  An effect runs in its cause's
-- instant, an async emission's instant is shared only beneath it, two
-- async emissions are never one instant, instants order the subscribe
-- frame first then by tick then by creator then by step, a cascade fires
-- after its creator, and an instant is an interval of positions.
open import denotation.Simultaneity using (effect-instant; cascade-own; frame-own; cascade-inj;
  frame-first; later-tick; same-tick; same-timer; after-creator; between)

-- THE ORDER IS THE CALL TREE'S PRE-ORDER: a position flattened to one
-- label list, its instant leading, orders and nests as that list does.
open import denotation.Flat using (flat-order; flat-inside; flat-onto)

-- THE ENGINE SCHEDULES IN THAT ORDER: a key, `after` read as one label
-- past every other, orders as its flat list does.
open import operation.Key using (flat-key)

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
