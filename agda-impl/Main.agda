{-# OPTIONS --guardedness #-}

-- MAIN IS THE TOP-LINE PROOF (Anthony).  Whatever it imports sticks
-- around; it names individual definitions, never a bare `open import`;
-- it is never touched without Anthony's explicit approval.  It is the
-- root `make wiring` traces from, and Agda checks exactly what it
-- reaches, so it is the build's coverage as well as its claim set.
module Main where

-- THE THEOREM, ON THE STATE TREE: the pure semantics' run
-- (`operation.PureObservable`) is the denotation's, observed at time 0.
-- The IO semantics is the same machine driven by the world
-- (`operation.Observable`).
open import adequacy.Adequacy using (adequacy)

-- THE THEOREM, PORTED (Tier 0): the same, over the pointer-free engine
-- (`port.operation.PureObservable`).
open import port.adequacy.Adequacy using (adequacy)

-- THE MEANING IS A FOLD: the theorem's denotation is the limit of each
-- operator's `MonotonicList` function applied to its children's.
open import denotation.Denote using (folded)

-- THE MEANING IS COMPOSITIONAL: a node's meaning is its operator applied
-- to its children's meanings, so proofs over it go one operator at a time.
open import denotation.Compositional using (compositional)

-- MAP FUSES: `map (f ∘ g)` and `map f ∘ map g` mean the same, and so,
-- through adequacy, run the same.
open import denotation.Laws using (map-fusion; map-fusionᴾ)

-- THE SIMULTANEOUS SPEC: an author's program, elaborated with
-- `batchSimultaneous` on top, groups what plain rxjs delivers by instant,
-- in order, releasing each batch the moment its instant is over.
open import simultaneous.Statement using (left-to-right; coherent; batchable; positioned)

-- THE ANCHOR: the same spec, met by what a reader of the pure runtime
-- sees, carried across `adequacy`.
open import simultaneous.Pure using (left-to-rightᴾ; batchableᴾ)

-- THE LIBRARY: what a user writes programs with, beyond the primitives
-- the theorem's statement already reaches.
open import Tree using (merge; flatMap; ones)
open import denotation.MonotonicList using (mergeᴰ; flatMapᴰ; fixᴰ; iterate; fix-unfold)

-- THE TESTS: the property the theorem asserts, sampled — and the oracle
-- that renders one program's run on each of the three runtimes.
open import quickcheck.Quickcheck using (quickcheck)
open import quickcheck.Oracle using (oracle)
