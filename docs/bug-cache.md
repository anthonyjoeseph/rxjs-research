# `make bug-cache` — type-level unit tests

When you discover an implementation bug, capture it immediately as a **type-level
unit test** in `agda/src/Implementation/Unit-Test.agda` — a `_ : impl prog ≡ expected`
that Agda checks by `refl` at compile time.

These are a **performance cache** of discovered work: faster to recheck than
QuickCheck, faster at the type level than at runtime. They pin down the exact value
the impl must produce for a specific canonical program (spec-derived), so a
regression fails the typechecker instantly instead of surfacing only in a random
seed.

Keep them dead simple — no fancy names, no abstraction, just a wall of little
`_ : … ≡ …` entries. They exist only to accelerate finding the implementation; they
are **not** meant to survive past the proof. Delete the module once
`The-Proof.agda` is discharged.

## Append-only

`scripts/gen-unit-tests.sh [FIRST] [LAST] [RUNS] [DEPTH]` appends each new
counterexample (deduped by program text) and never deletes or overwrites. A fixed
bug just becomes a passing guard that stays forever.

**Invariant: `Unit-Test.agda` fully typechecks ⟺ no known counterexample remains.**
Green there is the impl≡spec finish line.

`QuickCheck` reads `SEED [RUNS] [DEPTH]` on stdin (runs before depth; defaults 200
and 4): DEPTH caps program nesting, a hard size cap.

## Why the target exists

`Unit-Test.agda` is **not** reachable from `Main.agda`, so `make gate-heavy` does not check
it. `make bug-cache` enforces the invariant above — it exists precisely because
nothing else in the build would notice the cache rotting.
