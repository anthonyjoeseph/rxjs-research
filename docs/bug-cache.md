# `make bug-cache` — the cached-counterexample corpus

When you discover an implementation bug, capture it immediately as a row of
`agda/src/Implementation/Unit-Test.agda` — a named program, run by a compiled
binary rather than normalised by the typechecker.

These are a **performance cache** of discovered work: faster to recheck than
QuickCheck, and pinned to a specific canonical program (spec-derived), so a
regression is caught by one `make bug-cache` instead of surfacing only in a
random seed. They exist only to accelerate finding the implementation; they are
**not** meant to survive past the proof. Delete the corpus once
`The-Proof.agda` is discharged.

## It runs, it does not typecheck — and that is the whole design

A row used to be `_ : impl prog ≡ expected`, checked by `refl`. That put a whole
`evaluate` run inside the typechecker, and it cost **minutes per case**: the run
is normalised, the termination check is paid on the way, and the cache is
append-only, so the gate's bill grew with the corpus without bound. Two cases
were enough to take a gate run down.

Compiled, the same run is a function call. So the structure the cost forced —
one module per case, a ledger of import-and-pin blocks, two separate *types* for
the two predicates — is gone, and what is left is a list.

- `Unit-Test/Prelude.agda` — what a `Case` is (a label, a fuel, a program, its
  slots) and the two predicates every row is held to: `wellFormed` and `agrees`.
- `Unit-Test.agda` — the corpus: `cases : List Case`, one row per cached
  counterexample.
- `Unit-Test/Bug-Cache.agda` — the runner. A `MODULE_ROOTS` entry, compiled to
  `agda/_cli/Bug-Cache`.

## Both predicates, every row

Asking twice is free once the run is compiled, so a row says only *which run to
make* and the runner checks both properties of it. That is strictly more than
the type-level cache carried: a program cached for a protocol violation now also
guards agreement, the property the whole campaign is about. It is also what
makes the dedup key work — a program that fails both checks wants one row, not
two.

## The verdict is text, and the target demands the summary

`CLI.IO`'s whole FFI surface is stdin and stdout — there is no exit status to
hand back — so the runner prints

```
bug-cache: FAIL <name> <property>     (one per failing property)
bug-cache: ran <N> cases, <M> failures
```

and `make bug-cache` **requires the summary line before it refuses any `FAIL`
line**. That order matters: a binary that walked nothing prints nothing, and a
grep for failures alone would read that as green.

## Append-only

`scripts/gen-unit-tests.sh [FIRST] [LAST] [RUNS] [DEPTH]` appends each new
counterexample (deduped by program text) and never deletes or overwrites. A
fixed bug just becomes a passing guard that stays forever.

**Invariant: every row holds ⟺ no known counterexample remains.** Green is the
impl≡spec finish line for the cached cases.

`QuickCheck` reads `SEED [RUNS] [DEPTH]` on stdin (runs before depth; defaults
200 and 4): DEPTH caps program nesting, a hard size cap. It prints each failure
as a `-- <<<PASTE` / `-- PASTE>>>` block which **is already a corpus row**,
trailing `∷` included, with the name written `"?"` so that a hand-pasted block
typechecks as it stands. Both checks emit the same block shape, so the program
line dedups them against each other. The script substitutes the seed and splices
the row in above the list's `[]`; it never builds or parses Agda.

## The machine-owned import block

A row can mention any constructor the generator can emit, and nothing knows
which until the row exists. So the corpus's imports sit between `-- <<<IMPORTS`
and `-- IMPORTS>>>` markers, and the generator **rewrites that region wide
before appending, then runs `make imports-fix` to prune it**. Both halves are
owed: a dead import is an `imports-check` failure, and a pruned block cannot
scope the next row. Edit the wide form in the generator, never between the
markers.

The prune runs even when a sweep finds nothing, since the widening did too.

## Why the target exists

The corpus is **not** reachable from `Main.agda`, so `make gate-heavy`'s tower
does not check it. `make bug-cache` enforces the invariant above — it exists
precisely because nothing else in the build would notice the cache rotting.

## What is deliberately not cached

A run that went **dry** — a descent guard exhausted — is a counterexample to
`rank-sufficient`, which is a postulate rather than a disagreement between two
implementations of one batching. QuickCheck reports it loudly and without PASTE
markers, and it stays out of a corpus whose verdict gates the build.
