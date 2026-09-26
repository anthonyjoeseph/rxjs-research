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
  slots) and `checksOf`, the labelled properties every row is held to: the run
  well-formed, impl≡spec, plain-agrees, and the `WellFormed` fields `same`,
  `distinct` and `ends`.
- `Unit-Test.agda` — the corpus: `cases : List Case`, one row per cached
  counterexample.
- `Unit-Test/Bug-Cache.agda` — the runner. A `MODULE_ROOTS` entry, compiled to
  `agda/_cli/Bug-Cache`.

## Every property, every row

Asking again is free once the run is compiled — `checksOf` makes each run once
and hands it to every check — so a row says only *which run to make* and the
runner checks every property of it. A program cached for a protocol violation
also guards agreement, the property the whole campaign is about. It is also what
makes the dedup key work — a program that fails several checks wants one row,
not several.

## One row per process, under a budget

The runner reads a row number on stdin and runs that row alone; `0` asks for
the row count. The oracle tree is built with termination checking off, so a
row's run can fail to END — a counterexample like any other, but one that inside
a single walk of the corpus would take every later verdict with it and hold the
CI job to its timeout. So `make bug-cache` starts one process per row under
`BUG_CACHE_ROW_BUDGET` seconds (default 60), and a row over budget is a `FAIL`
named by the row: the runner prints and flushes the name before the run starts.

## The verdict is text, and the target demands it

`CLI.IO`'s whole FFI surface is stdin and stdout — there is no exit status to
hand back — so for one row the runner prints

```
bug-cache: row <name>
bug-cache: FAIL <name> <property>     (one per failing property)
bug-cache: done
```

and `make bug-cache` **requires every row's `done` line before it refuses any
`FAIL` line**, then prints `bug-cache: ran <N> cases, <M> failing`. That order
matters: a binary that ran nothing prints nothing, and a grep for failures alone
would read that as green.

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

## Why the target exists, and why it runs in the oracle job

The corpus is **not** reachable from `Main.agda`, so `make gate-heavy`'s tower
does not check it. `make bug-cache` enforces the invariant above — it exists
precisely because nothing else in the build would notice the cache rotting.

**It runs in CI's oracle job, not the gate.** What it checks is the evaluator
rather than the proof, so it belongs beside the sweep, on the same build: the
oracle's own tree (`make oracle-tree`, `scripts/oracle-mirror.py`), compiled with
termination checking off and cached as binaries keyed on the runners' import
cone. `make gate-heavy` still LINKS its own copy (`bug-cache-build`), so a runner
that stops compiling under the full check goes red there. In the oracle job it
runs last and on `always()`, so a red corpus and a red sweep are both reported.

**The runner matches its verdicts in a helper, never with a `with`.** A `with` on
`agrees c` makes the typechecker normalise a whole evaluator run and exhausts any
heap; see [agda-traps.md](agda-traps.md).

## What is deliberately not cached

A run that went **dry** — a descent guard exhausted — is a counterexample to
`rank-sufficient`, which is a postulate rather than a disagreement between two
implementations of one batching. QuickCheck reports it loudly and without PASTE
markers, and it stays out of a corpus whose verdict gates the build.
