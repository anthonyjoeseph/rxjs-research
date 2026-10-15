# `make bug-cache` — the cached-counterexample corpus

When a program trips the implementation, capture it immediately as a row of
`agda-impl/quickcheck/Bug-Cache.agda`: `cases : List (String × Prog natᵗ)`, a
label and a program. A wall of little entries — the tricky cases already
overcome, kept so none of them regresses.

## It runs, it does not typecheck

A row is checked by a compiled binary, `agda-impl/quickcheck/Bug-Cache-Runner.agda`
(a `MODULE_ROOTS` entry in the wiring checker), compiled to
`agda-impl/_cli/Bug-Cache-Runner`. A row checked by `refl` would put a whole run
inside the typechecker, and the corpus is append-only, so the gate's bill would
grow with it without bound.

The runner holds each row to `quickcheck.Quickcheck.prop` — the property the
QuickCheck sweep samples — and to `quickcheck.Placing.placing`, which `make
placing` samples: a meaning silent where the machine works on agrees with it by
ticks, and only the positional check sees it. A row says only which program to
run.

**The runner matches its verdicts in a helper, never with a `with`.** A `with` on
the verdict makes the typechecker normalise a whole run and exhausts any heap;
see [agda-traps.md](agda-traps.md).

## The verdict is text, and the target demands it

The runner prints one `bug-cache: FAIL <label>` per failing row, then
`bug-cache: done <N> rows`. `make bug-cache` **requires the `done` line before it
refuses any `FAIL` line** — a binary that died part-way prints no `done`, and a
grep for failures alone would read that as green.

## Append-only

Never delete or overwrite a row. A fixed bug becomes a passing guard that stays.

**Invariant: `make bug-cache` green ⟺ no known counterexample remains.**

## Where it runs

Not in `make gate`: it checks the evaluator through GHC and the FFI, not the
proof, so **no proof may ever depend on it**. CI runs it as its own job, with the
compiled MAlonzo objects cached on the toolchain. Never run locally — CI only.
