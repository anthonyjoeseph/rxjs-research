# `make agda-dev` — the iteration loop

```
make agda-dev ARGS='<file> <member>'   one member ← the grind loop; use constantly
make agda-dev ARGS='<file>'            one module, every member
make agda-dev ARGS='--list <file>'     free: which members are in which block
make agda-dev-selftest                 proves the loop is load-bearing
```

Paths are `src`-relative, and it works on ANY module you name. **Use it throughout
development and `make agda` once at the end** — seconds per member against minutes
for a real check of the same module.

One OPT-IN flag: **`HOLES=1`** tolerates `?` and missing clauses, off by default so
a `?` cannot pass silently. Its flags are scoped to the GENERATED module by a
file-level OPTIONS pragma — never on the command line, where they would apply to
the stdlib's `--safe` modules and fail inside `Data/Unit/Base.agda` before reaching
our code. (`SCOPE=1` is GONE: measured to buy no time, and against a dirty
dependency it wrote a scope-only interface and cost a rebuild.)

## Dev-green means the types line up, not that the proof is valid

**But only where something was STUBBED, and that is the part worth knowing.** A
module with no multi-member block is emitted VERBATIM with zero postulates, so the
sweep is a **real check** there; most of the repo is in that case.

Where a block IS stubbed, two things are given up:

- **Termination of the real mutual recursion is not checked** — and in this proof
  the mutual recursion IS the induction, so a bad measure passes dev and fails
  `make agda`. That is a proof-shape failure, not a typo.
- **Postulates do not reduce**, so a clause needing a sibling to unfold can pass dev
  and fail for real.

Self-recursion and recursion within one batch ARE checked. So the residual risk of
a dev-only workflow is concentrated in the handful of modules with a heavy block,
which is exactly where `make agda` earns its keep.

**`make agda` is still the merge gate:** never report a result as verified on a dev
run, never commit on one alone, never call dev-green "typechecks".

## There is no whole-project sweep, and do not rebuild one

It existed, was measured against `make gate`, and lost on both cost and fidelity —
strictly dominated, with no cache state in which it wins. It could not serve as a
cache-warmer either, since it checks a renamed copy and never writes the module's
real interface. **The loop's value is per-MEMBER, not per-tree.** The cheap pre-gate
role is already filled by `make wiring-gate` and `make unsafe-check`: textual,
seconds, and why `make gate` runs them first. A bare `make agda-dev` asks for a file
and exits 2.

## The per-file budget is enforced, not advisory

Over budget is a FAILURE, with the usual causes printed. The number lives in the
Makefile (`AGDA_DEV_BUDGET`) and is set from a full cold scan of every module,
sitting in the GAP in that distribution rather than just above the worst case —
**the gap is what makes a budget safe, not the margin**, because a budget set to
the worst observed time fails about half the time, that time being a distribution
and not a constant. Re-scan before moving it; the scan and the reasoning are in
`typecheck-performance-numbers.md`.

**A cold DEPENDENCY CHAIN still blows it** — edit one part of a split module, check
another, and you pay for the two in between. `BUDGET=<seconds>` exists for that
case, and that case only.

**A BUDGET THAT FAILS ON NORMAL WORK IS WORSE THAN NO BUDGET:** it trains everyone
to pass `BUDGET=` reflexively, and then a real regression sails through. Override
deliberately when the work has genuinely grown — and move the committed number when
it has, rather than overriding twice.

Rationale, measurements and the closed performance experiments also live in
`scripts/agda-dev.py`'s docstring; read that before re-opening any of it.

## A RED `agda-dev` on any file in `src` is a critical failure

**It must be GREEN on every file in `agda/src`, always.** A failure is a P0 defect
in the tooling, fixed *before* the work you were doing. Never route around it — not
with a skip list, not with "it's just the tool", not by falling back to `make agda`.
A single tolerated red teaches everyone to ignore the next one.

**The default assumption is that the TOOL is wrong, not the proof** — that is the
measured base rate, not politeness: every agda-dev failure ever investigated was a
bug in `scripts/agda-dev.py` and the proofs were fine.

**Do not diagnose from the error NAME.** Each such failure was misdiagnosed at least
once by reasoning about what the error class usually means, and solved in minutes by
reading the actual message and the generated file in the mirror's `_dev/`. Read the
file the tool produced — the bug is visible in it.

**The only acceptable "cannot check this file" is a MEASURED one, and it is a bug
report, not an exemption.** `NOT_DEV_CHECKABLE` exists for that, is currently EMPTY,
and empty is the target; its last entry was retired by splitting the file, not by
tolerating the exclusion.

## A block member in NO cycle is never stubbed, and that is what blows the budget

The loop's whole trick is that a focused check keeps ONE body real and replaces its
block-siblings with postulates. **A sibling the tool cannot stub is a sibling every
focused check re-proves in full** — and the tool cannot stub one whose body other
members' bodies need to reduce, which in practice is the members that are in the
block but in NO genuine cycle. Four such members are enough to make every check of
all the others cost what the whole file costs, and the symptom is uniform: every
shard times out at the same number, whatever body it was focused on. That symptom is
the tell — a per-member cost that does not vary with the member is not a member cost.

**`--list` already names them,** under `could in principle be hoisted out`, and its
warning is about a different and much smaller thing: the POSITIVITY cost inside
`make agda`, where hoisting 22 of 36 members bought 35s of 255s. The dev-loop effect
is the bigger one and points the same way, so a no-cycle member is worth hoisting on
the loop's evidence even when the gate would barely notice.

**Hoisting means MOVING IT OUT OF THE MODULE, not out of the block.** A definition
left in the file is still checked when the file is; only an import is cheap. A member
that takes the recursion as an ARGUMENT (`wl : WalkLevelAt …`) rather than calling it
is one that can move one arrow down and be imported back, which is the same fact that
kept it out of the cycle.

**And do not reach for the telescopes first, which is the tempting move and the wrong
one.** Naming a big signature as a `Set` abbreviation in a lower module is a real
device with a real second payoff — the obligation gets a name, so a caller states it
instead of retyping it — but as a COST fix it is noise: measured, moving a 72-line
telescope out was worth well under a second against the same file's 35s of unstubbable
bodies. Line counts predict nothing here. Attribute the cost first, on a coherent
cache, and hoist what the attribution names.

## Concurrency

`make agda-dev` sizes its own concurrency from measured RSS. But the dev loop and
the gate deliberately share ONE interface cache (the mirror's `_build`), so **a dev
run during a gate is a two-writer race** — Agda does not lock interfaces, and two
processes writing the same `.agdai` give a corrupt cache or a spurious failure in a
run that costs many minutes to repeat. Not obvious, and the easy way to trip it.
