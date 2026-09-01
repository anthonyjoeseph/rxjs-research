# `make agda-dev` — the iteration loop

```
make agda-dev ARGS='<file> <member>'   one member ← the grind loop; use constantly
make agda-dev ARGS='<file>'            one module, every member
make agda-dev ARGS='--list <file>'     free: which members are in which block
make agda-dev-selftest                 proves the loop is load-bearing
```

Paths are `src`-relative, and it works on ANY module you name. **Use it throughout
development and `make gate-heavy` once at the end** — seconds per member against minutes
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
  `make gate-heavy`. That is a proof-shape failure, not a typo.
- **Postulates do not reduce**, so a clause needing a sibling to unfold can pass dev
  and fail for real.

Self-recursion and recursion within one batch ARE checked. So the residual risk of
a dev-only workflow is concentrated in the handful of modules with a heavy block,
which is exactly where `make gate-heavy` earns its keep.

**`make gate-heavy` is still the merge gate:** never report a result as verified on a dev
run, never commit on one alone, never call dev-green "typechecks".

## A module's own number never predicts what its CONSUMER's first check costs

The loop stubs mutual blocks in the TARGET only, and checks every dependency for
real. So a per-module number is measured with that module's own blocks stubbed,
while the first check of any CONSUMER after an edit pays the UNSTUBBED cost of
every module in between — a quantity no row in the numbers file is about, since
no dev run ever measures it.

The asymmetry bites hardest in the middle of the tower, where a module with a
heavy block reads as seconds on its own and costs far more than that number
suggests when something downstream forces the real build. Measured once: an edit
to a mid-tower module invalidated two such modules, and four successive checks of
a consumer were killed by the budget while paying for them — each one reading as
a blowup in the consumer, which was never slow at all.

**The attribution, and it is two cheap runs.** Truncate the consumer to its
import list and check that: if the truncation is slow too, nothing in the module
is slow and the cost is entirely below it. Then check each import alone in a
throwaway module — a cached dependency answers in seconds and the culprit does
not. Both runs are decisive, and both are cheaper than one more killed check of
the consumer.

## There is no whole-project sweep, and do not rebuild one

It existed, was measured against `make gate`, and lost on both cost and fidelity —
strictly dominated, with no cache state in which it wins. It could not serve as a
cache-warmer either, since it checks a renamed copy and never writes the module's
real interface. **The loop's value is per-MEMBER, not per-tree.** The cheap pre-gate
role is already filled by `make wiring-gate` and `make unsafe-check`: textual,
seconds, and why `make gate` runs them first. A bare `make agda-dev` asks for a file
and exits 2.

## The per-file budget is enforced, not advisory

Over budget is a FAILURE, with the usual causes printed. The number reaches the
Makefile as `AGDA_DEV_BUDGET` but is picked per environment by
`scripts/detect_env.py` (see below), and the laptop's is set from a full cold
scan of every module,
sitting in the GAP in that distribution rather than just above the worst case —
**the gap is what makes a budget safe, not the margin**, because a budget set to
the worst observed time fails about half the time, that time being a distribution
and not a constant. Re-scan before moving it; the scan and the reasoning are in
`typecheck-performance-numbers.md`.

**A cold DEPENDENCY CHAIN still blows it** — edit one part of a split module, check
another, and you pay for the two in between. `BUDGET=<seconds>` exists for that
case, and that case only.

**AND A BUDGET-KILLED RUN CACHES NOTHING, so retrying at the same budget makes no
progress at all** — each attempt redoes the same partial rebuild and is killed at the
same place. The tell is a file that dev-checked in seconds yesterday and now runs for
minutes: something LOW in its cone was edited, and the loop is rebuilding that cone
for real, since it stubs mutual blocks only in the TARGET. The repair is to let ONE
run finish with a generous `BUDGET=`, after which the cone is warm and the normal
budget holds again — measured on this tree at three hundred and eighty-one seconds
for the first run after an edit to the caps recurrence, and fifteen for every run
after it. Retrying under the default in between costs the whole rebuild each time and
buys nothing.

**A BUDGET THAT FAILS ON NORMAL WORK IS WORSE THAN NO BUDGET:** it trains everyone
to pass `BUDGET=` reflexively, and then a real regression sails through. Override
deliberately when the work has genuinely grown — and move the committed number when
it has, rather than overriding twice.

Rationale, measurements and the closed performance experiments also live in
`scripts/agda-dev.py`'s docstring; read that before re-opening any of it.

## The budget is per-environment, not a laptop constant

`AGDA_DEV_BUDGET` (and `dev-changed`'s `--cone-budget`) used to be one number,
`45`, applied everywhere this tooling runs. It was measured on one laptop and
was simply wrong for the other two places this campaign runs: a cloud
container's four representative modules ran 1.2x-2.9x the laptop's own figure
for the same module, and `45` there is not a gap above the worst case, it is
routinely *below* it.

**`scripts/detect_env.py` picks the budget now, not the Makefile.** It decides
which of the three environments (`local` / `cloud` / `ci`) is live —
`GITHUB_ACTIONS=true` settles CI outright; `CLAUDE_CODE_REMOTE=true` or a
non-empty `CLAUDE_CODE_CONTAINER_ID` settles a Claude Code Remote container
(deliberately not the generic `CLAUDECODE=1`, which is set identically whether
Claude Code is running interactively on a laptop or inside a spawned
container, and so cannot tell the two apart); absent both, it is the laptop,
the correct fallback for a signal nobody has set. The Makefile does
`AGDA_DEV_BUDGET ?= $(shell scripts/detect_env.py --budget)` and the same for
`AGDA_DEV_CONE_BUDGET`, so `?=` still means `BUDGET=`/`CONE_BUDGET=` and an
explicit `AGDA_DEV_BUDGET=`/`AGDA_DEV_CONE_BUDGET=` on the command line win
outright and the detector never runs at all.

**The cloud figure has a measured FLOOR and a chosen CEILING, and only the
floor is evidence.** Four representative modules were dev-checked cold on a
real container — openly a smaller sample than the laptop's exhaustive cold
scan, since session time did not allow a full 66-module one — and they put a
worst case under the budget. Every number well clear of that satisfies the
argument, and the argument picks none of them, so where the ceiling actually
sits is Anthony's call about how long a loop may take. Do not read the cloud
budget back as a measurement of the container. The four modules and the
reasoning are in `scripts/detect_env.py` itself; the actual green rows are in
`typecheck-performance-numbers.md`'s cloud-container section, which grows
every time a real `agda-dev`/`gate-heavy` run completes there. CI currently
borrows the cloud figure as a placeholder (same non-macOS shape) until it
accumulates its own tagged rows the same way.

**A budget derived on one environment is not evidence for another,
ever** — do not eyeball a cloud number and decide the laptop's 45s "should"
also move, and do not re-scan the laptop to fix a cloud timeout. Each
environment's figure is re-scanned and re-derived independently, from that
environment's own rows.

## A RED `agda-dev` on any file in `src` is a critical failure

**It must be GREEN on every file in `agda/src`, always.** A failure is a P0 defect
in the tooling, fixed *before* the work you were doing. Never route around it — not
with a skip list, not with "it's just the tool", not by falling back to `make gate-heavy`.
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

## Every stub sits at its own source position, and that is a scope rule

A stubbed member's `postulate` is emitted where that member's own signature already
sits, never gathered with its block-siblings at the block's head. **Source order is
the scope argument**: the file compiles, so its own order is valid by construction,
and a stub that moves can only move ABOVE something its signature reads. That failure
does not surface where the move happened — it surfaces as a `NotInScope` naming the
definition that got jumped, which reads as a missing name rather than a reordering.

The case that forces per-member placement rather than one delayed block is a mutual
block whose members STRADDLE a Set-valued definition used in a later member's type —
common once a forward declaration joins two regions of a file into one block. Gathering
the stubs anywhere puts that later signature on the wrong side of the definition it
reads. Keeping each where it already was needs no regex enumerating what a signature
may mention, which is the only other way to get it right.

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
`make gate-heavy`, where hoisting 22 of 36 members bought 35s of 255s. The dev-loop effect
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
