# Working methodology

This repo pairs an **Agda model** (`agda/`) with a **TypeScript implementation** (`typescript/`).
Agda's spec is gospel; TS conforms to it.

## The Agda impl MUST mirror the TS impl

The Agda **implementation** (`Implementation/`, as opposed to the `Spec/`) exists to model
what the **real rxjs TypeScript** does, operator for operator. It may only use capabilities a
plain rxjs pipeline actually has. A Mealy machine is globally clocked by its input stream, so
it is tempting to lean on per-input boundaries that rxjs does NOT expose downstream — e.g.
grouping *every* synchronous tick's emissions when rxjs's `batchSync` can only bracket the
**subscribe frame** (its `isSync` flag), treating all later emits as individual `async` ones.
Do not do this. If the Agda impl relies on something the TS cannot do, it has diverged and the
correspondence is void. When in doubt about whether a mechanism is portable, **port it to TS
and run the oracle before building on it.**

## Open question: is observable-level provenance sufficient? (report immediately if not)

The impl batches by **observable-level provenance** — a provenance minted once per source
observable, plus a per-provenance subscription count (`cTotal`, the "counting machine") to
recover instant boundaries. The alternative is **per-emission (per-instant) provenance**, which
is exact by construction but costs an id allocation per firing. We are **committed to the
counting machine** for now (it is cheaper, and `Observable` is a hot primitive on the order of
`Promise`/`Array`).

The one finding that would force a change: **definitive proof that observable-level provenance is
fundamentally lossy — that the IMPLEMENTATION contradicts itself, not merely the spec.** This is
NOT the same as "impl disagrees with the spec": the spec is gospel and we are not uncertain about
the desired batching, so a single program where the counting machine gets the wrong answer is
only a *bug we fix by changing the implementation.* The implementation is a pipeline — the
primitives render a run to an emit stream, then `batchSimultaneous` (a pure function of that
stream) recovers the batches. The impossibility proof is **two real programs whose primitives
produce byte-identical emit streams (same provenances, init/close, values, order) but that
genuinely batch differently when run** (ground truth = what real rxjs does, i.e. its synchronous
grouping — independently of the Agda spec). Then a *single* emit stream is demanded to yield two
different batchings, so NO stream-reading implementation — the entire observable-provenance
paradigm — can satisfy both. That is the implementation in contradiction with itself: its own
emit-stream stage collapses two runs that its batching stage must separate, and no change to the
counting rule can recover information the interface already threw away. An attempt to build such
a pair failed once (distinct-value emits are unambiguous; registration counts tend to distinguish
the ambiguous cases), so it is genuinely open. **If you find such a pair, STOP and tell Anthony
immediately; do not act on it — we decide next steps together.**

## The goal: nothing short of a proof

The ultimate and only goal is a **complete machine-checked proof** that the implementation
equals the spec — **`agda/src/Verify-Batch-Simultaneous/The-Proof.agda` fully discharged**, **no
postulates, everything typechecks**, on *every* canonical program. Partial results, "passes almost all QuickCheck
seeds", "fixes the common case" — none of these are the finish line. They are waypoints.
A remaining counterexample (even 1 in 500, even a pathological nested program) means the
theorem is false and there is no proof. Keep going until it is airtight.

## Autonomy

You have standing approval to make any change that **does not alter the spec** — implementation
edits, protocol changes, new operators, refactors, experiments. Don't stop to ask permission
for these; just go. Finding the right implementation is inherently a throw-a-lot-at-the-wall
process: try approaches, keep what passes QuickCheck/oracle, revert what doesn't, commit the
wins. Only pause to ask when a change would touch the **spec** (`Spec/`, the root README's
semantics), or when the spec is genuinely ambiguous (then follow the ambiguity rule below).

## Division of labor: the design session directs, Sonnet workers grind

The design-authority session delegates the bulk of the work — clause grinds, falsity sweeps,
build babysitting — to subagents, keeping design spend confined to rulings, directives, and
report review. Standing protocol, per Anthony:

- **Workers run on Sonnet 4.6, and `model: "sonnet"` does NOT get you there.** The Agent
  tool's `model` parameter is a hard enum (`sonnet | opus | haiku | fable`) and
  `sonnet` resolves to **Sonnet 5** on this provider; full model IDs are rejected outright
  with an InputValidationError. Two levers actually pin a version, and **both apply only at
  session start**:
  - `export CLAUDE_CODE_SUBAGENT_MODEL=claude-sonnet-4-6` — highest precedence, overrides
    whatever the Agent call passes. This is the one to use.
  - `.claude/agents/worker-s46.md` (already written) carries `model: claude-sonnet-4-6` in its
    frontmatter plus the standing worker rules. Spawn with `subagent_type: "worker-s46"`.
    A definition created mid-session does NOT register — the registry loads at startup.
  So a running session cannot change or verify its workers' model. If Anthony asks for 4.6,
  say plainly that it needs one of the two above and cannot be done from inside the session.
  If worker output quality visibly degrades — wrong goal types reported, weakened statements,
  silent postulate reintroduction — say so and re-assess rather than absorbing the cost quietly.

- **WORKERS MUST NOT BABYSIT LONG BUILDS — the design session owns the gate.** Measured
  2026-08-05: THREE of four workers died mid-task polling a build they had launched, burning
  their turn budget on "still waiting" and losing all their context; one had already written
  263 good lines that then needed rediscovering. A worker's job ends when its edits are made
  and cheaply verified. Give workers this shape instead:
  1. iterate with **`make agda-dev ARGS='<file> <member>'`** — seconds per member against
     minutes for a real check of the same module. **This SUPERSEDES the probe-first
     shape**, which existed only because a cheap loop was not otherwise available:
     agda-dev gives that loop inside `src`, so the work needs no probe file to be
     classified, landed, or forgotten. Read that section's caveat first — dev-green does
     not check the real recursion's termination;
  2. land only dev-green bodies;
  3. hand the long `make gate` BACK to the design session, which can poll across
     turns without dying.
- **Parallel workers are AUTHORIZED, and so is parallel Agda — up to a measured ceiling.**
  This machine has **24 GB RAM and 14 cores**, ~12 GB free at rest, and a single heavyweight
  check peaks in the multi-GB range (figures in `typecheck-performance-numbers.md`). So:
  - **At most TWO heavyweight checks at once** (Subscribe-Face / Wet class, multi-GB). Two fit
    the headroom; three do not, and an OOM costs more than the wait. Re-measure with
    `ps -eo rss` before assuming otherwise.
  - **Cheap modules parallelize freely** (non-SCC modules solo-check in seconds and cost
    well under a GB).  `make agda-dev` sizes its own concurrency from measured RSS.
  - **Never let two workers edit the same module.** This is a correctness constraint that
    hardware does not relax: a shared file is a write conflict, not a parallel task. When
    several edits land in ONE file (Subscribe-Face is the usual case), have workers return
    replacement text and let the design session apply it and own the single recheck.
  - **Read-only fan-out is unconditionally safe** — analysis, goal-type census, locating
    definitions, tracing call sites. Split as wide as the task allows.
  - **THE GATE MEASURES THE TREE, NOT THE WORKER.** Parallel workers share ONE working
    directory, so `make wiring-gate` reports on everyone's uncommitted edits at once. A
    worker running it while another has `src/` edits in flight gets a verdict about work
    that is not its own — observed twice on 2026-08-06, once as a spurious FAIL (11
    "orphans" that were really a concurrent mid-edit) and once as a spurious PASS (a
    ledger line removed AFTER the gate was run, leaving an unledgered probe file
    committed — precisely the C1 condition the ratchet exists to catch). Consequences:
    **a worker's gate result is only meaningful for the files it committed**; the design
    session owns the authoritative post-merge gate; and **a worker must re-run the gate
    as its LAST act before committing**, never before its final edit. A red gate whose
    cause is another worker's tree is not a licence to commit — it is a signal to
    identify the cause explicitly, confirm your own staged files are clean, and say so.
  - **NEVER reach into another worker's lane to tidy a shared file.** `DEFERRED.txt`
    and `PROOF-STATE.md` are shared ledgers, and "helpfully" removing a
    line for a file another worker is mid-landing is how the ratchet got bypassed above.
    Workers report the ledger lines they need; the design session applies them.
- **No keep-alives.** The session runs on a persistent laptop, so the container does not
  suspend between tool calls — background workers and detached builds advance on their own,
  and worker completion notifications wake the design session. Keep only a SPARSE fallback
  check-in (~60 min) to catch workers wedged by harness restarts (a restart kills a worker's
  in-flight turn — diagnose via transcript mtime + ps, revive via SendMessage with re-verify
  instructions; **"queued" = alive, "resumed from transcript" = was dead**). Long builds
  still get detached with EXIT=$? logs and polled, since the Bash tool's ~600s foreground
  ceiling per call applies. **Launch it as `make bg T=<target>` and read it back with
  `make bg-check T=<target>`** — never a hand-rolled `(cmd > log; echo EXIT=$?)`, which
  exits with `echo`'s status and so reports every build green. (`setsid` does not exist
  on macOS; `run_in_background` is the detach mechanism.)
- **Directives carry the law.** Every worker prompt restates the standing rules it needs:
  spec is gospel; refute-before-grind; detached builds with EXIT= logs; report numbers
  plainly including failures; never extrapolate from shallow refutation rows; the
  impossibility-pair stop rule (report, don't act).
- **Workers commit and push per green task** to the working branch, in the repo's commit
  voice. `make agda && make bug-cache` green before any commit that touches `agda/src`.
- **Merging green work to main is authorized** — Anthony, 2026-07-31: "merge to main when
  you can." After each verified-green worker leg, the design session merges the working
  branch to main. This authorization is standing for the current autonomous run; it does
  not extend to spec changes, which still require asking first.
- **Run continuously through the weekend** — Anthony, 2026-07-31: "continue and continue,
  don't stop for context window or usage credits." Do not wind down because a session is
  long, context is compacting, or spend is high. Work the task queue (tiers 0 → 1 → 2 → 3) end
  to end: when a worker leg finishes, review it, merge it, launch the next. The only full
  stops are the standing ones: a spec question, or the impossibility pair.

## Running long Agda builds

`make agda` is the merge gate and takes many minutes; the Bash tool's ceiling is 600 s per
foreground call, so it must be detached. Iterate with `make agda-dev` (seconds) and reach
for the long build only to merge. Current timings: `typecheck-performance-numbers.md`.

**EVERY AGDA INVOCATION GOES THROUGH THE MAKEFILE'S `AGDA` VARIABLE, WHICH CARRIES
`-W error`. A WARNING IS A BUILD FAILURE (Agda exits 42).** Never call bare `agda` in the
Makefile — `grep -E '&& agda '` must stay empty. Rationale: a warning that costs nothing
gets ignored. A `RewritesNothing` — a `rewrite` step doing literally nothing — rode *every
single build for weeks*, printed twice per run, and nobody stopped, because green was
green. Warnings are cheap to fix at the moment they appear and invisible forever after.
**`DeprecationWarning` is deliberately included** (Anthony, 2026-08-12): when the stdlib
bumps, the gate goes red until the migration is done, which is the same call the repo made
by hand on the 2.3 bump (29 files migrated, `7664d8c`, rather than filtered).

- **THE FLAG MUST BE IDENTICAL IN THE MAKEFILE AND IN `scripts/agda-dev.py`'s
  `agda_flags()`. Change one, change both, in the SAME commit.** Agda records the warning
  mode in an interface's validity key, so a target running a different `-W` than the dev
  loop invalidates the whole cone on **every alternation** — measured 2026-08-11 at ~120
  modules rebuilt per switch, the cost landing on whatever module came next, with each
  tool blaming the other's module. Six call sites share the interface cache (`agda`,
  `bug-cache`, `cli-build`, `qc-build`, `harness-build`, `agda-dev`); the single `AGDA`
  variable exists so they cannot drift.
- **Changing it costs one full cold rebuild**, since it invalidates every interface. Budget
  for that before touching it, and never toggle it to quiet output.
- **Do NOT silence a warning to get green.** Fix the cause, as the 29-file stdlib migration
  did. If a warning is genuinely wrong, that is a finding worth reporting, not a filter.

**LAUNCH EVERY LONG BUILD WITH `make bg T=<target>`; READ IT BACK WITH
`make bg-check T=<target>`. Never hand-roll the wrapper.**

```
make bg T=agda          ← under the Bash tool's run_in_background
make bg-check T=agda    ← GREEN / RED + failing tail / STILL RUNNING (exit 3)
```

`make bg` **always exits non-zero, green or red, by design.** A launcher status that is
right most of the time gets believed, and then the rare false green sails through; an
invariant failure cannot carry a wrong answer. So **a completion notification is never a
result — `bg-check` is.** The hand-rolled `(cmd > log; echo EXIT=$?)` exits with `echo`'s
status and reports every build green; that is what this replaces.

- **`setsid` and `timeout` DO NOT EXIST ON macOS.** Piped to `tail`, the `$?` you read is
  `tail`'s zero. Detach with the Bash tool's `run_in_background`.
- **Pin the working directory in every build command** — `cd agda/` for a raw `agda`, repo
  root for `make` — and guard with `ls Makefile &&` so a mis-resolved path aborts instead
  of looking green. The tell that agda never started: `Total 0ms`, or no `Checking
  <Module>` line. Never pipe agda through `head`; it hides OOM kills.
- **`touch` does NOT dirty a module — invalidation is by CONTENT.** Unchanged content
  reuses the interface, so you cannot force a remeasurement without a real edit, and
  re-appending an IDENTICAL marker line measures nothing.

**COST MODEL, and it is short: mutual-BLOCK membership is everything and file size is
nearly irrelevant.** Most of the gate is Agda's occurrence/polarity (`Positivity`) pass, it
runs over a whole mutual block, and it **cannot be switched off** — every route was measured
and closed. TERM SIZE drives it, not member count. Before proposing any split: run
`make agda-dev ARGS='--list <file>'` (free) to see which members are in a genuine cycle,
then MEASURE on a coherent cache — **a rebuilding dependency masquerades as module cost and
has produced four phantom "slow module" diagnoses, each off by up to ~50×.** Attribute
whole-module passes with `--profile=internal` on a genuinely dirty module;
`--profile=definitions` files them under "Miscellaneous". **The splits are DONE and the
question is CLOSED: Caps-Face and Wet are both split, and Wet/Part2's remaining block is
irreducible.**

**ALL MEASURED TIMINGS LIVE IN `typecheck-performance-numbers.md`, AND NOWHERE ELSE.** That
includes the gate's cost, per-module costs, the pass attribution, the split before/afters
and every closed experiment. Numbers age far faster than rules, so quoting one here would
mean maintaining it in two places and getting it wrong in both. `make agda` and
`make agda-dev` append their own timings to that file, so it stays current on its own —
read it before re-opening any performance question, and re-measure before acting on it.

**A PROOF BODY ON THE `budget-sufficient` SPINE MUST BE SEALED (`abstract`), OR VWF DIES.**
Three OOMs (`Killed: 9`, tens of GB and tens of minutes — see
`typecheck-performance-numbers.md`) came from turning a postulate on this spine into a real
definition whose unfoldable body reached the `opIterD-dominated` / `lvls-mono` towers;
sealed, VWF checks in about a minute at a fraction of the memory. **Whenever a postulate
consumed transitively by `budget-sufficient` becomes a definition, seal it in the SAME
edit** — no consumer ever needs more than the type. A plain `abstract` block rejects
untyped `where`-bindings and with-abstractions, so those bodies use private-impl +
abstract-alias (`private f-go : T; f-go = …` then `abstract f : T; f = f-go`).

**THE BUILD IS NOT `--safe`, AND NOTHING MECHANICALLY STOPS AN UNSAFE PRAGMA.** `make agda`
runs a plain `agda src/Main.agda`, and a live `{-# TERMINATING #-}` already sits at
`src/QuickCheck.agda:170` (off the proof path). So police pragmas by grep:
**`make unsafe-check`** covers TERMINATING / NON_TERMINATING / NO_POSITIVITY_CHECK /
NO_UNIVERSE_CHECK / REWRITE / `--type-in-type`. Anything it finds on the proof path is a
soundness hole, and no mandate in this file authorises it. `--safe` cannot be enabled today
(it rejects `postulate`, and we have dozens by design), but it IS the finish-line
certificate: the day `The-Proof.agda` is discharged, `agda --safe src/Main.agda` verifies
"no postulates AND no unsafe pragma" in one command. Changing a flag invalidates
interfaces — it is not a free query.

## ALL NEW CODE IS WRITTEN IN `agda/src` — the `make wiring` jurisdiction

**New definitions, new lemmas, new assemblies go straight into `agda/src`**, where the
orphan check, the ⊤-postulate check, the reachability check and the claim graph see them
from the first minute. **Anything written outside `src` is invisible to the wiring law**,
which is how proven work parked itself for months and got re-derived — the repo's
number-one failure mode. Writing in `src` is what makes "did we already prove this?" a
`grep` instead of a memory. A `probe/` directory existed only because `src` had no cheap
loop; `make agda-dev` gives one, so it was deleted. Do not recreate it.

**Iterate with `make agda-dev`, land with `make agda`.** A dev-green body belongs in `src`
immediately; it does not wait for the slow gate to earn a home.

### `make agda-dev` — THE ITERATION LOOP

```
make agda-dev ARGS='<file> <member>'   one member ← the grind loop; use constantly
make agda-dev ARGS='<file>'            one module, every member
make agda-dev ARGS='--list <file>'     free: which members are in which block
make agda-dev-selftest                 proves the loop is load-bearing
```

**THE LOOP COVERS THE WHOLE DEVELOPMENT PROCESS — use `agda-dev` throughout and `make
agda` once at the end.** Paths are `src`-relative, and it works on ANY module you name.
Two OPT-IN flags: **`SCOPE=1`** (`--only-scope-checking`) fails fast on typos but is
**measured to buy no time**, so not a speedup; **`HOLES=1`** tolerates `?` and missing
clauses, off by default so a `?` cannot pass silently.

**THERE IS NO WHOLE-PROJECT SWEEP, AND DO NOT REBUILD ONE.** It existed, was measured
against `make gate`, and lost on both cost and fidelity — strictly dominated, with no cache
state in which it wins. It could not serve as a cache-warmer either, since it checks a
renamed copy and never writes the module's real interface. **The loop's value is
per-MEMBER, not per-tree.** The cheap pre-gate role is already filled by `make wiring-gate`
and `make unsafe-check`: textual, seconds, and why `make gate` runs them first. A bare
`make agda-dev` asks for a file and exits 2.

**THE PER-FILE BUDGET IS ENFORCED, NOT ADVISORY.** Over budget is a FAILURE. The number
lives in the Makefile (`AGDA_DEV_BUDGET`) and is set from a full cold scan; re-scan before
moving it, because **the gap in the distribution is what makes a budget safe, not the
margin** — a budget set to the worst observed time fails about half the time.

**DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID — BUT ONLY WHERE
SOMETHING WAS STUBBED, AND THAT IS THE PART WORTH KNOWING.** A module with no multi-member
block is emitted VERBATIM with zero postulates, so the sweep is a **real check** there;
most of the repo is in that case. Where a block IS stubbed, two things are given up:
**termination of the real mutual recursion is not checked** — and in this proof the mutual
recursion IS the induction, so a bad measure passes dev and fails `make agda`, which is a
proof-shape failure and not a typo — and **postulates do not reduce**, so a clause needing
a sibling to unfold can pass dev and fail for real. Self-recursion and recursion within one
batch ARE checked. So the residual risk of a dev-only workflow is concentrated in the
handful of modules with a heavy block, which is exactly where `make agda` earns its keep.
**`make agda` is still the merge gate:** never report a result as verified on a dev run,
never commit on one alone, never call dev-green "typechecks".

### A RED `agda-dev` ON ANY FILE IN `src` IS A CRITICAL FAILURE — FIX IT IMMEDIATELY

**It must be GREEN on every file in `agda/src`, always.** A failure is a P0 defect in the
tooling, fixed *before* the work you were doing. Never route around it — not with a skip
list, not with "it's just the tool", not by falling back to `make agda`. A single tolerated
red teaches everyone to ignore the next one.

**The default assumption is that the TOOL is wrong, not the proof** — that is the measured
base rate, not politeness: every agda-dev failure ever investigated was a bug in
`scripts/agda-dev.py` and the proofs were fine. **Do not diagnose from the error NAME**;
each such failure was misdiagnosed at least once by reasoning about what the error class
usually means, and solved in minutes by reading the actual message and the generated file
in `agda/_dev/`. Read the file the tool produced — the bug is visible in it.

**The only acceptable "cannot check this file" is a MEASURED one, and it is a bug report,
not an exemption.** `NOT_DEV_CHECKABLE` exists for that, is currently EMPTY, and empty is
the target; its last entry was retired by splitting the file, not by tolerating the
exclusion.

### `make harness` — THE COMPILED CALCULATOR (numbers the typechecker cannot reach)

```
make harness-build        compile it (agda --compile → agda/_harness/Main)
make harness              the terminating rows, one process each, calibrated first
make harness ARGS='10'    ONE row by index (the only way to run a quarantined row)
```

`agda/src/Harness/Main.agda` is a **MODULE_ROOT** — in `src` under the wiring law, but
not reached by `src/Main.agda`, so `make agda` never pays for it. **It exists because the
GHC backend ignores `abstract`**: opacity is a *typechecking* contract, not a runtime one,
so the compiled binary runs the real bodies of families the checker refuses to unfold
(`fLvlD` at Evaluator:729, `blowH` at :899), and it laughs at rungs that OOM the checker.

**⚠ EVERY NUMBER IT PRINTS IS `measured-not-rechecked`, AND SAYING SO IS MANDATORY.**
A harness row is **not** a `refl` pin: it cannot discharge a postulate, no proof may
depend on it, and reporting one as "verified" or "typechecks" is the same false-green
failure as calling a dev run a gate. Its two legitimate uses are to **AIM the grind** and
to **REFUTE** — and a row that contradicts a postulate is a lead to chase back to a
type-level witness, not itself the finding.

- **ROW 0 IS A CALIBRATION AND IT IS LOAD-BEARING.** It prints a value the module also
  pins by `refl` (`towerℕ 4 ≡ 65536`), so the typechecker fixes the expected number and
  the binary prints the computed one. `make harness` runs it FIRST and **stops on
  mismatch**, because a backend that has quietly diverged makes every other row a
  confident lie. Never bypass it by calling `./_harness/Main` directly.
- **Adding a row:** extend `rowAt`, keep row 0 where it is, and say what would make the
  row INTERESTING — the "a row that could not have failed is not a row" rule applies here
  exactly as it does to probes.
- **Pins are ANONYMOUS (`_ : lhs ≡ rhs`), by the bug-cache idiom.** A *named* pin is a
  proven definition with no consumer — an orphan — and `make wiring-gate` correctly fails
  it. Learned by doing it wrong while landing the file.

**WHAT IT CANNOT DO — DEAD ROUTE 2026-08-12, and this one is settled.** The **caps
counting family is unreachable by measurement, and compiling it does not change that**:
`poolCount 1 0` and `blowH 0` — the smallest possible arguments — were each still running
at 45 s natively at `-O`, while row 0 calibrated correctly in the same binary. The
harness was built partly to test whether `poolCount`'s silence was mere opacity; **it is
not**. `blowH m = 6 + m + 2 · poolCount (towerℕ m) m` feeds `poolCount` a TOWER, so the
value is astronomically large by construction and no backend or hardware prints it. This
**independently confirms the "THE ANCHOR CANNOT BE PROBED" ruling** by a route with no
typechecker in it, and confirms its stated reason (the blowup is computational, not
definitional). Those rows are quarantined at 10+ and excluded from the default sweep.
**Do not build a probe, a harness row, or a `refl` pin against that family.**

## Module granularity: keep typechecks short

Mutual-BLOCK membership is what costs, not file size — see the cost model above. Rules:

- **Cut at mutual-SCC boundaries.** A mutual block is an indivisible checking unit and
  cannot span modules; everything else can and should. A module holds at most one
  heavyweight SCC and as little else as possible. **Never restructure genuine mutuality**
  (indirection layers, WF recursion) just to shrink a module — proof shape wins over check
  time.
- **A new lemma family not mutual with an existing SCC gets its own module**, even when it
  is "about" that SCC — consuming another family's results as finished facts is an import,
  not mutuality. `open import X public` chains keep the namespace flat, so consumers never
  notice where a lemma physically lives.
- **Target ≤20 s solo recheck for every non-SCC module**; past that, split at the next
  natural seam. SCC modules pay their SCC's price, which is irreducible in a real check —
  so keep it from being paid per-mistake: iterate with `agda-dev`, land bodies in verified
  batches, and detach the big recheck while writing the next batch.

## Agda: work from the outside in

Define and refine the **datatypes, primitives, and end goals first**, then link them
together with **postulates**. Before any serious proof work, all types should be settled
and the top-line results fully stated and typechecking _in terms of postulates_. Only then
start chipping the postulates away, one at a time, until everything is defined and there are
no gaps.

**A Σ-receipt has content only through its witness.** If every conjunct of a Σ-statement is
upward-closed in the witness (each survives enlarging it), the statement is vacuously
satisfiable and proves nothing — check this BEFORE grinding clauses. Pin the witness to the
one the consumers actually bound (share the Σ with the statement whose witness is spent), or
put the bound itself in as a conjunct. (Learned 2026-08-03: the exit-level count face was
machine-refuted as vacuous — `count-vacuous`, machine-checked 2026-08-03.)

**This rule applies recursively, and violating it inside a subproblem is an anti-pattern:
never prove pieces before their assembly exists.** For any lemma cluster, first state the
assembly — the statement that *consumes* the pieces — with the pieces as postulates, and
make the whole thing typecheck. Only then prove pieces, starting with the **most uncertain
one**, so that if the assembly has to change it changes *in place*, cheaply, instead of
invalidating a pile of finished proofs. Pieces proven ahead of their assembly are
speculative inventory: they may get thrown out wholesale, and worse, their sunk cost biases
the design toward keeping them. Better to have a wrong assembly you can amend than proven
pieces with no assembly at all.

## Survey the whole hole-set before discharging any of it

Outside-in applies to the HOLES too, not just the statements. When a batch of deferred sites
(a shared `-TEMP` postulate, a wall of `?`) has to be discharged, **census every site's goal
first, then classify, then prove — never site-by-site.** Depth-first grinding through a hole
set is the standard way this campaign has lost time: each design blocker is discovered only
when its turn comes, and every blocker found late can invalidate proofs already finished
above it. The census is one pass and it converts an unknown-length grind into a worklist.

- **You usually do NOT need a typecheck to read a goal.** When the obligation is *declared*
  rather than inferred — a Σ-returning family where each head's signature fixes the conjunct's
  transformer and index, and the clause supplies the witness — the goal is `substitute the
  witness into the head's conjunct`. Read the signature, read the tuple, done. Free, and no
  20-minute SCC recheck. Batch-mode Agda will not hand you goal types anyway: holes report
  only source positions, and forcing the type into an error message aborts the module at the
  FIRST error, so the "just ask Agda" route costs one full build per site.
- **Classify into four buckets, and do the LAST one first.** (a) trivial/inflationary — one
  lemma usually closes many; (b) an existing lemma applies as-is; (c) needs a new lemma;
  (d) BLOCKED — the site cannot close until a signature, a call-site argument, or a measure
  changes. Bucket (d) is the schedule. Buckets (a) and (b) are safe, batchable, and the right
  work to delegate; grinding them first only buys the illusion of progress.
- **Check every conjunct at zero before grinding it.** These bounds routinely go FALSE at
  `bud = 0`, `ops = 0`, `dep = 0` — the transformer is the identity there and a positive
  witness cannot fit. A one-screen refutation in `src`
  tells you the site needs a positivity hypothesis threaded rather than a cleverer proof.
- **Count the sites by grepping the BARE postulate name.** A hyphenated guess
  (`grep TEMP-`) misses `level-TEMP` and reports a false all-clear; comment mentions of the
  name inflate the count the other way. Grep the bare word, then subtract the declaration
  and the prose.
- **A shared deferral postulate hides call-site ARGUMENTS, not shapes.** Indices and
  transformers are pinned by the Σ above, so a wrong index is a type error at the reporting
  clause. What it absorbs is a callee handed the wrong `dep`/`bud`. Record each one in the
  postulate's header comment the moment you notice it, so the census inherits it instead of
  rediscovering it.

## Keep the repo lean — no fat

This repo always represents the **most present, up-to-date code**. Every definition must be
used somewhere — the only exceptions are the top-level, most-important exports. No
backwards-compatibility shims, nothing "stored for reference", no legacy, no deprecated.
**Do not be afraid to throw out code or documentation.** Git history is the archive.

### DELETION: the wiring pass is COMPLETE, so the freeze is lifted (2026-08-06)

The freeze that ran through 2026-08-05 existed because deletion and wiring interfere
in one direction only: **wiring only ADDS consumers** (monotone, safe to act on),
while **deletion CREATES orphans** by stranding whatever fed only into the deleted
cluster — measured once at six further definitions. Deleting mid-pass corrupts the
very measurement used to decide what to delete.

The pass is now done (zero orphans, zero unreachable modules, every postulate
consumed), so `make wiring`'s orphan set is trustworthy again and an orphan may be
deleted on its merits. Two rules survive the freeze, permanently:

- **"No consumer today" and "no consumer ever" are DIFFERENT QUESTIONS.** A sweep
  answers the first; only building the consumer answers the second. A definition
  needed by work not yet written reads as dead, and a lemma stated AFTER its own
  specialisation is orphaned by placement alone and wires in one line. Prefer
  wiring to deleting whenever a plausible consumer is nameable.
- **The commit message carries the finding** for anything substantial removed —
  write what the deleted thing established, so `git log` answers "what did that
  prove" without restoring it. Git history is the archive only if someone can
  find the entry. If the deletion leaves a NAMEABLE future consumer (apparatus
  a later proof might want back), add a one-line `-- RECOVERY: git show <sha>
  restores …` pointer to the header of the thing that would consume it — same
  locality rule as `-- DEAD ROUTE`.

### DE-RISK MODE: test for falsity first, grind last (Anthony, 2026-08-06)

**The wiring pass is over; the current pass is DE-RISKING.** Every postulate carries
a probability of being FALSE or EMPTY, and the proof's total risk is the SUM over the
ledger — so work is ordered by *risk reduced per unit effort*, not by proof-progress
optics. The tier-ordered roadmap lives in PROOF-STATE.md (order and one-line hooks
only — the research lives in the postulates' own headers); read it before picking
up any postulate.

- **A machine refutation is worth as much as a proof — usually more, since it is
  cheaper.** A false statement found now costs a restatement; found after the towers
  above it are ground, it costs the towers.
- **THE TRUTH-AUDIT PROHIBITION IS LIFTED.** It was scoped "during the wiring pass"
  and the pass is done. Auditing statements for truth — especially by machine probe —
  is now the priority, not a distraction. A `-- SUSPECT:` note is no longer the
  correct response to a doubt you can test: test it.
- **PROBE BEFORE GRINDING.** If a postulate's sides are computable (`evaluate`,
  `capsOK?`, `opIterD`, `depthE`, `spec-batchSimultaneous` …), instantiate it at
  concrete programs **in `src`, checked with `make agda-dev`** and pinned by `refl` —
  bug-cache shaped, seconds per loop. Every probe ends in exactly one of two states: a refutation (record,
  restate, re-rank) or a confidence receipt (`-- PROBED <date>:` in the postulate's
  own header, saying what shapes were covered). **An unprobed probeable postulate is
  the cheapest unmanaged risk in the repo.**
- **Never extrapolate a probe past its shapes.** Green on three canonical programs is
  a receipt, not a theorem; say which shapes were covered and which were not.
- **A row that could not have failed is not a row.** Label every probe row
  LOAD-BEARING or DEGENERATE and state what would make it fail. Three ways a probe
  lies green, all observed in one day, all erring toward false comfort:
  **(1) vacuous rows** — the quantifier is empty (`all _ [] = true`, `0 ≤ᵇ _`), so
  name the covered CONJUNCTS, not the covered programs; **(2) hand-built states** —
  a state written as `record (st-init e) { … }` is not one the evaluator can reach,
  so reach states by RUNNING, and treat a constructed state where the predicate
  FAILS as a refutation candidate whose reachability is the finding, not a
  "non-vacuity witness"; **(3) reading an assembly backwards** — `P = P-core o₁ … oₖ`
  proves P FROM the postulated core, never the core; the `oᵢ` are its hypotheses.

**RECORD A DEAD ROUTE WHERE THE NEXT PERSON WILL STAND (`-- DEAD ROUTE <date>:`).**
A *refuted statement* and a *dead route* are different findings, and only the first
has a natural home. A refutation is machine-checkable — state it in `src` as a proven
`→ ⊥` (`Depth-Bound.agda:11`: unconditional `depthE ≤ capsH` is FALSE) and it can
never decay. **A dead route has no `⊥` to state**: the statement may well be true, but
*this way of proving it* cannot work. Those findings have historically lived only in
PROOF-STATE prose, far from the postulate someone picks up six weeks later — and
re-deriving a dead route is the same wasted week as re-deriving a proof.

So: **when an attempt fails for a structural reason, add a `-- DEAD ROUTE <date>:`
line to the header of the postulate you were trying to discharge** — not to a
roadmap, not to a separate file. Same locality rule as `-- PROBED`. It must say
**what was tried and what structurally blocked it**, because "tried X, didn't work"
does not stop anyone: "route #2 is STRUCTURALLY DEAD — `cascadeLatch` sets `dying`
before any chain is processed, so the invariant cannot be established at that point"
does.

- **This is the ONLY sanctioned home for a failed attempt. Do NOT create a
  `dead-ends/` directory** (nor resurrect `probe/` under another name). A tree of
  failure files outside the claim graph is read by nobody at the moment it would
  help, and becomes the next thing every session has to read and classify — the
  precise cost that got `probe/` deleted. What prevents a repeated mistake is
  LOCALITY: the note sitting in the header of the thing you are about to grind.
- **A dead route is not a licence to weaken the statement.** It kills a *route*.
  The postulate stays at full strength; see "Do NOT weaken a statement to make it
  typecheck".
- **Deleting a dead-route line requires the route to be shown WORKABLE**, not merely
  untried-again. It is evidence, and it ages better than the code around it.

**TIER ORDER IS LAW: TIER 0 FINISHES FIRST, THEN TIER 1, THEN 2 AND 3 (Anthony,
2026-08-06; TIER 0 added 2026-08-11).** Strictly — not "mostly", not "while a
build runs". Tier 2 (`evaluate-well-formed`) is built ON tier 1's
`budget-sufficient`, so proving a tier-2 statement while the anchor question is
open bets on ground a design failure would move. The one carve-out is answering
a *design question* (cheap, and it aims the grind) — never grinding over one.

**TIER 0 IS THE ANCHOR, and it exists because prose priority did not hold.**
`cascadeGo-wet-core`, `subscribeE-wet-core`, `dry-tick-core`. For five days the anchor sat inside tier 1 while every tier-1 discharge
went to a non-anchor row — 12 live rows down to 5, anchor 4-for-4 untouched,
`cascadeGo-wet-core` edited in `agda/src` exactly once. **Priority that lives
only in prose gets spent on whatever is nearest**, so it is a tier now.

**Before starting any task: if the postulate is not in PROOF-STATE's tier-0
list, and the work is not one of the two design questions, it is parked — say
so and take a tier-0 item.** This explicitly parks **all of tier 1**, including
`subscribeE-walk-core`'s 20 sub-postulates. Those 20 are the most
gratifying-looking work left and the least informative: they are 14 instances of
one clause pattern plus 5 μ-preservation facts, none of which can discover a
design failure, and a `cascadeGo-wet-core` failure would move the ground under all of them.

**TWO ANCHOR RULINGS THAT CHANGE HOW YOU WORK IT (2026-08-11):**

- **THE ANCHOR CANNOT BE PROBED — do not spend a session trying.** Tested and
  closed: `blowH` is `abstract` (Evaluator:898) and `blowH-body` unfolds it, but
  `poolCount` then sticks on a SECOND abstract family (Evaluator:727 — `fLvlD`,
  `lvls`, `iterL`, `iterSize`, `dWalkᶜ`) sealed for the same measured
  performance reason; `poolCount 1 0` does not reduce to a numeral at the
  smallest possible arguments. `towerℕ` is NOT the blocker (it computes to
  height 4). `cascadeGo` takes no `Gas` parameter, so a small concrete Gas
  cannot be injected around it. A non-abstract COPY of the counting family fails
  too — the blowup is computational, not definitional. **Consequence: every
  probe of the anchor reaches only the region where `B`/`Ψ` do not matter, so a green
  probe here is not evidence. The anchor is symbolic-or-nothing.**
- **A RISK CLASS MAY ONLY BE LOWERED BY EVIDENCE THAT REACHED THE RISKY
  REGION.** The anchor was downgraded FALSITY → DIFFICULTY on a probe covering only
  root-path chains — the near-degenerate case — and was reverted. Name the
  region the evidence reached, or the receipt does not count. This is the
  general form of "never extrapolate a probe past its shapes", and it is the
  specific way this campaign has made itself feel safer than it was.

**These still hold, unchanged from the wiring pass:**

**A RISING POSTULATE COUNT IS THE MECHANISM WORKING, NOT A REGRESSION.** This needs
saying because every instinct — and every subagent's default — runs the other way.
Anthony, in the session that set this rule: *"the relentless mindset of reducing those
numbers is very harmful."* The ledger is not a scoreboard. One vague postulate split
into six specific ones is PROGRESS: each is separately attackable and none can hide.
The only number that matters is whether `The-Proof.agda` is discharged.

So, in worker directives and in your own work:

- **Do NOT minimise the postulate count. Do NOT apologise for it.** Do not describe an
  increase as a cost, a regression, or a trade — it is the intended outcome.
- **Do NOT weaken a statement to make it typecheck.** Weakening is the one move that
  looks like a shortcut and is not: it silently makes a claim smaller. Postulate the
  full-strength statement instead, and report the obstacle.
- **Never grind a hard proof when a postulate will do.** If a lemma is real
  mathematics, state it and move on. Note it in the ledger and keep wiring.

**THE PATTERN THAT DOES THE WORK — postulate-to-assembly conversion.** Most orphans are
orphaned because *their only would-be consumer is itself a monolithic postulate*. So:
take that postulate, convert it into a REAL DEFINITION over several smaller postulates,
and have the definition CALL the orphans it was always meant to consume. This wires
proven work, makes each remaining gap greppable, and proves nothing hard. It is what
retired the last orphan in the repo, and it remains the move whenever a new proof has
nowhere to plug in.

**WRITING AN ASSEMBLY — the mechanics.** For a parent postulate `P : T` with proven
pieces `o₁…oₖ`, `T` is unchanged; it becomes

```agda
postulate P-core : <type of o₁> → … → <type of oₖ> → T
P : T
P = P-core (λ {a} {b} → o₁ {a} {b}) … oₖ
```

`P-core` is equivalent to `P` exactly when every hypothesis is a PROOF. A
*function*-valued piece must be wired by its DEFINING EQUATION instead (`ΩAt` in
`.Measures` is the worked example) — passing the function's type quantifies over
every inhabitant and makes the core strictly STRONGER. Four rules, each of which
otherwise costs a full build to rediscover:

1. **EXTRACT hypothesis types from source; never retype them.**
   `scripts/check-wiring.py`'s `signature_text` does it exactly.
2. **Pass every lemma ETA-EXPANDED with explicit implicits** —
   `(λ {n} {Γ} → f {n} {Γ})`. When a statement reduces away its own implicit,
   bare arguments give `Unsolved metas`; the eta form always works.
3. **Copied signatures drag in VOCABULARY the parent module does not import.**
   Collect the names in one pass; Agda stops at the FIRST scope error.
4. **ORDERING: a postulate cannot reference a definition below it.** The `-core`
   sits where the postulate was; the definition sits after the last piece it
   consumes. `make wiring` section B3 reports violations — do not learn this
   from a failed typecheck.

One more, from two discharges that shared it: **a `-core`'s hypothesis list is a
HYPOTHESIS about the route, not a specification.** Both `opIterD-budget` and
`init-capsOK?-base` shed seven-plus leading hypotheses because the direct proof
never needed them — check whether it does before grinding through the list.

**TWO SHAPES THAT ARE ALMOST ALWAYS WRONG — check every new postulate for both.** A
statement whose conclusion needs information appearing in NONE of its hypotheses (e.g.
deriving a path-LENGTH bound from `pathB?`, which carries no length conjunct), and a
Σ-statement upward-closed in its witness (see "A Σ-receipt has content only through its
witness" above). Under de-risk mode these are refutation targets, not `SUSPECT:` notes:
build the counterexample.

**Prefer a free hypothesis to a carried postulate.** If a missing hypothesis is
available at the call site, adding it and deleting the postulate is less work than
carrying it. (`depthE ≤ capsH` unconditionally is FALSE, `Depth-Bound.agda:11`; the
`capsOK?`-conditioned form costs nothing extra, so it is the one that is stated.)

### CODE BEATS PROSE: if you can assemble it, ASSEMBLING IT IS THE JOB (Anthony, 2026-08-13)

**A finding written in English that could have been written in Agda is not done — it is
deferred.** This is not a matter of priority or of "documentation is also valuable". Work is
not finished until it is **as discharged as the current knowledge allows**: if you have just
worked out that A follows from B, the deliverable is the assembly `A = A-core B …`, not a
header paragraph saying that it does.

The tell, and it is easy to miss because the paragraph feels like progress: you write
"X could be implemented in terms of Y" / "this reduces to Z" / "the route is …", and then
you commit. **That sentence is a work order addressed to you, right now.** Either carry it
out, or say plainly why you cannot (a signature must change, a hypothesis is missing, the
grind is genuinely large) and postulate the residue at full strength. What is forbidden is
recording the insight and moving on as though the insight were the deliverable.

Why it matters more here than in ordinary code: an assembly is CHECKED — the typechecker
holds the reduction to the actual hypotheses, `grep` finds the residue, and the wiring law
counts it. A paragraph is checked by nobody, ages silently, and gets re-derived. (Two costs
already paid: `frameStep-reg≤size` sat machine-proven for eight days while a header called
the same arithmetic "hand derivation, not yet machine"; and `subscribeInner-nodry` was
described in prose as assemblable from the walk face's `hasDry` conjunct, and committed that
way, when the assembly was available — it turned out to discharge the `g0` clause outright
and prove the burst-split transport, both of which the paragraph had silently classified as
part of the postulate.)

Corollary for headers: a header's job is what CANNOT be code — a refuted route, a coverage
boundary, a ruling and its rationale, a recovery pointer. The moment a header explains a
derivation that would typecheck, move it into the derivation.

### THE GATE INCLUDES `PROOF-STATE.md` (Anthony, 2026-08-13)

**`make gate` is necessary, not sufficient. Update PROOF-STATE before every commit that
changes the ledger, in that same commit** — a postulate discharged, added, renamed, split,
reclassified, or reordered. The roadmap is the file every session reads FIRST, so a stale
row misdirects the next session's whole leg; one already did, naming two postulates that had
become real definitions.

And update it **to the hygiene rules in its own header, which are also part of the gate**:
one line per item (name + risk class + hook), NO numbering of any kind (list indices,
conjunct positions, source sections, timings), research in source headers rather than here,
completed items DELETED rather than marked done, no dated narrative. Re-read that header
when you touch the file; every one of those rules exists because it was violated.

### The wiring law: NEVER LEAVE A PROOF HANGING (Anthony, 2026-08-05)

**THE RULE. Nothing in this repo may exist without a consumer that traces to a top-level
theorem.** No invisible debt, no dead code, no gap that lives only in prose. Two corollaries,
and both are *checkable* rather than aspirational:

- **Every GAP is a postulate with a real signature** — never a comment, never a merely-missing
  statement. "This still needs X" in prose is invisible to the compiler and to `grep`. State X.
  Then `grep -rn '^postulate' agda/src` **is** the complete remaining-work ledger and no branch
  of the proof can hide. (A hidden branch is exactly how the eight well-formedness postulates
  went uncounted for months while the index claimed the campaign reduced to two.)
- **Every DEFINITION and every POSTULATE is consumed, in code, transitively by a top-level
  theorem.** Then "did we forget something?" is answered by the typechecker instead of by
  memory — if a piece is not needed, `The-Proof.agda` does not compile.

**THE WORKFLOW that keeps it true.** Before proving a lemma, extend the assembly that will
consume it — postulating whatever else that assembly needs — and land both in the SAME commit.
Never finish a proof and leave its wiring "for later": later is where every instance below came
from. If the assembly needs a different signature to accept the piece, **change the signature
first.** A piece that cannot be plugged in is not progress, and its shape is not yet known to be
right.

**A POSTULATE MUST ASSERT SOMETHING.** Wiring an orphan with a vacuous bridge is worse than
leaving it orphaned, because it looks discharged. Two traps, both live in this repo:
`⊤`-typed postulates whose real claim sits in a trailing comment (`id-inheritance`,
`defer-shift` — fix on sight), and Σ-statements that are upward-closed in their witness (see
"A Σ-receipt has content only through its witness" above). Check every new postulate for both
BEFORE landing it.

**FORBIDDEN STATES.** An **orphan** — a proven definition nothing consumes; it is either a
missing wire or dead weight, both are findings, and leaving it undecided is not an option. A
**lying comment** — prose describing an intent the code does not encode; `FoldOut`'s header said
it was "deliberately NOT yet stated" while the record sat stated 60 lines below, so
`foldPath-root-out` was proven against an assembly that never existed.

**MAIN IS THE TOP-LINE PROOF (Anthony, 2026-08-05).** `agda/src/Main.agda` is the
root of the consumption graph and the deletion exemption. Three rules:
**(1) whatever Main imports sticks around**; **(2) Main names individual
definitions — NEVER a bare `open import`**, so that "imported" means "claimed"
and not merely "compiled"; **(3) Main is never touched without Anthony's
explicit approval** — draft the change and ask. `make wiring` reads Main's
`using` clauses to get its exempt set, so a filename never earns an exemption
and a claim cannot self-certify.

Because Agda compiles exactly what is transitively imported, Main also defines
the build's COVERAGE — **`make agda` IS the claim graph**, and anything outside
it is not being checked at all. `make wiring` guards that boundary directly: a
module nothing reaches fails the gate (section A2) in seconds, rather than
needing a second full compile of the tower to notice. **Never close a coverage
gap by re-adding a bulk import to Main — that is the loophole, not the repair.**

**ACCEPTANCE TEST: `make gate`** — `wiring-gate`, `unsafe-check`, `agda`,
`bug-cache`, in that order. **Cheap checks run FIRST, deliberately:** an orphan or an
unsafe pragma is decidable in seconds by grep while the full gate costs many minutes, so
there is no reason to spend those minutes only to fail on something a textual pass already
knew. `make wiring-gate` is the report-turned-gate — it EXITS 1 (rather than always 0)
on an orphan outside the exempt families, on a `⊤`-typed postulate that asserts nothing,
or on a bare `open import` in Main. Run it rather than trusting a memo — including this
one. Also: grep for a fact before planning its proof, and grep for a definition's
consumers before believing any status claimed for it.

Four things the checker now enforces that it previously only documented:
- **UNREACHABLE MODULES fail the gate** (section A2). This closes a blind spot that
  hid a dead file for most of the campaign: the orphan report scans DEFINITIONS for
  consumers, so a module holding only `open import … public` re-exports has nothing
  to orphan and reads as clean however dead it is. **A module can be entirely unused
  while every other number says zero** — module reachability is a different question
  from definition reachability. Reachability is computed from Main plus the
  `MODULE_ROOTS` entry points (each a separately compiled binary with its own make
  target), so anything those import is covered automatically.
- **Inline trailing comments are stripped before consumer counting.** A name mentioned
  only in a `-- …` tail used to count as a real consumer, so a genuinely orphaned
  definition could read as WIRED — a false negative in the dangerous direction.
- **`⊤`-typed postulates are reported and gated** (`VACUOUS_ALLOWLIST` carries the one
  deliberate exception, `defer-shift`, whose own comment says it is "an honest gap, not
  a claim"). A NEW one fails the gate.
- **The ordering hazard is reported** (section B3): an orphan that no postulate in its
  own file can consume, because they all precede it. Decidable from line numbers — do
  not learn it from a failed typecheck.

**WHY THIS IS LAW.** Unwired proven work costs this campaign more than refutations do. Its
two failure modes: a proof nobody calls sits inert while the work it would have done gets
re-derived inline at the site that needed it, so the same thing is proven **twice**; and a
tower built without its consumer is a tower whose shape was never checked against anything.

## TypeScript implementation style

- The TS implementation should be as purely functional as possible: avoid manipulating mutable state and avoid calling .subscribe()
  directly. Delegate any form of IO/statefulness (e.g. accumulation) to rxjs operators like scan.
- Rationale is twofold: (1) aesthetic/cosmetic cleanliness, and (2) to keep the primitives and batchSimultaneous implementations in
  near-direct correspondence with the Agda, so translation between the two is straightforward.

## The change workflow — for changes to the batchSimultaneous IMPLEMENTATION

This workflow governs exactly one kind of change: a change to the
**batchSimultaneous implementation** (the primitives + batching pipeline
mirrored between `agda/src/Implementation` and `typescript/`) or, rarely and
only after asking, to its spec. It does not apply to proof work, tooling, or
documentation — those have their own rules above. For an impl/spec change,
follow these phases in order:

1. **Agda first.** Make the change to the spec/impl in Agda before touching TypeScript.
2. **QuickCheck dev loop.** Use `npm run agda:qc` (the all-Agda QuickCheck comparing
   `impl-batchSimultaneous` vs `spec-batchSimultaneous`) to align the implementation and
   spec quickly. **The spec is gospel — do NOT touch it to resolve a mismatch.** When impl
   and spec disagree, the implementation is wrong by default; change the implementation.
   Only touch the spec under very special circumstances, and only after asking.

   **Resolving ambiguity.** When the spec seems ambiguous or you're unsure what the "right"
   answer is, defer to **naive plain rxjs** — the semantics should mirror ordinary rxjs
   wherever a case is underspecified. Actually run the example in rxjs and see. If that
   still doesn't resolve it, surface the question to the user with a clear TypeScript rxjs
   example that **avoids the `*All()` higher-order operators where possible** and follows
   the style of the README's edge-case examples.

3. **Ignore `Verify-Batch-Simultaneous/The-Proof.agda` for now.** It may have errors during this
   phase — that's fine. Leave it until the end.
4. **Port to TypeScript** — but only once QuickCheck passes.
5. **Oracle.** Make the fast-check/Agda-alignment oracle (`npm run oracle`, TS-impl vs
   Agda-impl via the CLI) pass.
6. **Formal verification, last.** Now prove the implementation equals the spec. Do it in
   **phases** — leave middle steps as postulates and **commit in-between results**. Work
   until there are **no gaps**: no postulates, everything typechecks.

## Bug cache: type-level unit tests

When you discover an implementation bug, capture it immediately as a **type-level unit test**
in `agda/src/Implementation/Unit-Test.agda` — a `_ : impl prog ≡ expected` that Agda checks
by `refl` at compile time. These are a **performance cache** of discovered work: faster to
recheck than QuickCheck, faster at the type level than at runtime. They pin down the exact
value the impl must produce for a specific canonical program (spec-derived), so a regression
fails the typechecker instantly instead of surfacing only in a random seed.

Keep them dead simple — no fancy names, no abstraction, just a wall of little `_ : … ≡ …`
entries. They exist only to accelerate finding the implementation; they are **not** meant to
survive past the proof. Delete the module once `The-Proof.agda` is discharged.

The cache is **append-only**: `scripts/gen-unit-tests.sh [FIRST] [LAST] [RUNS] [DEPTH]`
appends each new counterexample (deduped by program text) and never deletes or overwrites. A
fixed bug just becomes a passing guard that stays forever. Invariant: **`Unit-Test.agda` fully
typechecks ⟺ no known counterexample remains** — green there is the impl≡spec finish line.
`QuickCheck` reads `SEED [RUNS] [DEPTH]` on stdin (runs before depth; defaults 200 and 4):
DEPTH caps program nesting, a hard size cap.

Note `Unit-Test.agda` is **not** reachable from `Main.agda`, so `make agda` does not check it.
Run **`make bug-cache`** to enforce the invariant above — it exists precisely because nothing
else in the build would notice the cache rotting.

In some cases, however, it might make sense to adding a new "naive rx" operator to fix an Agda-impl bug.

This is allowed and encouraged when it's the best solution. But follow the port order:

- Develop the new operator in TypeScript first (as a proper rxjs-delegating, purely-functional operator).
