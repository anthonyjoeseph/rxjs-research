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
  1. iterate with **`make agda-dev ARGS='<file> <member>'`** — ~6 s per member against
     927 s for a real Subscribe-Face check (2026-08-11). **This SUPERSEDES the
     probe-first shape**, which existed only because a cheap loop was not otherwise
     available: agda-dev gives the same ~6 s inside `src`, so the work needs no probe
     file to be classified, landed, or forgotten. Read that section's caveat first —
     dev-green does not check the real recursion's termination;
  2. land only dev-green bodies;
  3. hand the long `make gate` BACK to the design session, which can poll across
     turns without dying.
- **Parallel workers are AUTHORIZED, and so is parallel Agda — up to a measured ceiling.**
  Measured on this machine: **24 GB RAM, 14 cores**, ~12 GB free at rest,
  and **Subscribe-Face peaks ~5.2 GB** as a single check. So:
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
  long, context is compacting, or spend is high. Work the task queue (tiers 1 → 2 → 3) end
  to end: when a worker leg finishes, review it, merge it, launch the next. The only full
  stops are the standing ones: a spec question, or the impossibility pair.

## Running long Agda builds

`make agda` takes tens of minutes; the Bash tool's ceiling is 600s per foreground call.
**Solo dirty per-module costs, re-measured 2026-08-11 under Agda 2.8** (the older 44-minute
figure for Subscribe-Face included its downstream cone, not the module): Subscribe-Face
**384 s**, Wet ~**350 s** (908 s under 2.7), Caps-Face **63.9 s**. Two facts to keep:
Subscribe-Face and Wet are ~90% positivity over one mutual block that no flag touches —
**Caps-Face is not, and is not a bottleneck**: only 24% positivity (15.2 s), and its
83-member block is the biggest in the repo — which is the whole point: **MEMBER COUNT
DOES NOT PREDICT COST, TERM SIZE DOES.** 83 members cost 15.2 s there; 15 members cost
300 s in Subscribe-Face. So "split the big mutual block up" is not the lever it looks
like, and two refactors were measured and rejected on that basis (2026-08-11): Caps-Face's
83-member block is *entirely spurious* — zero cycles, three gratuitous forward
declarations sweeping in 80 unrelated definitions — and dissolving it saves nothing;
hoisting the 22 non-SCC members out of Wet's 36 is worth 255 s → 220 s of positivity,
~35 s of a ~17-minute build, for a large refactor with real meta-coupling risk.
`make agda-dev ARGS='--list <file>'` reports which members are in a genuine cycle, so
check that before proposing either. And
**`make agda-dev` checks the same bodies in seconds** — reach for the long build only as
the merge gate.

**LAUNCH EVERY LONG BUILD WITH `make bg T=<target>`, AND READ IT BACK WITH
`make bg-check T=<target>`. Do not hand-roll the wrapper (Anthony, 2026-08-11).**

```
make bg T=agda          ← under the Bash tool's run_in_background
make bg-check T=agda    ← GREEN / RED + failing tail / STILL RUNNING
```

The hand-rolled shape everyone reaches for **reports every build as green:**

```
(make agda > /tmp/x.log 2>&1; echo EXIT=$? >> /tmp/x.log)   # ← WRONG
```

A subshell exits with its LAST command's status, and that is `echo` — always 0. So
the launcher's exit code carries no information, and a RED build is indistinguishable
from a green one unless someone remembers to open the log. On 2026-08-11 a whole-project
`agda-dev` run that had gone RED (over budget, one module killed at 180 s) was reported
as green on exactly this basis; the log's last line said `EXIT=1` the whole time.

**`make bg` THEREFORE ALWAYS FAILS — green or red, every time (Anthony, 2026-08-11).**
It exits 7 by construction and says so. This is deliberate and must not be "fixed" into
propagating the real status: **a launcher status that is right most of the time is worse
than one that is never right**, because the reliable one gets read and believed, and then
every rare false green sails through. An invariant failure carries no information, so it
cannot carry a WRONG answer — and the only way to learn anything is to ask `bg-check`,
which reads the log. Treating "the background task finished with exit 0" as a verdict is
the exact mistake this removes the possibility of.

So: **a completion notification is never a result. `make bg-check T=<target>` is the
result.** It answers GREEN, RED with the failing tail, or **STILL RUNNING** (exit 3) —
and that third answer is a distinct one, because a log with no `EXIT=` line has not
passed, it has not finished.

This is the same family as the two traps below, and the reason the rule is now a make
target rather than a habit: each of them produces a *green-looking lie*, which is the
one failure mode that does not announce itself.

- **`setsid` DOES NOT EXIST ON macOS** — `nohup setsid …` silently does nothing. Detach
  with the Bash tool's `run_in_background`, which is what `make bg` is designed for.
- **`timeout` DOES NOT EXIST ON macOS EITHER.** `timeout 580 make …` fails with
  `command not found`, so make never runs — and piped to `tail`, the `$?` you read is
  `tail`'s zero. Hit 2026-08-06.

Never pipe agda through `head` (it hides OOM kills); `tail -3` and read indentation (an
importer prints as the last line for its importee's whole leg). Detached builds advance
on their own — polling is for pacing and verification, not for keeping anything awake.

**Pin the working directory in EVERY build command — `cd agda/` for a raw `agda` call, repo
root for `make` — and read the log's first lines, not just its exit code.** `make agda` from a
subdirectory dies with `No rule to make target 'agda'` and `EXIT=2`, which greps as zero
error-ish lines and looks like a clean build to anything that only checks for the word "error".
Guard the command with `ls Makefile &&` (or `ls src/…agda &&`) so the chain aborts instead of
mis-resolving. The shell's working directory drifts between
tool calls, and a run launched from the repo root fails instantly with `Cannot read file
…/src/…` — which looks like a fast green result if you only check that a log exists, and looks
like a *proof failure* if you only count error-ish lines. Two separate incidents on
2026-08-04. The tell is `Total 0ms` or a missing `Checking <Module>` line: agda never started.
Same class of trap as trusting a pipe's exit code — verify the run actually ran before
believing anything it says. `agda --profile=definitions` gives per-definition cost; note
`--profile` takes ONE type, and combining `definitions` with `modules` is rejected outright.

**`touch` does NOT dirty an Agda module — invalidation is by CONTENT, not mtime.** A touched
file with unchanged content reuses its interface, so a "recheck" of it measures only
deserialization (6.4 s for Subscribe-Face, of which 5.1 s IS deserialization) and reports zero
`Checking` lines. Two consequences: you cannot force a remeasurement without a real edit, and
an experiment run with weakened flags cannot silently poison the cache this way either.

**A PROOF BODY ON THE `budget-sufficient` SPINE MUST BE SEALED (`abstract`), OR VWF DIES.**
Measured 2026-08-07, THREE times now — the third was `opIterD-budget`'s discharge, whose
unsealed body handed VWF the whole Op-Budget tower and OOM'd it again. **The rule is
cheap and the failure costs 40 minutes: whenever a postulate on this spine becomes a real
definition, seal it IN THE SAME EDIT, before running anything.** The first two were
`Killed: 9` OOMs (>15 GB, 30-50 min in VWF before death):
converting the `sub-charge-capsOK-lift` / `init-capsOK?` / `depth-compositional` postulates
into REAL definitions handed VWF's conversion their unfoldable bodies, which reach the
`opIterD-dominated`/`lvls-mono` proof towers. With the same proofs sealed, VWF checks in
~1 min at <2 GB. So: **whenever a postulate consumed (transitively) by `budget-sufficient`
becomes a real definition, seal it** — no consumer ever needs more than the type. Two
mechanics: a plain `abstract` block REJECTS untyped `where`-bindings and with-abstractions
("types of abstract definitions are never inferred"), so bodies that use them get the
**private-impl + abstract-alias** pattern instead (`private f-go : T; f-go = …` then
`abstract f : T; f = f-go`). This is the caps axis's existing normalisation contract
(`sizeCount`'s header) extended from counting functions to proof bodies.

**THE BUILD IS NOT `--safe`, AND NOTHING MECHANICALLY STOPS AN UNSAFE PRAGMA.** `make agda`
runs a plain `agda src/Main.agda`; there is no `--safe` on the command line, no `OPTIONS`
pragma anywhere in `src/`, and no flags in `rxjs-research.agda-lib`. Verified, along with the
fact that a live `{-# TERMINATING #-}` already sits at `src/QuickCheck.agda:170` — off the
proof path (Main does not import QuickCheck), but proof that the guard does not exist. So:

- **Police unsafe pragmas by grep, not by faith.** `make unsafe-check` greps the proof path
  for `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`/`NO_UNIVERSE_CHECK`/`REWRITE`/
  `--type-in-type`. Anything one of those turns up on the proof path is a soundness hole,
  not a shortcut, and no mandate in this file authorises it.
- **`--safe` CANNOT be turned on today, because it rejects `postulate` too** ("Cannot
  postulate X with safe flag") — and we have dozens by design. Do not try to add it.
- **`--safe` IS THE FINISH-LINE CERTIFICATE, and this is the useful part.** The day
  `The-Proof.agda` is discharged with no postulates, `agda --safe src/Main.agda` should pass —
  and that ONE command mechanically verifies both halves of the goal at once: no postulates
  AND no unsafe pragma. It is a better acceptance test than any grep, so aim the endgame at it.
- Beware that changing a flag (e.g. experimenting with `--safe`) invalidates interfaces and
  forces rechecks — it is not a free query.

Whole-module analyses cannot be switched off to time them; attribute them with
`--profile=internal` on a genuinely dirty module instead.

## ALL NEW CODE IS WRITTEN IN `agda/src` — the `make wiring` jurisdiction (Anthony, 2026-08-11)

**There is no longer a reason to write Agda anywhere else, and therefore no licence to.**
A `probe/` directory used to exist for exactly one reason — `src` had no cheap iteration
loop, so work was staged outside the claim graph where a fast check was possible. It was
DELETED on 2026-08-11 along with its ledger, its make targets and its scripts, because
`make agda-dev` gives the same seconds-level loop **inside `src`**. Do not recreate it.

So the rule is now simply:

- **New definitions, new lemmas, new assemblies: straight into `agda/src`**, under
  `make wiring`'s jurisdiction, where the orphan check, the ⊤-postulate check, the
  reachability check and the claim graph all see them from the first minute.
- **Anything written outside `src` is by definition invisible to the wiring law**, which
  is how proven work parked itself for months and got re-derived — the repo's number-one
  failure mode. Writing in `src` is not a tidiness preference; it is what makes "did we
  already prove this?" a `grep` instead of a memory.
- **Iterate with `make agda-dev`, land with `make agda`.** A dev-green body belongs in
  `src` immediately; it does not wait for the slow gate to earn a home.

### `make agda-dev` — THE ITERATION LOOP, and how to use it properly

Full rationale, measurements and limits are in `scripts/agda-dev.py`'s docstring, which
is the archive for the performance investigation. The working subset:

```
make agda-dev ARGS='<file> <member>'   ~6 s   ← the grind loop; use this constantly
make agda-dev ARGS='<file>'            11-17 s  every member of one module
make agda-dev ARGS='--list <file>'     free   which members are in which mutual block
make agda-dev                          ~86 s  every dirty dev-checkable module
make agda-dev-selftest                        proves the loop is load-bearing
```

Paths are `src`-relative (`Verify-Budget-Sufficient/Wet.agda`). Two OPT-IN flags:
**`SCOPE=1`** (`--only-scope-checking`) — a fail-fast for typos and bad names, and
**measured to buy no time at all**, so do not reach for it as a speedup; **`HOLES=1`**
tolerates `?` holes and missing clauses, and stays off by default so a `?` can never
pass silently.

**BUDGETS ARE ENFORCED, NOT ADVISORY: 30 s per file, 180 s for the whole project.**
Over budget is a FAILURE with the usual causes printed. If the work genuinely grew, move
the number in the Makefile deliberately — a loop that quietly drifts to two minutes has
stopped being a loop.

### A RED `agda-dev` ON ANY FILE IN `src` IS A CRITICAL FAILURE — FIX IT IMMEDIATELY (Anthony, 2026-08-11)

**`make agda-dev` must be GREEN on every file in `agda/src`, always.** If it fails on a
file, that is a P0 defect in the tooling and it gets fixed *before* the work you were doing.
Never route around it: not by adding the file to a skip list, not by "it's just the tool",
not by falling back to `make agda` and moving on. The loop is only trustworthy if it is
universally green, and a single tolerated red teaches everyone to ignore the next one.

**The default assumption is that the TOOL is wrong, not the proof.** This is not politeness
— it is the measured base rate. Every single agda-dev failure investigated on 2026-08-11
was a bug in `scripts/agda-dev.py`, and the proofs were fine in every case:

- 22 `NotInScope` in Caps-Face — the renderer **relocated bodies** to the head of their
  mutual block, so a body written at line 7,500 was emitted at 4,259, ahead of the
  `abstract` block defining what it calls. Position carries scope.
- 7 `SplitError` + 9 `UnequalTerms` — it **stubbed acyclic members**. Stubbing exists to
  break cycles; postulating an orderable definition only costs reduction.
- `InstanceNoCandidate` in Caps — focus modules did not repeat the original `open import`
  lines, and **instance arguments resolve from what is opened**.
- `MissingTypeSignature` in Rx/Exp and 3 more modules — all collateral from the relocation
  bug, fixed without touching those files.

**Corollary: do not diagnose these from the error NAME.** Each of the above was
misdiagnosed at least once by reasoning about what the error class usually means; each was
solved in minutes by reading the actual message and looking at the generated file in
`agda/_dev/`. Read the file the tool produced — the bug is visible in it.

**The only acceptable "cannot check this file" is a MEASURED one, and it is a bug report,
not an exemption.** `NOT_DEV_CHECKABLE` in the script exists for that, it is currently
EMPTY, and empty is the target. Its last entry, `Verify-Well-Formed`, was retired by
splitting the file rather than by tolerating the exclusion.

**THE THREE THINGS A NEW AGENT MUST KNOW BEFORE TRUSTING A GREEN RUN:**

1. **DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID.** The real mutual
   recursion's **termination is not checked** — and in this proof the mutual recursion IS
   the induction, so a bad measure passes dev and fails `make agda`. That is a
   proof-shape failure, not a typo. (Self-recursion, and recursion within one batch, are
   checked.) And **postulates do not reduce**, so a clause needing a sibling to unfold
   can pass dev and fail for real.
2. **`make agda` is still the merge gate.** Never report a result as verified on a dev
   run, never commit on one alone, and never describe dev-green as "typechecks".
3. **Some modules are NOT dev-checkable**, listed with reasons in the script's
   `NOT_DEV_CHECKABLE`. `Caps-Face` is there for an *inherent* reason — its proofs
   case-split on sibling results, which a postulate cannot provide — so it needs the real
   check; the others are parser gaps and are fixable. Do not "fix" a red dev run on those
   by weakening anything.

## Module granularity: keep typechecks short

**CORRECTED 2026-08-11 BY MEASUREMENT: module SIZE is nearly irrelevant; mutual-BLOCK
membership is everything.** Subscribe-Face's 904-line prelude — 45 definitions, each its
own block — checks in **7.8 s**; its 15-member mutual block costs **919 s**. A
5,000-line module of independent lemmas would be fast; a 200-line module with one
15-member block would not. The rules below are right, but the reason to follow them is
block membership, not line count. (86-91% of the build is Agda's occurrence/polarity
pass over those blocks, and no flag or pragma touches it — three routes measured and
closed — the record is `scripts/agda-dev.py`'s docstring, which is where that
investigation was archived when the roadmap file was deleted.)

**THE ITERATION LOOP IS `make agda-dev`.**
`make agda-dev ARGS='<file> <member>'` checks ONE mutual-block member against its
siblings postulated at their exact signatures — **~6 s for one member, 11 s for all of
Subscribe-Face, 17 s for all of Wet**, against 927 s and 908 s for the real modules. It
runs **inside `src`**, so work stays under `make wiring`'s jurisdiction and there is no
probe file to classify, land, or forget. `agda/src` is never written to.

**DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID.** Two things are given
up: **termination of the real mutual recursion is not checked** (and in this proof the
mutual recursion IS the induction, so a bad measure passes dev and fails `make agda` —
that is a proof-shape failure, not a typo), and **postulates do not reduce**. Self-
recursion and recursion within a batch are still checked. `make agda` stays the merge
gate. `make agda-dev-selftest` proves the loop is load-bearing rather than
green-by-construction; run it whenever the stubbing logic changes.

Rules (Anthony, 2026-08-03):

- **Cut at mutual-SCC boundaries.** A mutual block is an indivisible checking unit and
  cannot be split across modules; everything else can and should be. A module holds at most
  one heavyweight SCC and as little else as possible. Never restructure genuine mutuality
  (indirection layers, WF recursion) just to shrink a module — proof shape wins over
  check time.
- **A new lemma family that is not mutual with an existing SCC gets its own module**, even
  when it is "about" that SCC — consuming another family's results as finished facts is an
  import, not mutuality. "Related" is not a reason to co-locate: `open import X public`
  chains keep the namespace flat, so consumers never notice where a lemma physically lives.
- **Target ≤20 s solo recheck for every non-SCC module.** Past that, split at the next
  natural seam. SCC modules pay their SCC's price (Subscribe-Face 6.4 min under Agda
  2.8) — that cost is irreducible in a real check, so keep it from being paid
  per-mistake: iterate with `make agda-dev` (~6 s per member), land bodies in verified
  batches, and detach the big module's recheck while writing the next batch.

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
- **Record the commit SHA in PROOF-STATE.md** for anything substantial removed.
  Git history is the archive only if someone can find the entry.

### DE-RISK MODE: test for falsity first, grind last (Anthony, 2026-08-06)

**The wiring pass is over; the current pass is DE-RISKING.** Every postulate carries
a probability of being FALSE or EMPTY, and the proof's total risk is the SUM over the
ledger — so work is ordered by *risk reduced per unit effort*, not by proof-progress
optics. The ranked ledger and the phase order live in PROOF-STATE.md; read it before
picking up any postulate.

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
  lies green — vacuous rows, hand-built (unreachable) states, and reading an assembly
  backwards — are itemised in PROOF-STATE's roadmap; all three were observed in one
  day, and all three erred toward false comfort.

**TIER ORDER IS LAW: TIER 0 FINISHES FIRST, THEN TIER 1, THEN 2 AND 3 (Anthony,
2026-08-06; TIER 0 added 2026-08-11).** Strictly — not "mostly", not "while a
build runs". Tier 2 (`evaluate-well-formed`) is built ON tier 1's
`budget-sufficient`, so proving a tier-2 statement while the anchor question is
open bets on ground a design failure would move. The one carve-out is answering
a *design question* (cheap, and it aims the grind) — never grinding over one.

**TIER 0 IS THE ANCHOR, and it exists because prose priority did not hold.**
`cascadeGo-wet-core` (T0-1), `subscribeE-wet-core` (T0-2), `dry-tick-core`
(T0-3). For five days the anchor sat inside tier 1 while every tier-1 discharge
went to a non-anchor row — 12 live rows down to 5, anchor 4-for-4 untouched,
`cascadeGo-wet-core` edited in `agda/src` exactly once. **Priority that lives
only in prose gets spent on whatever is nearest**, so it is a tier now.

**Before starting any task: if the postulate is not in PROOF-STATE's TIER 0
table, and the work is not one of the two design questions, it is parked — say
so and take a tier-0 item.** This explicitly parks **all of tier 1**, including
`subscribeE-walk-core`'s 20 sub-postulates. Those 20 are the most
gratifying-looking work left and the least informative: they are 14 instances of
one clause pattern plus 5 μ-preservation facts, none of which can discover a
design failure, and a T0-1 failure would move the ground under all of them.

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
  probe of T0-1 reaches only the region where `B`/`Ψ` do not matter, so a green
  probe here is not evidence. The anchor is symbolic-or-nothing.**
- **A RISK CLASS MAY ONLY BE LOWERED BY EVIDENCE THAT REACHED THE RISKY
  REGION.** T0-1 was downgraded FALSITY → DIFFICULTY on a probe covering only
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
nowhere to plug in. The mechanics — hypothesis extraction, eta-expanded implicits,
ordering — are written up in PROOF-STATE.md § "WRITING AN ASSEMBLY".

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
unsafe pragma is decidable in seconds by grep while `agda` costs ~40 minutes, so there
is no reason to spend the 40 minutes only to fail on something a textual pass already
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

## The change workflow

Follow these phases in order for any change to the implementation or spec:

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
