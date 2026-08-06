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

The design-authority session delegates the bulk of the work — clause grinds, probe sweeps,
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
  1. iterate in `agda/probe/` with minimal imports — an UNCHANGED heavy module is a cached
     interface, so a probe importing Wet deserializes in ~6 s instead of rechecking for 9 min
     (see `agda/probe/Caps-Thread-Probe.agda`'s header; this is a ~90× loop speedup);
  2. land only probe-green bodies;
  3. hand the long `make agda && make agda-all && make bug-cache` gate BACK to the design
     session, which can poll across turns without dying.
- **Parallel workers are AUTHORIZED, and so is parallel Agda — up to a measured ceiling.**
  Measured on this machine: **24 GB RAM, 14 cores**, ~12 GB free at rest,
  and **Subscribe-Face peaks ~5.2 GB** as a single check. So:
  - **At most TWO heavyweight checks at once** (Subscribe-Face / Wet class, multi-GB). Two fit
    the headroom; three do not, and an OOM costs more than the wait. Re-measure with
    `ps -eo rss` before assuming otherwise.
  - **Cheap modules parallelize freely** (probes and non-SCC modules solo-check in seconds and
    cost well under a GB).
  - **Never let two workers edit the same module.** This is a correctness constraint that
    hardware does not relax: a shared file is a write conflict, not a parallel task. When
    several edits land in ONE file (Subscribe-Face is the usual case), have workers return
    replacement text and let the design session apply it and own the single recheck.
  - **Read-only fan-out is unconditionally safe** — analysis, goal-type census, locating
    definitions, tracing call sites. Split as wide as the task allows.
- **No keep-alives.** The session runs on a persistent laptop, so the container does not
  suspend between tool calls — background workers and detached builds advance on their own,
  and worker completion notifications wake the design session. Keep only a SPARSE fallback
  check-in (~60 min) to catch workers wedged by harness restarts (a restart kills a worker's
  in-flight turn — diagnose via transcript mtime + ps, revive via SendMessage with re-verify
  instructions; **"queued" = alive, "resumed from transcript" = was dead**). Long builds
  still get detached with EXIT=$? logs and polled, since the Bash tool's ~600s foreground
  ceiling per call applies. **`setsid` does not exist on macOS** — use the Bash tool's
  `run_in_background`, not `nohup setsid`.
- **Directives carry the law.** Every worker prompt restates the standing rules it needs:
  spec is gospel; probe-before-grind; detached builds with EXIT= logs; report numbers
  plainly including failures; never extrapolate from shallow probe rows; the
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

`make agda` takes ~35-40 minutes (Caps-Face ~80 s, Wet ~14-18 min, and **Subscribe-Face ~44 min
peaking ~6.9 GB when dirty**); the Bash tool's ceiling is 600s per foreground call. Detach long builds (`nohup setsid bash
-c '… ; echo EXIT=$? >> log' &`) and poll the log for its EXIT= line with short foreground
calls. Since 2026-08-03 the session runs on a persistent machine, so detached builds advance
on their own — the polling is for pacing and verification, not for keeping anything awake.
Never pipe agda through `head` (it hides OOM kills); read EXIT= from the log; `tail -3` and
read indentation (an importer prints as the last line for its importee's whole leg).

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

**The build is `--safe`.** So `--no-termination-check` and friends are rejected outright
(the stdlib's own `OPTIONS` pragma trips first). Good for soundness — no pragma can quietly
weaken this proof — but it means whole-module analyses cannot be switched off to time them;
attribute them with `--profile=internal` on a genuinely dirty module instead.

## Module granularity: keep typechecks short

Agda rechecks a whole module on any edit, so module size IS iteration speed. Rules
(Anthony, 2026-08-03):

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
  natural seam. SCC modules pay their SCC's price (Subscribe-Face ~7 min) — that cost is
  irreducible, so keep it from being paid per-mistake: iterate in `agda/probe/` with
  minimal imports (<20 s loops), land bodies in verified batches, and detach the big
  module's recheck while writing the next batch.

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
machine-refuted as vacuous — `count-vacuous` in `agda/probe/Count-Level-Probe.agda`.)

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
  witness cannot fit. A one-screen refutation probe (`agda/probe/Queue-Push-Probe.agda` § 1)
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

### DELETION FREEZE: wire everything BEFORE deleting anything (Anthony, 2026-08-05)

**No orphan gets deleted until the wiring pass is finished.** Not a mood — a
rule, because deletion and wiring interfere in one direction only:

- **Wiring only ADDS consumers.** It never creates an orphan, so its signal is
  monotone and safe to act on.
- **Deletion CREATES orphans**, by stranding whatever fed only into the deleted
  cluster. Measured: one cluster's removal orphaned six further definitions whose
  consumer chain terminated inside it.

So deleting before wiring is complete **corrupts the very measurement used to
decide what to delete.** Wire first; the orphan set that survives a finished
wiring pass is the only one whose emptiness means anything.

**"No consumer today" and "no consumer ever" are DIFFERENT QUESTIONS**, and only
building the consumer answers the second. A sweep answers the first. Two traps
that make the difference concrete: a definition needed by work not yet written
reads as dead; and a lemma stated AFTER its own specialisation is orphaned by
placement alone, and wires in one line.

**The one standing exemption** is code the SOURCE ITSELF retires in writing.
Even then: record the commit SHA in PROOF-STATE.md, because git history is the
archive only if someone can find the entry.

### SHORTCUT MANDATE: postulate freely until the wiring pass is done (Anthony, 2026-08-05)

**The current pass is WIRING, not proving. Take as many shortcuts as possible until it
is finished.** What we do not yet know, we POSTULATE. Get the repo settled first;
decisions about what to actually prove come after.

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
proven work, makes each remaining gap greppable, and proves nothing hard. Applied
2026-08-05 to `opIterD≤capsH-root` (wires `depth-capped`); the same move is open for
`subscribeE-wet-via-caps` (wires `sub-charge`) and `subscribeE-wf` (wires its five
proven clauses).

**THE ONE CONSTRAINT, and it is the only way a shortcut can actually hurt: A POSTULATE
MUST ASSERT SOMETHING TRUE.** Postulating a known-FALSE statement looks like progress
and poisons everything above it. Two live examples: `depthE ≤ capsH` is FALSE
unconditionally (`Depth-Bound.agda:11` — it dies against an adversarial stored state),
so only the `capsOK?`-conditioned version may be postulated; and see "A Σ-receipt has
content only through its witness" above for the vacuity trap. Check both before landing
a postulate. That check is cheap — it is reading the statement, not proving it.

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
the build's COVERAGE. **`make agda` is the claim graph; `make agda-all`
compiles every module under `src/` regardless of reachability** — the rot-guard
for proven work not yet wired to a claim. The DIFFERENCE between the two is the
unwired debt, and `agda-all` is self-retiring — when the two cover the same set,
delete it. Never close that gap by re-adding a bulk import to Main: that is the
loophole, not the repair.

**ACCEPTANCE TEST: `make wiring` reports zero orphans** outside its two documented exempt
families (`*-absurd` refutation witnesses, whose consumer is the design record; and the
top-line semantic claims in `*-Theorems.agda`, which ARE the claims). Run it rather than
trusting a memo — including this one. Also: grep for a fact before planning its proof, and grep
for a definition's consumers before believing any status claimed for it.

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
