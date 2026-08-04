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
postulates, everything typechecks**, on *every* canonical program. (That file is the artifact
once called `Formal-Verification`; the old name survives nowhere but in memories and stale
memos, so read any reference to it as pointing here.) Partial results, "passes almost all QuickCheck
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

- **Workers run on Sonnet 4.6** (Agent tool, `model: "sonnet"`) as of 2026-08-04, replacing
  Opus 5. The cheaper worker buys parallelism (below); Anthony: "we'll give this a shot for a
  while, and we'll re-assess later." If worker output quality visibly degrades — wrong goal
  types reported, weakened statements, silent postulate reintroduction — say so and re-assess
  rather than absorbing the cost quietly.
- **Parallel workers are AUTHORIZED (2026-08-04), and the hardware now allows parallel Agda
  too — up to a measured ceiling.** The old one-worker-at-a-time rule was a memory constraint,
  not a credits one, and Anthony moved the session to stronger hardware on 2026-08-04 ("no
  need to worry"). Measured on that machine: **24 GB RAM, 14 cores**, ~12 GB free at rest,
  and **Subscribe-Face peaks ~5.2 GB** as a single check. So:
  - **At most TWO heavyweight checks at once** (Subscribe-Face / Wet class, multi-GB). Two fit
    the headroom; three do not, and an OOM costs more than the wait. Re-measure with
    `ps -eo rss` before assuming otherwise — the 13 GB peaks in the campaign's history were
    real, just on the old container.
  - **Cheap modules parallelize freely** (probes and non-SCC modules solo-check in seconds and
    cost well under a GB).
  - **Never let two workers edit the same module.** This is a correctness constraint that
    hardware does not relax: a shared file is a write conflict, not a parallel task. When
    several edits land in ONE file (Subscribe-Face is the usual case), have workers return
    replacement text and let the design session apply it and own the single recheck.
  - **Read-only fan-out is unconditionally safe** — analysis, goal-type census, locating
    definitions, tracing call sites. Split as wide as the task allows.
- **Keep-alives RETIRED (2026-08-03).** The session now runs on a persistent laptop
  (Anthony: "no need for the keep-alives anymore"), so the container no longer suspends
  between tool calls — background workers and detached builds advance on their own, and
  worker completion notifications wake the design session. The old protocol (110-second
  serial foreground keep-alive chains + 20-minute `send_later` re-arms) is retired; keep
  only a SPARSE fallback check-in (~60 min) to catch workers wedged by harness restarts
  (a restart still kills a worker's in-flight turn — diagnose via transcript mtime + ps,
  revive via SendMessage with re-verify instructions; "queued" = alive, "resumed from
  transcript" = was dead). Long builds still get setsid-detached with EXIT=$? logs and
  polled, since the Bash tool's ~600s foreground ceiling per call still applies.
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
peaking ~6.9 GB when dirty** — measured 2026-08-04; the older "~7 min" figure in memos predates
the clique's growth and will mislead your planning, so budget the real number);
the Bash tool's ceiling is 600s per foreground call. Detach long builds (`nohup setsid bash
-c '… ; echo EXIT=$? >> log' &`) and poll the log for its EXIT= line with short foreground
calls. Since 2026-08-03 the session runs on a persistent machine, so detached builds advance
on their own — the polling is for pacing and verification, not for keeping anything awake.
Never pipe agda through `head` (it hides OOM kills); read EXIT= from the log; `tail -3` and
read indentation (an importer prints as the last line for its importee's whole leg).

**Always `cd` into `agda/` explicitly in the same command as the `agda` invocation, and read
the log's first lines, not just its exit code.** The shell's working directory drifts between
tool calls, and a run launched from the repo root fails instantly with `Cannot read file
…/src/…` — which looks like a fast green result if you only check that a log exists, and looks
like a *proof failure* if you only count error-ish lines. Two separate incidents on
2026-08-04. The tell is `Total 0ms` or a missing `Checking <Module>` line: agda never started.
Same class of trap as trusting a pipe's exit code — verify the run actually ran before
believing anything it says. `agda --profile=definitions` gives per-definition cost; note
`--profile` takes ONE type, and combining `definitions` with `modules` is rejected outright.

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
