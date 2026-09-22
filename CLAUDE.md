# Working methodology

Agda model (`agda/`) + TypeScript impl (`typescript/`). Agda's spec is gospel; TS conforms.

## This file

- **File of record for every directive.** Ruling, standing rule, correction, "from now on" — here, in the section it belongs to, same commit. Not recorded until it is in this file; don't answer "noted" and carry it in context only.
- **Never the auto-memory directory** (`~/.claude/projects/…/memory/`) or any other out-of-repo note. Outside the repo = no gate, no grep, invisible to every worker.
- **Ask before changing this file (Anthony).** Draft the wording, show it, land it on his yes. An agent's own inference installed as law propagates further than any code change.
- **Rules here; mechanics in `docs/`** (one file per tool, indexed by `docs/README.md`). Split by KIND, not length. This file carries only what must be obeyed *prophylactically* — before you'd have reason to open a doc.
- **Rules, not citations.** State the *shape* of a trap, not a name that gets discharged next week. Specific instances live in source headers. Exceptions: the load-bearing documents and commands (this file, PROOF-STATE.md, EVIDENCE.md, `typecheck-performance-numbers.md`, `docs/`, `make` targets, `agda/src`, `agda/evidence`) — vocabulary, not instances.
- **No calendar dates, including on a ruling (Anthony).** The name alone makes it unarguable; the timestamp does nothing. Conflicting rulings get MERGED, not ordered by date.
- **No line numbers, here or in a source comment.** A stale name fails a grep loudly; a stale line number resolves, points at unrelated code, and is believed.
- `make roadmap-check` enforces dates on this file and `docs/`; `make comments-check` on `agda/src` and `agda/evidence`. A date is a build failure.
- **Edit a single file with `Edit`, not `sed`/python heredoc (Anthony).** Auto mode's Bash preference does not extend to editing. Carve-out: a genuinely multi-hunk patch, with `assert old in s` per hunk, written once at the end.

## THE GATE — `make gate`

Cheap textual checks run FIRST — seconds by grep vs. many minutes of Agda. **Run it rather than trusting a memo, including this one.**

Every `*-selftest` proves its checker still fires; they are not findings, they are the reason a green check means something.

| Target | What it will not let you do | Mechanics |
| --- | --- | --- |
| `wiring-gate` | a definition/postulate/module with no route to Main; a `⊤`-typed postulate; a bare `open import` in Main. A name PASSED to a postulate earns no credit — that is "a postulate must be a leaf" | [docs/wiring.md](docs/wiring.md) |
| `wiring-refuted` / `wiring-probed` | same law over the two evidence trees, rooted at `Refuted.Main` / `Probed.Main` | [docs/wiring.md](docs/wiring.md), [docs/evidence.md](docs/evidence.md), EVIDENCE.md |
| `evidence-check` | E1 a `src` file importing an evidence tree; E2 a probe with no `-- TARGET:`, or one naming a dead statement; E3 a receipt outliving its subject — discharging a postulate fails until the receipt above it is re-read and DELETED; E5 an unstamped or stale fingerprint; E6 a fork that doesn't inhabit `Separates`; E7 a target with no `Confirms` row; E8 the receipt cap | [docs/evidence.md](docs/evidence.md), EVIDENCE.md |
| `unsafe-check` | `TERMINATING` / `NO_POSITIVITY_CHECK` / `REWRITE` / `--type-in-type` on the proof path. The build is not `--safe`, so this is the only thing stopping a soundness hole | [docs/unsafe-check.md](docs/unsafe-check.md) |
| `dup-check` | two declarations proving one fact, up to binder spelling and type synonyms | [docs/find.md](docs/find.md) |
| `imports-check` | an unused import, or an unused name in a surviving clause | [docs/imports-check.md](docs/imports-check.md) |
| `roadmap-check` | PROOF-STATE unsorted, missing a live postulate or naming a dead one, over the row/preamble budget, dated, fewer than 3 or more than 7 legs, a leg over budget, a wrong DERIVED evidence field, a DIFFICULTY row standing on nothing, or a row of the tier being worked that nothing has instantiated. `make roadmap-evidence` writes the field | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `monster-check` | a line ADDED to `agda/src` outside the lowest open tier's monster's own dependency CONE — what its statement and body REACH, read off the tree AS EDITED | [docs/monster.md](docs/monster.md) |
| `roadmap-order` | discharging a GRINDABLE or DIFFICULTY row while its tier holds an open FALSITY or SHAPE. Only DISCHARGE is held — delete, rename, split, restate, reclassify stay free; a PREREQUISITE the risky statement names is exempt | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `roadmap-moved` | a branch landing proof work with PROOF-STATE byte-identical to **main**. Baseline is the merge-base, so fix-ups inside a branch cost nothing | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `comments-check` | a date, a historical marker or a LINE NUMBER in `agda/src`/`agda/evidence`; evidence not last and in order; a DOUBLED marker (`-- -- RECOVERY:`); a `TWIN`/`REFUTED`/`PROBED`/`RECOVERY` that doesn't resolve. `DEAD ROUTE` is unvalidated — it names nothing | [docs/comments-check.md](docs/comments-check.md) |
| the tower (inline in `gate-heavy`) | **a warning is a failure** (`-W error`, exit 42) | [docs/agda-build.md](docs/agda-build.md) |
| `refuted` / `probed` | the evidence trees not typechecking | EVIDENCE.md |
| `bug-cache` | a known impl counterexample regressing. `Unit-Test.agda` is off Main, so nothing else would notice | [docs/bug-cache.md](docs/bug-cache.md) |

Also: `make imports-fix`, `make postulates` (the complete remaining-work ledger, by name), `make find`, `make find-prose`, `make strip-selftest`, `make agda-dev-selftest`.

## Autonomy

Standing approval for any change that **does not alter the spec** — impl edits, protocol changes, new operators, refactors, experiments. Don't ask; go. Throw a lot at the wall, keep what passes QuickCheck/oracle, revert what doesn't.

**The `Exp` tree is FIXED, and the evaluator is not (Anthony).** Its formers are not the spec, so the standing approval above reads as licensing a new one — it does not. Evaluator internals are free: change the relation, the scheduling, the carrier, whatever makes it work and provable. A change that needs a new `Exp` former, or re-types an existing one, is a question instead.

**The stop conditions are exhaustive — nothing else is one (Anthony: "never stop working until you hit a stop condition").** All three are questions only Anthony can answer:

- **The spec must move** (`agda/src/Spec.agda`) — a question, never a patch.
- **The proof is SPIRALLING** — the same region producing FALSITY across three successive subdivisions. Reconsider the mechanism, don't subdivide a fourth time.
- **The impossibility pair** — two programs whose primitives produce byte-identical emit streams (same provenances, init/close, values, order) but that genuinely batch differently in real rxjs. **STOP and tell Anthony; do not act on it.** Not the same as "impl disagrees with spec", which is just a bug to fix in the impl.

## The goal

`agda/src/Verify-Batch-Simultaneous/The-Proof.agda` fully discharged, no postulates, everything typechecks, on every canonical program. "Passes almost all seeds" is a waypoint, not the line. One counterexample in 500 means the theorem is false.

## Delegation — the design session directs, Sonnet workers grind

- **Workers run Sonnet 4.6, and `model: "sonnet"` does NOT get you there** — that alias resolves to Sonnet 5 here. Both levers apply only at session start, so a running session cannot change or verify its workers' model; say so plainly. → [docs/delegation.md](docs/delegation.md)
- **Workers never babysit long builds.** Iterate with `make agda-dev`, land dev-green bodies, hand `make gate` back to the design session.
- **A worker must kill any detached build before reporting**, and say nothing is running. Agda doesn't lock interfaces — two processes on one `.agdai` is a corrupt cache or a spurious failure. Covers `make agda-dev`, which shares the gate's cache.
- **Delegation has a FIXED context cost — amortise it or do it yourself (Anthony).** Delegate on BREADTH (several independent items, concurrently), REPETITION (one context, many similar obligations), or NARROWNESS (a small nameable slice). **Keep DEPTH:** one hard thing in a file already loaded is cheaper to do than to delegate.
- **The tell, and it is reliable: if writing the directive required you to do the analysis, you have already done the expensive part.**
- Parallel workers authorized; parallel Agda up to two heavyweight checks at once, cheap modules freely → [docs/typecheck-cost.md](docs/typecheck-cost.md).
- **Directives carry the law** — every worker prompt restates the rules it needs.
- Workers don't commit. Land green work via a PR, never a direct push to main — ask first.
- **Stage explicitly while a worker holds a file — never `git add -A` (Anthony).**
- **Run continuously** (Anthony: "continue and continue, don't stop for context window or usage credits"). Review, merge, launch the next.

## Long Agda builds

- **`make gate` is the merge gate and it ROUTES — type it and let it decide.** It prints which path and why. **Don't run it to merge — open a PR and let the `Gate` workflow run it.** Timings: `typecheck-performance-numbers.md`.
- **Carve-out for forcing `gate-heavy`: TERMINATION** — the one property the dev loop can't see, since it stubs mutual blocks.
- **A warning is a build failure.** Every invocation goes through the Makefile's `AGDA` (carries `-W error`). Never call bare `agda` in the Makefile. Never silence a warning to get green — a warning you believe is wrong is a finding. The flag must be identical in the Makefile and `agda_flags()`, changed in the same commit. → [docs/agda-build.md](docs/agda-build.md)
- **Agda never checks `agda/src` — it checks the comment-stripped mirror, which is why a comment edit is free.** Never run `agda` against `agda/src` directly: a second interface cache, and every alternation invalidates the other's cone.
- **Two commands: `make bg T=<target>` as a BACKGROUND tool call, then `make bg-check T=<target>`.** `bg` blocks, logs, appends `EXIT=<code>`. `bg-check` reports GREEN / RED-with-tail / STILL-RUNNING. `bg-wait` is for a human. A `sleep N; tail` or `until` loop is the apparatus re-implemented worse. `make bg` always exits non-zero by design, so **a completion notification is never a result — `bg-check` is.**
- **"Detached" means the Bash tool's background flag, never shell syntax (Anthony).** Type the command bare. No `&` (backgrounds a wrapper the harness already manages), no `>/dev/null 2>&1` (throws away WHERE the log is), **and never a pipe — a pipeline exits with the LAST command's status, so `make gate | tail` reports the tail's success over a RED build.** A foreground call is capped at 600 s and a build that outruns it is KILLED. **One build at a time.** → [docs/bg.md](docs/bg.md)
- **The Bash tool's cwd persists between calls — pin it.** Absolute paths; never rely on a previous `cd`.
- `touch` does NOT dirty a module — invalidation is by CONTENT.
- **A proof body on the `budget-sufficient` spine must be sealed (`abstract`)** — three multi-hour OOMs came from unsealing one.
- A mid-build RSS of 7–12 GB is normal and evidence of nothing.
- **Cost model: mutual-BLOCK membership is everything; file size is nearly irrelevant.** Run `make agda-dev ARGS='--list <file>'` before believing it, and MEASURE on a coherent cache — a rebuilding dependency masquerading as module cost has produced four phantom diagnoses. Positivity splits are done; that question is closed.
- **Second axis: a block member in NO cycle is never stubbed, so every focused check of every OTHER member re-proves it in full.** Tell: per-member times don't vary with the member. Hoisting means moving to ANOTHER module. Attribute before splitting. → [docs/agda-dev.md](docs/agda-dev.md)
- **All measured timings live in `typecheck-performance-numbers.md` and nowhere else.** `gate-heavy` and `agda-dev` append their own.

### `make agda-dev` — the iteration loop

```
make agda-dev ARGS='<file> <member>'   one member ← the grind loop
make agda-dev ARGS='<file>'            one module, every member
make agda-dev ARGS='--list <file>'     free: which members are in which block
make warm ARGS='<file>'                build a file's deps; unbudgeted
```

- **`ARGS=` takes at most ONE file plus ONE focus member.** A second file is read as the focus member and reported absent, which reads as a proof failure.
- **Dev-green means the types line up, not that the proof is valid — but only where something was STUBBED.** A module with no multi-member block is emitted VERBATIM, so the sweep is a real check there. Where a block is stubbed, termination of the real mutual recursion is not checked.
- **A dev check that is not seconds is a FINDING, not a budget to raise.** Read `typecheck-performance-numbers.md` first. Work BOTTOM-UP. Third cause the other two hide: the module has outgrown the loop. Do NOT reach for `--only-scope-checking` — measured, buys nothing, removed.
- **A red `agda-dev` on any file in `src` is a P0 — fix it before the work you were doing.** Never route around it.
- → [docs/agda-dev.md](docs/agda-dev.md) for the budget, `HOLES=1`, `NOT_DEV_CHECKABLE`.

## Where code goes

- **All new proof code in `agda/src`**, where reachability, the ⊤-postulate check and the claim graph see it from minute one. That is what makes "did we already prove this?" a grep.
- The failure prevented is being UNCLAIMED, not being outside `src`. Work no claim root reaches is what parks itself for months and gets re-derived.
- **Evidence goes outside `src`, and that is not an exemption (Anthony).** A refutation and a probe are not proof code; nothing may depend on either. Both live in `agda/evidence/`, each with its own claim root, gated in full; a `.agda-lib` boundary makes a `src` import unresolvable. **`EVIDENCE.md` is the law — read it before adding, retargeting or deleting either.**
- Do not recreate the old bare `probe/` directory — it sat outside every claim graph.

### Module granularity

- **Cut at mutual-SCC boundaries.** A mutual block is an indivisible checking unit. **Never restructure genuine mutuality to shrink a module** — proof shape wins over check time. Target ≤20 s solo recheck for every non-SCC module. → [docs/typecheck-cost.md](docs/typecheck-cost.md)
- **A new fact goes in the SHALLOWEST module reaching its consumers, not the deepest that could host it (Anthony).** A four-line lemma near the bottom invalidates that module's whole cone. Check the cone before placing it. Does not contradict `dup-check`'s "move the fact DOWN", which is about a fact that already exists twice.

## Agda traps

Each cost real time at least once, and they share a shape: **Agda reports them against the WRONG thing.** Before reasoning from an Agda error, check whether it is one → [docs/agda-traps.md](docs/agda-traps.md).

- "X is not a constructor of T" for something you meant as a variable → grep for `X :` before touching the proof.
- An implicit used inside an `all`-predicate lambda is a fresh unsolved meta per element → bind it on the clause's left-hand side (`{e = e}`).

## Work from the outside in

Datatypes, primitives and end goals first; link with postulates; top-line results stated and typechecking *in terms of postulates*; only then chip away, one at a time.

- **One at a time means TOPMOST first (Anthony).** Only the layer directly beneath the settled one is being worked; everything below stays postulated. Tell that a session has slipped a layer: the edit threads an argument through a fourth signature while the statement it serves is still red.
- **A Σ-receipt has content only through its witness.** If every conjunct is upward-closed in the witness, the statement is vacuously satisfiable — check BEFORE grinding. Pin the witness to the one the consumers bound, or put the bound in as a conjunct. A face of this development was machine-refuted as vacuous by exactly this shape.
- **Recursively: never prove pieces before their assembly exists.** State the assembly with the pieces as postulates, make it typecheck, then prove pieces starting with the MOST UNCERTAIN. Pieces proven ahead of their assembly are speculative inventory, and their sunk cost biases the design toward keeping them.

## SEARCH FIRST — assume it already exists

Treat "I need a lemma saying X" as a SEARCH task until a search has failed. The cost is asymmetric: a search costs seconds; skipping it costs whatever you build instead, which is usually *weaker* than what was there.

```
make find Q='≤ slotsSize'     every STATEMENT whose type mentions it
make find-prose Q='...'       findings, which are prose by construction
```

- **Run `make find` before you state a postulate, write a lemma, or commission a probe.** It walks all of `agda/src` and takes no narrowing argument — which is the point: a hand-rolled `grep` was FOLLOWED and still failed, scoped to two arguments instead of the tree.
- **Run `make find-prose` before picking up any row that is not GRINDABLE, and before commissioning a probe.** It answers *has anyone already been here* — dead routes, coverage boundaries, rulings, measured traps — none of which `make find` can see. Returns the BLOCK. → [docs/find-prose.md](docs/find-prose.md)
- **Search the CONCLUSION's shape, not the name you imagine.** Names here are idiosyncratic. A miss is weak evidence; two misses on different phrasings is strong. **Read the SIGNATURE, never the header prose** — a header saying a route is dead is a claim about an attempt.
- **`make dup-check`: a finding is two SITES, not two names.** Agda's `ClashingDefinition` says nothing when either copy is `private`. **When it fires, MOVE THE FACT DOWN — do not pick a winner**; deleting one copy at random re-creates it later. Keep ONE naming convention per class of fact.
- **This does not license citing something you have not opened.** Find it, read its actual type, confirm the indices line up.

## Survey the hole-set before discharging any of it

**Census every site's goal first, then classify, then prove — never site-by-site.** Depth-first grinding is the standard way this campaign loses time: every blocker found late can invalidate proofs already finished above it.

**Same for ERRORS, because Agda reports one per module and aborts (Anthony).** A red module is a queue of unknown length, and the early runs are fast for the wrong reason — they measure how long it took to ABORT. When a module goes red after a change to something widely consumed, **census the consumer sites TEXTUALLY first**: one grep lists every site, and the build then CONFIRMS a list instead of discovering one.

- **You usually do NOT need a typecheck to read a goal.** Where the obligation is *declared* — a Σ-returning family whose head fixes the conjunct — the goal is `substitute the witness into the head's conjunct`. Batch Agda won't hand you goal types anyway: holes report source positions, and forcing the type aborts at the FIRST error.
- **Four buckets, and do the LAST one first.** (a) trivial/inflationary; (b) an existing lemma applies; (c) needs a new lemma; (d) BLOCKED until a signature, a call-site argument or a measure changes. (d) is the schedule. (a) and (b) are the right work to delegate.
- **Check every conjunct at zero before grinding it.** These bounds routinely go FALSE at `bud = 0`, `ops = 0`, `dep = 0`. A one-screen refutation says the site needs a positivity hypothesis threaded, not a cleverer proof.
- **Count sites by grepping the BARE postulate name.** A hyphenated guess misses every suffix site and reports a false all-clear.
- **A shared deferral postulate hides call-site ARGUMENTS, not shapes.** Record each one in the postulate's header the moment you notice it.

## Keep the repo lean

Every definition used somewhere; only the top-level exports are exempt. No back-compat shims, nothing "stored for reference", no legacy, no deprecated. **Don't be afraid to throw out code or documentation** — git history is the archive.

### DELETION

`make wiring` is trustworthy, so a name it reports is a finding to act on. **Deciding is yours, and asking is the failure mode (Anthony: "let's delete it if it's not used? That seems obvious to me").** Every rule below names something to VERIFY, never a reason to escalate.

- **"No consumer today" and "no consumer ever" are different questions.** A lemma stated AFTER its own specialisation is orphaned by placement and wires in one line. **Prefer wiring to deleting whenever a plausible consumer is nameable.**
- **The commit message carries the finding** — write what the deleted thing established. If a NAMEABLE future consumer remains, add `-- RECOVERY: git show <sha> restores …` to the header of the thing that would consume it.
- **A superseded predecessor is deleted, always (Anthony)** — not wired, not parked, not kept until the successor is proven. It drags a whole support cone that every local check reads as wired, because a mutual cluster consumes itself. **But ESTABLISH that it is one first:** both clusters the first sweep reported turned out not to be. The question is not "does a successor exist" but **"does the successor prove everything the predecessor proves?"** — answered by diffing the two bodies' ARMS, not their statements.

## DE-RISK MODE: test for falsity first, grind last (Anthony)

Total risk is the SUM over the ledger, so work is ordered by *risk reduced per unit effort*, not by proof-progress optics. The tier-ordered roadmap is PROOF-STATE.md; read it before picking up any postulate.

### The risk classes — worst first

Every live postulate carries exactly one. PROOF-STATE assigns them; this file defines them.

- **FALSITY** — may be false. Worst because retroactive: everything ground above it is wasted, not delayed. **Also where a statement nothing has ever instantiated sits**, however plausible — "may be false" is a claim about what is KNOWN. The class a new postulate is born into; a probe reaching its risky region moves it.
- **SHAPE** — wrong as written, restatement *guaranteed* (typically a conclusion needing information no hypothesis carries). Worse than DIFFICULTY because restating cascades and can INTRODUCE falsity. **Never grind a SHAPE row; restate it.** A header recording a gap between hypotheses and conclusion has ALREADY put its row here.
- **VACUITY** — typechecks, asserts nothing. Worse than DIFFICULTY because it reads as discharged. Two live shapes: ⊤-typed postulates, and Σ-statements upward-closed in their witness.
- **DIFFICULTY** — true and correctly stated, proof is just hard. The DESIGN half (shape of the induction, the measure, the index) is the expensive part. **"True and correctly stated" is a claim about EVIDENCE** — a probe that reached the risky region, a refutation pinning this form, a proven mirror. Absent one the row is SHAPE if the gap is written down and FALSITY if nothing is. **The class with no floor under it and the one that reads as safe**, so it is where an unexamined row lands by gravity.
- **GRINDABLE** — the shape is ALREADY KNOWN: a proven twin whose clauses correspond, or a mechanical route. Nothing to decide, only to type. Weakest class.

**`make roadmap-check` enforces the floor at both classes that claim something (Anthony).** A DIFFICULTY row whose headers carry no durable marker is a build failure, as a GRINDABLE row naming no twin already was. FALSITY/SHAPE/VACUITY are exempt — they assert nothing about the statement being right. **The repair is never to acquire a marker; it is to reclassify DOWN.**

**GRINDABLE is the delegation boundary — that is what the class is for.** The expensive part is already decided and written down, so a fresh context can execute it. A DIFFICULTY row is the design session's own work; delegating one hands over a decision that has not been made, and it comes back as analysis instead of edits. Measured once: a Sonnet-4.6 session discharged seven GRINDABLE rows in under four hours, then spent two full context windows on ONE DIFFICULTY row and produced a proof plan and no code.

**Risk-reduction priority outranks parallelism: while a tier's roadmap has an open leg above the GRINDABLE ones, do NOT fan workers out across its mechanical rows — work the top leg, and take it yourself (Anthony, twice: "Don't! Do the hard stuff first").** Fan-out looks like leverage and buys optics while the row that could move the ground stays open. **Carve-out: a GENUINE prerequisite the risky row's own statement or header NAMES** — "adjacent" or "same module" is not one, and the near-miss is the common case. Parallel fan-out across mechanical rows is for a tier whose open rows are ALL GRINDABLE.

**`make roadmap-order` enforces it.** The pull is structural, not careless: `roadmap-moved` requires every commit to move the roadmap, a risky leg routinely ends in a FINDING rather than a discharge, and a finding-only commit reads as unfinished — so a mechanical row gets closed alongside it to make the commit feel whole. **Settle risk near the trunk:** work proven under an open FALSITY is not delayed but FORFEIT if that statement is refuted.

**Only BANKING is held (Anthony).** Deleting, renaming, splitting, restating and reclassifying a row are all free. The one held move is a name leaving the postulate ledger while still declared in `agda/src`.

**Earning GRINDABLE: name the precedent in a `TWIN:` section**, where `make comments-check` resolves it and refuses a twin that is itself still a postulate. Absent one, the row is DIFFICULTY.

**A class is a property of EVIDENCE, not of confidence, and may only be lowered by evidence that reached the risky region.** Name the region, or the receipt does not count. A row was once downgraded FALSITY → DIFFICULTY on a probe covering only the near-degenerate case, and had to be reverted. **Corollary: a named route is not evidence.** A proof sketch and a green probe of the near-degenerate case lower nothing.

### Tier order is law (Anthony)

**Lower tiers finish first. Strictly — not "mostly", not "while a build runs".** Each tier is built ON the one below, so grinding an upper-tier statement while a lower tier is open bets on ground a design failure would move. **Carve-out: answering a DESIGN question** — cheap, and it aims the grind. Never grinding over one.

**Before starting any task: if the postulate is not in the lowest open tier, and the work is not a design question, it is PARKED — say so and take a lowest-tier item.** Which postulates those are lives in PROOF-STATE.md; this file never names them. Measured once at five days of discharges that all went to non-anchor rows while the anchor sat untouched.

**Within the tier, follow the BIG PICTURE ROADMAP, not the next row down (Anthony).** Take the top leg and work it end to end. The rows are the ledger the legs are drawn from, and reading straight down them proves one postulate at a time — the wrong unit, because the expensive discovery here is never the clause but the neighbours a restatement drags with it, and a row cannot show you those.

### The convergence test

Grinding a FALSITY row routinely spawns new postulates, and a new FALSITY is not by itself bad news.

- **Converging** — the new FALSITY's risky region is strictly SMALLER (a sub-case of the same edge). Localisation is what buys probeability: a statement about one branch can usually be instantiated; one about a whole clause cannot.
- **Spiralling** — not smaller, or reaching UPSTREAM into machinery already ground.
- **Stop condition:** the SAME region producing FALSITY across three successive subdivisions. Wrong design in the mechanism underneath; reconsider it.

**FALSITY does not mean the theorem is false** — it means this STATEMENT might be, and you restate. The common refutation is repaired by a hypothesis already available where needed. The expensive shape is a repair needing a hypothesis NOT available at the call site; name that one when you find it.

### Probing

- **A machine refutation is worth as much as a proof — usually more, since it is cheaper.** False now costs a restatement; false under a tower costs the tower.
- **Auditing statements for truth is the PRIORITY.** A `-- SUSPECT:` note is not the response to a doubt you can test: test it.
- **PROBE BEFORE GRINDING.** If the sides compute, instantiate at concrete programs in `agda/evidence/probed/`, checked with `make agda-dev`, pinned by `refl`. Every probe ends in a refutation or a `-- PROBED:` receipt saying what shapes were covered. **An unprobed probeable postulate is the cheapest unmanaged risk in the repo.**
- **Probe the ASSEMBLY's conclusion, not only its leaves.** A real body over postulated leaves has a conclusion that COMPUTES, and nobody instantiates it because it typechecks. Its falsity is the retroactive kind. Tell that it is worth the minute: the leaf's bound and the assembly's bound are stated in the SAME currency.
- **Assume a probe already existed until a search has failed (Anthony).** Binds on every row that is not GRINDABLE.
  ```
  git log -S'<postulate name>' --all --format='%h %s'
  ```
  **Search by the TARGET'S NAME, never by the probe directory's path** — probes have not always lived where they live now, so a path-scoped search reports a false ALL-CLEAR. Then `git show <sha>^:<path>`. The receipt convention does not make this redundant: ten receipts in the tree against ninety-eight probe files deleted.
- **What you recover is usually worth more than a verdict** — the HARNESS (real-evaluator plumbing, ⊔-shaped measures, refutation families already tried) and the BLOCKED/BOUNDED verdicts, which are findings about what CANNOT be probed.
- **Read the recovered probe's STATEMENT, not its verdict.** A probe is expired by its target being discharged *or restated*, so what you find is usually evidence about a statement that is gone. A green on `A + B + C` says nothing about `(A + B) ⊔ C`.
- **A probe expires with its target, mechanically.** `-- TARGET: <postulate>`, and `make evidence-check` fails the moment that name leaves the ledger. Then DELETE or retarget it; never relax the check. Probes and refutations decay differently and only one says so: a refutation dies when `src` can no longer STATE it and `make refuted` goes red that day; a probe dies when its target is PROVEN and nothing happens at all. **A probe that outlives its target because what it pins is the EVALUATOR is a unit test — its home is the bug cache.**
- **A probe's TARGETS are what its ROWS are evidence about**, not everything its findings touch. A receipt naming a statement the rows never reached is a FALSE coverage claim. A FINDING is ordinary prose in whatever statement it CONSTRAINS — usually not the target, and often a definition, which cannot carry a receipt at all; name the probe module in backticks there.
- **A probe informing N statements gets N one-line pointers, never N copies of its coverage claim.** Several `-- TARGET:` lines in one probe are supported.
- **Provenance travels with the FINDING, not with the receipt.** Whether something came from instantiation or from reading the definitions belongs beside the claim it justifies, not above a `PROBED:` section where it reads as narrating the ledger.
- **Determine computability by LOOKING, never from a remembered list.** An `abstract` block seals a family, and blocks get added for performance without the statements changing. Any list of "the computable ones" here would be a research finding pretending to be a rule — one was, and it named a family that had since been sealed.
- **Hypothesis-side and conclusion-side computability are separate questions.** Say which SIDE is blocked; "sealed somewhere in the statement" does not imply symbolic-or-nothing.
- **Never extrapolate a probe past its shapes.** Say which were covered and which were not.
- **Decide which axes CAN refute before sweeping any: only a measure-side axis can.** For `lhs ≤ rhs`, a parameter that moves only the RIGHT weakens the claim, so no instantiation of it can refute — unfalsifiable by construction, however tight the rows read. It runs the other way too: an axis with no coverage is a finding only if it moves the measure. Both errors were made on one row of this campaign.
- **A row that could not have failed is not a row.** Label every row LOAD-BEARING or DEGENERATE and state what would make it fail. Three ways a probe lies green: **(1) vacuous rows** — the quantifier is empty (`all _ [] = true`, `0 ≤ᵇ _`), so name the covered CONJUNCTS, not the covered programs; **(2) hand-built states** — `record (st-init e) { … }` is not reachable, so reach states by RUNNING, and treat a constructed failing state as a refutation candidate whose reachability is the finding; **(3) reading an assembly backwards** — `P = P-core o₁ … oₖ` proves P FROM the core, never the core.

### Dead routes

A refuted statement and a dead route are different findings, and only the first is machine-checkable — a dead route has no `⊥` to state. **When an attempt fails for a structural reason, add `-- DEAD ROUTE:` to the header of the postulate you were trying to discharge.** Say what was tried and **what structurally blocked it** — "tried X, didn't work" stops nobody.

- **Machine-checked refutations live in `agda/evidence/refuted/`**, checked by `make refuted` and `make wiring-refuted`. **Keeping one in `src` is actively harmful** — `src` must then keep whatever machinery makes the dead route STATE-able, measured at seven live definitions held up by six refutations. `src` may name a refutation in a `-- REFUTED:` comment; it may never import one.
- **A dead route is not a licence to weaken the statement.** Deleting a dead-route line requires the route shown WORKABLE, not merely untried again.

## THE MONSTER — the one thing each tier is trying to kill (Anthony)

Rows are the ledger, legs are the schedule, the MONSTER is what the schedule is FOR. A NAME, because a name is what a machine can hold. `make monster-check` fails on a line added outside its dependency CONE.

**Choosing one: as likely false as possible, as far down the tree as possible, with as big a blast radius as possible (Anthony).** Falsity and blast radius are both monotone UP the tree, so maximising those two alone returns the tier's top line forever. **Depth is the only pressure that selects anything else** — among nodes that could genuinely be false, take the DEEPEST that still takes its siblings and parents with it.

**The floor under the descent is the cone itself**, which is the commit licence: a leaf is usually past it, since its cone is its statement's vocabulary and the assembly it serves is off-tree. **The monster need not be a postulate and usually is not** — a relation every leaf is stated in can be wrong in a way no ledger records.

TOO HIGH is the cone percentage the check prints; TOO DEEP is an offender list that repeats until `also:`-ed in, so a growing `also:` ledger means the monster is misplaced. Exceptions are declared with an `also:` line in the tier's own section, never a flag. → [docs/monster.md](docs/monster.md)

**A rising postulate count is the mechanism working, not a regression** (Anthony: *"the relentless mindset of reducing those numbers is very harmful"*). One vague postulate split into six specific ones is PROGRESS. The only number that matters is whether `The-Proof.agda` is discharged.

- **Do NOT minimise the count, do NOT apologise for it**, do not describe an increase as a cost or a trade.
- **Do NOT weaken a statement to make it typecheck.** Postulate the full-strength statement and report the obstacle.
- **Never grind a hard proof when a postulate will do.**

## A POSTULATE MUST BE A LEAF (Anthony)

**Postulate-to-assembly conversion** — when a proof has nowhere to plug in because its only would-be consumer is a monolithic postulate: convert that postulate into a REAL DEFINITION over smaller postulates, and have the definition **CALL** the pieces. **CALL, not pass.**

```agda
postulate l₁ : L₁                        -- the gap, a true leaf
P : T
P = <real body applying l₁ …>            -- the composition is CHECKED
```

**Not** `postulate P-core : L₁ → … → T` with `P = P-core l₁ …`, where the composition is checked by nobody. That form verifies only that the types are well-formed, never that they SUFFICE — two postulates each shed seven-plus leading hypotheses when finally proven. **A `-core`'s hypothesis list is a HYPOTHESIS about the route, not a specification.**

**When the body cannot be written yet, postulate the parent BARE and mint no leaves.** Nothing is ever blocked; the rule only changes the ORDER to assembly-first. An unwritten route goes in the parent's header.

**Enforced as a corollary of reachability:** `wiring-gate` gives a name passed to a postulate no credit, so a lemma whose only use is being handed to one has no route home. No grandfather list, no name-based heuristic. → [docs/wiring.md](docs/wiring.md)

**Writing the body does not licence breaking other laws (Anthony).** The temptation is sharp: **writing a body turns an unpaid premise into a TYPE ERROR, and the fastest way to clear one is to add a hypothesis to the parent** — which launders TRACKED debt into UNTRACKED debt, and *feels* like progress because the file goes green.

**So a missing invariant found by a fit test goes in the INVARIANT RECORD, not in a signature (Anthony).** A field obliges every producer and consumer; a hypothesis obliges only whoever calls today. **Cascading through the record's consumers is the COST OF THE FACT BEING TRUE.**

Likewise: do not WEAKEN the parent, do not close an arm with a vacuous postulate, do not seal a gap in prose. **If a body cannot land without breaking one of these, it has FOUND something and it STOPS.**

**A stop is a FINDING, not a discharge (Anthony).** The roadmap row STAYS and the parent is still a parent until the body lands. A good finding is the most convincing thing there is to mistake for progress.

**Pass every lemma ETA-EXPANDED with explicit implicits** — `(λ {n} {Γ} → f {n} {Γ})` — or a statement that reduces away its own implicit gives `Unsolved metas`. Other mechanics: [docs/wiring.md](docs/wiring.md).

**Two shapes that are almost always wrong — check every new postulate for both.** A conclusion needing information in NONE of its hypotheses; and a Σ-statement upward-closed in its witness. Under de-risk mode these are refutation targets, not `SUSPECT:` notes.

**For the first shape, suspect a MISPLACED CALL before a missing lemma.** Often nothing is unproven — the statement is being made at the wrong INDEX and the caller is what is misplaced. **Tell: the gap is a fixed small offset (one level, one frame, one `suc`)** rather than a missing fact about the domain. The check is cheap: find the same operation where it is already PROVEN and **diff the ARGUMENTS, not the statements.** Which families mirror which is recorded in the source headers, never in a list here. Two postulates fell to moving the call, with no new mathematics. **But a mirrored counterpart is a property some parts happen to have** — don't force the analogy.

**Adding a hypothesis is a RESTATEMENT and needs a restatement's justification.** `A → B` is weaker than `B`, and a hypothesis is invisible to the ledger where a postulate greps, gets counted, carries a class and sits in PROOF-STATE. **The one sufficient justification is that the unconditional form has been REFUTED.** **"The call site happens to supply it" is NOT a reason** — today's call sites are an artifact of today's assembly.

## CODE BEATS PROSE (Anthony)

**A finding written in English that could have been written in Agda is not done — it is deferred.** If you have just worked out that A follows from B, the deliverable is the assembly, not a header paragraph saying so.

**The tell:** you write "X could be implemented in terms of Y" / "this reduces to Z" / "the route is …", and then you commit. **That sentence is a work order addressed to you, right now.** Carry it out, or say plainly why you cannot and postulate the residue at full strength.

An assembly is CHECKED, greppable and counted; a paragraph is checked by nobody, ages silently, and gets re-derived. **Corollary for headers: the moment a header explains a derivation that would typecheck, move it into the derivation.**

**NEVER WRITE CODE IN A COMMENT (Anthony).** Not a body, not a signature, not a "here is the lemma we need" block. Not checked, not counted, and it *looks* discharged. The excuse that produces it every time is the wiring law — the piece typechecks but its consumer is still a postulate. **The right repair is to convert the consumer into a real body over a smaller leaf**, however thin. If it genuinely cannot be split yet, say in one sentence what is owed and let git hold the text.

## HEADER SHAPE (Anthony)

**Explanation first, then evidence — `REFUTED`/`DEAD ROUTE`/`TWIN`, then `PROBED`, then `RECOVERY` — evidence LAST.** That is what gives a long header landmarks. A marker is a **LEDGER ENTRY**: to mention a refutation in passing, name its module in backticks rather than opening a section mid-paragraph.

**A marker that names something must name something that EXISTS (Anthony).** Write the reference BACKTICKED or DOTTED — English is full of words this tree declares.

- **`TWIN:` names a PROVEN definition.** If the named twin is itself still a postulate the class is wrong — the row is DIFFICULTY.
- **A `PROBED:` receipt for a deleted probe carries the SHA.** A probe is supposed to outlive nothing, so the receipt is all that is left.
- **`DEAD ROUTE:` is unvalidated by construction** — it records that a *way of proving* cannot work, and there is no object to resolve. The section to reach for when a finding is real but names nothing.

**Sections are optional when absent and validated when present — never mandatory.** A filler `TWIN:` is worse than empty: it earns a class the row has not earned.

**The repair for an over-budget block is usually to SPLIT it, not to cut it.** A block is separated by a genuinely blank line, so the ceiling caps ONE unstructured explanation. An essay holding ten findings becomes ten blocks and nothing is lost. Reach for the knife only when a block holds ONE finding and still runs long. Worked instance: a 154-line wall became ten skimmable blocks with no prose deleted.

**Only the EXPLANATION is charged (Anthony)** — evidence sections and `git show` pointers are free. Budgeting the destination too would mean a finding with nowhere to go gets DELETED. The budget is the measured p99: its job is to declare a block **over-explained**, not to trim writing.

**Say it once: the explanation does not narrate the ledger below it (Anthony: "no redundancy in documentation").** The prose copy ages while the section stays live, which is how a block ends up carrying a refutation it no longer has. `make comments-check` fires on the narrow half; the rule is wider than the check.

**A header records what is true of the STATEMENT, never what happened to the DECLARATION (Anthony).** "Was restated", "was split", "converted from a `-core`", "measured at 400 s" are git's subject. **The superseded framing goes too** — a paragraph kept "so the dead candidates are not retried" is a dead route, which is one `DEAD ROUTE` line.

## THE GATE INCLUDES `PROOF-STATE.md` (Anthony)

**`make gate` is necessary, not sufficient. Update PROOF-STATE in the same commit that changes the ledger** — discharged, added, renamed, split, reclassified, reordered. A stale row misdirects the next session's whole leg.

**A leg is one PR of work, and `make roadmap-moved` enforces it (Anthony).** A leg is a GROUP sized by the BRANCH: the chunk this session intends to land next. **The unit is the branch, not the commit** — a branch takes as many commits as the work takes, and taxing every keystroke bought edits made to satisfy the check, which is fatal to a check whose subject is whether someone said something true.

**Three outcomes, and one always applies (Anthony).** The leg LANDED — retire it, promote the others, write a new one. The leg was NOT FINISHED — **rewrite the first leg as the work that remains**, which is worth more than the retirement. The leg's ROUTE DIED — **DISCARD it**, do not rewrite it; "the work that remains" keeps the old framing and shrinks it, and a refuted framing shrunk still steers the next session. The finding goes where a dead route goes.

**Every leg after the first may aim at the SAME postulates.** The legs are the next that many commits, not that many subjects. Pick the risk order first, then cut at commit boundaries.

**The legs are AIMED AT THE MONSTER (Anthony).** A set of legs that does not narrow it is that many commits with nothing underneath it that got smaller. Write each leg so its own prose says what it decides about the monster.

**Narrowing counts — it is usually what a leg buys (Anthony).** The monster is not expected to FALL; it is expected to have a smaller region left. When a leg retires, write down what it RULED OUT. **Narrowing is not REPLACING**, which is what happens when the old monster falls or the tier descends past it.

**One exception: a leg that removes a cost stopping the questions being worked at all** — a loop that is no longer a loop, a check that cannot run, apparatus a face needs before any of it can be instantiated. It narrows nothing and is still right, because the monster is unreachable until it lands. **Never more than one leg of the set** — a schedule that is all tooling is a tier that has stopped being worked.

**Three is a FLOOR, not a quota — write the fourth down (Anthony).** A route already worked out and cut into commit-sized pieces is the most expensive thing here to rediscover and the cheapest to type. Seven is the ceiling, past which the list has become a second copy of the ledger. **The legs do NOT cover the tier** — covering it is the ROWS' job.

Update it to its own header's hygiene rules, which are also part of the gate: one line per item (name + class + hook), NO numbering of any kind, research in source headers, completed items DELETED, no dated narrative. → [docs/roadmap-check.md](docs/roadmap-check.md)

## The wiring law: NEVER LEAVE A PROOF HANGING (Anthony)

**Nothing may exist without a consumer that traces to a top-level theorem.**

- **Every GAP is a postulate with a real signature** — never a comment, never a missing statement. Then **`make postulates`** IS the complete remaining-work ledger. (Do NOT substitute `grep '^postulate'`: that finds block HEADERS, a third of the count.)
- **Every definition and postulate is consumed, in code, transitively by a top-level theorem.** Then "did we forget something?" is answered by the typechecker.

**The workflow:** before proving a lemma, extend the assembly that will consume it — postulating whatever else that assembly needs — and land both in the SAME commit. **If the assembly needs a different signature to accept the piece, change the signature first.**

**A postulate must ASSERT something.** Wiring an unreachable definition in with a vacuous bridge is worse than leaving it unreachable. Two traps live here: ⊤-typed postulates whose real claim sits in a trailing comment, and Σ-statements upward-closed in their witness.

**Forbidden states.** An **unreachable definition** — a missing wire or dead weight, both findings, and leaving it undecided is not an option. A **lying comment** — prose describing an intent the code does not encode.

**MAIN IS THE TOP-LINE PROOF (Anthony).** `agda/src/Main.agda` is the root of the consumption graph and the deletion exemption. **(1) Whatever Main imports sticks around. (2) Main names individual definitions — NEVER a bare `open import`. (3) Main is never touched without Anthony's explicit approval** — draft and ask. `make wiring` reads Main's `using` clauses, so a filename never earns an exemption.

Main also defines the build's COVERAGE — **`make gate-heavy` IS the claim graph**, and anything outside it is not being checked. **Never close a coverage gap by re-adding a bulk import to Main.**

**Why this is law:** unwired proven work costs more than refutations. A proof nobody calls sits inert while the work it would have done is re-derived inline, so the same thing is proven twice; and a tower built without its consumer is a tower whose shape was never checked.

## TypeScript style

As purely functional as possible: no mutable state, no direct `.subscribe()`. Delegate IO/statefulness to rxjs operators like `scan`. Two reasons — cleanliness, and keeping the primitives and `batchSimultaneous` in near-direct correspondence with the Agda.

## The change workflow — batchSimultaneous IMPLEMENTATION only

Not for proof work, tooling or documentation.

1. **Agda first**, before touching TypeScript.
2. **QuickCheck dev loop** — `npm run agda:qc`. **The spec is gospel; when impl and spec disagree, the implementation is wrong by default.**
3. **Ignore `The-Proof.agda`** during this phase; errors there are fine.
4. **Port to TypeScript**, only once QuickCheck passes.
5. **Oracle** — `npm run oracle`.
6. **Formal verification last**, in phases, committing in-between results, until there are no gaps.

**Resolving ambiguity:** defer to naive plain rxjs — actually run the example and see. If that doesn't settle it, surface the question with a TypeScript rxjs example that **avoids the `*All()` higher-order operators where possible**.

**Authority ordering (Anthony, most → least): Anthony's discretion, then the Agda spec. There is no third source.** `agda/README.autogenerated.md` is NOT an authority (Anthony: "I don't care about the readme.autogenerated, for the record") — nothing generates it, no gate reads it, nothing fails when the spec moves out from under it. Do not resolve an ambiguity by citing it, do not treat a case it is silent on as a gap, do not surface a conflict with it as a question.

**The Agda impl MUST mirror the TS impl.** If the Agda relies on something TS cannot do, the correspondence is void. When in doubt about portability, **port it to TS and run the oracle before building on it.**

## Bug cache

Capture an implementation bug immediately as a **row of the corpus** in `agda/src/Implementation/Unit-Test.agda` — a program, not a claim about one. Dead simple: a wall of little entries, no fancy names, no abstraction. **Append-only**, and the invariant is **`make bug-cache` green ⟺ no known counterexample remains**.

The run happens in a BINARY, not the typechecker — a row used to be a `refl` over a whole `evaluate` run, so an append-only corpus charged the gate forever. Corollary: a green row is checked by the GHC backend and the FFI, so **no proof may ever depend on the cache**. Delete the module once `The-Proof.agda` is discharged. → [docs/bug-cache.md](docs/bug-cache.md)

A new "naive rx" operator to fix an Agda-impl bug is allowed and encouraged when it is the best solution — but follow the port order: TypeScript first, as a proper rxjs-delegating, purely-functional operator.
