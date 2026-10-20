# Working methodology

Agda model (`agda-impl/`) + TypeScript impl (`typescript/`). **`agda/` is reference only** — never edited, to be deleted.

## The point of this repo (Anthony)

The point of this repo is to be able to write proofs about actual executable programs written with Observable.

There will always be gaps, because IO is non deterministic. That's why it's important to share as much code as possible between the pure operational semantics (PureObservable) and the io operational semantics (Observable). This shared engine is called AbstractObservable.

A denotation is much easier to write proofs with than operational semantics - it's able to look at all emissions at once, rather than one at a time, and proofs written over top of it are compositional. The MonotonicList is this clairvoyant data structure.

The point of "adequacy" is to link these two worlds, and give us what we want - simple, compositional proofs that have meaning on the IO side - the "real world" that can actually be executed.

The Obs tree represents a minimal list of primitive operators that more complex operators can be built on top of. It's useful for proofs. It has three interpretations - denotational, pure-operational and io-operational. They all share a tree to facilitate this central idea.

As we try to prove adequacy, it's important that we be able to change the implementations of MonotonicList and AbstractObservable, in order to make our job easier. But we always want to preserve four things - compositionality of the denotation, clairvoyance of MonotonicList, as much shared by PureObservable and Observable as possible, and all of these semantics must match the behavior of real rxjs exactly.

## This file

- **File of record for every directive.** Ruling, standing rule, correction, "from now on" — here, in the section it belongs to, same commit. Not recorded until it is in this file; don't answer "noted" and carry it in context only.
- **Never the auto-memory directory** (`~/.claude/projects/…/memory/`) or any other out-of-repo note. Outside the repo = no gate, no grep, invisible to every worker.
- **Ask before changing this file (Anthony).** Draft the wording, show it, land it on his yes. An agent's own inference installed as law propagates further than any code change.
- **Rules here; mechanics in `docs/`** (one file per tool, indexed by `docs/README.md`). Split by KIND, not length. This file carries only what must be obeyed *prophylactically* — before you'd have reason to open a doc.
- **Fragments over paragraphs; omit rather than explain the omission (Anthony).** Every word here is paid on every turn.
- **Rules, not citations.** State the *shape* of a trap, not a name that gets discharged next week. Specific instances live in source headers. Exceptions: the load-bearing documents and commands (this file, PROOF-STATE.md, `docs/`, `make` targets, `agda-impl`) — vocabulary, not instances.
- **No calendar dates, including on a ruling (Anthony).** The name alone makes it unarguable; the timestamp does nothing. Conflicting rulings get MERGED, not ordered by date.
- **No line numbers, here or in a source comment.** A stale name fails a grep loudly; a stale line number resolves, points at unrelated code, and is believed.
- `make roadmap-check` enforces dates on this file and `docs/`; `make comments-check` on `agda-impl`. A date is a build failure.
- **Edit a single file with `Edit`, not `sed`/python heredoc (Anthony).** Auto mode's Bash preference does not extend to editing. Carve-out: a genuinely multi-hunk patch, with `assert old in s` per hunk, written once at the end.

## THE GATE — `make gate`

Cheap textual checks run FIRST, then `make agda` checks `agda-impl/Main.agda`. **Run it rather than trusting a memo, including this one.**

Every `*-selftest` proves its checker still fires; they are not findings, they are the reason a green check means something.

| Target | What it will not let you do | Mechanics |
| --- | --- | --- |
| `wiring-gate` | a definition/postulate/module with no route to Main; a `⊤`-typed postulate; a bare `open import` in Main. A name PASSED to a postulate earns no credit — that is "a postulate must be a leaf" | [docs/wiring.md](docs/wiring.md) |
| `unsafe-check` | `TERMINATING` / `NO_POSITIVITY_CHECK` / `REWRITE` / `--type-in-type` on the proof path. The build is not `--safe`, so this is the only thing stopping a soundness hole | [docs/unsafe-check.md](docs/unsafe-check.md) |
| `dup-check` | two declarations proving one fact, up to binder spelling and type synonyms | [docs/find.md](docs/find.md) |
| `imports-check` | an unused import, or an unused name in a surviving clause | [docs/imports-check.md](docs/imports-check.md) |
| `roadmap-check` | a live postulate in no group or in two; a group member naming nothing live (pruned — deleting a postulate is free, Anthony); a group without `Members:`; a tier subsection other than its ledger; over a prose budget; a date | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `comments-check` | a date, a historical marker or a LINE NUMBER in `agda-impl`; evidence not last and in order; a DOUBLED marker (`-- -- RECOVERY:`); a `REFUTED`/`RECOVERY` that doesn't resolve. `DEAD ROUTE` is unvalidated — it names nothing | [docs/comments-check.md](docs/comments-check.md) |
| `agda` | anything that does not typecheck from Main — **a warning is a failure** (`-W error`, exit 42) | [docs/agda-build.md](docs/agda-build.md) |

Also: `make imports-fix`, `make postulates` (the complete remaining-work ledger, by name), `make find`, `make find-prose`.

## Autonomy

Standing approval for any change — impl edits, protocol changes, new operators, refactors, experiments. Don't ask; go. Throw a lot at the wall, keep what passes QuickCheck/oracle, revert what doesn't.

**The `Obs` tree (`Tree.agda`) is FIXED, and the engine is not (Anthony).** Its formers are not the batchSimultaneous spec, so the standing approval above reads as licensing a new one — it does not. Engine internals are free: the kernels, the runtimes, the relation, whatever makes it work and provable. A change that needs a new `Obs` former, or re-types an existing one, is a question instead.

**The stop conditions are exhaustive — nothing else is one (Anthony: "never stop working until you hit a stop condition").** Both are questions only Anthony can answer:

- **The semantics must move** — the denotation disagrees with real rxjs in a way that is not a bug in either, or the batchSimultaneous spec's statement needs restating. A question, never a patch.
- **The impossibility pair** — two programs whose primitives produce byte-identical emit streams (same provenances, init/close, values, order) but that genuinely batch differently in real rxjs. **STOP and tell Anthony; do not act on it.** Not the same as "the batchSimultaneous impl disagrees with the batchSimultaneous spec", which is just a bug to fix in the impl.

## The goal

Every PROOF-STATE.md tier discharged: no postulates, everything typechecks. "Passes almost all seeds" is a waypoint, not the line. One counterexample in 500 means the theorem is false.

## Delegation — the design session directs, Sonnet workers grind

- **Workers run Sonnet 4.6, and `model: "sonnet"` does NOT get you there** — that alias resolves to Sonnet 5 here. Both levers apply only at session start, so a running session cannot change or verify its workers' model; say so plainly. → [docs/delegation.md](docs/delegation.md)
- **Workers never babysit long builds.** Hand `make gate` back to the design session.
- **A worker must kill any detached build before reporting**, and say nothing is running. Agda doesn't lock interfaces — two processes on one `.agdai` is a corrupt cache or a spurious failure.
- **Delegation has a FIXED context cost — amortise it or do it yourself (Anthony).** Delegate on BREADTH (several independent items, concurrently), REPETITION (one context, many similar obligations), or NARROWNESS (a small nameable slice). **Keep DEPTH:** one hard thing in a file already loaded is cheaper to do than to delegate.
- **The tell, and it is reliable: if writing the directive required you to do the analysis, you have already done the expensive part.**
- Parallel workers authorized; Agda builds one at a time.
- **Directives carry the law** — every worker prompt restates the rules it needs.
- Workers don't commit. Land green work via a PR, never a direct push to main — ask first.
- **Stage explicitly while a worker holds a file — never `git add -A` (Anthony).**
- **Run continuously** (Anthony: "continue and continue, don't stop for context window or usage credits"). Review, merge, launch the next.

## Agda builds

- **`make gate` is the merge gate, run in reconciliation:** `gate-cheap`, then `make agda` (`agda-impl/Main.agda`).
- **The harness never runs locally — only in CI, in the background (Anthony).** Bug cache, oracle, every `quickcheck/` binary (placing, ghosts, exact, hand, spin): never built or run in a session, so it never blocks real work. Checked by GHC and the FFI — never a proof's dependency.
- **A warning is a build failure.** Every invocation goes through the Makefile's `AGDA` (carries `-W error`). Never call bare `agda` in the Makefile. Never silence a warning to get green — a warning you believe is wrong is a finding. → [docs/agda-build.md](docs/agda-build.md)
- **Two commands: `make bg T=<target>` as a BACKGROUND tool call, then `make bg-check T=<target>`.** `bg` blocks, logs, appends `EXIT=<code>`. `bg-check` reports GREEN / RED-with-tail / STILL-RUNNING. `bg-wait` is for a human. A `sleep N; tail` or `until` loop is the apparatus re-implemented worse. `make bg` always exits non-zero by design, so **a completion notification is never a result — `bg-check` is.**
- **"Detached" means the Bash tool's background flag, never shell syntax (Anthony).** Type the command bare. No `&` (backgrounds a wrapper the harness already manages), no `>/dev/null 2>&1` (throws away WHERE the log is), **and never a pipe — a pipeline exits with the LAST command's status, so `make gate | tail` reports the tail's success over a RED build.** A foreground call is capped at 600 s and a build that outruns it is KILLED. **One build at a time.** → [docs/bg.md](docs/bg.md)
- **The Bash tool's cwd persists between calls — pin it.** Absolute paths; never rely on a previous `cd`.
- `touch` does NOT dirty a module — invalidation is by CONTENT.

## Where code goes

- **All new proof code in `agda-impl`**, where reachability, the ⊤-postulate check and the claim graph see it from minute one. That is what makes "did we already prove this?" a grep.
- The failure prevented is being UNCLAIMED, not being outside `src`. Work no claim root reaches is what parks itself for months and gets re-derived.

### Module granularity

- **Cut at mutual-SCC boundaries.** A mutual block is an indivisible checking unit. **Never restructure genuine mutuality to shrink a module** — proof shape wins over check time.
- **Over 1000 lines is too long (Anthony).** `make split` cuts one and retargets its consumers → [docs/split.md](docs/split.md).
- **A new fact goes in the SHALLOWEST module reaching its consumers, not the deepest that could host it (Anthony).** A four-line lemma near the bottom invalidates that module's whole cone. Check the cone before placing it. Does not contradict `dup-check`'s "move the fact DOWN", which is about a fact that already exists twice.

## Agda traps

Each cost real time at least once, and they share a shape: **Agda reports them against the WRONG thing.** Before reasoning from an Agda error, check whether it is one → [docs/agda-traps.md](docs/agda-traps.md).

- "X is not a constructor of T" for something you meant as a variable → grep for `X :` before touching the proof.
- An implicit used inside an `all`-predicate lambda is a fresh unsolved meta per element → bind it on the clause's left-hand side (`{e = e}`).

## Work from the outside in

Datatypes, primitives and end goals first; link with postulates; top-line results stated and typechecking *in terms of postulates*; only then chip away, one at a time.

- **A Σ-receipt has content only through its witness.** If every conjunct is upward-closed in the witness, the statement is vacuously satisfiable — check BEFORE grinding. Pin the witness to the one the consumers bound, or put the bound in as a conjunct. A face of this development was machine-refuted as vacuous by exactly this shape.
- **Recursively: never prove pieces before their assembly exists.** State the assembly with the pieces as postulates, make it typecheck, then prove pieces starting with the MOST UNCERTAIN. Pieces proven ahead of their assembly are speculative inventory, and their sunk cost biases the design toward keeping them.

## SEARCH FIRST — assume it already exists

Treat "I need a lemma saying X" as a SEARCH task until a search has failed. The cost is asymmetric: a search costs seconds; skipping it costs whatever you build instead, which is usually *weaker* than what was there.

```
make find Q='≤ slotsSize'     every STATEMENT whose type mentions it
make find-prose Q='...'       findings, which are prose by construction
```

- **Run `make find` before you state a postulate or write a lemma.** It walks all of `agda-impl` and takes no narrowing argument — which is the point: a hand-rolled `grep` was FOLLOWED and still failed, scoped to two arguments instead of the tree.
- **Run `make find-prose` before starting a writing phase.** It answers *has anyone already been here* — dead routes, coverage boundaries, rulings, measured traps — none of which `make find` can see. Returns the BLOCK. → [docs/find-prose.md](docs/find-prose.md)
- **Search the CONCLUSION's shape, not the name you imagine.** Names here are idiosyncratic. A miss is weak evidence; two misses on different phrasings is strong. **Read the SIGNATURE, never the header prose** — a header saying a route is dead is a claim about an attempt.
- **`make dup-check`: a finding is two SITES, not two names.** Agda's `ClashingDefinition` says nothing when either copy is `private`. **When it fires, MOVE THE FACT DOWN — do not pick a winner**; deleting one copy at random re-creates it later. Keep ONE naming convention per class of fact.
- **This does not license citing something you have not opened.** Find it, read its actual type, confirm the indices line up.

## Keep the repo lean

Every definition used somewhere; only the top-level exports are exempt. No back-compat shims, nothing "stored for reference", no legacy, no deprecated. **Don't be afraid to throw out code or documentation** — git history is the archive.

### DELETION

`make wiring` is trustworthy, so a name it reports is a finding to act on. **Deciding is yours, and asking is the failure mode (Anthony: "let's delete it if it's not used? That seems obvious to me").** Every rule below names something to VERIFY, never a reason to escalate.

- **"No consumer today" and "no consumer ever" are different questions.** A lemma stated AFTER its own specialisation is orphaned by placement and wires in one line. **Prefer wiring to deleting whenever a plausible consumer is nameable.**
- **The commit message carries the finding** — write what the deleted thing established. If a NAMEABLE future consumer remains, add `-- RECOVERY: git show <sha> restores …` to the header of the thing that would consume it.
- **A superseded predecessor is deleted, always (Anthony)** — not wired, not parked, not kept until the successor is proven. It drags a whole support cone that every local check reads as wired, because a mutual cluster consumes itself. **But ESTABLISH that it is one first:** both clusters the first sweep reported turned out not to be. The question is not "does a successor exist" but **"does the successor prove everything the predecessor proves?"** — answered by diffing the two bodies' ARMS, not their statements.

## PROOF-STATE.md — the risk ledger (Anthony)

Per tier: a one-line description (≤150 chars), then a **ledger** of GROUPS. No rules in the file — they live here.

- **A group = postulates sharing one design issue:** an undecided invariant, or a fact suspected false. Block: the issue, what would settle it, then its member names. Every live postulate in exactly one group (`make roadmap-check`).
- **Ranked riskiest first, by judgement.** Untried outranks probed; refutations and dead routes raise risk. Re-rank freely.
- **A group's issue says only what is still open.** As the top group narrows, rewrite its issue and settle test smaller; findings go to source headers.
- **The only work is the top group of the lowest open tier.** Carve-out: answering a design question.
- Names, never numbers. No history — a settled group is deleted, git holds it. Research in source headers.

## Two phases, alternating (Anthony)

- **Writing.** Long, manic, caution to the wind: no Agda invocation at all, no gate. Commit and push WIP; red is expected. Grind everything relevant to the top group in full — leave a new postulate only if meaningfully separate from the group's issue, filed under its own group. Ends when the top group's risk is SETTLED either way: its suspect fact proven, or refuted and restated so the route is known.
- **Reconciliation.** All effort on green: `make gate`, and every law below paid (leaf, wiring, headers, comments, imports). No new proof work. The PR is merge-ready only after.
- **Laws are deferred in writing, never suspended** — whatever writing leaves, reconciliation pays.
- Workers in both phases. Agda builds one at a time.

### Dead routes

A refuted statement and a dead route are different findings. **When an attempt fails for a structural reason, add `-- DEAD ROUTE:` to the header of the postulate you were trying to discharge.** Say what was tried and **what structurally blocked it** — "tried X, didn't work" stops nobody.

- **A dead route is not a licence to weaken the statement.** Deleting a dead-route line requires the route shown WORKABLE, not merely untried again.

## The postulate count

**A rising postulate count is the mechanism working, not a regression** (Anthony: *"the relentless mindset of reducing those numbers is very harmful"*). One vague postulate split into six specific ones is PROGRESS. The only number that matters is whether the tiers are discharged.

- **Do NOT minimise the count, do NOT apologise for it**, do not describe an increase as a cost or a trade.
- **Do NOT weaken a statement to make it typecheck.** Postulate the full-strength statement and report the obstacle.

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

**A stop is a FINDING, not a discharge (Anthony).** The postulate STAYS in its group and the parent is still a parent until the body lands. A good finding is the most convincing thing there is to mistake for progress.

**Pass every lemma ETA-EXPANDED with explicit implicits** — `(λ {n} {Γ} → f {n} {Γ})` — or a statement that reduces away its own implicit gives `Unsolved metas`. Other mechanics: [docs/wiring.md](docs/wiring.md).

**Two shapes that are almost always wrong — check every new postulate for both.** A conclusion needing information in NONE of its hypotheses; and a Σ-statement upward-closed in its witness. These are refutation targets, not `SUSPECT:` notes.

**For the first shape, suspect a MISPLACED CALL before a missing lemma.** Often nothing is unproven — the statement is being made at the wrong INDEX and the caller is what is misplaced. **Tell: the gap is a fixed small offset (one level, one frame, one `suc`)** rather than a missing fact about the domain. The check is cheap: find the same operation where it is already PROVEN and **diff the ARGUMENTS, not the statements.** Which families mirror which is recorded in the source headers, never in a list here. Two postulates fell to moving the call, with no new mathematics. **But a mirrored counterpart is a property some parts happen to have** — don't force the analogy.

**Adding a hypothesis is a RESTATEMENT and needs a restatement's justification.** `A → B` is weaker than `B`, and a hypothesis is invisible to the ledger where a postulate greps, gets counted and sits in a PROOF-STATE group. **The one sufficient justification is that the unconditional form has been REFUTED.** **"The call site happens to supply it" is NOT a reason** — today's call sites are an artifact of today's assembly.

## CODE BEATS PROSE (Anthony)

**A finding written in English that could have been written in Agda is not done — it is deferred.** If you have just worked out that A follows from B, the deliverable is the assembly, not a header paragraph saying so.

**The tell:** you write "X could be implemented in terms of Y" / "this reduces to Z" / "the route is …", and then you commit. **That sentence is a work order addressed to you, right now.** Carry it out, or say plainly why you cannot and postulate the residue at full strength.

An assembly is CHECKED, greppable and counted; a paragraph is checked by nobody, ages silently, and gets re-derived. **Corollary for headers: the moment a header explains a derivation that would typecheck, move it into the derivation.**

**NEVER WRITE CODE IN A COMMENT (Anthony).** Not a body, not a signature, not a "here is the lemma we need" block. Not checked, not counted, and it *looks* discharged. The excuse that produces it every time is the wiring law — the piece typechecks but its consumer is still a postulate. **The right repair is to convert the consumer into a real body over a smaller leaf**, however thin. If it genuinely cannot be split yet, say in one sentence what is owed and let git hold the text.

## HEADER SHAPE (Anthony)

**Explanation first, then evidence — `REFUTED`/`DEAD ROUTE`, then `RECOVERY` — evidence LAST.** That is what gives a long header landmarks. A marker is a **LEDGER ENTRY**: to mention a refutation in passing, name its module in backticks rather than opening a section mid-paragraph.

**A marker that names something must name something that EXISTS (Anthony).** Write the reference BACKTICKED or DOTTED — English is full of words this tree declares.

- **`DEAD ROUTE:` is unvalidated by construction** — it records that a *way of proving* cannot work, and there is no object to resolve. The section to reach for when a finding is real but names nothing.

**Sections are optional when absent and validated when present — never mandatory.**

**The repair for an over-budget block is usually to SPLIT it, not to cut it.** A block is separated by a genuinely blank line, so the ceiling caps ONE unstructured explanation. An essay holding ten findings becomes ten blocks and nothing is lost. Reach for the knife only when a block holds ONE finding and still runs long. Worked instance: a 154-line wall became ten skimmable blocks with no prose deleted.

**Only the EXPLANATION is charged (Anthony)** — evidence sections and `git show` pointers are free. Budgeting the destination too would mean a finding with nowhere to go gets DELETED. The budget is the measured p99: its job is to declare a block **over-explained**, not to trim writing.

**Say it once: the explanation does not narrate the ledger below it (Anthony: "no redundancy in documentation").** The prose copy ages while the section stays live, which is how a block ends up carrying a refutation it no longer has. `make comments-check` fires on the narrow half; the rule is wider than the check.

**A header records what is true of the STATEMENT, never what happened to the DECLARATION (Anthony).** "Was restated", "was split", "converted from a `-core`", "measured at 400 s" are git's subject. **The superseded framing goes too** — a paragraph kept "so the dead candidates are not retried" is a dead route, which is one `DEAD ROUTE` line.

## The wiring law: NEVER LEAVE A PROOF HANGING (Anthony)

**Nothing may exist without a consumer that traces to a top-level theorem.**

- **Every GAP is a postulate with a real signature** — never a comment, never a missing statement. Then **`make postulates`** IS the complete remaining-work ledger. (Do NOT substitute `grep '^postulate'`: that finds block HEADERS, a third of the count.)
- **Every definition and postulate is consumed, in code, transitively by a top-level theorem.** Then "did we forget something?" is answered by the typechecker.

**The workflow:** before proving a lemma, extend the assembly that will consume it — postulating whatever else that assembly needs — and land both in the SAME commit. **If the assembly needs a different signature to accept the piece, change the signature first.**

**A postulate must ASSERT something.** Wiring an unreachable definition in with a vacuous bridge is worse than leaving it unreachable. Two traps live here: ⊤-typed postulates whose real claim sits in a trailing comment, and Σ-statements upward-closed in their witness.

**Forbidden states.** An **unreachable definition** — a missing wire or dead weight, both findings, and leaving it undecided is not an option. A **lying comment** — prose describing an intent the code does not encode.

**MAIN IS THE TOP-LINE PROOF (Anthony).** `agda-impl/Main.agda` is the root of the consumption graph and the deletion exemption. **(1) Whatever Main imports sticks around. (2) Main names individual definitions — NEVER a bare `open import`. (3) Main is never touched without Anthony's explicit approval** — draft and ask. `make wiring` reads Main's `using` clauses, so a filename never earns an exemption.

Main also defines the build's COVERAGE — **`make agda` IS the claim graph**, and anything outside it is not being checked. **Never close a coverage gap by re-adding a bulk import to Main.**

**Why this is law:** unwired proven work costs more than refutations. A proof nobody calls sits inert while the work it would have done is re-derived inline, so the same thing is proven twice; and a tower built without its consumer is a tower whose shape was never checked.

## TypeScript style

As purely functional as possible: no mutable state, no direct `.subscribe()`. Delegate IO/statefulness to rxjs operators like `scan`. Two reasons — cleanliness, and keeping the primitives and `batchSimultaneous` in near-direct correspondence with the Agda.

## The change workflow — engine IMPLEMENTATION only

Not for proof work, tooling or documentation.

1. **Agda first**, before touching TypeScript.
2. **QuickCheck** — `quickcheck.Quickcheck`: the pure runtime against the denotation on drawn programs.
3. **Port to TypeScript**, only once QuickCheck passes.
4. **Oracle** — all three Agda engines against real rxjs. Every divergence becomes a bug-cache row.
5. **Formal verification last**, in phases, committing in-between results, until there are no gaps.

**Resolving ambiguity:** naive plain rxjs — actually run the example and see. If that doesn't settle it, surface the question with a TypeScript rxjs example that **avoids the `*All()` higher-order operators where possible**.

**Batching never reorders (Anthony).** Values leave in exactly the order plain rxjs delivers them, and later in the array means later in time. For `1, 5, 3, 7, 0`: `[1,5] [3] [7,0]` is legal, and so are `[1] [5] [3,7,0]` and `[1,5,3,7,0]`. `[1,5,3,0,7]` never is.

**Every example takes one form (Anthony):** input observables labelled up front, a combination of primitive operators, `.subscribe()` at the very end, and comments underneath showing what emits.

**Authority ordering (Anthony, most → least): Anthony's discretion, then real rxjs, then the Agda denotation. There is no fourth source.** Nothing under `agda/` (its READMEs included) is an authority.

**The Agda impl MUST mirror the TS impl.** If the Agda relies on something TS cannot do, the correspondence is void. When in doubt about portability, **port it to TS and run the oracle before building on it.**

## Bug cache

Capture an implementation bug immediately as a **row of the corpus** in `agda-impl/quickcheck/Bug-Cache.agda` — a label and a program, not a claim about one. Dead simple: a wall of little entries, no fancy names, no abstraction. **Append-only** — it is the list of tricky cases already overcome — and the invariant is **`make bug-cache` green ⟺ no known counterexample remains**.

The run happens in a BINARY, not the typechecker, so an append-only corpus never charges the gate. **It runs in its own CI job, not in `make gate`.** A green row is checked by the GHC backend and the FFI, so **no proof may ever depend on the cache**. → [docs/bug-cache.md](docs/bug-cache.md)
