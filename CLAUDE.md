# Working methodology

This repo pairs an **Agda model** (`agda/`) with a **TypeScript implementation** (`typescript/`).
Agda's spec is gospel; TS conforms to it.

**THIS FILE IS THE FILE OF RECORD FOR EVERY AGENT DIRECTIVE — DO NOT USE THE
AUTO-MEMORY DIRECTORY (Anthony).** A ruling, a standing rule, a correction, a "from
now on" — it goes HERE, in the section it belongs to, in the commit that establishes
it. The per-project memory directory under `~/.claude/projects/…/memory/` is
**vestigial**: it was emptied deliberately and nothing is to be written back into it.
Neither is any other out-of-repo note file — this is the same law as "There is no
second roadmap" in PROOF-STATE.md, one level up, and for the same reason.

**Why, and it is not a filing preference.** A memory file is outside the repo, so no
gate, no `grep` and no reviewer can see it rot, and it is invisible to every worker —
the sessions that most need a directive are the ones that never receive it. At
deletion, **three of the six memory files were flatly wrong about the repo**, each
having aged silently past a change that a tracked file would have been updated
alongside: they named a top-authority document that no longer exists, they described a
hand-rolled FFI constraint since replaced by plain stdlib, and they listed as a
canonical primitive something the semantics deliberately handle another way. None was
a careless entry — each was true when written, which is the point.

The corollary is the part that costs something: **a directive is not recorded until it
is in this file.** Do not answer "noted" and carry the rule only in context — write it
down, in the same turn.

**AND ASK BEFORE YOU CHANGE THIS FILE (Anthony).** Writing a directive down in the
same turn is the obligation above; deciding what the directive SAYS is not yours. A
rule here is read by every session and obeyed prophylactically, so an agent's own
inference installed as law propagates further than any code change and nothing
downstream ever questions it. Draft the wording, show it, and land it once Anthony
has said yes — the same rule Main already carries, for the same reason.

**THIS FILE HOLDS RULES; `docs/` HOLDS MECHANICS (Anthony).** Every byte here is read
by every session, so this file carries only what must be obeyed **prophylactically** —
before you have any reason to open a doc. How a tool works, what its flags mean, which
trap cost a day, what a measurement showed: that goes in `docs/`, one file per tool,
indexed by `docs/README.md`. The split is by KIND, not by length. When a rule here has
a tool behind it, the rule states the shape of the trap and names the doc; the doc
never restates the rule.

**AND WRITE RULES, NOT CITATIONS: THIS FILE AVOIDS POINTING AT CODE (Anthony).** A
rule here outlives every file path, definition name, and line number it might mention,
so a direct code reference is a decay clock attached to a rule that would otherwise
stay true. State the *shape* of the trap or the ruling and let the reader grep — "a
two-letter constructor of one of this development's own small relations" ages better
than a name that gets discharged next week, and it teaches the same lesson. Where a
specific instance really is the content, its home is the source header, which moves
when the code moves; that is the locality argument the `-- DEAD ROUTE` and `-- PROBED`
conventions already rest on. The standing exceptions are the load-bearing *documents*
and *commands* — this file, PROOF-STATE.md, EVIDENCE.md,
`typecheck-performance-numbers.md`, `docs/`, `make` targets and
the directories the laws are stated over (`agda/src`, `agda/evidence`) — which are the
vocabulary the rules are written in rather than instances they cite.

**AND NO CALENDAR DATES, INCLUDING ON A RULING (Anthony).** An attribution's job is to
say a rule is Anthony's and not an agent's inference — that is what makes it
unarguable, and the name alone does all of it. The timestamp beside it does nothing: a
ruling in the file of record is in force whatever its age, which is what "file of
record" means, and two rulings that genuinely conflict get MERGED rather than ordered
by date. Same for the evidence under a rule — the fact that three of four workers died
polling a build is the argument; when it happened is decoration, and a timing figure
has one home and this is not it.

**AND THE SAME GOES FOR A SOURCE COMMENT, WHICH USED TO BE THE ONE CARVE-OUT
(Anthony).** This file argued that a `-- PROBED` or `-- DEAD ROUTE` receipt
is only as good as the code being unmoved since, so its age was a signal about the
evidence. That reasoning was wrong twice over. A receipt's content is its **coverage
statement** — which shapes were reached and which were not — and coverage is
*re-runnable*, so the date adds nothing a reader can act on; and nobody has ever
checked one, which makes it a stale line number in prose form, the exact failure the
rule directly below this one exists for.

What the date actually buys is **enforcement of the history ban**, and it buys it
cheaply. Purely historical prose arrives WITH a timestamp attached, because the writer
knows they are recording a change rather than a fact — "corrected `<date>`", "ANSWERED
`<date>`", "moved here from the walk face when …". Measured on the sweep that set this
rule, the marker WORD does not separate history from fact and the date does: `SEALED
<date>. This was a POSTULATE …` is history, `SEALED, and this is not optional: …` is
the load-bearing reason the seal may not come off, and every dated instance of the
ambiguous markers was historical while every undated one was durable. So a date ban is
the cheapest machine-visible proxy for "delete purely historical information", which is
the standing directive it serves.

**`make roadmap-check` ENFORCES THIS on this file and on `docs/`, and `make
comments-check` on every comment in `agda/src` and `agda/evidence`; a date is a build
failure** — since a rule stated in a file nobody checks is the thing this whole section
is about.

**LINE NUMBERS ARE THE WORST CASE AND THERE IS NO EXCEPTION FOR THEM, HERE OR IN A
SOURCE COMMENT.** A stale name at least fails a `grep` loudly; a stale line number
resolves, points at unrelated code, and is believed. Measured on the sweep that recorded
this rule: of the citations this file carried, two named things that had since been
deleted, one named a duplicate the compiler had already removed, one enumerated a set of
`make` targets that had since grown, and every line number in the file was wrong. Not
one of the rules they were attached to had stopped being true — which is the argument in
a sentence.

**AND `agda/src` WAS NO BETTER, WHICH IS WHY `make comments-check` NOW POLICES IT.** Of
the `file:line` citations in the two trees, TEN pointed past the end of the file they
named — a module had been split — and the in-range ones had drifted onto continuation
lines, one being cited eight times. Every single site already named the declaration in
backticks beside the number, so deleting 141 of them cost nothing: the name is the part
that works, and `make find` takes names.

**EDIT A SINGLE FILE WITH THE `Edit` TOOL, NOT WITH `sed` OR A PYTHON HEREDOC
(Anthony).** Auto mode says to prefer Bash for file work; that preference does not
extend to editing, and reaching for a shell rewrite of one file costs tokens and a
round trip to do what one tool call does directly. The carve-out is a genuinely
multi-hunk patch, where an `assert old in s` per hunk fails loudly on a stale anchor
and the file is written once at the end — never half-applied.

## THE GATE — `make gate`, and what each check will not let you do

Cheap checks run FIRST, deliberately: an unreachable name or an unsafe pragma is
decidable in seconds by grep while the full gate costs many minutes, so there is no
reason to spend those minutes only to fail on something a textual pass already knew.
**Run it rather than trusting a memo — including this one.**

| Target | What it enforces | Mechanics |
| --- | --- | --- |
| `wiring-selftest` | the wiring checker still fires — R2 fires on nothing in `src` today, so without a fixture it would rot untested | [docs/wiring.md](docs/wiring.md) |
| `wiring-gate` | every definition, postulate and module has a route to Main; no `⊤`-typed postulate; no bare `open import` in Main. A name PASSED to a postulate gets no credit, which is how "a postulate must be a leaf" is enforced | [docs/wiring.md](docs/wiring.md) |
| `wiring-refuted` | same law over `agda/evidence/refuted`, rooted at `Refuted.Main` — every witness is claimed | [docs/wiring.md](docs/wiring.md), EVIDENCE.md |
| `wiring-probed` | same law over `agda/evidence/probed`, rooted at `Probed.Main` — this is what replaced the probes' old self-granted reachability exemptions | [docs/evidence.md](docs/evidence.md), EVIDENCE.md |
| `evidence-selftest` | every evidence law still fires, and the shapes that are LEGAL stay quiet | [docs/evidence.md](docs/evidence.md) |
| `evidence-check` | E1: no `src` file imports the evidence trees — the `.agda-lib` layout already makes such an import UNRESOLVABLE, so this is the fast legible failure on top of the mechanism. E2: every probe declares a `-- TARGET:` and every target is a LIVE postulate, because a probe whose target is discharged stays green forever while being evidence for nothing. E3: the RECEIPT is held to the same discipline, since it outlives the probe and is usually the only trace left — it sits above a declaration, whose statement must still be a POSTULATE, so DISCHARGING one fails the gate until the receipt above it has been re-read and DELETED. A receipt has exactly one tense, and no dated variant of the marker: the theorem says more than the probe ever did, so on discharge the coverage claim is superseded rather than historicised, and whatever harness is worth keeping becomes a `RECOVERY:` pointer. Every NEAR MISS is a finding too, because a receipt a strict pattern walks past leaves the check reporting a tidy zero — which is what a requirement for a DATE in the marker did, silently, from the day its sibling check outlawed dates in source comments . E4 holds the HARNESS to the same expiry law, series by series, for a stronger reason than the probes have: nothing depends on a row and the gate never builds that tree. And the STATEMENT FINGERPRINT holds a receipt's rows to the statement they were taken against and not merely to the name: every `-- TARGET:` carries a hash of its target's type, and a target RESTATED under the same name is a build failure — the case the live-postulate check is blind to, since the name survives and the postulate is still live, so the probe goes on being green as evidence about text that is gone. The repair is never to restamp alone, which converts a false coverage claim into a certified one: re-run the rows against the statement as it now reads, or delete the probe. E6 splits the two products a probe can have and refuses a file claiming both — a receipt instantiates ONE statement and reports that it held, a FORK stands at a design choice between two candidate mechanisms and its product is a separation — because a receipt written from a file that also separates claims coverage the separating rows never bought; and a fork proves its separation in a TYPE whose apartness field is UNINHABITED when the candidates agree, so the marker decides only which law applies and Agda decides whether the claim is true. E7 closes the gap no comment convention could: a probe used to RESTATE its target's predicate by hand and pin THAT by `refl`, so a quietly weaker predicate stayed green and earned a receipt for a claim nobody had instantiated. Every target now carries at least one row whose type is the target APPLIED at the probe's own point — Agda generates it from the statement as it reads, so the probe chooses only the point and a restatement changes every row underneath. And the BODY may name NO POSTULATE, since ANY inhabitant would typecheck, the target handed back as its own proof included — and a row discharged out of a DIFFERENT postulate is evidence for one statement exactly as far as another is true. It is a LAUNDERING test and not a computation test, and the difference is what makes the rule satisfiable: a conclusion denominated in a family this tower SEALS for cost reduces at no point whatever, so a body held to a numeral could never be written against one at all, and a weakening through a PROVEN inequality is a stronger receipt than a numeral rather than a weaker one. And the head under the tie must be a declared target reached through the statement's own eliminators, because an arbitrary function applied to a postulate returns whatever type it likes and the tie is gone. E8 caps a live postulate's receipts at SEVEN, because past that the probes have stopped deciding anything: a probe AIMS a grind or REFUTES a statement, and a seventh receipt on one target has not told anyone something the sixth did not while the ledger row stays open — so what the evidence is then buying is more evidence to DELETE when the statement is discharged. Seven rather than three because a coverage LATTICE is legitimate, and rather than twelve because past seven the evidence has stopped converting into proof. The count is over `-- TARGET:` DECLARATIONS and not files, so a probe carrying three targets pays for three — and **the repair is to DISCHARGE the postulate or to DELETE the receipts that no longer earn their place, NEVER to merge probe files**, which satisfies a file count and changes nothing, the same laundering as trading a postulate for a hypothesis. A REFUTATION is uncapped, and that is not leniency: it kills a statement that is then GONE, so it cannot accumulate against a live row, and `make refuted` goes red the day `src` can no longer state it. A FORK is uncapped from the other side — it declares no target, and deciding between two mechanisms is the one job a single file does. And the cap is off a DISCHARGED target, whose receipts are E2's finding rather than a second one | [docs/evidence.md](docs/evidence.md), EVIDENCE.md |
| `unsafe-check` | no `TERMINATING` / `NO_POSITIVITY_CHECK` / `REWRITE` / `--type-in-type` etc. on the proof path. The build is not `--safe`, so this is the only thing stopping a soundness hole | [docs/unsafe-check.md](docs/unsafe-check.md) |
| `dup-selftest` | the duplicate checker still fires | [docs/find.md](docs/find.md) |
| `dup-check` | no two declarations proving the same fact, up to binder spelling and type synonyms | [docs/find.md](docs/find.md) |
| `imports-selftest` | the import checker still fires, in both directions | [docs/imports-check.md](docs/imports-check.md) |
| `imports-check` | **NO UNUSED IMPORT, AND NO UNUSED NAME IN A SURVIVING CLAUSE (Anthony: "no unused imports, either")** — an import is a module-graph EDGE, fixing what must be built BEFORE this file and what an edit to the imported module INVALIDATES, and Agda has no warning for a dead one so `-W error` cannot see it. `make imports-fix` deletes them, but never a **claim root**'s imports (one file per tree — they ARE the claim, so unused is the design) nor a **sole-route** edge, which is a wiring finding rather than dead weight. AND no import may put names in a file's SCOPE without naming them: a missing `using` list is a finding in every file, claim roots included (`using ()` and a qualified `import M as Q` are fine). AND **no `public` re-exports** — a name is imported from where it is DEFINED, so that `grep` and `make find` point at its real home. AND no `using` clause may ask a module of this tree for a name that module does not have — a definition MOVES, one consumer's clause is repaired and its sibling's is not, and Agda reports that only as a scope warning `-W error` promotes MANY MINUTES down the tower, one instance per build, naming the importer and not the name's new home. What makes the cheap check sound is the `public` ban directly above: with no re-exports, a module can only export what its own text mentions. AND every file DECLARES its own module name, matching its path: a missing header is not a syntax error, so Agda checks such a file as a target and then crashes every IMPORTER with an internal error naming neither end — and a dev check cannot see it, because it checks a generated copy carrying its own header. Every part of this buys LEGIBILITY, not time: `using` filters scope rather than the build, a re-export removes no edge since a ladder's name-level dependencies are genuine, and a clause with one live name holds its edge open however many dead names sit beside it — which is why the name-level half was once argued to be optional, and is the wrong measure. A list naming thirty things the file never touches is not a record of what the file depends on | [docs/imports-check.md](docs/imports-check.md) |
| `roadmap-selftest` | the roadmap checker still fires | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `roadmap-check` | PROOF-STATE is sorted riskiest-first, names every live postulate AND NOTHING ELSE in a row head, keeps rows AND TIER PREAMBLES within a character budget — the second because holding every row to a line and writing the finding into the section text above them satisfies the first exactly — carries no date, and neither does this file or `docs/`; opens every tier with a BIG PICTURE ROADMAP of exactly three legs, each within a prose budget several times a row's, because the legs are the schedule and the rows are only the ledger it is drawn from; and every classed row carries the DERIVED evidence field its postulates' headers dictate, which is why a field may be mandatory where the `TWIN:` section it summarises is not — a derived field cannot be filled with filler, so the blank is the product. `make roadmap-evidence` writes it; and no DIFFICULTY row stands on nothing, which is the same law the GRINDABLE half already carried | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `roadmap-moved-selftest` | the movement checker still fires, in both directions — and that a trailing-whitespace edit does NOT count as movement | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `roadmap-moved` | PROOF-STATE has CHANGED against HEAD. A LEG IS ONE COMMIT, so a commit that leaves the roadmap byte-identical has either finished a leg without retiring it or abandoned one without saying so. The check is deliberately dumb — did the file change — because what it defends is not resolvable by a machine: the checker above verifies a row's NAME, and nothing can verify that the plan a leg describes is still the plan | [docs/roadmap-check.md](docs/roadmap-check.md) |
| `comments-selftest` | every comment check still fires, and four precision properties still don't | [docs/comments-check.md](docs/comments-check.md) |
| `comments-check` | no comment in `agda/src` or `agda/evidence` carries a date, a historical marker or a LINE NUMBER — in any of `Module.agda:414`, the extensionless `Wet:514`, or the prose `line 1920`; a block's evidence sits LAST and in order; no marker is DOUBLED into the comment text (`-- -- RECOVERY:`), which is a marker every checker here reads as prose while a human reads it as a marker; every `TWIN`/`REFUTED`/`PROBED`/`RECOVERY` reference RESOLVES — a twin to a definition that is proven and not still a postulate, a spent probe to the sha holding it — while `DEAD ROUTE` is unvalidated because it names nothing; no explanation names the subject of a section the same block already carries, which is redundancy that DRIFTS rather than merely repeats; and the EXPLANATION — the prose before the first evidence marker, sha pointers free — is within a character budget. Charging explaining and not evidence is the whole design: this header is where the roadmap's own budget SENDS research, so a flat per-block ceiling would budget the destination and a finding with nowhere to go gets deleted rather than moved | [docs/comments-check.md](docs/comments-check.md) |
| the tower (inline in `gate-heavy`, no target of its own) | the tower typechecks. **A WARNING IS A FAILURE** (`-W error`, exit 42) | [docs/agda-build.md](docs/agda-build.md) |
| `refuted` | the refutations typecheck | EVIDENCE.md |
| `probed` | the probes typecheck | EVIDENCE.md |
| `bug-cache` | no known impl counterexample has regressed. `Unit-Test.agda` is off Main, so nothing else would notice it rotting | [docs/bug-cache.md](docs/bug-cache.md) |

Also `make imports-fix` (delete every dead import), `make postulates` (the complete remaining-work ledger, by name),
`make find` (search by the shape of a STATEMENT — see [docs/find.md](docs/find.md)),
`make strip-selftest`, `make agda-dev-selftest`.

## The Agda impl MUST mirror the TS impl

The Agda **implementation** (`agda/src/Implementation.agda`, as opposed to
`agda/src/Spec.agda`) exists to model
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
wins. Only pause to ask when a change would touch the **spec** (`agda/src/Spec.agda`),
or when the spec is genuinely ambiguous (then follow the ambiguity rule below).

**AND THE STOP CONDITIONS ARE AN EXHAUSTIVE LIST — NOTHING ELSE IS ONE (Anthony:
"never stop working until you hit a stop condition: the spec has to change, or the
proof is spiraling").** There are three, and all three are questions only Anthony can
answer:

- **The spec must move** — a question, and never a patch.
- **The proof is SPIRALLING** — the same region producing FALSITY across three
  successive subdivisions. That is the convergence test's own stop condition, defined
  with the test rather than restated here; it means the mechanism underneath is wrong,
  and a fourth subdivision is not the answer.
- **The impossibility pair** — two programs whose primitives produce byte-identical
  emit streams but that genuinely batch differently. Report it, do not act on it.

Everything else is worked through. Context compacting, a long session, a high spend, a
finished leg, a green gate, a good stopping point, a finding worth reporting — none of
these is a stop. A finding gets written down and the work continues past it; a leg that
finishes gets merged and the next one starts. **A STOP IS A FINDING, NOT A REST**, which
is the same law the postulate-assembly section states about bodies, arriving at the
session's own scheduling. Work the tier order from its lowest open tier upward, end to
end, taking that tier's BIG PICTURE ROADMAP leg by leg, and when a leg is genuinely
blocked take the next one rather than stopping on it — a blocked leg is a leg to report
and route around, not a stop condition.

**AND THE ORDER INSIDE A TURN IS ACT FIRST, REPORT SECOND (Anthony).** The stop
conditions are the three above, and none of them is "a good report is ready". But a
report is where a run actually stops, because a finished paragraph feels like a finished
unit of work in a way a half-applied edit does not — so the session writes up what it
just learned, and the action that finding implied is left as a sentence in the future
tense.

**A SENTENCE IN THE FUTURE TENSE ABOUT YOUR OWN NEXT STEP IS A WORK ORDER, AND ITS
DEADLINE IS THIS TURN.** "Next I will commit this", "the following row is the one to
pick up", "that wants one more sweep before it is written down" — each of those is
something to DO, and writing it instead of doing it converts a queued action into prose
that nothing executes. This is **CODE BEATS PROSE** arriving at the turn boundary rather
than at a header, and it is the same failure for the same reason: the insight is
genuinely worth having, and recording it leaves the tree in exactly the state it was in.

So: run the queued action, then report what it did. A report that ends by naming the
next action has not finished the turn — it has described it.

## Division of labor: the design session directs, Sonnet workers grind

The design-authority session delegates the bulk of the work — clause grinds, falsity
sweeps, build babysitting — to subagents, keeping design spend confined to rulings,
directives, and report review. Standing protocol, per Anthony:

- **Workers run on Sonnet 4.6, and `model: "sonnet"` does NOT get you there** — that
  alias resolves to Sonnet 5 on this provider. Two levers pin a version and **both apply
  only at session start**, so a running session cannot change or verify its workers'
  model; say so plainly rather than pretending otherwise.
  → [docs/delegation.md](docs/delegation.md)

- **WORKERS MUST NOT BABYSIT LONG BUILDS — the design session owns the gate.** Measured
  THREE of four workers died mid-task polling a build they had launched, burning their
  turn budget on "still waiting" and losing all their context; one had already written
  263 good lines that then needed rediscovering. A worker's job ends when its edits are
  made and cheaply verified: iterate with **`make agda-dev`**, land only dev-green
  bodies, hand the long `make gate` BACK to the design session, which can poll across
  turns without dying.

- **AND A WORKER MUST NOT LEAVE A DETACHED BUILD RUNNING WHEN IT REPORTS.** Agda does not
  lock interfaces, so a worker's "cache-warming" check racing the design session's gate
  has two processes writing the same `.agdai` — a corrupt cache or a spurious failure, in
  a run that costs many minutes to repeat. It is also pure waste: the gate rebuilds that
  module anyway. Kill it before reporting, and say in the report that nothing is still
  running. **This covers `make agda-dev` too**, which is the easy way to trip it: the dev
  loop and the gate deliberately share ONE interface cache.

- **DELEGATION HAS A FIXED CONTEXT COST — AMORTISE IT OR DO THE WORK YOURSELF
  (Anthony).** A fresh worker must rebuild the model from nothing: read the 2000-line
  module, chase the definitions, trace the statement. Measured twice at **~20 minutes and
  hundreds of thousands of tokens BEFORE ANY OUTPUT**, one of the two returning analysis
  with **zero edits**. That cost is roughly CONSTANT in the size of the task, so it is
  the whole question. Delegate only when it is amortised: **BREADTH** (several
  independent items, each paying the cost once, concurrently — wall-clock wins even when
  token-expensive); **REPETITION** (one context, many similar obligations — read once,
  grind N times); **NARROWNESS** (a small nameable slice rather than a module's whole
  design).

  **KEEP DEPTH: a single hard thing in a file the design session already has loaded is
  CHEAPER TO DO THAN TO DELEGATE**, because the session has already paid the cost and
  pays it again reviewing the result.

  **THE TELL, and it is reliable: if writing the directive required you to do the
  analysis, the analysis WAS the expensive part and you have already done it.** A prompt
  carrying an instantiation map, a list of expected residues, and a pre-warning about a
  trap is a prompt whose author could have typed the proof in the time spent describing
  it. Notice this BEFORE spawning, not after; both measured misfires had exactly this
  shape. Read-only fan-out is the standing exception — it is cheap, parallel, and its
  whole product is the reading.

- **Parallel workers are AUTHORIZED, and so is parallel Agda — up to a measured ceiling**
  (two heavyweight checks at once; cheap modules freely —
  [docs/typecheck-cost.md](docs/typecheck-cost.md)). **BUT THAT CEILING IS ABOUT
  HARDWARE, AND IT BUYS NOTHING WHERE THE TWO CHECKS SHARE AN INTERFACE CACHE — WHICH
  EVERY CHECK IN THIS REPO DOES.** Concurrent Agda over one cache does not merely
  contend for cores: each run invalidates what the other is depending on, so the
  cheaper one measures a REBUILDING CONE and reports it as its own cost. Measured on
  the module that is this tree's claim door, **a 140× misreading — over fifteen
  minutes without finishing, against six and a half seconds on a quiet machine** — and
  it did not resolve on a retry, because every retry raced something too. The
  rule the delegation section states over a WORKER's stray build is the same rule and
  binds the design session identically: **while a gate is live, run no other check —
  not a dev loop, not a "quick" one.** The concurrency worth having is READ-ONLY
  fan-out, which touches no cache at all. Beyond hardware:
  **never let two workers edit the same module** — a shared file is a write conflict, not
  a parallel task, so have workers return replacement text and let the design session
  apply it and own the single recheck; **read-only fan-out is unconditionally safe**, so
  split analysis, censuses and call-site traces as wide as the task allows; and **THE
  GATE MEASURES THE TREE, NOT THE WORKER**, so a worker's gate result is only meaningful
  for the files it committed and must be re-run as its LAST act before committing
  ([docs/delegation.md](docs/delegation.md)).

- **Directives carry the law.** Every worker prompt restates the standing rules it needs:
  spec is gospel; refute-before-grind; detached builds with EXIT= logs; report numbers
  plainly including failures; never extrapolate from shallow refutation rows; the
  impossibility-pair stop rule (report, don't act).
- **Workers commit and push per green task**, gate-green, in the repo's commit voice; and
  **never reach into another worker's lane to tidy a shared file**
  ([docs/delegation.md](docs/delegation.md)).
- **Land green work via a PR, never a direct push to main** — after each verified-green
  worker leg, open a PR from the working branch instead of pushing to main directly, and
  merge once GitHub Actions' gate run is green (see below). Standing for the current
  autonomous run; it does not extend to spec changes, which still require asking first.
- **Run continuously** — Anthony: "continue and continue, don't stop for context window
  or usage credits." When a worker leg finishes, review it, merge it, launch the next.
  The stop conditions are the three in **Autonomy** and there are no others; this
  bullet is that rule applied to a delegated leg rather than a second version of it.

## Running long Agda builds — the rules; mechanics in `docs/`

**`make gate` IS THE MERGE GATE, AND IT ROUTES — TYPE IT AND LET IT DECIDE.** It takes
the light path when the changed set is light-checkable and the full tower when it is not,
and it prints which and why. Choosing the expensive path by habit is how the cheap
checks — the ones that fail in seconds — get skipped in favour of many minutes. The heavy
path takes many minutes and the Bash tool's ceiling is 600 s per foreground call, so
iterate with **`make agda-dev`** (seconds). **DO NOT RUN `make gate` YOURSELF TO MERGE —
open a PR and let the `Gate` GitHub Actions workflow run it**, and subscribe to the PR
with `subscribe_pr_activity` to learn when the run completes rather than polling. Timings:
`typecheck-performance-numbers.md`.

**AND THE CARVE-OUT IS TERMINATION, NOT ANY NAMEABLE REASON (Anthony).** Forcing
`make gate-heavy` is for a change that could have broken the TERMINATION CHECK — the one
property the dev loop cannot see, since it stubs mutual blocks and the real mutual
recursion is where the induction lives. A module with no multi-member block is emitted
VERBATIM, so its dev check already covers termination and a heavy gate buys nothing
there. Everything else is the router's call, a light path you expect to fail included:
red costs minutes and says why. **AND A LIGHT PATH THAT FAILED ONCE IS NOT A REASON TO
FORCE THE NEXT ONE** — carrying the verdict forward untested is how two heavy gates came
to run back to back for one blocker, and the usual cause of such a blocker is a cache the
first heavy gate has since made coherent.

- **A WARNING IS A BUILD FAILURE.** Every Agda invocation goes through the Makefile's
  `AGDA` variable, which carries `-W error` (Agda exits 42). Never call bare `agda` in
  the Makefile. Never silence a warning to get green — fix the cause; a warning you
  believe is wrong is a finding, not a filter. The flag must be IDENTICAL in the Makefile
  and in the dev loop's `agda_flags()`, changed in the SAME commit.
  → [docs/agda-build.md](docs/agda-build.md)
- **AGDA NEVER CHECKS `agda/src`. It checks the comment-stripped mirror, and that is why
  a comment edit is free.** **Never run `agda` against `agda/src` directly** — that
  builds a second interface cache and every alternation invalidates the other's cone.
  → [docs/agda-build.md](docs/agda-build.md)
- **LAUNCH EVERY LONG BUILD WITH `make bg T=<target>`, AS A BACKGROUND TOOL CALL, AND
  READ THE VERDICT WITH `make bg-check T=<target>`. THOSE ARE THE TWO COMMANDS A
  SESSION NEEDS.** What each of the three does, since none of them is guessable:
  **`make bg T=<target>`** runs the build, writes everything to a log, and appends a
  terminal `EXIT=<code>` line — it BLOCKS until the build is done, which is why it is
  launched in the background; **`make bg-check T=<target>`** reads that log and reports
  GREEN / RED-with-the-failing-tail / STILL-RUNNING; **`make bg-wait T=<target>`**
  blocks until the log is terminal and then exits 0 GREEN / non-zero RED — it is for a
  human at a terminal, or for a caller that genuinely has to block, and a session
  driving `make bg` in the background does not need it, because the completion
  notification IS the wait. **One background call per build, and never a second while
  one is live.** `bg-check` is never LOOPED: make collapses its exit status into its own
  exit 2, so still-running and failed read as the same number. **A `sleep N; tail` loop, an
  `until` loop, or a `pgrep` for the waiter, is the whole apparatus re-implemented
  worse** — a turn burnt per tick, reading a log buffered until the run ends, unable to tell a live build
  from a dead one. **Never hand-roll the wrapper either** — the obvious
  `(cmd > log; echo EXIT=$?)` exits with `echo`'s status and reports every build green.
  `make bg` always exits non-zero by design, so **a completion notification is never a
  result** — `bg-check` is.
  **AND "DETACHED" MEANS THE BASH TOOL'S OWN BACKGROUND FLAG, NEVER SHELL SYNTAX
  (Anthony).** Launch `make bg` as a BACKGROUND tool call and type the command
  itself bare — no `&`, no redirect, NO PIPE. The flag is what gives the run no
  time limit and a completion notification; a FOREGROUND call is capped at 600 s
  and a build that outruns the cap is KILLED, which is the one failure the whole
  apparatus is not immune to — a killed build's log gets its terminal marker only
  from the recipe's signal trap. The three forbidden decorations are one mistake
  wearing three faces: a trailing `&` backgrounds a wrapper the harness is already
  managing, a `>/dev/null 2>&1` throws away the one thing the launch prints (WHERE
  the log is), and **A PIPE IS THE WORST OF THEM, BECAUSE IT ANSWERS** — a pipeline
  exits with the LAST command's status, so `make gate | tail` reports the tail's
  success over a RED build. That is the hand-rolled wrapper's false green exactly,
  arriving from outside rather than inside: the wrappers defend the LOG, and a pipe
  goes around the log. The exit status is not the result and hiding it is not the
  fix; `bg-check` reads the log and is. **AND ONE BUILD AT A TIME** — never launch a
  second while one is live, since every check here shares one interface cache.
  → [docs/bg.md](docs/bg.md)
- **`setsid` and `timeout` DO NOT EXIST ON macOS.** Detach with the Bash tool's
  `run_in_background`. Pin the working directory in every build command and guard with
  `ls Makefile &&`; never pipe agda through `head`, which hides OOM kills.
- **THE BASH TOOL'S WORKING DIRECTORY PERSISTS BETWEEN CALLS, SO PIN IT.** A `cd` in one
  call is where the next call starts, and a `make` typed from the wrong directory finds
  no Makefile or the wrong one; the harness resets the directory only at a turn boundary,
  which is exactly when nobody is looking. Use absolute paths, and never rely on a
  previous call's `cd`.
- **`touch` does NOT dirty a module — invalidation is by CONTENT.** You cannot force a
  remeasurement without a real edit.
- **A PROOF BODY ON THE `budget-sufficient` SPINE MUST BE SEALED (`abstract`), OR VWF
  DIES** — three multi-hour OOMs came from unsealing one. Seal in the SAME edit that
  turns the postulate into a definition; no consumer ever needs more than the type.
  **AND A CAP OR MEASURE IS WORSE THAN A BODY, BECAUSE IT LANDS IN TYPES.** A body is
  normalised when someone unfolds it; a quantity named in a PREMISE is normalised at
  every application of every statement carrying that premise, so ONE transparent
  definition whose body reaches the caps recurrence puts the whole recurrence inside
  every call site of the instant loop. **The tell: the body mentions a family the tower
  already seals for cost.** Seal in the edit that introduces it, and export the one or
  two equations consumers genuinely need as lemmas proven INSIDE the block — always
  cheaper than transparency, and it makes the dependence on the body explicit.
  → [docs/typecheck-cost.md](docs/typecheck-cost.md)
- **A MID-BUILD RSS OF SEVEN TO TWELVE GB IS NORMAL AND IS NOT EVIDENCE OF ANYTHING.**
  Agda frees nothing across a single invocation, so the figure is the whole run's
  allocation and the peak lands on whichever module happens to be LATE in the order —
  which makes it a reading about position, not about the module the log names. Nor is a
  long silence under one `Checking` line: the per-module figures in the numbers file come
  from the dev loop, which STUBS mutual blocks, so a module that reads as seconds there
  legitimately takes many minutes under the real termination check. **The consequence, and
  it is the whole reason this is a rule: DO NOT KILL A LONG BUILD ON EITHER SIGNAL.** A
  full gate run is a matter of tens of minutes at every tower size on record; killing at
  fifteen because the number looked alarming costs the run, poisons the next one's
  attribution, and buys a diagnosis of something that was never happening. Twice, in one
  session. Read the numbers file BEFORE concluding a build is sick.
  → [typecheck-performance-numbers.md](typecheck-performance-numbers.md)
- **THE BUILD IS NOT `--safe`, AND NOTHING MECHANICALLY STOPS AN UNSAFE PRAGMA** — so
  `make unsafe-check` policies them by grep, and anything it finds on the proof path is a
  soundness hole no mandate in this file authorises.
  → [docs/unsafe-check.md](docs/unsafe-check.md)
- **COST MODEL, in one line: mutual-BLOCK membership is everything and file size is
  nearly irrelevant** — but run `make agda-dev ARGS='--list <file>'` before believing it,
  because a module with no mutual block cannot be paying for one, and MEASURE on a
  coherent cache, because a rebuilding dependency masquerading as module cost has
  produced four phantom diagnoses. The POSITIVITY splits are done and that question is
  closed. → [docs/typecheck-cost.md](docs/typecheck-cost.md)
- **BUT A SECOND AXIS COSTS MORE, AND IT IS NOT FILE SIZE: A BLOCK MEMBER IN NO CYCLE
  IS NEVER STUBBED, so every focused check of every OTHER member re-proves it in
  full.** The tell is that per-member times do not vary with the member — a cost that
  ignores which body is real is not a body cost. `--list` already names the
  candidates; hoisting means moving them to ANOTHER MODULE, since a definition left in
  the file is checked when the file is. **Attribute before splitting, on a coherent
  cache**: measured on one module, moving out the statement telescopes, the lemma shelf
  and a named signature together bought under two seconds, and moving out four
  no-cycle members took the per-member loop from timing out to a quarter of the budget.
  → [docs/agda-dev.md](docs/agda-dev.md)
- **ALL MEASURED TIMINGS LIVE IN `typecheck-performance-numbers.md`, AND NOWHERE ELSE.**
  Numbers age far faster than rules, so quoting one elsewhere means maintaining it in two
  places and getting it wrong in both. `make gate-heavy` and `make agda-dev` append their own,
  so it stays current on its own.

## ALL NEW PROOF CODE IS WRITTEN IN `agda/src` — the `make wiring` jurisdiction

**New definitions, new lemmas, new assemblies go straight into `agda/src`**, where the
reachability check, the ⊤-postulate check and the claim graph see them from the first
minute. Writing in `src` is what makes "did we already prove this?" a `grep` instead of
a memory.

**AND THE FAILURE THIS PREVENTS IS BEING UNCLAIMED, NOT BEING OUTSIDE `src`.** That
distinction used to cost nothing, because `src` was the only claimed tree; it is stated
now because it is not. Work no claim root reaches is what parked itself for months and
got re-derived — the repo's number-one failure mode — and a tree with its own root and
its own gate target is not in that position.

**SO EVIDENCE IS WRITTEN OUTSIDE `src`, AND THAT IS NOT AN EXEMPTION (Anthony).** A
refutation and a probe are not proof code: nothing may depend on either, and a probe in
particular is a `refl` at a handful of concrete inputs that must never be mistaken for a
theorem. Both live in `agda/evidence/`, whose two trees each carry their OWN claim root,
so the wiring law applies out there in full — and a `.agda-lib` boundary makes a `src`
import of either one UNRESOLVABLE rather than merely forbidden. **`EVIDENCE.md` is the
law; read it before adding, retargeting or deleting either.**

A bare `probe/` directory once existed for a different reason — `src` had no cheap loop —
and was deleted when `make agda-dev` gave one. **`evidence/probed/` is not that
directory**: the old one sat outside every claim graph, this one is rooted at
`Probed.Main`, gated, and expires its own contents. Do not recreate the former.

**Iterate with `make agda-dev`, land with `make gate`.** A dev-green body belongs in
`src` immediately; it does not wait for the slow gate to earn a home.

### `make agda-dev` — the iteration loop

```
make agda-dev ARGS='<file> <member>'   one member ← the grind loop; use constantly
make agda-dev ARGS='<file>'            one module, every member
make agda-dev ARGS='--list <file>'     free: which members are in which block
```

**`ARGS=` TAKES AT MOST ONE FILE PLUS ONE FOCUS MEMBER.** Two files, or a file and a
list of members, is not a batch — the loop reads the extra word as the focus member and
reports that member absent, which reads as a proof failure. One module per call; a sweep
over several is several calls.

**Use it throughout development and `make gate` once at the end.** Three rules you must
carry before opening the doc:

- **DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID — but only where
  something was STUBBED.** A module with no multi-member block is emitted VERBATIM, so
  the sweep is a REAL check there, which is most of the repo. Where a block IS stubbed,
  **termination of the real mutual recursion is not checked** — and in this proof the
  mutual recursion IS the induction, so a bad measure passes dev and fails the tower,
  a proof-shape failure and not a typo — and **postulates do not reduce**, so a clause
  needing a sibling to unfold can pass dev and fail for real. **Never report a result as
  verified on a dev run, never commit on one alone, never call dev-green "typechecks".**
- **A DEV CHECK THAT IS NOT SECONDS IS A FINDING, NOT A BUDGET TO RAISE.** The budget
  exists to SAY the loop has stopped being the loop; raising it converts a diagnosis into
  a wait. **Read `typecheck-performance-numbers.md` FIRST** — it carries a per-module row,
  so a slow reading is checkable in seconds against a recorded best, and it marks a run
  the budget killed as a FLOOR rather than a measurement. Two causes, both cheap to rule
  out: a second Agda on the same interface cache, measured at 140× and forbidden anyway;
  or a CONE you just invalidated, since the loop stubs mutual blocks in the TARGET only
  and checks every dependency for real. **So work BOTTOM-UP: the module you edited, then
  its consumers.** Asking for a root-ward module right after a leaf-ward edit hands the
  seconds-scale loop the gate's bill, and the gate is what should pay it.
- **A RED `agda-dev` ON ANY FILE IN `src` IS A CRITICAL FAILURE — FIX IT IMMEDIATELY.**
  It is a P0 defect in the tooling, fixed *before* the work you were doing. Never route
  around it — not with a skip list, not with "it's just the tool", not by falling back to
  `make gate-heavy`. A single tolerated red teaches everyone to ignore the next one. **The
  default assumption is that the TOOL is wrong, not the proof** — that is the measured
  base rate, and every such failure ever investigated was a bug in the script. **Do not
  diagnose from the error NAME**; read the generated file, where the bug is visible.

→ [docs/agda-dev.md](docs/agda-dev.md) for the budget, `HOLES=1`, why there is no
whole-project sweep, and the `NOT_DEV_CHECKABLE` policy.

### `make harness` — the compiled calculator

`agda/src/Harness/Main.agda` is a MODULE_ROOT that `make gate-heavy` never pays for. It exists
because **the GHC backend ignores `abstract`**, so the binary runs the real bodies of
families the checker refuses to unfold, and laughs at rungs that OOM the checker.

**⚠ EVERY NUMBER IT PRINTS IS `measured-not-rechecked`, AND SAYING SO IS MANDATORY.** A
harness row is not a `refl` pin: it cannot discharge a postulate, no proof may depend on
it, and reporting one as "verified" is the same false-green failure as calling a dev run
a gate. Its two legitimate uses are to **AIM the grind** and to **REFUTE** — and a row
contradicting a postulate is a lead to chase back to a type-level witness, not itself
the finding. → [docs/harness.md](docs/harness.md)

**AND A SERIES EXPIRES LIKE A PROBE (Anthony).** Every `-- SERIES` declares a
`-- TARGET:` and `make evidence-check` fails the moment that name leaves the postulate
ledger; the series is then DELETED or retargeted, and the check is never relaxed. Its
FINDINGS do not go with it — a coverage boundary, a blocked verdict or a dead route
belongs in the header of the statement it CONSTRAINS, which is where it was owed in the
first place.

**AND IT DECAYS WORSE THAN THE PROBE TREE IT BORROWS THE LAW FROM, WHICH IS WHY THE LAW
HAD TO BE BORROWED.** A probe at least sits in a tree the gate typechecks; nothing
depends on a harness row, and the gate never builds this MODULE_ROOT, so a series
measuring a statement that was proven months ago goes on printing numbers with nothing
anywhere going red — the silent-decay failure of the probe tree, with the one check that
would notice it absent as well. Measured on the sweep that set this rule: twenty-four
series, ZERO target declarations, and TWELVE of them evidence about statements that were
by then proven definitions or deleted outright. Half the file, and every line of it read
as live.

## Module granularity: keep typechecks short

**Cut at mutual-SCC boundaries** — a mutual block is an indivisible checking unit and
cannot span modules; everything else can and should. **Never restructure genuine
mutuality** (indirection layers, WF recursion) just to shrink a module: proof shape wins
over check time. A new lemma family not mutual with an existing SCC gets its own module,
even when it is "about" that SCC. Target ≤20 s solo recheck for every non-SCC module.
→ [docs/typecheck-cost.md](docs/typecheck-cost.md)

## Agda language and stdlib traps

Traps inside the language, each of which cost real time at least once, and they
share a shape worth naming: **Agda reports these against the WRONG thing**, so the error
message actively misdirects. **Before reasoning from an Agda error, check whether it is
one of them** — [docs/agda-traps.md](docs/agda-traps.md). The one that generalises
furthest: when an error says "X is not a constructor of T" for something you meant as a
variable, grep for `X :` before touching the proof. The one that hides longest: an
implicit used inside an `all`-predicate lambda is a fresh unsolved meta per element, so
bind it on the clause's left-hand side (`{e = e}`) rather than expecting the lambda to
see it — the shape and the error it produces are in the doc.

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
put the bound itself in as a conjunct. This is a rule and not a caution because a face of
this development was machine-refuted as vacuous by exactly this shape, having typechecked
and read as discharged for as long as nobody asked what its witness was pinned to.

**This rule applies recursively, and violating it inside a subproblem is an anti-pattern:
never prove pieces before their assembly exists.** For any lemma cluster, first state the
assembly — the statement that *consumes* the pieces — with the pieces as postulates, and
make the whole thing typecheck. Only then prove pieces, starting with the **most uncertain
one**, so that if the assembly has to change it changes *in place*, cheaply, instead of
invalidating a pile of finished proofs. Pieces proven ahead of their assembly are
speculative inventory: they may get thrown out wholesale, and worse, their sunk cost biases
the design toward keeping them. Better to have a wrong assembly you can amend than proven
pieces with no assembly at all.

## SEARCH FIRST — assume the thing already exists until proven otherwise

**Before you probe it, prove it, or write it: look for it.** The default assumption is that
the fact you need is ALREADY IN THE REPO — proven, named, and greppable. That assumption is
right far more often than it feels, because this campaign has been running long enough that
most small facts have been needed before. Treat "I need a lemma saying X" as a SEARCH task,
not a proof task, until a search has actually failed.

This is the same law as the wiring pass, arriving from the other side: the wiring law exists
so that "did we already prove this?" is a `grep` instead of a memory, and that only pays off
if you actually run the grep. Every hour spent re-deriving something proven is an hour the
wiring law already bought back and someone declined to collect.

**The cost is asymmetric and that is the whole argument.** A search costs seconds and its
worst case is that you learn the shape of the neighbourhood. Skipping it costs whatever you
build instead — and what you build instead is usually *weaker* than what was already there,
because a probe gives a receipt at concrete programs while the existing lemma gives a
theorem. Three cases from a single night, each found only after the expensive route: three
probe series were commissioned to test something two proven substitution lemmas already
settle, and none of them COULD have refuted; a path-length unit was recorded as a
`-- DEAD ROUTE` on arithmetic that a proven chain lemma delivers exactly, with a sibling
site already spending it for the identical purpose; and a monotonicity postulate stated
fresh duplicated a proven widening lemma outright, caught by a name clash — the compiler
noticing, not the author.

### `make find` FIRST, BEFORE WRITING ANYTHING NEW

```
make find Q='≤ slotsSize'        every STATEMENT whose type mentions it
```

**Run it before you state a postulate, write a lemma, or commission a probe. Not "consider
searching" — run this command.** It walks the whole of `agda/src` and prints the declared
TYPE of every match.

**IT REPLACES A HAND-ROLLED `grep`, AND THAT IS THE POINT — the rule above used to say
"grep for the conclusion's shape", and it was FOLLOWED and STILL FAILED.** Three lemmas
were rewritten from scratch and collided on the name with copies that had been sitting in
a `Part1` module for months. The search had been run, and run for the right shape — it was
scoped to two `grep` arguments instead of the tree. `make find` takes no argument that
narrows it, so that mistake is not available. **A rule you can satisfy while still failing
is a rule that needs a machine.**

Then the judgement no command can do for you: **search for the CONCLUSION's shape, not the
name you imagine** (names here are idiosyncratic and a name-guess reliably misses); **a
miss is weak evidence, two misses on different phrasings is strong** — try the operator
alone, or read what sits AROUND a neighbouring lemma, since related facts cluster in one
file; and **read the SIGNATURE, never the header prose** — a header saying a route is dead
is a claim about an attempt, the signature is a fact.

**AND `make find-prose` FOR A FINDING, WHICH IS NOT A TYPE.** `make find` cannot see a
dead route, a coverage boundary, a ruling or a measured trap — those are prose by
construction, and the search that misses them reports a clean all-clear. Run it before
picking up any row that is not GRINDABLE, and before commissioning a probe: the question
it answers is *has anyone already been here*, and the answer is in a comment block or a
document rather than in a type. It returns the BLOCK, because one line out of a
forty-line header is a hit and not an answer. Two phrasings before believing a miss.
→ [docs/find-prose.md](docs/find-prose.md)

**AND THE CHECK BEHIND IT: `make dup-check`** fails the build when two declarations prove
the same fact, up to binder spelling and atomic type synonyms. **A FINDING IS TWO SITES,
NOT TWO NAMES** — Agda's `ClashingDefinition` says nothing when either copy is `private`
or the two modules are never in scope together, which is how one fact sat verbatim in two
faces of this development, invisible to the compiler. **When it fires, MOVE THE FACT DOWN
— do not pick a winner among the copies**; the usual cause is two SIBLING modules needing
a fact neither can import from the other, so the repair is to put it in the lowest module
that reaches both. Deleting one copy at random re-creates it later. **And keep ONE naming
convention per class of fact**, because two conventions are the machine that generates
duplicates. → [docs/find.md](docs/find.md)

**The one thing this rule does NOT license** is assuming a fact exists and building on it
unchecked. "Assume it exists" is a directive about where to spend the next five minutes, not
permission to cite something you have not opened. Find it, read its actual type, confirm the
indices line up — the off-by-one above was invisible from the name and obvious from the type.

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
  witness cannot fit. A one-screen refutation in `agda/evidence/refuted/`
  tells you the site needs a positivity hypothesis threaded rather than a cleverer proof.
- **Count the sites by grepping the BARE postulate name.** A hyphenated guess
  (`grep TEMP-`) misses every site where the marker is a SUFFIX and reports a false
  all-clear; comment mentions of the name inflate the count the other way. Grep the bare
  word, then subtract the declaration and the prose.
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

### DELETION: an unreachable definition may be deleted on its merits

`make wiring` is trustworthy — every definition, postulate and module in `agda/src`
has a route to Main today — so a name it reports is a finding to act on.

**DECIDING IT IS YOURS, AND ASKING IS THE FAILURE MODE (Anthony: "let's delete it
if it's not used? That seems obvious to me — not sure why you needed my input").**
A reachability finding is not a design question, and the autonomy grant already
covers it: no spec moves when dead code goes. The three rules below say how to
decide, and every one of them names something to VERIFY, never a reason to
escalate — "prefer wiring when a plausible consumer is nameable" means go look for
one, and "establish that it is a superseded predecessor" means diff the arms.
Routing the decision upward turns a check worth minutes into a round trip and
leaves the finding sitting in the tree meanwhile, which is the state this whole
section exists to end. Three rules govern acting on it:

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
- **A SUPERSEDED PREDECESSOR IS DELETED, ALWAYS (Anthony).** When a
  successor lands and the generation it replaced is left standing, the old one
  goes — not wired, not parked, not kept "until the successor is proven". It is
  the repo's most expensive orphan shape, because a predecessor drags a whole
  support cone with it and every local check reads that cone as wired: a mutual
  cluster consumes itself, so "has ≥1 consumer" is satisfied by dead code. Only
  reachability sees it.
  **But ESTABLISH that it is one before invoking this rule.** Both clusters the
  first reachability sweep reported as predecessor generations turned out not to
  be: one was a checker blind spot (a module APPLICATION conducting the cluster's
  only edge), the other a MISSING WIRE whose successor was re-proving what the
  predecessor already proved — delete either and live proof goes with it. The
  distinguishing question is not "does a successor exist" but **"does the
  successor prove everything the predecessor proves?"** — and it is answered by
  diffing the two bodies' arms, not their statements.

### DE-RISK MODE: test for falsity first, grind last (Anthony)

**The current pass is DE-RISKING.** Every postulate carries a probability of being FALSE
or EMPTY, and the proof's total risk is the SUM over the ledger — so work is ordered by
*risk reduced per unit effort*, not by proof-progress optics. The tier-ordered roadmap
lives in PROOF-STATE.md (order and one-line hooks only — the research lives in the
postulates' own headers); read it before picking up any postulate.

**THE RISK CLASSES — worst first.** Every live postulate carries exactly one, and the
class is what orders the work; PROOF-STATE.md assigns them, this file defines them.

- **FALSITY** — the statement may be false. Worst because it is retroactive: everything
  ground above it is wasted, not merely delayed. **This is also where a statement nothing
  has ever instantiated sits**, however plausible it reads: "may be false" is a claim
  about what is KNOWN, and nothing is known about an unprobed row. So this is the class a
  new postulate is born into, and a probe reaching its risky region is what moves it.
- **SHAPE** — the statement is wrong as written and a restatement is *guaranteed*
  (typically a conclusion needing information no hypothesis carries). Not FALSITY,
  because it is already known; worse than DIFFICULTY, because restating cascades through
  a family and can INTRODUCE falsity — you are changing statements, not discharging them.
  Never grind a SHAPE row; restate it. **A header recording a gap between what the
  hypotheses carry and what the conclusion needs has ALREADY put its row here**, whatever
  class the roadmap says: the finding is the classification, not an input to it.
- **VACUITY** — it typechecks and asserts nothing. Worse than DIFFICULTY because it reads
  as discharged. The two live shapes are ⊤-typed postulates and Σ-statements
  upward-closed in their witness; check both before landing anything.
- **DIFFICULTY** — true and correctly stated; the proof is just hard. Labour, but labour
  with a DESIGN decision still inside it: the shape of the induction, the measure that
  decreases, the index the statement belongs at. Grinding is the right response, and the
  deciding is the expensive half. **"True and correctly stated" is a claim about EVIDENCE
  and is earned exactly as GRINDABLE's is** — a probe that reached the risky region, a
  refutation of the alternatives that pins this form, a proven mirror. Absent one the row
  is not DIFFICULTY: it is SHAPE if the gap is written down and FALSITY if nothing is.
  **This class is the one with no floor under it and the one that reads as safe**, so it
  is where an unexamined row lands by gravity and then sits, scheduled behind rows whose
  proofs are merely long. Measured on the sweep that set this: one tier held seven rows at
  `DIFFICULTY, NO EVIDENCE`, not one of them instantiated, and re-reading their own headers
  moved five.

  **AND `make roadmap-check` ENFORCES THE FLOOR, AT BOTH CLASSES THAT CLAIM SOMETHING
  (Anthony: "we need to mechanically outlaw a 'difficulty' or 'grindable' row with no
  evidence").** A DIFFICULTY row whose postulates' headers carry no durable marker is a
  build failure, exactly as a GRINDABLE row naming no proven twin already was. The three
  classes below them are exempt and that is not leniency: FALSITY, SHAPE and VACUITY
  assert nothing about the statement being right, so a blank there is the honest reading.
  The repair for a row that cannot name its evidence is never to acquire a marker — it is
  to reclassify DOWN.
- **GRINDABLE** — true, correctly stated, and the shape is ALREADY KNOWN: a proven twin
  exists whose clauses correspond, or the route is mechanical — transport a hypothesis,
  widen a bound, re-establish an invariant a sibling face already preserves at the same
  indices. Nothing remains to decide, only to type. Weakest class: it is the absence of
  every risk above it, including the design risk that keeps DIFFICULTY expensive.

**GRINDABLE IS THE DELEGATION BOUNDARY — THAT IS WHAT THE CLASS IS FOR.** A GRINDABLE row
is what a worker (or a cheaper model) should be handed: the expensive part, deciding the
shape, is already done and written down, so a fresh context can execute it without
rebuilding the design. A DIFFICULTY row is the design session's own work — delegating one
pays the fixed context cost to hand over a decision that has not been made yet, and it
comes back as analysis instead of edits. This is the "KEEP DEPTH" rule of the delegation
section, stated as a property of the row rather than a judgement call at spawn time.

Measured once, and it is why the class exists: a Sonnet-4.6 session discharged seven
GRINDABLE rows in under four hours (the ledger went 107 → 100, gate green, PROOF-STATE
updated per commit) and then spent two full context windows on ONE DIFFICULTY row,
producing a complete proof plan and no code. Same session, same rules, same repo — the
class of the row predicted the outcome.

**RISK-REDUCTION PRIORITY OUTRANKS PARALLELISM: WHILE A TIER'S ROADMAP HAS AN OPEN LEG
ABOVE THE GRINDABLE ONES, DO NOT FAN WORKERS OUT ACROSS ITS MECHANICAL ROWS — WORK THE
TOP LEG (Anthony, twice — the second time intercepting the spawn mid-turn: "Don't! Do the
hard stuff first").** This is the ordering law of de-risk mode applied to *scheduling*, so
it is stated over the ORDER and not over any one class: whatever sits highest in the
tier's roadmap is what gets worked, and the design session takes it itself. The rule above
says *who* work goes to once picked up; this says *what is picked up at all*.

The fan-out looks like leverage and buys proof-progress optics while the row that could
still move the ground stays open — and the per-worker context cost is paid again if a
design failure on the risky row invalidates what they ground.

**The one carve-out is a GENUINE PREREQUISITE — and verify it, do not assume it.** A
GRINDABLE row the risky row actually consumes is fair game; "adjacent", "same family" or
"same module" is NOT, and the near-miss is the common case, since a candidate unblocking a
SIBLING of the row in hand reads exactly like one unblocking the row in hand. The risky
row's own statement or header must name the candidate. **This NARROWS PROOF-STATE.md's
tier preamble**: its licence to grind mechanical rows in parallel is for a tier whose open
rows are all GRINDABLE.

**EARNING THE CLASS: NAME THE PRECEDENT.** GRINDABLE is not "feels easy", it is "here is
the worked instance." The postulate's own header must name the proven twin or the
mechanical route; absent one, the row is DIFFICULTY. **Name it in a `TWIN:` section, where
`make comments-check` resolves it** — and refuses a twin that is itself still a postulate,
which is this rule finally having teeth instead of a convention. Without this the class becomes the
place everything nobody wants to think about gets parked, which is the one failure mode
that would make it worse than not having it.

**A CLASS IS A PROPERTY OF EVIDENCE, NOT OF CONFIDENCE. A RISK CLASS MAY ONLY BE LOWERED
BY EVIDENCE THAT REACHED THE RISKY REGION.** Name the region the evidence reached, or the
receipt does not count. This is the general form of "never extrapolate a probe past its
shapes", and it is the specific way this campaign has made itself feel safer than it was:
a row was once downgraded FALSITY → DIFFICULTY on a probe covering only the
near-degenerate case, and had to be reverted. **Corollary: a named route is not
evidence** — knowing how a proof would go says nothing about whether the statement is
true. A proof sketch and a green probe of the near-degenerate case lower nothing.

**THE CONVERGENCE TEST — the one thing that distinguishes progress from a spiral.**
Grinding a FALSITY row routinely spawns new postulates, and spawning a new FALSITY is
*not* by itself bad news. Apply this test:

- **Converging** — the new FALSITY's risky region is strictly SMALLER than the one it
  replaced (a sub-case of the same edge). That is the risk localising, and localisation is
  what buys probeability: a region small enough to name is a region small enough to
  instantiate. A statement about a whole clause cannot be probed; a statement about one
  branch of it usually can.
- **Spiralling** — the new FALSITY is not smaller, or reaches UPSTREAM into machinery
  already ground. Each layer needing a fact at least as risky as the layer itself means
  the decomposition is not converging, and more subdivision will not find the problem.
- **THE STOP CONDITION, and hold to it:** the SAME region producing FALSITY across three
  successive subdivisions. That is not a hard proof — it is a wrong design in the
  mechanism under it, and the response is to reconsider the mechanism, not to subdivide a
  fourth time.

**FALSITY does not mean the theorem is false.** It means this STATEMENT might be, and if
it is, you restate. The common refutation is repairable by a hypothesis that is already
available where it is needed, and costs a restatement. The expensive shape is a refutation
whose repair needs a hypothesis NOT available at the call site — that one forces the
design to move, and it is the one worth naming when you find it.

- **A machine refutation is worth as much as a proof — usually more, since it is
  cheaper.** A false statement found now costs a restatement; found after the towers above
  it are ground, it costs the towers.
- **AUDITING STATEMENTS FOR TRUTH IS THE PRIORITY, not a distraction** — especially by
  machine probe. A `-- SUSPECT:` note is not the correct response to a doubt you can test:
  test it.
- **PROBE BEFORE GRINDING.** If a postulate's sides are computable, instantiate it at
  concrete programs **in `agda/evidence/probed/`, checked with `make agda-dev`** and pinned by `refl` —
  bug-cache shaped, seconds per loop. Every probe ends in exactly one of two states: a
  refutation (record, restate, re-rank) or a confidence receipt (`-- PROBED:` in
  the postulate's own header, saying what shapes were covered). **An unprobed probeable
  postulate is the cheapest unmanaged risk in the repo.**
- **AND PROBE THE ASSEMBLY'S CONCLUSION, NOT ONLY ITS LEAVES.** A real body over
  postulated leaves has a conclusion that COMPUTES exactly as a postulate's does, so
  it is probeable — and it is the one thing nobody instantiates, because it
  typechecks and so reads as settled. Its falsity is the retroactive kind: every
  clause already ground under it was proving something false, and the leaves inherit
  the defect without any of them being individually wrong. Measured once on this
  campaign's expensive spine: a leaf was probed, refuted, and the same witness then
  refuted the definition consuming it, whose own bound was smaller — so the leaf's
  refutation was the *cheaper* half of the finding. **The tell that it is worth the
  minute: the leaf's bound and the assembly's bound are stated in the SAME currency**,
  since then a witness against one arithmetic is a witness against both, and you get
  the upper result for free by instantiating the parent at the same program.

- **AND ASSUME A PROBE ALREADY EXISTED, UNTIL A SEARCH HAS FAILED (Anthony).** This
  is SEARCH FIRST arriving at the evidence, and it binds on every row that is not
  GRINDABLE — a FALSITY, SHAPE, VACUITY or DIFFICULTY row is exactly the kind that
  has been picked up before, put down, and probed on the way. The default
  assumption is that someone has already instantiated this statement, and the
  search costs one command:

  ```
  git log -S'<postulate name>' --all --format='%h %s'
  ```

  **SEARCH BY THE TARGET'S NAME, NEVER BY THE PROBE DIRECTORY'S PATH.** Probes
  name the statement they test in their own headers, so the name reaches them
  wherever they lived — and they have not always lived where they live now, so a
  path-scoped search reports a false ALL-CLEAR, which is the worst possible answer
  to this question. Then `git show <sha>^:<path>` reads the probe back, and
  `git log --diff-filter=D` on the commit names everything it deleted.

  **The receipt convention does not make this redundant, and the numbers say so:**
  a probe's finding is supposed to land as a `-- PROBED` line in its target's
  header, and at the sweep that recorded this rule the tree held ten such receipts
  against **ninety-eight probe files deleted** over the campaign. A convention
  capturing a tenth of the evidence is a convention that needs a search behind it.

  **AND WHAT YOU RECOVER IS USUALLY WORTH MORE THAN A VERDICT.** Two kinds of
  thing, both expensive to rebuild and neither of which fits in a header line.
  The **HARNESS** — real-evaluator plumbing, the ⊔-shaped measures a bound needs,
  and the refutation families someone already thought to try — is most of the cost
  of a probe and none of its receipt. And the **BLOCKED or BOUNDED verdict**: "both
  families are sealed, so this side cannot be instantiated at all", or "the cost is
  geometric in two parameters, so this reached k ≤ 4 and not the k = 9 that was
  asked for". Those are coverage boundaries and infrastructure limits, they are
  findings about what CANNOT be probed, and rediscovering one costs exactly what it
  cost the first time.

  **THE TRAP, AND IT IS THE COMMON CASE: READ THE RECOVERED PROBE'S STATEMENT, NOT
  ITS VERDICT.** A probe is expired by its target being discharged *or restated*,
  so the probe you find is usually evidence about the statement that USED to be
  there. A green on `A + B + C` says nothing about `(A + B) ⊔ C`, which is a
  strictly smaller bound — the rows have to be re-run even though the harness
  transfers. This is "never extrapolate a probe past its shapes" applied one level
  up, to the statement rather than the inputs, and it is the mistake a found probe
  invites: the verdict is the part you read first and the part least likely to
  still apply.

- **AND A PROBE EXPIRES WITH ITS TARGET, MECHANICALLY (Anthony).** A probe declares
  `-- TARGET: <postulate>` and `make evidence-check` fails the moment that name leaves the
  postulate ledger — discharged, restated or deleted. The probe is then DELETED or
  retargeted; the check is never relaxed, because an expired probe is exactly what it
  exists to surface. This is needed because probes and refutations decay differently and
  only one of them says so: a refutation dies when `src` can no longer STATE it, and `make
  refuted` goes red that day, whereas a probe dies when its target is PROVEN and nothing
  happens at all — the rows still compute, the `refl`s still hold, and the file stays
  green forever as evidence for a question already settled. A probe that outlives its
  target because what it really pins is the EVALUATOR is not a probe: it is a unit test,
  and its home is the bug cache.
- **A PROBE'S TARGETS ARE WHAT ITS ROWS ARE EVIDENCE ABOUT — NOT EVERYTHING ITS
  FINDINGS TOUCH.** A probe yields two products with different homes, and conflating
  them is how a receipt comes to claim coverage nobody bought. The ROWS are evidence
  about the statements they instantiate: they land as `TARGET:` declarations and
  `PROBED:` receipts, and a receipt naming a statement the rows never reached is a FALSE
  coverage claim — worse than no receipt, since the next reader budgets nothing for a
  region nothing covered. A FINDING is ordinary charged prose in whatever statement it
  CONSTRAINS, which is usually not the target: an obligation on a quantity the target
  merely takes as given is owed where that quantity is DEFINED, and a definition cannot
  carry a receipt at all, since `make evidence-check` requires one to sit above a
  postulate. So the finding goes in the definition's own block, naming the probe module
  in backticks — the sanctioned in-passing form, one hop, and `make find` takes the name.
- **AND A PROBE INFORMING N STATEMENTS GETS N ONE-LINE POINTERS, NEVER N COPIES OF ITS
  COVERAGE CLAIM.** Several `-- TARGET:` lines in one probe are supported, so the probe
  stays the single home for what it covered. N copies is the drift failure the
  explanation-echo check exists for, arriving one level up: the copies age
  independently, and nothing then says which one is current.
- **AND THE PROVENANCE OF A FINDING TRAVELS WITH THE FINDING, NOT WITH THE RECEIPT.**
  Whether something was turned up by INSTANTIATION or by reading the definitions is a
  reason to trust it, so it belongs in the same block as the claim it justifies. Put it
  in an explanation sitting above a `PROBED:` section instead and it reads as narrating
  the ledger, which is charged, checked, and the wrong place; put it beside the finding
  and it is neither.
- **DETERMINE COMPUTABILITY BY LOOKING, NEVER FROM A REMEMBERED LIST.** Whether a family
  reduces is a property of the code TODAY: an `abstract` block seals it, and blocks get
  added for measured performance reasons without the statements above them changing. Check
  the definition site. Any list of "the computable ones" written in this file would be a
  research finding pretending to be a rule, and would go stale silently — one did, and it
  named a family that had since been sealed.
- **HYPOTHESIS-SIDE AND CONCLUSION-SIDE COMPUTABILITY ARE SEPARATE QUESTIONS.** A
  statement can be unprobeable in its hypotheses (you cannot discharge them at concrete
  numerals) while its conclusion computes fine. That is still worth probing: compute the
  conclusion at reachable states, and if a conjunct is false, the hypotheses'
  satisfiability is a smaller job than proving them. "Sealed somewhere in the statement"
  does NOT imply symbolic-or-nothing — say which SIDE is blocked.
- **Never extrapolate a probe past its shapes.** Green on three canonical programs is a
  receipt, not a theorem; say which shapes were covered and which were not.
- **AND DECIDE WHICH AXES CAN REFUTE BEFORE SWEEPING ANY OF THEM: ONLY A
  MEASURE-SIDE AXIS CAN.** For a statement of the form `lhs ≤ rhs`, a parameter
  that moves only the RIGHT weakens the claim, so no instantiation of it can
  produce a counterexample — a sweep over such an axis is unfalsifiable by
  construction, however many rows it has and however tight they read. This is
  the rule below applied to the STATEMENT rather than to a row, and it is worth
  having separately because it is decidable by looking at the type, before any
  harness exists. It also runs the other way, which is where it costs something:
  an axis with no coverage is a finding only if it moves the measure, so reading
  a bound-side gap as a risk over-ranks the row and holds a class that nothing
  is holding. Both errors were made on one row of this campaign, in that order.
- **A row that could not have failed is not a row.** Label every probe row LOAD-BEARING or
  DEGENERATE and state what would make it fail. Three ways a probe lies green, all
  observed in one day, all erring toward false comfort: **(1) vacuous rows** — the
  quantifier is empty (`all _ [] = true`, `0 ≤ᵇ _`), so name the covered CONJUNCTS, not
  the covered programs; **(2) hand-built states** — a state written as
  `record (st-init e) { … }` is not one the evaluator can reach, so reach states by
  RUNNING, and treat a constructed state where the predicate FAILS as a refutation
  candidate whose reachability is the finding, not a "non-vacuity witness"; **(3) reading
  an assembly backwards** — `P = P-core o₁ … oₖ` proves P FROM the postulated core, never
  the core; the `oᵢ` are its hypotheses.

**RECORD A DEAD ROUTE WHERE THE NEXT PERSON WILL STAND.** A *refuted statement* and a
*dead route* are different findings, and only the first has a natural home: a refutation
is machine-checkable, while a dead route has no `⊥` to state — the statement may well be
true, but *this way of proving it* cannot work. Such findings historically lived only in
PROOF-STATE prose, far from the postulate someone picks up six weeks later, and
re-deriving a dead route is the same wasted week as re-deriving a proof.

So: **when an attempt fails for a structural reason, add a `-- DEAD ROUTE <date>:` line to
the header of the postulate you were trying to discharge** — not to a roadmap, not to a
separate file. Same locality rule as `-- PROBED`. It must say **what was tried and what
structurally blocked it**, because "tried X, didn't work" does not stop anyone: "route #2
is STRUCTURALLY DEAD — `cascadeLatch` sets `dying` before any chain is processed, so the
invariant cannot be established at that point" does.

- **A PROSE note is the home for a dead ROUTE; a machine-checked refutation lives in
  `agda/evidence/refuted/` (Anthony)** — a separate library checked by `make refuted` and
  `make wiring-refuted`, whose rules are in **`EVIDENCE.md`; read it before adding,
  repairing or deleting a refutation, or a probe.** **KEEPING A REFUTATION IN `src` IS ACTIVELY
  HARMFUL**, because `src` must then keep whatever machinery makes the dead route
  STATE-able, and that machinery is otherwise deletable — measured at seven live
  definitions held up by nothing but the six refutations that mention them. `src` may
  refer to a refutation in a `-- REFUTED:` comment, since a refuted route does not change;
  it may never import one. This does NOT reopen a tree of failure *notes*: everything in
  `agda/evidence/refuted/` is TYPECHECKED and claimed by `Refuted.Main`, so it cannot rot
  unnoticed, while prose outside the claim graph is read by nobody when it would help.
- **A dead route is not a licence to weaken the statement.** It kills a *route*; the
  postulate stays at full strength. **Deleting a dead-route line requires the route to be
  shown WORKABLE**, not merely untried-again — it is evidence, and it ages better than the
  code around it.

**TIER ORDER IS LAW: LOWER TIERS FINISH FIRST (Anthony).** Strictly — not "mostly", not
"while a build runs". Each tier is built ON the one below it, so grinding an upper-tier
statement while a lower tier is open bets on ground that a design failure would move. The
one carve-out is answering a *design question* (cheap, and it aims the grind) — never
grinding over one.

**Before starting any task: if the postulate is not in the lowest open tier, and the work
is not a design question, it is parked — say so and take a lowest-tier item.** Which
postulates those are, and why each is ranked where it is, lives in PROOF-STATE.md; **this
file never names them.** The tier structure exists because priority that lives only in
prose gets spent on whatever is nearest — measured once at five days of discharges that
all went to non-anchor rows while the anchor sat untouched.

**AND WITHIN THE TIER, THE BIG PICTURE ROADMAP IS THE THING FOLLOWED — NOT THE NEXT ROW
DOWN (Anthony).** Every tier there opens with its next three LEGS, ranked riskiest-first,
each a GROUP of postulates aggregated across the whole ledger: statements sharing a
currency, a claim and the sites that consume it, one shelf of mechanical work. Take the
top leg and work it end to end. The rows are the ledger the legs are drawn from, and
reading straight down them proves one postulate at a time — which is the wrong unit,
because the expensive discovery in this campaign is never the clause but the neighbours a
restatement drags with it, and a row cannot show you those. Where the grouping is not
real, a leg falls back on the risk classes and may name a single row; that is a leg too.
`make roadmap-check` holds each tier to exactly three legs, and each leg to a prose budget
several times a row's, since a group has no header to send its reasoning to.

**AND THE THREE DO NOT COVER THE TIER (Anthony).** They are the NEXT three legs, not a
partition of what is left — covering the ledger is the ROWS' job and they already do it.
What comes after the third leg is left unnamed deliberately: it will be re-grouped by
whatever the first three turn up, so naming it now writes a schedule that ages before
anyone reads it. A leg enumerating every remaining row has stopped being a plan.

**A RISING POSTULATE COUNT IS THE MECHANISM WORKING, NOT A REGRESSION.** This needs saying
because every instinct — and every subagent's default — runs the other way. Anthony, in
the session that set this rule: *"the relentless mindset of reducing those numbers is very
harmful."* The ledger is not a scoreboard. One vague postulate split into six specific ones
is PROGRESS: each is separately attackable and none can hide. The only number that matters
is whether `The-Proof.agda` is discharged. So, in worker directives and in your own work:

- **Do NOT minimise the postulate count. Do NOT apologise for it.** Do not describe an
  increase as a cost, a regression, or a trade — it is the intended outcome.
- **Do NOT weaken a statement to make it typecheck.** Weakening is the one move that looks
  like a shortcut and is not: it silently makes a claim smaller. Postulate the
  full-strength statement instead, and report the obstacle.
- **Never grind a hard proof when a postulate will do.** If a lemma is real mathematics,
  state it and move on. Note it in the ledger and keep wiring.

### A POSTULATE MUST BE A LEAF (Anthony)

**THE PATTERN THAT DOES THE WORK — postulate-to-assembly conversion.** When a proof has
nowhere to plug in because its only would-be consumer is itself a monolithic postulate:
take that postulate, convert it into a REAL DEFINITION over several smaller postulates,
and have the definition **CALL** the pieces it was always meant to consume. This makes
each remaining gap greppable and proves nothing hard. **CALL, not pass** — which is the
rest of this section.

**Nothing proven may be PASSED INTO a postulate as its only use.** Write an assembly as a
REAL BODY over POSTULATED LEAVES — never as a postulate over proven pieces:

```agda
postulate l₁ : L₁                        -- the gap, a true leaf
P : T
P = <real body applying l₁ …>            -- the composition is CHECKED
```

**not** the `-core` form `postulate P-core : L₁ → … → T` with `P = P-core l₁ …`, where the
composition is asserted and **checked by nobody**. That form verifies only that `L₁…Lₖ`
and `T` are well-formed types; it never verifies that they SUFFICE. Two postulates each
shed seven-plus leading hypotheses when finally proven — ingredients claimed, never
actually ingredients, undetected until someone wrote the real proof. **A `-core`'s
hypothesis list is a HYPOTHESIS about the route, not a specification**, and the leaf-only
form is what makes the typechecker say so at the moment the leaf is proven rather than
months later.

**When the body cannot be written yet, postulate the parent BARE and mint no leaves.**
Nothing is ever blocked: the bare postulate is always available, so the rule only changes
the ORDER to assembly-first, leaves-second — which is what outside-in already demands
("never prove pieces before their assembly exists"; leaf-only is that rule with teeth,
since today "assembly exists" is satisfiable by a postulate that checks nothing). An
unwritten route goes in the parent's header, not into a type that verifies nothing.

The payoff is that **a leaf's FIT is tested the moment it is proven**, because its
consumer is a body that must reduce.

**HOW THIS IS ENFORCED — as a corollary of reachability, needing no ledger of its own.**
`make wiring-gate` gives a name PASSED to a postulate no reachability credit from that
site, so a lemma whose only use is being handed to a postulate has no route home and
fails. There is no grandfather list and no name-based heuristic: the rule sees EVERY
postulate, not the ones that happen to be named `-core`. The check reads the eta form and
the continuation line too, because together they are how this rule's own worked example
escaped it for months. → [docs/wiring.md](docs/wiring.md)

**WRITING THE BODY DOES NOT LICENSE BREAKING OTHER LAWS (Anthony).** The temptation is
sharp and specific, so name it: **writing a body turns an unpaid premise into a TYPE
ERROR, and the fastest way to clear a type error is to add a hypothesis to the parent.**
That is exactly the laundering "ADDING A HYPOTHESIS IS A RESTATEMENT" forbids — tracked
debt (a postulate: counted by `make wiring`, carrying a risk class, listed in
PROOF-STATE) becomes untracked debt (a hypothesis: invisible to all three) — and it
*feels* like progress, because the file goes green as you do it.

**So when a fit test reveals a MISSING INVARIANT, it goes in the INVARIANT RECORD, not in
a signature** (Anthony's ruling; the finding is in the header of the postulate it was
found at). A field on the invariant record obliges every producer to supply it and every
consumer to re-establish it, so the typechecker carries the fact everywhere it is needed.
A hypothesis obliges only whoever happens to call today — the "the call site happens to
supply it" trap, one call site later. **Cascading through the record's consumers is the
COST OF THE FACT BEING TRUE, not a reason to avoid it.**

The same yields to the rest: do not WEAKEN the parent to make its body typecheck, do not
close an arm with a ⊤-typed or otherwise vacuous postulate, do not seal a gap in prose.
**If a body cannot land without breaking one of these, it has FOUND something and it
STOPS.**

**A STOP IS A FINDING, NOT A DISCHARGE — IT IS NOT DONE TILL IT IS DONE (Anthony).**
Stopping produces a real result and is the right move; what it does not produce is a
completed item. The roadmap row STAYS and the parent is still a parent until the body
actually lands and the parent stops taking proven lemmas. Write the finding in the
postulate's header, record the ruling, and leave the row exactly where it was. This needs
saying because a good finding is the most convincing thing there is to mistake for
progress: genuinely valuable, genuinely publishable in a commit message, and it leaves the
code in precisely the state it was in — the same failure as **CODE BEATS PROSE**, work
converted into a paragraph and the paragraph counted as the work.

**Mechanics that bite when you write an assembly** — four of them, each otherwise costing
a full build, in [docs/wiring.md](docs/wiring.md). The one to carry before you type the
line: **pass every lemma ETA-EXPANDED with explicit implicits** — `(λ {n} {Γ} → f {n} {Γ})`
— because when a statement reduces away its own implicit, bare arguments give
`Unsolved metas`.

**TWO SHAPES THAT ARE ALMOST ALWAYS WRONG — check every new postulate for both.** A
statement whose conclusion needs information appearing in NONE of its hypotheses (e.g.
deriving a path-LENGTH bound from a predicate carrying no length conjunct), and a
Σ-statement upward-closed in its witness (see "A Σ-receipt has content only through its
witness" above). Under de-risk mode these are refutation targets, not `SUSPECT:` notes:
build the counterexample.

**AND FOR THE FIRST SHAPE, SUSPECT A MISPLACED CALL BEFORE A MISSING LEMMA.** When a
statement's hypotheses cannot supply its conclusion, the instinct is that something is
unproven. Often nothing is: the statement is being made at the wrong INDEX — a level, a
fuel, a path depth — and the caller is what is misplaced, not the mathematics. The tell is
that the gap is a fixed, small offset (one level, one frame, one `suc`) rather than a
missing fact about the domain. Nothing about the problem changes when you stare at it;
only where the call sits does.

The check is cheap: find the same operation somewhere it is already PROVEN, and diff the
ARGUMENTS rather than the statements. Two statements can read identically and still differ
in the index each is made at, which is invisible if you only compare their types.

**Parts of this development have a proven counterpart that answers "at what index should
this be stated?" directly** — a second face of the same operation, already discharged,
whose clauses correspond one-to-one with the ones still open; where the two disagree, the
undischarged side is the one that has not been checked. **Which families mirror which is
recorded in the source headers of the statements themselves**, not in any list kept here,
which would go stale silently with nothing grepping it. That comparison has retired
postulates that read as hard: a one-unit gap dismissed as an irreparable off-by-one turned
out to be a call sitting one level too low, visible the moment its discharged
counterpart's arguments were put beside it. Two postulates fell to moving the call, with
no new mathematics. **But a mirrored counterpart is a property some parts of this
development happen to have, not a general fact** — do not force the analogy where the
correspondence was never claimed. What generalises is the smaller claim: *an index-shaped
gap points at the call site, so before proving anything, find the same operation where it
already works and compare the arguments.*

**ADDING A HYPOTHESIS IS A RESTATEMENT, AND NEEDS A RESTATEMENT'S JUSTIFICATION.**
`A → B` is weaker than `B`, and a hypothesis is INVISIBLE to the ledger in a way a
postulate is not: a postulate greps, gets counted by `make wiring`, carries a risk class,
and sits in PROOF-STATE; a hypothesis threaded into a signature does none of that. So
trading a postulate for a hypothesis discharges nothing — it launders TRACKED debt into
UNTRACKED debt, which is precisely the invisible debt the wiring law exists to prevent, in
the one form that feels like progress while you do it.

The one sufficient justification is that the unconditional form has been **REFUTED**: then
the conditioned form is the true statement replacing a false one, which is not a weakening
at all. (One inequality on the caps face is FALSE unconditionally — refuted in
`agda/evidence/refuted/`, against an adversarial stored state — so the conditioned form is the one
that is stated.)

**"The call site happens to supply it" is NOT a reason.** Today's call sites are an
artifact of today's assembly — usually exactly one caller. A hypothesis baked in because
the current caller offers it makes the statement's shape accidental, and when a second
caller appears that cannot supply it you do not discover a missing hypothesis, you discover
the lemma does not apply. Same distinction as "no consumer today" vs "no consumer ever".

### CODE BEATS PROSE: if you can assemble it, ASSEMBLING IT IS THE JOB (Anthony)

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
already paid: an arithmetic lemma sat machine-proven for eight days while a header called
the same arithmetic "hand derivation, not yet machine"; and a nodry lemma was described in
prose as assemblable from the walk face's `hasDry` conjunct, and committed that way, when
the assembly was available — it turned out to discharge a clause outright and prove a
burst-split transport, both of which the paragraph had silently classified as part of the
postulate.)

Corollary for headers: a header's job is what CANNOT be code — a refuted route, a coverage
boundary, a ruling and its rationale, a recovery pointer. The moment a header explains a
derivation that would typecheck, move it into the derivation.

### A HEADER HAS A SHAPE, AND HISTORY IS NOT PART OF IT (Anthony)

**EXPLANATION FIRST, THEN EVIDENCE — `REFUTED`/`DEAD ROUTE`/`TWIN`, then `PROBED`,
then `RECOVERY` — AND THE EVIDENCE COMES LAST.** Not a style preference: it is what
gives a long header landmarks to skip by, and it is what makes the budget below
definable at all. Rank one answers *what is ruled out and what the route is*, rank two
*what was covered*, rank three *where deleted apparatus went*. A marker is a **LEDGER
ENTRY**, so prose that wants to mention a refutation in passing names its module in
backticks rather than opening a `REFUTED:` section mid-paragraph — a ledger interleaved
with the argument is neither.

**AND A MARKER THAT NAMES SOMETHING MUST NAME SOMETHING THAT EXISTS (Anthony).** Every
one of those sections except `DEAD ROUTE` refers to an object that can be deleted, so
its disappearance is a build failure — the same law `make evidence-check` already puts
on a probe's `-- TARGET:`, arriving from the header's side and closing the loop with it:
that check expires a probe when its target is discharged, and this one catches the
receipt left pointing at the probe it just deleted. **Write the reference BACKTICKED or
DOTTED**, because English is full of words this tree happens to declare and a bare word
resolves by accident.

- **`TWIN:` NAMES A PROVEN DEFINITION, AND THAT IS WHAT MAKES "NAME THE PRECEDENT"
  CHECKABLE.** The de-risk rule below demands a GRINDABLE row name its worked instance;
  nothing checked it, and a mirror recorded in prose is a claim no machine reads. **If
  the named twin is ITSELF STILL A POSTULATE the class is wrong** — the route has not
  been walked, so the row is DIFFICULTY. That is a mis-classification caught
  mechanically, which is the one thing the class system exists to prevent.
- **A `PROBED:` RECEIPT FOR A DELETED PROBE CARRIES THE SHA.** A probe is *supposed* to
  outlive nothing — it expires with its target — so "the probe is deleted" is a normal
  state and the receipt is all that is left. Then the sha is the whole recovery route,
  and it is what makes the `git log -S` rule below actually work rather than aspire to.
- **`DEAD ROUTE:` IS UNVALIDATED, BY CONSTRUCTION.** It has no referent: it records that
  a *way of proving* something cannot work, and there is no object to resolve. That is
  precisely why it got a prose convention instead of a check, and it is the section to
  reach for when a finding is real but names nothing.

**THE SECTIONS ARE OPTIONAL WHEN ABSENT AND VALIDATED WHEN PRESENT — NEVER MANDATORY.**
A required field on a row that has no twin produces a filler `TWIN:`, and filler there
is **worse than empty**, because it earns a class the row has not earned. Structure is
enforced on *order and resolution*, never on presence.

**AND THE REPAIR FOR AN OVER-BUDGET BLOCK IS USUALLY TO SPLIT IT, NOT TO CUT IT.**
This is what the budget is FOR, and it is worth knowing before you start deleting: a
block is separated from the next by a genuinely blank line, so the ceiling caps **one
unstructured explanation**, not how much a declaration may carry. An essay holding ten
findings under one banner becomes ten blocks, each with its own heading and its own
ledger, and nothing is lost — the reader gains landmarks and the budget stops firing
because each finding now fits. Reach for the knife only when a block holds ONE finding
and still runs long; then what is over budget is genuinely superseded framing. Worked
instance: a 154-line wall in the evaluator became ten skimmable blocks with no prose
deleted at all.

**AND ONLY THE EXPLANATION IS CHARGED (Anthony).** The prose before the first evidence
marker has a character budget; the evidence sections and any `git show` pointer are
free. This asymmetry is the entire design, and the tempting symmetric rule is wrong: a
source header is precisely where the roadmap's own budget SENDS research, so budgeting
the destination too means a finding with nowhere to go does not MOVE, it gets DELETED —
the one outcome the directive behind all of this rules out. Same principle as the
roadmap's rows, where names are free and explaining is charged. The budget is set at
the measured p99 for a reason: its job is to declare a block **over-explained**, not to
trim writing, and a module's front matter legitimately runs long.

**AND SAY IT ONCE: THE EXPLANATION DOES NOT NARRATE THE LEDGER BELOW IT (Anthony: "no
redundancy in documentation").** A structured section is a machine-checked reference
sitting a few lines down, so an explanation that also mentions the probe, re-argues the
dead end, or repeats the sha is spending charged characters to say what the free part
already says — and says it WORSE, because the prose copy is the one nothing resolves.
The redundancy is not merely wasteful; it is the mechanism by which the two halves
DRIFT. The prose copy ages while the section stays live, so a block ends up carrying a
refutation it no longer has and a coverage claim the receipt contradicts, with no way to
tell which sentence is the current one. Leaning on the sections is what keeps a header
lean enough to read: state what the statement SAYS and why it is shaped that way, and
let `REFUTED`, `DEAD ROUTE`, `TWIN`, `PROBED` and `RECOVERY` carry the evidence — they
are the vocabulary, not a summary of the paragraph. **`make comments-check` fires when
an explanation duplicates a section the same block already has**, which is the narrow,
false-positive-free half; the general rule is wider than the check, and the check is not
its whole content.

**AND A HEADER RECORDS WHAT IS TRUE OF THE STATEMENT, NEVER WHAT HAPPENED TO THE
DECLARATION (Anthony: "I definitely do want to delete purely historical information —
nobody needs that").** The four durable markers pass that test — coverage, a dead
route, a refutation, where deleted apparatus went. "Was restated", "was split", "was
sealed on", "converted from a `-core`", "measured at 400 s" do not: that is git's
subject, `git log -S<name> --all` finds it, and it cannot rot there because nobody
maintains it. **The superseded framing goes too** — a paragraph kept "so the dead
candidates are not retried" is a dead route, and a dead route is one `DEAD ROUTE` line,
not the argument that produced it.

**NEVER WRITE CODE IN A COMMENT (Anthony).** Not a body, not a signature, not a
"here is the lemma we need" block. This is the sharpest form of the rule above and it is
absolute: **if you are sure the code is needed, take the time to wire it in — with the
SIMPLEST assembly that will hold it.** A commented-out proof is the worst of both worlds. It
is not checked, so it rots the moment anything under it moves; it is not counted, so it is
invisible to `make postulates`, `make wiring` and PROOF-STATE; and it *looks* discharged, so
the next reader budgets nothing for it.

The excuse that produces it, every time, is the wiring law: the piece typechecks but its
consumer is still a postulate, so `make wiring-gate` calls it unreachable and it gets parked
in a comment "until the consumer lands". **That is the wrong repair.** The right one is to
convert the consumer into a real body over a smaller leaf — the postulate-to-assembly
conversion above — so the piece has somewhere to plug in TODAY. The assembly may be as thin
as splitting one conjunct off a tuple; thin is fine, because the leaf-only shape is what
makes the fit checked rather than asserted. (Worked instance: a register-length lemma was
dev-checked, reverted into a postulate's header as commented code, and landed only after
that postulate was split into a four-leaf version plus a real body — an assembly that cost
four lines.)

If the consumer genuinely cannot be split yet, **do not keep the code**. Say in one sentence
what is owed and why the assembly is blocked, and let git history hold the text.

### THE GATE INCLUDES `PROOF-STATE.md` (Anthony)

**`make gate` is necessary, not sufficient. Update PROOF-STATE before every commit that
changes the ledger, in that same commit** — a postulate discharged, added, renamed, split,
reclassified, or reordered. The roadmap is the file every session reads FIRST, so a stale
row misdirects the next session's whole leg; one already did, naming two postulates that had
become real definitions.

**A LEG IS ONE COMMIT OF WORK, AND `make roadmap-moved` ENFORCES IT (Anthony:
"let's mechanically enforce that the roadmap cannot stay the same across
commits").** A leg is still a GROUP — that is how PROOF-STATE states it — but
the group is SIZED BY THE COMMIT: it is the chunk of work this session intends
to land next, not a theme or a region that happens to be coherent. So the
roadmap changes with every commit, and the check fails when it does not.

**THE THREE OUTCOMES, AND ONE OF THEM ALWAYS APPLIES (Anthony: "we also want to
discard routes that are no longer applicable").** The leg LANDED: retire it,
promote the other two, and write a new third — so the file moves. The leg was NOT
FINISHED: **rewrite the first leg as the work that remains**, which is worth more
than the retirement, because it is the only record of what the leg turned out to
cost. Or the leg's ROUTE DIED — the plan it described rested on something now
known not to work — and then it is **DISCARDED**, not rewritten. The third needs
saying because the second HIDES it: "the work that remains" is a rewrite that
keeps the old framing and shrinks it, and a refuted framing shrunk is still a
refuted framing steering the next session. Nothing of that shape remains to be
done. The finding goes where a dead route goes — the header of the statement it
constrains — and the leg replacing it is written from the risk as it NOW stands,
not from what is left of the old plan. None of the three leaves the roadmap
untouched, so an unchanged file means a leg was finished without being retired,
abandoned without being restated, or refuted without being dropped.

**Legs two and three may aim at the SAME postulates as the first.** The three
are not three subjects — they are the next three commits, and a single group of
statements routinely takes three. What the trio owes is a coherent vision for
reducing the most risk, cut into pieces each of which is a reasonable single
commit. Parcel the work that way: pick the risk order first, then cut it at
commit boundaries, rather than picking three topics and hoping each is
commit-sized.

And update it **to the hygiene rules in its own header, which are also part of the gate**:
one line per item (name + risk class + hook), NO numbering of any kind, research in source
headers rather than here, completed items DELETED rather than marked done, no dated
narrative. Re-read that header when you touch the file; every one of those rules exists
because it was violated. `make roadmap-check` mechanises the sort, the coverage, its
REVERSE at row heads (a head may not name a postulate that has been discharged or
deleted), the row budget and the dates — → [docs/roadmap-check.md](docs/roadmap-check.md).

### The wiring law: NEVER LEAVE A PROOF HANGING (Anthony)

**THE RULE. Nothing in this repo may exist without a consumer that traces to a top-level
theorem.** No invisible debt, no dead code, no gap that lives only in prose. Two corollaries,
and both are *checkable* rather than aspirational:

- **Every GAP is a postulate with a real signature** — never a comment, never a merely-missing
  statement. "This still needs X" in prose is invisible to the compiler and to `grep`. State X.
  Then **`make postulates`** — every postulate by name — **is** the complete remaining-work
  ledger and no branch of the proof can hide. (Do NOT substitute `grep '^postulate'`: that
  finds the block HEADERS, a third of the count, and a branch hidden inside a block is
  exactly how eight well-formedness postulates once went uncounted while the index claimed
  the campaign reduced to two.)
- **Every DEFINITION and every POSTULATE is consumed, in code, transitively by a top-level
  theorem.** Then "did we forget something?" is answered by the typechecker instead of by
  memory — if a piece is not needed, `The-Proof.agda` does not compile.

**THE WORKFLOW that keeps it true.** Before proving a lemma, extend the assembly that will
consume it — postulating whatever else that assembly needs — and land both in the SAME commit.
Never finish a proof and leave its wiring "for later": later is where every instance below came
from. If the assembly needs a different signature to accept the piece, **change the signature
first.** A piece that cannot be plugged in is not progress, and its shape is not yet known to be
right.

**A POSTULATE MUST ASSERT SOMETHING.** Wiring an unreachable definition in with a vacuous
bridge is worse than leaving it unreachable, because it looks discharged. Two traps, both live
in this repo: `⊤`-typed postulates whose real claim sits in a trailing comment (fix on sight),
and Σ-statements that are upward-closed in their witness. Check every new postulate for both
BEFORE landing it.

**FORBIDDEN STATES.** An **unreachable definition** — one with no route from Main; it is
either a missing wire or dead weight, both are findings, and leaving it undecided is not an
option. A **lying comment** — prose describing an intent the code does not encode; one
record's header said it was "deliberately NOT yet stated" while the record sat stated 60 lines
below, so a downstream lemma was proven against an assembly that never existed.

**MAIN IS THE TOP-LINE PROOF (Anthony).** `agda/src/Main.agda` is the root of the consumption
graph and the deletion exemption. Three rules: **(1) whatever Main imports sticks around**;
**(2) Main names individual definitions — NEVER a bare `open import`**, so that "imported"
means "claimed" and not merely "compiled"; **(3) Main is never touched without Anthony's
explicit approval** — draft the change and ask. `make wiring` reads Main's `using` clauses to
get its reachability seeds, so a filename never earns an exemption and a claim cannot
self-certify.

Because Agda compiles exactly what is transitively imported, Main also defines the build's
COVERAGE — **`make gate-heavy` IS the claim graph**, and anything outside it is not being checked at
all. `make wiring` guards that boundary directly: a module nothing reaches fails the gate in
seconds, rather than needing a second full compile of the tower to notice. **Never close a
coverage gap by re-adding a bulk import to Main — that is the loophole, not the repair.**

**WHY THIS IS LAW.** Unwired proven work costs this campaign more than refutations do. Its
two failure modes: a proof nobody calls sits inert while the work it would have done gets
re-derived inline at the site that needed it, so the same thing is proven **twice**; and a
tower built without its consumer is a tower whose shape was never checked against anything.

The checker's exit conditions, how reachability is seeded from `MODULE_ROOTS`, and what the
selftest pins: → [docs/wiring.md](docs/wiring.md).

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
   the style of `agda/README.autogenerated.md`'s edge-case examples.

   **AUTHORITY ORDERING WHEN SOURCES CONFLICT** (Anthony, most → least):
   **Anthony's discretion**, then **the Agda spec**. There is no third source.
   `agda/README.autogenerated.md` is NOT an authority (Anthony: "I don't care about
   the readme.autogenerated, for the record") — nothing generates it despite the
   name, no gate reads it, and no check fails when the spec moves out from under
   its prose, so ranking it above the spec put a document that cannot rot loudly
   above the one thing in this repo a machine holds to account. It is the
   memory-directory argument one file over. Do not resolve an ambiguity by citing
   it, do not treat a case it is silent on as a gap owed to anyone, and do not
   surface a conflict with it as a question. This does not soften "the spec is
   gospel" — that rule orders the spec above the *implementation*, and is what you
   apply for every impl/spec mismatch.

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
in `agda/src/Implementation/Unit-Test.agda` — a `_ : impl prog ≡ expected` that Agda checks by
`refl` at compile time. Keep them dead simple: a wall of little `_ : … ≡ …` entries, no fancy
names, no abstraction. They are a performance cache of discovered work, **not** meant to
survive past the proof — delete the module once `The-Proof.agda` is discharged.

The cache is **append-only**, and the invariant is that **`Unit-Test.agda` fully typechecks ⟺
no known counterexample remains** — green there is the impl≡spec finish line. It is off Main,
so `make bug-cache` is what enforces it. → [docs/bug-cache.md](docs/bug-cache.md)

In some cases it might make sense to add a new "naive rx" operator to fix an Agda-impl bug.
This is allowed and encouraged when it's the best solution. But follow the port order: develop
the new operator in TypeScript first, as a proper rxjs-delegating, purely-functional operator.
