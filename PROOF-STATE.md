# PROOF-STATE — the roadmap

**What this file is.** The ordered worklist for the one goal: discharging
`agda/src/Verify-Batch-Simultaneous/The-Proof.agda` — no postulates, everything
typechecks. This file holds the SCHEDULE — each tier's next legs — over a
LEDGER of one-line hooks; everything else lives in the code.

**Hygiene — the rules this file lives by:**

- **Stay current.** This file describes the repo's present state and the work
  ahead — never its history. No dated narrative, no "was X, now Y", no
  superseded plans, no references to code that no longer exists. Git history
  is the archive.
  **`make roadmap-check` ENFORCES THE DATE HALF** — this file names no calendar
  date, anywhere, and one is a build failure. The same scan holds CLAUDE.md to
  the rule, for the neighbouring reason: this file must be CURRENT, that one
  must be TIMELESS. It is the half a machine can see
  with no judgement, and it catches most of the rest by proxy: history arrives
  here WITH a timestamp attached, because the writer knows the reader will want
  to know when. Dates are wanted in a postulate's header, where their age is
  the point, and in CLAUDE.md, where a ruling's attribution belongs. A "was X,
  now Y" that carries no date still has to be caught by eye — which is a reason
  to read the file, not a reason to catch none of it.
- **Completed items are DELETED, not marked complete.** No ~~strikethrough~~,
  no "✅ DONE" rows, no discharged-count bookkeeping in tier headings. The
  deletion happens in the same commit as the discharge, and the commit
  message carries what was proven. A completed row left in place is the seed
  of dated-narrative rot.
- **Research lives in source comments**, in the header of the postulate or
  definition it is about — probe receipts (`-- PROBED`), failed routes
  (`-- DEAD ROUTE`), proof sketches, coverage residue, recovery pointers.
  If a note here outgrows its one line, it belongs in a header instead.
  **`make roadmap-check` ENFORCES A CHARACTER BUDGET, on a row's hook AND on
  a tier's PREAMBLE.** The second is not redundant: holding every bullet to a
  line while writing the finding into the section text above them satisfies
  the row budget exactly, and one tier's preamble reached 4387 characters
  that way — a deleted face's refutation history, a superseded predecessor's
  deletion story, and the research for a currency swap that was already in
  the source header it belongs in. A preamble says what the tier IS: the one
  statement it exports, the doors in and out, and what orders the rows.
- **No numbering.** Items are referred to BY NAME (postulates are unique,
  greppable names — the wiring law guarantees it). Order within a tier is
  the schedule: top item first. Reorder freely, in the same commit as the
  finding that reorders it. This covers EVERY positional scheme, not just
  list indices: conjunct positions ("conjunct (8)" — say `the hasDry
  conjunct`), source section numbers ("§ 5a" — say the postulate's name),
  timing figures (those live in typecheck-performance-numbers.md alone).
  A position silently re-aims when the thing it indexes is edited; a name
  greps or it errors.
- **THE BIG PICTURE TIER ROADMAP IS WHAT YOU FOLLOW; THE ROWS ARE THE LEDGER
  IT IS DRAWN FROM (Anthony).** Every tier opens with a
  `### Big picture tier roadmap` ... `### The ledger` carrying
  the rows. A leg is a GROUP: several postulates sharing a currency, a
  statement together with the sites that consume it, one shelf of mechanical
  rows. Group where the grouping is real and fall back on the risk classes
  where it is not; a leg naming a single row is still a leg.
  **AND A LEG IS ONE COMMIT OF WORK (Anthony).** That is the unit — not a theme
  and not a region, but the chunk this session intends to land next. So the legs
  are the next COMMITS, and every leg after the first may aim at the very same
  postulates as the first; what the set owes is a coherent vision for reducing
  the most risk, cut at commit boundaries. Pick the risk order first, then cut —
  never pick topics and hope each is commit-sized.
  **SO THE FILE MOVES WITH EVERY COMMIT, and `make roadmap-moved` fails when it
  does not.** Three outcomes. The leg landed: retire it, promote the rest, write
  a new last one. It did not finish: **rewrite the first leg as the work that
  remains**, the only record of what it turned out to cost. Or its ROUTE DIED:
  **discard it** — a refuted framing rewritten smaller is still steering, so the
  finding goes to the header of the statement it constrains and the leg that
  replaces it is written from the risk as it now stands.
  **THE LEGS DO NOT HAVE TO COVER THE TIER (Anthony).** They are the NEXT ones,
  not a partition of the remaining work — the coverage rule is the LEDGER's job,
  and the rows already discharge it. Work beyond the last leg is left unnamed on
  purpose: it will be re-grouped by what the earlier ones find, so naming it now
  writes a plan that ages before it is read.
  **Pick up the top LEG, not the top row.** Reading straight down the ledger
  works exactly one postulate at a time, and the expensive part of this
  campaign is never the clause — it is discovering, after the clause is ground,
  that the statement's neighbours had to move with it.
  **`make roadmap-check` ENFORCES THE COUNT AND A PROSE BUDGET PER LEG.** At
  least three — unless the tier has fewer live postulates than that to plan over
  — and at most seven. Fewer than three is a tier planning one leg ahead; more
  than seven is a backlog, and the rows already are the backlog. Between them
  the schedule is free, because a route already decided and cut into commits is
  written down rather than displaced by the next one. The budget is several
  times a row's, because a leg carries its own reasoning and a group has no
  header to send research to; past it, the leg has stopped saying why this group
  is next and started proving it.
- **EVERY TIER NAMES ITS MONSTER, in a `### The monster` section (Anthony).** The
  rows are the ledger and the legs are the schedule; the monster is what the
  schedule is FOR — the one declaration the tier judges most likely to be FALSE,
  and `make monster-check` holds every line added to `agda/src` to its dependency
  CONE. Choose it as likely false as possible, as far DOWN the tree as possible,
  and with as big a blast radius as possible; depth is the pressure doing the
  selecting, since the other two are monotone up the tree and alone would always
  return the tier's top line. The floor under the descent is the cone itself, which
  is the commit licence. An exception is declared with an `also:` line, which is
  free of the section's prose budget because charging a ledger buys exceptions left
  undeclared rather than exceptions not taken.
- **EVERY TIER IS SORTED RISKIEST-FIRST, AND THE SORT IS AN INVARIANT —
  NOT A ONE-TIME TIDY.** Within a tier, rows appear
  in risk-class order: FALSITY, then SHAPE, then VACUITY, then DIFFICULTY,
  then GRINDABLE. **Re-sort in the SAME commit as any edit that could move a
  row** — a class raised or lowered, a postulate added, discharged, split, or
  renamed. A split is the easy one to miss: it can put a SHAPE child in a
  parent's GRINDABLE slot.
  **Why it is an invariant and not cosmetics:** the ledger's order is what the
  roadmap above it is drawn FROM, so a stale sort silently re-aims the next leg
  — and it re-aims it toward the SAFE end, because grinding is what
  looks like progress. A riskiest row buried below four safer ones goes
  untouched for exactly one reason: the list said it was ninth.
  **`make roadmap-check` ENFORCES THIS — it is part of `make gate`.** It fails
  the build when a tier's classes improve and then worsen, naming the row and
  the row it must move above. Order WITHIN a class is a judgement call and is
  deliberately NOT checked: if two rows share a class, order them by what
  unblocks more. A row naming no class is reported but not ordered, so an item
  cannot dodge the check by omitting its class.
  **It is machine-checked rather than trusted because the by-eye version is
  satisfiable while still failing** — a hand re-sort fixes the tier being
  looked at and silently leaves the others. `make roadmap-selftest` pins the failing
  path against fixtures, including the row that must NOT fire: a row whose
  prose mentions a better class later still reads at its declared one.
- **One line per item: name + risk class + hook.** The hook says where
  the risk lives and where the full story is (always a source header) —
  it does not TELL the story. An entry that has grown sentences of
  mechanism, receipts, or history is a header that leaked; move it to the
  postulate's header and cut the entry back to its line.
  **`make roadmap-check` ENFORCES A CHARACTER BUDGET on each row's PROSE**,
  names excluded, and over budget is a FAILURE. Names are free because the
  coverage rule below requires every scheduled postulate to be named — charging
  for them would put the two checks in conflict and the shorter file would win
  by deleting a name. The budget is set from the distribution and lives in
  `scripts/check-roadmap.py`; re-scan before moving it, since it is the GAP
  between the compliant rows and the leaked ones that makes it safe.
  A leaked row is not merely untidy: it puts the finding far from the postulate
  someone picks up six weeks later, which is the locality argument behind
  `-- DEAD ROUTE` running backwards.
- **The evidence field is DERIVED — never type it, run `make roadmap-evidence`.**
  Every classed row carries a backticked field directly after its risk class,
  naming the durable markers that row's postulates carry in their own source
  headers — `REFUTED`, `DEAD ROUTE`, `TWIN`, `PROBED`, `RECOVERY`, with `×N` for
  a repeat — or `NO EVIDENCE` when they carry none. **`make roadmap-check`
  RECOMPUTES IT and fails on any disagreement**, which is the only reason it is
  allowed to live here: a count is a function of the headers, not a copy of
  them, so the two cannot drift the way a duplicated receipt would. The blank is
  the point rather than a gap to fill — a row reading `NO EVIDENCE` says nobody
  has instantiated the statement, refuted a route through it, or found it a
  twin, and an unprobed probeable postulate is the cheapest unmanaged risk in
  the repo. It reads as nothing today only because absence had no marker.
- **The ledger is the source of truth, not this file.** `make postulates` lists
  every live postulate by name; every one of them appears in exactly one tier
  below, and a name here that no longer greps is a bug in this file — fix on
  sight. **`make roadmap-check` ENFORCES THE COVERAGE HALF** — a live postulate
  no row names fails the build, so a postulate cannot be added and never
  scheduled. Unscheduled debt is exactly the kind the wiring law exists to
  prevent, one level up: `make wiring` proves every postulate is CONSUMED, and
  nothing else proves any of them is PLANNED. Shorthand counts as naming —
  `{a,b}` expansion, `readme-*` globs, and a `-suffix` after a sibling in the
  same row — but a collective phrase does not: a row reading "nine postulated
  abstractions" names nothing the check can see.
- **There is no second roadmap.** Not a session task list, not a worker's
  notes, not a scratch file. A parallel list is outside the repo, so no gate
  and no `grep` can see it rot: it keeps its completed rows, it survives this
  file's rewrites, and it gets read in preference to this file because it is
  the one the session wrote. The tell is citing work by a NUMBER — names come
  from here and from the ledger, numbers come from somewhere that should not
  exist. Find it and delete it.

**The tier law and the risk classes are DEFINED IN CLAUDE.md** — the
lowest-numbered tier below finishes first, strictly, and an emptied tier is
DELETED rather than renumbered, so the numbers are names and not positions;
classes worst-first are FALSITY, SHAPE, VACUITY, DIFFICULTY, GRINDABLE. This
file only ASSIGNS them, and schedules them into legs. Read that section
before re-classifying anything: what counts as evidence for lowering a class, the
convergence test for whether a spawned FALSITY is progress, and why GRINDABLE is
the delegation boundary, all live there. A GRINDABLE row must name its worked
precedent in the postulate's own header — if the hook here cannot point at one,
the row is DIFFICULTY.


## The theorem chain (top → leaves)

```
formal-verification-batchSimultaneous    The-Proof.agda — a REAL body over
 │                                        three leaves
 ├─ batchSimultaneousᵖ                    Rx/Batch.agda — a REAL body:
 │                                        scan for the state, mergeMap→EMPTY
 │                                        for the silence — tier 2 finishes it
 ├─ batch-transcription                   that operator's run computes
 │                                        step-batch — tier 3
 └─ elaborated-accepted                   PROVEN, over run-wellFormed, whose
     └─ subscribe-shaped, cascade-shaped   two leaves are tier 3

  batch-agreement, batch-online           PROVEN; claimed by Main in their own
                                          right — nothing above consumes them

  evaluate↓ = proj₁ ∘ evaluate!           Rx/Evaluator/Builder.agda — REAL
     └─ every value-path leaf is a body; the corpus runs; the tower descends

  toPlain                                 Rx/Elaborate.agda — a REAL body,
                                          0 postulates

  every tier above is stated over Rx.Exp's syntax
```

The descent is the evaluator's own and is stated nowhere else: a Girard–Tait
reducibility candidate `Red`, recursing on the TYPE rather than on any measure
read off the program. The three edges no structural reading reaches — the μ
peel, the flattener's hop, a share's connect — are answered by it and by
nothing else; every other member of the subscribe cycle descends on a term or
shortens a list, which Agda reads for itself. The evaluator is `proj₁` of a
builder that returns a run together with its derivation, which is what let
every guard, every `<?` and the dry marker leave the machine entirely.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 1 — the plain evaluator mirrors rxjs

**THIS TIER HAS NOTHING TO DO WITH SRXJS.** No `SExp`, no elaboration, no
envelope, no simul variant of anything. The question is whether `Rx.Exp` and
its evaluator mirror plain rxjs, and the judge is the TypeScript differential
harness: `prop-test.ts` draws a program, runs it through ordinary rxjs
operators in `plain-eval.ts`, runs the same program
through the Agda evaluator reached via `CLI.Decode`, and compares two LISTS OF
VALUES exactly.

**DONE IS BOTH HALVES OF THE JOB GREEN AND THE TARGET BACK IN THE GATE.** The
random draw and the replay of the pinned corpus are separate steps and both
are red: 490 of 500 on the draw, 3 of 15 rows on the replay. Neither may be
narrowed to pass. What both contradict is the burst carrier rather than an
operator, and every failing case has ONE signature — the evaluator emits
nothing where rxjs emits — so that is one mechanism seen 12 times.

### The monster

`subscribeE⇓`'s burst carrier — a subscription's result is a LIST which its
caller pushes, rather than values reaching the root as produced. Everything
else in the evaluator is stated in terms of it, and a differential run has
contradicted it.

NARROWED TO A COUNT. A region-biased draw reaches it 8 times in 500 where the
old one reached 0; the evaluator fails all eight and 10 in all, a pushing
carrier fails none, and those rows are pinned, so the close is a count rather
than a memory.

NARROWED AGAIN, on the STATEMENT side. The relation now says the push, so the
carrier is no longer a question about shape. What is left is whether a tower
stands over it, and the store is where that bites.

NARROWED FROM THE OTHER END, AND THE TWO JUDGES NOW DISAGREE. The batching
carrier is refuted by the draw; the INLINE push is refuted by the descent — a
subscription that steps the frames of its own continuation writes a fold's
accumulator from inside itself, and four routes for carrying that obligation
are recorded dead in `Reducible.agda`. So what is left of the monster is not
whether values are pushed but whether a pushing carrier can avoid re-entering
a fold's own frame, which is a strictly smaller region than either judge has
ruled on.

also: `chainStep⇓`, `chainStep!` — the carrier is a batch on BOTH faces and only one of them is `subscribeE⇓`; a scheduled arrival folds its value and its end together for the same reason a subscription hands back a list, so the split separating them is the monster's fact landing off the monster's cone.

### Big picture tier roadmap

- **A CARRIER THAT DOES NOT RE-ENTER A FOLD'S OWN FRAME, MEASURED BEFORE IT IS
  PROVEN.** The inline push is refuted by the descent, not by the draw: four
  routes for carrying a fold's accumulator obligation are dead in
  `Reducible.agda`'s header. What the batching carrier had, and the whole of
  what the candidate spent it on, is that a subscription never stepped a frame
  of its own continuation. A TRAMPOLINED push — emissions queued at the
  outermost subscribe, drained in creation order — keeps the values the draw
  says the batch loses and may keep that property too. A carrier is cheap in
  the TypeScript, so settle it there: a reference beside `ref-push.ts`, same
  500-draw, same 15 rows. First — every leg below is stated over it.

- **THE FRESHNESS FACE GAINS THE PREMISE ANY PUSH OWES IT.** A pushing
  subscription writes the nodes its continuation's frames name, however the
  push is carried, so `subscribeE-preserves` is false as stated — refuted at
  the very fold the store question is about. The repair is the premise its
  frame-level members already carry, added across the family; `pushBurst⇓` has
  no subject left and its member goes. It is a leg rather than a fix-up
  because it is the one piece the carrier verdict cannot move, so it is the
  work that is safe to land while that verdict is being measured.

- **THE TOWER RE-THREADED ONTO WHATEVER CARRIER SURVIVES.** Not a re-shaping
  of results: under any push the subscribe cycle and the fold cycle are ONE
  cycle, spanning the candidate's module and the builder's, so the cut between
  them has to move before a clause can be typed. The measure the fan-out needs
  is written down in `Builder.agda`'s header — the count of shared slots not
  yet connected, above the floor the fold already runs on — and lands here,
  since nothing consumes a measure until the block it measures exists.

- **THE REFERENCE RETIRES WITH THE CARRIER.** `ref-eval.ts` is the burst
  machine, and the moment the Agda pushes it is a superseded predecessor —
  deleted, not parked, and `ref-push.ts` takes the `--machine ref` name so the
  transcription check keeps meaning what it says. It is its own leg because
  the check that entitles every measurement here is the one being rewired, and
  a leg that both moves the carrier and re-points its judge has nothing left
  to check itself against.

- **ENABLE THE ORACLE IN CI.** Flip the job off `if: false`. It is the leg
  that makes the tier STAY done: until it lands the sweep is a thing somebody
  remembers running, and a green memory is what this tier was disabled behind
  in the first place. `oracle` stays out of `GATE_CHEAP`, whose invariant is
  that nothing on it compiles, and this target links the CLI.

### The ledger

(empty — this tier states nothing in Agda, so it postulates nothing.)


## Tier 2 — finish `batchSimultaneousᵖ`

**THE OPERATOR HAS A BODY AND THE BODY IS HONEST ABOUT WHAT IT SKIPS.**
`Rx.Batch` is a `scanᵉ` carrying `BatchStᵗ` behind a `mergeAllᵉ` to `emptyᵉ` —
scan for the state, mergeMap→EMPTY for the silence, since a batcher is one
value in and ZERO OR ONE out. Two things are deliberately missing, both named
in that file: the owed/live arithmetic that decides WHEN an instant flushes,
and the final flush, `scanᵉ` having no end hook.

**DONE IS THE AGDA QUICKCHECK PASSING FULLY.** `QuickCheck.agda` draws an
`SExp`, runs the batching operator inside the machine, and compares against
`spec-batchSimultaneous` applied to the run without it — so it is exactly the
match this tier is for, and it decides the tier rather than merely informing
it.

**STOP AND REPORT if this work turns out to need a new former in `Rx.Exp`.**
Not a suspicion — only if there is provably no way around it. The vocabulary
is small on purpose and every addition is a forgery surface.

### The monster

(no monster) — the tier is one operator's body against one executable check.
There is no declaration here whose falsity a cone could bound.

### Big picture tier roadmap

- **THE OWED/LIVE ARITHMETIC INTO `BatchStᵗ`.** `Rx.Protocol`'s automaton run
  in producing mode: `live` as a `listᵗ uniqᵗ`, `owed` as a
  `listᵗ (uniqᵗ ×ᵗ natᵗ)`, both data, so both are `Ty`s and the carrier just
  grows fields. The pending slot is already where a flush announces itself, so
  this is filling in rather than reshaping. `settleBatch` / `applyBatch` /
  `paidOff` in `typescript/src/batch-simultaneous.ts` are the reference, and
  `Implementation.step-batch` is the Agda twin to agree with.

- **`complete` AS A FLUSH TRIGGER.** The missing end hook. `splitEventsᵛ`
  already returns the completion flag this code ignores, so the source's own
  completion can close the open batch — which is what `foldBatch`'s terminal
  `flushBatch` does over a list. Worth doing second: it is only observable
  once the owed arithmetic has stopped flushing late.

- **DRIVE THE QUICKCHECK TO GREEN.** The sweep can RUN now — the GHC backend
  had nothing to compile while the operator was a postulate, so this leg is
  the first time the match has ever been executed. Expect the first failures
  to be in the generator's reach rather than in the operator, and cache
  counterexamples as rows in `Implementation.Unit-Test` as they are found.

- **ENABLE THE QUICKCHECK IN CI.** Flip its job off `if: false`. Its own note
  gives two reasons for the disable and BOTH are now spent — the machine it
  swept has been replaced and the replacement runs, and the elaborator arm it
  named as permanently red is no longer a postulate. What keeps it off is the
  operator, so this is the leg that closes the tier: the check that decides
  tier 2 is the check that then guards it. Nothing in the job may be narrowed
  to make it pass.

### The ledger

(empty — `batchSimultaneousᵖ` is a definition, not a postulate.)


## Tier 3 — the two run leaves, and the transcription

**THIS IS WHERE THE SRXJS OPERATORS ARE ACTUALLY JUDGED.** `cascade-shaped` is
one cascade emitting a well-shaped burst and preserving `Owes`, and its
per-former split is the whole content: `map-f` and `scan-f` are cheap, and the
traffic-bearing frames — the cut, the three flatteners, a share's connect —
are the operators this proof exists to judge.

**EXPECT THE ELABORATION TO MOVE, AND PLAN FOR IT.** Writing the proof will
find things the implementation has wrong, and fixing the implementation will
find things the proof has wrong. That cycle is the work, not an interruption
to it — but it is also the failure mode, so report if it starts spiralling out
rather than in.

**STOP AND REPORT if this needs a new former in `Rx.Exp`** — same bar as tier
2: only on certainty, never on suspicion. `Run-Well-Formed`'s BOUNDARIES
header carries the other stop conditions.

### The monster

`Owes` — `Run-Well-Formed.agda`. It is the single place the evaluator's state
reaches the wire, its own header says "expect it to be wrong in detail and
corrected by contact", and it replaced four guessed invariants that
measurement refuted. Every row in this tier routes through it, and it is a
definition rather than a postulate, so its cone is real.

### Big picture tier roadmap

- **`Owes` UNDER CONTACT, AT THE FIRST TRAFFIC-BEARING FRAME.** The monster,
  and the one thing worth attacking before anything is ground. Its two sides
  count in different namespaces — `chainsOf` over registry rows carrying the
  evaluator's dynamic source ids, `ProtocolSt.live` over announces carrying the
  ids `mintᵉ` bound — and measured, those differ. So the equation holds only if
  an arrival carries the WIRE's naming, which is a requirement on the
  elaboration that nothing yet discharges. Settle it at a cut or a share's
  connect, where a node is read back out of the registry; do not settle it on
  `map-f`, which cannot tell the two readings apart.

- **THE mergeAll-LOCALITY LEMMA, WHICH TWO ROWS WANT.** `batchSimultaneousᵖ`
  is now `mergeAllᵉ ∘ mapᵉ ∘ scanᵉ`, so neither `batch-transcription` nor
  `cascade-shaped` can treat a flattener as schedule-free any more. The fact
  to prove: `hasRoom nothing active = true`, so at unlimited concurrency
  nothing is ever queued and each synchronous inner drains inside the cascade
  that opened it. Cheap, and it unblocks both.

- **`cascade-shaped`'S CHEAP ARMS, TO FIX THE SHAPE.** `map-f` and `scan-f`
  leave `sched` and `st` untouched. Landing them first is not grinding for its
  own sake: it forces the per-former statement into its final form against
  arms whose content is nil, so the traffic-bearing arms are written against a
  shape that has already survived contact.

- **THE TRAFFIC-BEARING FRAMES, AND THE ELABORATION CHANGES THEY FORCE.** The
  cut, the three flatteners, a share's connect. This is the leg where the
  virtuous cycle is expected to run, so it is also where the spiral is
  expected if there is one — cut it into commits by FORMER, and report rather
  than push if two consecutive formers each undo the previous one's fix.

- **`batch-transcription` OVER THE FINISHED OPERATOR.** Blocked until tier 2
  lands: the equation's right side is `foldBatch`, whose flush points the
  current body does not have, so the statement is FALSE rather than merely
  unproven. Its header says so.

- **`subscribe-shaped` LAST.** Deliberately. `st-init`'s registry and
  `protocol-init`'s live set are both empty, so the seed is trivial and the
  content is what the subscribe walk installs on the way down — which is a
  strictly smaller question once `cascade-shaped` has settled what a
  well-shaped burst and a preserved `Owes` actually are.

### The ledger

- **`batch-transcription`** (The-Proof) — FALSITY, `NO EVIDENCE`: false against
  the landed operator until tier 2 finishes it; its locality argument also
  needs re-establishing over `mergeAllᵉ`.
- **`cascade-shaped`** (Run-Well-Formed) — SHAPE, `NO EVIDENCE`: the per-former
  split, and the `EvalSt` node-provenance invariant it is probably still
  missing.
- **`subscribe-shaped`** (Run-Well-Formed) — SHAPE, `NO EVIDENCE`: trivial seed,
  content is what the walk installs — but its `Owes` conclusion carries the
  monster's own recorded gap, so the class is the gap's and not the grind's.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.
