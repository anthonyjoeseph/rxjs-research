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
formal-verification-batchSimultaneous    The-Proof.agda — three statements
 │                                        side by side, meeting in raw values
 ├─ input-well-formed                     REAL body: the impl run is WellFormed
 │   ├─ arrival-same, arrival-distinct, arrival-ends       tier 3
 │   └─ run-wellFormed                    PROVEN over its two leaves
 │       └─ subscribe-shaped, cascade-shaped               tier 3
 ├─ plain-agrees                          the run's values are the plain
 │                                        program's, per arrival — tier 3
 └─ batch-agrees                          over any WellFormed run, the batcher
                                          gives the spec's batches — tier 3

  wf-batches, wf-arrival-batch,           PROVEN; the README's semantics over
  spec-preserves-order                    the spec, claimed by Main
  batch-online                            PROVEN; claimed by Main

  evaluate↓ = proj₁ ∘ evaluate!           Rx/Evaluator/Builder.agda — REAL
     └─ every value-path leaf is a body; the corpus runs; the tower descends

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

## Tier 2 — an impl envelope the spec batches agree with

**THE BOUNDARY: `Rx.Exp`, its `Ty`/`Tm` language, `Rx.SExp` and the evaluator
are OFF LIMITS (Anthony).** If there is CONVINCING PROOF that the tier cannot
close without changing one of them, STOP and report that proof. The envelope's
shape is free; TypeScript is out of scope this tier (Anthony).

The top line is three statements over the impl run, and `QuickCheck` decides
each on random programs, `WellFormed` field by field. **DONE IS THE AGDA
QUICKCHECK PASSING FULLY**, driven by `make qc-fast`. Dead routes go in
`Rx.Envelope`'s header; counterexamples go in the bug cache.

### The monster

(no monster) — the tier is one operator and its envelope against one
executable check. There is no declaration here whose falsity a cone could
bound.

### Big picture tier roadmap

- **ONE INSTANT PER SUBSCRIBE FRAME, AND A CASCADE INHERITS ITS TRIGGER'S.**
  The QuickCheck's SAME rows are a share's connect minting its own instant
  inside the subscribe frame, and a spawned inner stamped with the subscribe
  instant rather than its trigger's; DISTINCT, WF and every FAIL so far fall
  on the same rows (bug-cache `seed 9 depth 1 case 2`, `seed 2 depth 1
  case 15`). Fix the elaboration's stamping.

- **THE ELABORATED `switchAll` AND `exhaustAll` KEEP WHAT PLAIN RXJS DROPS.**
  The PLAIN rows: a switched-away inner stays subscribed (`seed 6 depth 1
  case 4`), and an inner arriving while one is live is not dropped (`seed 7
  depth 1 case 12`). Mirror the plain formers' bookkeeping in the envelope.

- **MARK WHERE EACH INSTANT ENDS — POSSIBLY A QUESTION FOR ANTHONY.** ENDS
  fails on nearly every run: a subscribe-kind instant owes nothing, and
  `paidOff []` is false. The same mark is what batching a later arrival
  needs (bug-cache row 4); the four routes tried are dead routes in
  `Rx.Envelope`'s header, and what is left may move `Rx.Exp` or the evaluator.

- **HOLD `qc-fast` GREEN UNDER THE 2-MINUTE CAP (Anthony), ON EVERY CHECK.**
  Depth 1 is the sweep that fits, and some programs cost exponentially in
  fuel, so a sweep bounds each CASE in wall clock
  (`typecheck-performance-numbers.md`). Every counterexample becomes a
  bug-cache row first. Three rows — an `of` pair merged inside a
  delivery's inner — give no verdict in 60 s even at fuel 1, while the
  same programs read plain run at once: the cost is the ELABORATION's.

- **ENABLE THE QUICKCHECK IN CI.** Flip its job off `if: false` and build it
  from the oracle's tree, as `qc-build` does. This leg closes the tier: the
  check that decides tier 2 then guards it. Nothing in the job may be
  narrowed to make it pass.

### The ledger

(empty — the tier's work is definitions, not postulates.)


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
  connect, where a node is read back out of the registry.

- **THE mergeAll-LOCALITY LEMMA.** `batchSimultaneousᵖ` is
  `mergeAllᵉ ∘ mapᵉ ∘ scanᵉ`, so `cascade-shaped` cannot treat a flattener as
  schedule-free. The fact to prove: `hasRoom nothing active = true`, so at
  unlimited concurrency nothing is ever queued and each synchronous inner
  drains inside the cascade that opened it. Cheap, and it unblocks the arms.

- **`cascade-shaped`'S CHEAP ARMS, TO FIX THE SHAPE.** `map-f` and `scan-f`
  leave `sched` and `st` untouched. Landing them first forces the per-former
  statement into its final form against arms whose content is nil, so the
  traffic-bearing arms are written against a shape that survived contact.

- **THE TRAFFIC-BEARING FRAMES, AND THE ELABORATION CHANGES THEY FORCE.** The
  cut, the three flatteners, a share's connect — the frames tier 2's SAME and
  PLAIN rows fall on. Cut it into commits by FORMER, and report rather than
  push if two consecutive formers each undo the previous one's fix.

- **`batch-agrees` OVER THE REPLAY.** Its run is a hot script, one delivery
  per emit, so the batcher's run is one flattener over one scan — the shape
  the recovered `fold-agree` proved against a grouping spec. Probe the replay
  on the tier's bug-cache runs before any grind.

- **`subscribe-shaped` LAST.** Deliberately. `st-init`'s registry and
  `protocol-init`'s live set are both empty, so the seed is trivial and the
  content is what the subscribe walk installs on the way down — a strictly
  smaller question once `cascade-shaped` has settled what a well-shaped burst
  and a preserved `Owes` actually are.

### The ledger

- **`arrival-same`** (The-Proof) — FALSITY, `NO EVIDENCE`: QuickCheck finds two
  instants in one arrival on today's impl; tier 2's first leg.
- **`arrival-distinct`** (The-Proof) — FALSITY, `NO EVIDENCE`: falls on the
  same rows as `arrival-same`.
- **`arrival-ends`** (The-Proof) — FALSITY, `NO EVIDENCE`: false at every
  subscribe frame today; tier 2's end-mark leg.
- **`plain-agrees`** (The-Proof) — FALSITY, `NO EVIDENCE`: the elaborated
  `switchAll`/`exhaustAll` disagree with plain rxjs; tier 2's second leg.
- **`subscribe-shaped`** (Run-Well-Formed) — FALSITY, `NO EVIDENCE`: the
  QuickCheck's WF rows break acceptance inside the subscribe frame.
- **`cascade-shaped`** (Run-Well-Formed) — FALSITY, `NO EVIDENCE`: WF rows
  break acceptance in later arrivals too.
- **`batch-agrees`** (The-Proof) — FALSITY, `NO EVIDENCE`: nothing has
  instantiated the replay.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.
