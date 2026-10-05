# PROOF-STATE — the roadmap

**What this file is.** The ordered worklist for the one goal: discharging the
top-line statement modules (`Left-To-Right`, `Timed`, `Batchable`) — no
postulates, everything typechecks. This file holds the SCHEDULE — each tier's
next legs — over a LEDGER of one-line hooks; everything else lives in the
code.

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
lowest-numbered tier below finishes first, strictly;
classes worst-first are FALSITY, SHAPE, VACUITY, DIFFICULTY, GRINDABLE. This
file only ASSIGNS them, and schedules them into legs. Read that section
before re-classifying anything: what counts as evidence for lowering a class, the
convergence test for whether a spawned FALSITY is progress, and why GRINDABLE is
the delegation boundary, all live there. A GRINDABLE row must name its worked
precedent in the postulate's own header — if the hook here cannot point at one,
the row is DIFFICULTY.


## The theorem chain (top → leaves)

```
Main                                     four top-line statements, claimed
 │                                        side by side, meeting in raw values
 ├─ left-to-right                         Left-To-Right/Statement.agda — the
 │   │                                    batches, joined, are the plain
 │   │                                    program's values — tier 2
 │   ├─ simulation                        Simulation/Statement.agda — the
 │   │   │                                impl's run is the plain run, each
 │   │   │                                value named by its arrival
 │   │   └─ arrival-runs                  each plain arrival one impl
 │   │       │                            arrival, one instant to it
 │   │       └─ correspondence            schedules in step, stores related
 │   │           ├─ machines              the stores' relation, kept by each
 │   │           │                        subscribe and cascade
 │   │           └─ cascade-mono          no cascade runs a counter back
 │   └─ batched-sandwich                  the batcher against its own run
 ├─ timing-correct                        Timed/Timing-Correct.agda — stamps
 │   │                                    group emits as the timed
 │   │                                    translation's packets do — tier 2
 │   ├─ simulation                        at the timed program
 │   └─ packets-name-arrivals             one packet per plain arrival
 ├─ batchable                             Batchable/Statement.agda — a second
 │                                        evaluator running the batcher over
 │                                        the run's emits gives the spec's
 │                                        grouping of them — tier 2
 └─ timed-faithful                        Timed/Faithful.agda — the timed run
                                          carries the plain run's values — tier 2

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

## Tier 2 — proving the spec

**WHERE THE IMPLEMENTATION IS ACTUALLY JUDGED.** Every row is a top-line
statement or a leaf one is assembled over. Expect the
elaboration and the batcher to move under contact, and report rather than push
if that starts spiralling out rather than in.

**`Rx.Exp` AND `SExp.Syntax` ARE OFF LIMITS (Anthony).** Both are fixed; a
proof that needs either to move is a question for Anthony, never a patch.
`make quickcheck`, locally or in CI, decides all four statements, the
simulation and its leaf on drawn programs, and a case past its clock is
undecided, never a failure (Anthony).

### The monster

`simulation` — what both top lines stand on, by induction on
arrivals over `correspondence`: schedules in step, pops partnered, stores related; the root
subscribes set them (`subscribe-related`) and each cascade keeps
(`cascade-related`), both sending agreeing values in one instant. RULED
OUT: an impl arrival the plain schedule lacks, a split arrival, a gap or
stray in a cascade's instant, an echo apart from its inners; a subscribe
installing a run the relation lacks (hot, cold, deferred read,
one-lane merge); a pop unrelating a read; a map moving an instant; a close
emptying a merge its rows name; a hot end past its block.
Left: a deeper flattener's subscribe, and which former's cascade breaks it.

also: `main` — the QuickCheck's entry point, and every generator and decider it calls: the sweep is how this tier's monster is measured, and no proof reads it.

### Big picture tier roadmap

- **SPLIT THE CASCADE PER PATH CONSTRUCTOR.** The subscribe half walks the
  program, one arm per former, `walk-flatten` its riskiest. A minted source's
  chain is `path-pass`, one arm per plain frame; a hot slot's is `fan-go` over
  the share's readers, paired by the proven `slot-chains`, after `hot-start`
  and `hot-end-start` find the impl's one raw chain by the store's census. Both ends drop
  alike: `finish-store` and `hot-finish` are proven, and a connected hot
  end's store is proven over the evaluator's `hot-block-end`. Left: the arms as real bodies, riskiest first, each owing the
  store's `swept` and the arrival's `lists` persisted, and `lane-arm` over
  `inner-arm` once `Arm` carries an impl-only step; the monster drops to
  whichever arm fails.

- **SPLIT THE INSTANTS PER FORMER.** An arrival's values carry one
  instant and no two arrivals share one: `cascade-stamps`, a claim the
  impl's cascade makes one former at a time. State it beside the values split so both recurse on the same
  configuration, and the monster drops to whichever stays riskier.

- **ONLY THEN GRIND THE REST.** The per-former leaves by a two-run
  relation recursing on the type as `Red` does, reusing its descent for
  the μ peel, the flattener's hop and a share's connect; the batcher's
  leaves are list lemmas. A case the impl's one-past fuel slack in
  `left-to-right` does not cover is a fuel finding for Anthony, not a
  restatement.

### The ledger

- **`hot-block-end`** (Simulation.Hot-End) — FALSITY, `NO EVIDENCE`: a block
  no live row threads runs its end into the share writing only its own nodes,
  which stay a block; schedule and every other part of the state stand.
- **`outer{Elem,Explode}-arm`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: an
  outer's step on both sides; the explode hands the flattener every inner a
  sync outer subscribed before the step returns.
- **`{inner,lane,deferInner}-arm`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`:
  leaving an inner, the flattener's lane, an impl-only lane merge ahead of it
  and a deferred body's hop.
- **`{block,hop}-arm`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: a cold
  chain's input block hands its path the popped head; a deferred hop subscribes
  its body on both sides.
- **`{scan,take,takeWhile}-arm`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: a
  cell, count or test steps alike on both sides; a cut takes rows on both.
- **`sink-pass`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: a group reaching
  a shared slot's subject fans out to related readers on both sides.
- **`root-values`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: a group's emits
  sent to the root read as the plain group's values.
- **`hot-block`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: a connected hot
  slot's raw row steps its input block alone and hands the share one emit
  carrying the value; the plain side does not move.
- **`read-arm`** (Simulation.Pass) — FALSITY, `NO EVIDENCE`: a slot reader's
  restamp moves the impl alone and keeps the emit's values.
- **`init-{numbers,distinct}`** (Simulation.Walk) — FALSITY, `NO EVIDENCE`: the
  hot scripts live before anything is subscribed are numbered by their slots,
  one per slot.
- **`cascade-stamps`** (Simulation.Statement) — FALSITY, `NO EVIDENCE`: an impl
  cascade's values carry one instant between the counters it enters and leaves.
- **`walk-*`** (Simulation.Walk) — FALSITY, `PROBED×7`: one former's subscribe
  keeps the stores related; holds at a hot, cold and deferred read. Riskiest is
  `walk-flatten`, past the typechecker: a one-lane merge only in normal form.
  No take, scan or `μ` run.
- **`lifts-map`** (Simulation.Walk) — FALSITY, `PROBED`: the elaborated map
  step keeps an emit's instant and maps its payloads as the plain map does.
- **`init-{sources,sync}`** (Simulation.Walk) — FALSITY, `PROBED×2`: the hot
  scripts live before anything is subscribed are related and in step, source
  for source; one hot script only, so no rank compared.
- **`subscribe-stamps`** (Simulation.Statement) — FALSITY, `PROBED`: the root
  subscribes send under one instant below the clock; holds at an `of` of one
  and two values. A cold read's decode is past the typechecker.
- **`batched-sandwich`** (Left-To-Right.Statement) — DIFFICULTY,
  `REFUTED, PROBED`: the unbatched values between the joined run at a batcher
  fuel never less and one past it; the sweep, deciding it directly, reached
  held-back values under a flattener with no red.
- **`timed-faithful`** (Timed.Faithful) — DIFFICULTY, `PROBED`: probed
  first-order; the sweep, deciding it directly, reached values on two arrivals
  under a flattener with no red.
- **`batchable`** (Batchable.Statement) — DIFFICULTY, `PROBED`: probed
  first-order; the sweep, deciding it directly, reached values grouping under a
  flattener and a `μ` with no red.
- **`packets-name-arrivals`** (Timed.Timing-Correct) — DIFFICULTY, `PROBED`:
  one packet per arrival, injectively; the sweep, deciding it directly, reached
  values on two arrivals under a flattener with no red.
- **`cascade-mono`** (Simulation.Statement) — GRINDABLE, `TWIN`: a cascade
  never runs a mint counter back.
- **`cascade-latched`** (Simulation.Statement) — GRINDABLE, `TWIN`: a cascade
  never unlatches a completed source.
- **`renExp-id`** (Simulation.Walk) — GRINDABLE, `TWIN`: renaming by the
  identity is the identity, the impl's mint body against its elaboration.
