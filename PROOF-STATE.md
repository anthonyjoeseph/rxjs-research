# PROOF-STATE — the roadmap

**What this file is.** The ordered worklist for the one goal: discharging the
three tiers below — no postulates, everything typechecks. This file holds the SCHEDULE — each tier's
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
  definition it is about — failed routes (`-- DEAD ROUTE`), proof sketches, coverage residue, recovery pointers.
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
  conjunct`), source section numbers ("§ 5a" — say the postulate's name).
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
- **EVERY TIER IS SORTED RISKIEST-FIRST, AND THE SORT IS AN INVARIANT —
  NOT A ONE-TIME TIDY.** Within a tier, rows appear
  in risk-class order: FALSITY, then GRINDABLE. **Re-sort in the SAME commit as any edit that could move a
  row** — a class raised or lowered, a postulate added, discharged, split, or
  renamed. A split is the easy one to miss: it can put a FALSITY child in a
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
  headers — `REFUTED`, `DEAD ROUTE`, `TWIN`, `RECOVERY`, with `×N` for
  a repeat — or `NO EVIDENCE` when they carry none. **`make roadmap-check`
  RECOMPUTES IT and fails on any disagreement**, which is the only reason it is
  allowed to live here: a count is a function of the headers, not a copy of
  them, so the two cannot drift the way a duplicated receipt would. The blank is
  the point rather than a gap to fill — a row reading `NO EVIDENCE` says nobody
  has refuted a route through the statement or found it a twin.
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
classes worst-first are FALSITY, GRINDABLE. This
file only ASSIGNS them, and schedules them into legs. A GRINDABLE row names
its proven precedent in the postulate's own `TWIN:` — if the hook here cannot
point at one, the row is FALSITY.


## Tier 1 — the adequacy theorem

**THE LINK.** `adequacy`: the pure run's limit is the fold's meaning observed
at the root, positions forgotten down to ticks. SAFETY, every prefix placed
against the meaning's events, is a body: SORTED (`adequacy.Sorted`, the
machine alone) and ALIKE as sets (`content`) is placed (`placing`). LIVENESS
is by an item's depth, then the witness's `measure` (`adequacy.Progress`).
Sortedness rides SCOPED positions: `under l m k` runs `m` at
`pos ++ [l]` and puts `pos` back, so the run's positions are a tree's
pre-order; each kernel is well-positioned (`Well`, unary) given its
observer is; `preserve` is the tree walk, the timers and the loop's turn,
a body: a turn opens an epoch at its timer's cascade, and setting a timer
moves the last to where it was set, so same-tick timers pop in order.
Content rides a GHOST, the meaning's own configuration, which the machine's
runs; at the launch its residual is the events (`begun`, by `subscribed`).
Only re-entry configurations are related to the ghost; the rest reach one
by their own silent steps (`Mirror`).

### Big picture tier roadmap

- **B. THE LOCAL INVARIANT.** Each field of `Carried` a fold over the tree
  of node-local predicates reading only the node's `names`, with one
  framing lemma per field over `Local`'s `Alike` and `Off`: a store at a
  node's own name keeps every other node's predicate, so a step owes only
  its node's fact. `climb-scan` is a body over the `scan-*` framing
  leaves; next `close-outer`, `close-lanes`, `close-source` the same way.
  Decides whether the four writes fall with only node-local leaves;
  `scan-behind` is the whole-tree one, a part's head bounded by its
  children's, and surviving as one is the finding. Done when the
  framing leaves are proven.
- **C. THE CALLBACK RELATION.** One per-operator lemma: an observer at a
  path, run from a related state, reaches a related state with the ghost
  advanced, by recursion up the path. `Climbing` and `Closing` become one
  record over it, `climb` and `close` its two instances. Decides whether
  every mid-climb state is the callback relation's, so no third record is
  ever needed. Done when `climb` and `close` are bodies over it and the
  old records are deleted.
- **D. THE KERNEL FOOTPRINT.** A kernel's cells allocated together and read
  only through its own node, `names` agreeing by construction. `names`
  already lists each node's cells, so this leg is CONDITIONAL: done when
  B's framing names no kernel cell read from outside its node, or when
  that kernel is regrouped through the engine workflow (Agda, QuickCheck,
  TypeScript, oracle). Decides whether the engine needs to move at all.

### The ledger

- **`under-shown-connect`** (Placed) — FALSITY, `RECOVERY`, `X`: no step a
  connect's body shows or leaves lies under where a source step shows.
- **`step-skips`** (Stepper) — FALSITY, `REFUTED×2, DEAD ROUTE, RECOVERY×2`,
  `X`: a sane, placed root ghost's meaning is what its step shows, then the
  stepped node's.
- **`within-step`** (Stepper) — FALSITY, `REFUTED×2`, `X`: a sane, placed root
  ghost's step leaves its parts placed.
- **`close-source`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's source
  ended closes its subject, its subscribers' finish owed.
- **`close-lanes`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane ended shuts,
  refills, or ends the flatMap past its outer's end.
- **`close-outer`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's outer ended
  settles: the flatMap ends with no lane left, or runs on.
- **`take1-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a takeWhile's
  completion begun under its failing value, its cut the frame's rest.
- **`last-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a spent `of`'s
  completion begun at its end.
- **`fin-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's feed of its
  source's end, nothing left or the next subscriber's completion begun.
- **`note-least`** (Lift) — FALSITY, `NO EVIDENCE`: a note records the least
  value the ghost holds.
- **`turn-dry`** (Lift) — FALSITY, `NO EVIDENCE`: nothing held and no timer
  queued, the ghost shows nothing.
- **`spread-past`** (Lift) — FALSITY, `NO EVIDENCE`: no sibling an open
  `of`'s path passes heads under its base; what a source fed, joiners took.
- **`behind-fire`** (Lift) — FALSITY, `NO EVIDENCE`: a timer popped at the
  turn, its fired cold heads no earlier than the run.
- **`shut-step`** (Lift) — FALSITY, `NO EVIDENCE`: a connect past its
  source's end, an `of` in its body: the body shut steps as it does, shut
  after.
- **`emit-run`** (Lift) — FALSITY, `NO EVIDENCE`: an open `of`'s value
  handed on under its scope, the climb starts aloft.
- **`take-end`** (Lift) — FALSITY, `NO EVIDENCE`: an exclusive take's
  failing value lands at its completion owed, the ghost alike, a stage on.
- **`take-out`** (Lift) — FALSITY, `NO EVIDENCE`: an inclusive take's
  failing value climbs under `ix 0`, the take ending where the run is.
- **`emit-void`** (Lift) — FALSITY, `DEAD ROUTE`: an `of` the ghost does not
  hold emits to a guard that drops it, the ghost alike, a value fewer.
- **`climb-lanes`** (Lift) — FALSITY, `NO EVIDENCE`: a lane's value climbs
  into its flatMap through `wkObs same`, equal up to `≗`.
- **`scan-behind`** (Frame) — FALSITY, `NO EVIDENCE`: the parts above a
  written accumulator still head no sooner than the run.
- **`scan-lifts`** (Frame) — FALSITY, `NO EVIDENCE`: a lift above a scan
  survives a write at its accumulator.
- **`scan-owned`** (Frame) — FALSITY, `NO EVIDENCE`: `Owned` survives a write
  at a scan's accumulator.
- **`scan-kernels`** (Frame) — FALSITY, `NO EVIDENCE`: `Kernels` survives a
  write at a scan's accumulator.
- **`scan-meaning`** (Frame) — FALSITY, `NO EVIDENCE`: `Meaning` survives a
  write at a scan's accumulator.
- **`scan-queue`** (Frame) — FALSITY, `NO EVIDENCE`: `Queue` survives a write
  at a scan's accumulator.
- **`climb-outer`** (Lift) — FALSITY, `NO EVIDENCE`: an outer value opens a
  lane and stops at the subscription it begins.
- **`climb-source`** (Lift) — FALSITY, `NO EVIDENCE`: a connect source's
  value feeds its subject's joiners and stops there.
- **`emit-shut`** (Lift) — FALSITY, `NO EVIDENCE`: an `of` whose observer
  path is closed skips its value.
- **`sub-onward`** (Lift) — FALSITY, `NO EVIDENCE`: a subscription begun
  runs its kernel to the next re-entry state.
- **`feed-onward`** (Lift) — FALSITY, `NO EVIDENCE`: the rest of a connect's
  feed of a value, each subscriber showing or skipping it.
- **`src-onward`** (Lift) — FALSITY, `NO EVIDENCE`: a connect's source
  subscribed once its body is.
- **`kont-onward`** (Lift) — FALSITY, `NO EVIDENCE`: a subscription's
  continuation stashes its unsubscribe, a call fewer.
- **`burst-poll`** (Lift) — FALSITY, `NO EVIDENCE`: a live burst's sink
  polled, open to play or closed and dropped.
- **`burst-play`** (Lift) — FALSITY, `NO EVIDENCE`: a polled burst's frame
  played, a value run on, a stall passed, a close scheduled.
- **`placing`** (Adequacy) — FALSITY, `NO EVIDENCE`: an ascending record alike
  a program's events as a set is placed against them.
- **`ticks-up`** (Adequacy) — FALSITY, `RECOVERY`: the meaning's ticks never
  fall.

## Tier 2 — the simultaneous spec

**THE STATEMENT.** Define the new "simultaneous" spec over the denotation,
adapted from the old `agda/` tree's statement modules (reference only). No
rows until the statements exist; each lands as a postulate here.

## Tier 3 — the simultaneous spec, proven

**THE PROOF.** Discharge Tier 2's statements using the denotation and
`adequacy`. No rows until Tier 2 states them.
