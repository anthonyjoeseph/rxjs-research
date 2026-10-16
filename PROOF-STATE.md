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

- **C. THE CALLBACK RELATION.** `Calling` is one record over the signal
  climbing, a value or an end with its calls owed, and `call` its one
  recursion, by `call-step` over one lemma per operator. Ruled out: a
  third mid-call state.
  An operator's call is reads, writes and a RESTAGE of its node,
  node-local but for carrying stack, calls and agenda across it: a
  take's stage, a connect's feed, a flatMap's pool, its admit by
  policy, a lane's end down to its refill's send. Every guard read open
  by `calling-open`. Remaining: `lane-dequeue`, the queue read then settle or start;
  `outer-start`, which allocates, so it waits on a strong tree's
  transport along `_⊑_` that `sub-onward` and a dequeue's start owe too.
- **UP-ENDED.** `up-ended` is a body: the rest's skips by `Each.rests`,
  the shut body by `shut-heads` over what it tells. Ruled out: the end
  signal's fields carrying it; the non-local residue is `tells-past`,
  which `shut-step` reads too. Decides whether `tells-past` is a field
  `Carried` owes, every producer framing it, or follows from `Owned`'s
  finishes and the agenda's placement.
- **B. THE LOCAL INVARIANT.** Each field of `Carried` a fold over the tree
  of node-local predicates, one framing lemma per field over `Alike` and
  `Off`. Ruled out for the scan: a write needs no non-local leaf but
  `tells-past`. Remaining: an own-cell apartness fold carrying
  `scan-defined`, `scan-owned`, `scan-meaning`, `scan-sees`; `up-outer`
  and `up-lanes` by a flatMap head bound; then `lane-dequeue` and
  `close-outer`'s `sd-*` the same way, in the form C consumes.
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
- **`lane-dequeue`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane's freed slot
  handed on settles the flatMap, or begins the next queued value's lane.
- **`calling-open`** (Climbs) — FALSITY, `NO EVIDENCE`: a climbing signal's
  path reads open.
- **`outer-start`** (Climbs) — FALSITY, `NO EVIDENCE`: an admitted value with
  room begins a lane, the run at its pending node, the ghost past the skip.
- **`outer-switch`** (Climbs) — FALSITY, `NO EVIDENCE`: a switch kills its
  lanes, their rests the pool's, and begins one.
- **`outer-queued`** (Climbs) — FALSITY, `NO EVIDENCE`: a full bounded merge
  queues the value, the ghost past the skip.
- **`outer-drop`** (Climbs) — FALSITY, `NO EVIDENCE`: a busy exhaust drops the
  value, the ghost past the skip.
- **`active-lanes`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's count reads
  zero exactly when no lane is live.
- **`pool-ghost`** (Climbs) — FALSITY, `NO EVIDENCE`: an outer ended with lanes
  or a queue left: the pool restaged, the ghost past the outer's skip.
- **`pool-calls`** (Climbs) — FALSITY, `NO EVIDENCE`: the calls owed carry
  across a flatMap's pool restaged.
- **`pool-stack`** (Climbs) — FALSITY, `NO EVIDENCE`: a stack against the tree
  stands against it with a flatMap's pool restaged.
- **`pool-ticked`** (Climbs) — FALSITY, `NO EVIDENCE`: the stack ticks as it did
  with a flatMap's pool restaged.
- **`pool-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: `Owned` holds with a
  flatMap's pool restaged.
- **`pool-kernels`** (Climbs) — FALSITY, `NO EVIDENCE`: `Kernels` survives a
  flatMap's pool restaged.
- **`pool-meaning`** (Climbs) — FALSITY, `NO EVIDENCE`: `Meaning` survives a
  flatMap's pool restaged.
- **`pool-queue`** (Climbs) — FALSITY, `NO EVIDENCE`: `Queue` survives a
  flatMap's pool restaged.
- **`pool-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no
  sooner than the run with a flatMap's pool restaged.
- **`sd-active`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves its count.
- **`sd-fifo`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done flag
  leaves its queue.
- **`sd-part`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done flag
  leaves every part.
- **`sd-lifts`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves every lift.
- **`sd-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves `Owned`.
- **`sd-kernels`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves `Kernels`.
- **`sd-meaning`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves `Meaning`.
- **`sd-queue`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves `Queue`.
- **`sd-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: writing a flatMap's done
  flag leaves every part's head.
- **`take1-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a takeWhile's completion
  begun under its failing value, its cut the frame's rest.
- **`last-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a spent `of`'s completion
  begun at its end.
- **`fin-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's feed of its
  source's end, nothing left or the next subscriber's completion begun.
- **`note-least`** (Lift) — FALSITY, `NO EVIDENCE`: a note records the least
  value the ghost holds.
- **`turn-dry`** (Lift) — FALSITY, `NO EVIDENCE`: nothing held and no timer
  queued, the ghost shows nothing.
- **`spread-past`** (Lift) — FALSITY, `NO EVIDENCE`: no sibling an open `of`'s
  path passes heads under its base; what a source fed, joiners took.
- **`behind-fire`** (Lift) — FALSITY, `NO EVIDENCE`: a timer popped at the
  turn, its fired cold heads no earlier than the run.
- **`shut-step`** (Lift) — FALSITY, `NO EVIDENCE`: a connect past its source's
  end, an `of` in its body: the body shut steps as it does, shut after.
- **`emit-run`** (Lift) — FALSITY, `NO EVIDENCE`: an open `of`'s value handed
  on under its scope, the climb starts aloft.
- **`end-stack`** (Climbs) — FALSITY, `NO EVIDENCE`: a stack against the tree
  stands against it with a take restaged `ending`.
- **`end-ticked`** (Climbs) — FALSITY, `NO EVIDENCE`: the restaged stack ticks
  as the stack did.
- **`end-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: `Owned` holds of the take
  restaged `ending`, its completion the one call owed.
- **`end-kernels`** (Climbs) — FALSITY, `NO EVIDENCE`: `Kernels` survives a
  take restaged `ending`.
- **`end-meaning`** (Climbs) — FALSITY, `NO EVIDENCE`: `Meaning` survives a
  take restaged `ending`.
- **`end-queue`** (Climbs) — FALSITY, `NO EVIDENCE`: `Queue` survives a take
  restaged `ending`.
- **`end-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no
  sooner than the run with a take restaged `ending`.
- **`end-ghost`** (Climbs) — FALSITY, `NO EVIDENCE`: the tree with a take
  restaged `ending` has a sane, placed part meaning what the ghost did.
- **`out-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: `Owned` holds of the take
  restaged `ending`, its completion owed in the frame its failing value runs
  under.
- **`out-queue`** (Climbs) — FALSITY, `NO EVIDENCE`: `Queue` survives a take
  restaged `ending`, the run gone under `ix 0`.
- **`out-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no
  sooner than the run under `ix 0` with a take restaged `ending`.
- **`emit-void`** (Lift) — FALSITY, `DEAD ROUTE`: an `of` the ghost does not
  hold emits to a guard that drops it, the ghost alike, a value fewer.
- **`up-lanes`** (Frame) — FALSITY, `NO EVIDENCE`: a flatMap above a written
  scan in one of its lanes heads no sooner than that lane's part.
- **`up-outer`** (Frame) — FALSITY, `NO EVIDENCE`: a flatMap above a written
  scan in its outer heads no sooner than the outer's part.
- **`tells-past`** (Frame) — FALSITY, `NO EVIDENCE`: a call under way, a
  connect past its source's end tells its body's untold joiners no sooner than
  the run.
- **`shut-heads`** (Frame) — FALSITY, `NO EVIDENCE`: a shut heads where its
  node did, or at an end it tells.
- **`up-untold`** (Frame) — FALSITY, `NO EVIDENCE`: a write at a scan's
  accumulator leaves which joiners are untold alike.
- **`scan-sees`** (Frame) — FALSITY, `NO EVIDENCE`: a path seen after the write
  was seen before, to a node alike or above the scan.
- **`scan-defined`** (Frame) — FALSITY, `NO EVIDENCE`: whether a node has a
  part never reads an accumulator.
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
- **`src-idle`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's source signals
  its subject only with no feed under way.
- **`fed-ghost`** (Climbs) — FALSITY, `NO EVIDENCE`: the tree with a feed
  restaged has a sane, placed part, the ghost past the source's skip.
- **`fed-stack`** (Climbs) — FALSITY, `NO EVIDENCE`: a stack against the tree
  stands against it with a connect's feed restaged.
- **`fed-ticked`** (Climbs) — FALSITY, `NO EVIDENCE`: the stack ticks as it did
  with a connect's feed restaged.
- **`fed-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: `Owned` holds with a feed
  restaged, the feed the one call owed.
- **`fed-kernels`** (Climbs) — FALSITY, `NO EVIDENCE`: `Kernels` survives a
  connect's feed restaged.
- **`fed-meaning`** (Climbs) — FALSITY, `NO EVIDENCE`: `Meaning` survives a
  connect's feed restaged: the joiners' parts move with it.
- **`fed-queue`** (Climbs) — FALSITY, `NO EVIDENCE`: `Queue` survives a
  connect's feed restaged.
- **`fed-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no
  sooner than the run with a connect's feed restaged.
- **`fin-calls`** (Climbs) — FALSITY, `NO EVIDENCE`: the calls owed carry
  across a connect's subject closed and its finish staged.
- **`fin-ghost`** (Climbs) — FALSITY, `NO EVIDENCE`: the tree with a finish
  staged has a sane, placed part, the ghost past the source's skip.
- **`fin-stack`** (Climbs) — FALSITY, `NO EVIDENCE`: a stack against the tree
  stands against it with a connect's finish staged.
- **`fin-ticked`** (Climbs) — FALSITY, `NO EVIDENCE`: the stack ticks as it did
  with a connect's finish staged.
- **`fin-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: `Owned` holds with a
  finish staged, the finish ahead of the calls owed.
- **`fin-kernels`** (Climbs) — FALSITY, `NO EVIDENCE`: `Kernels` survives a
  connect's subject closed and its finish staged.
- **`fin-meaning`** (Climbs) — FALSITY, `NO EVIDENCE`: `Meaning` survives a
  connect's subject closed and its finish staged.
- **`fin-queue`** (Climbs) — FALSITY, `NO EVIDENCE`: `Queue` survives a
  connect's subject closed and its finish staged.
- **`fin-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no
  sooner than the run with a connect's finish staged.
- **`emit-shut`** (Lift) — FALSITY, `NO EVIDENCE`: an `of` whose observer path
  is closed skips its value.
- **`sub-onward`** (Lift) — FALSITY, `NO EVIDENCE`: a subscription begun runs
  its kernel to the next re-entry state.
- **`feed-onward`** (Lift) — FALSITY, `NO EVIDENCE`: the rest of a connect's
  feed of a value, each subscriber showing or skipping it.
- **`src-onward`** (Lift) — FALSITY, `NO EVIDENCE`: a connect's source
  subscribed once its body is.
- **`kont-onward`** (Lift) — FALSITY, `NO EVIDENCE`: a subscription's
  continuation stashes its unsubscribe, a call fewer.
- **`burst-poll`** (Lift) — FALSITY, `NO EVIDENCE`: a live burst's sink polled,
  open to play or closed and dropped.
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
