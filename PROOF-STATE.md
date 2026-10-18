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

- **THE LANE START, GROWN.** The growth frame's own cells:
  `grow-stack`/`alone`/`ticked` and `grow-owned`/`holds`/`joined` are the
  kernels' code natural in the world, over `walk-grow` and the `-wk`
  toolkit (Alike). Then route the rest of the `bg-*` row, `bg-ghost`
  included, through the frame.
- **RESTAGE AND KERNEL CELLS.** The restage `heading`/`lingering` cells
  and `fr-holds`/`gated`/`spent`/`fed`: fold over the frames that exist.
- **DEEP ORDER.** `gapped-past` holds only where every node under a rest is
  in order, which `Placed` does not see (`stepped-deep` reads it from
  nothing). Decides whether `Deep` is a field `Carried` keeps, each move
  framing it, or `Placed` itself descends; then `gapped-past` by operator.
- **THE FREE SOURCE.** `lifts-source` leaves the source node free, and an
  end lifted through a connect's source reads it: `fin-ghost` and
  `end-ghost` need it tied to the heap's leftover, beyond `Tied`'s first
  pin, before either is a lift.
- **NODE FACTS, FALSITY FIRST.** Only now discharge: the node facts the
  fold left, riskiest first, then the per-move facts no column holds.
- **HIDDEN RUNS.** Parked behind the fold. The core: `pooled-pin`,
  `left-pin`, `pool-off`, `spread-held`, one fact: nothing but the `of`
  heads under the run (`Carried.behind` bounds only at its `p`).
- **UP-ENDED.** Parked behind the fold. Decides whether `tells-past` is a
  field `Carried` owes, every producer framing it, or follows from
  `Owned`'s finishes and the agenda's placement.

### The ledger

- **`under-shown-connect`** (Placed) — FALSITY, `RECOVERY`, `X`: no step a
  connect's body shows or leaves lies under where a source step shows.
- **`step-skips`** (Stepper) — FALSITY, `REFUTED×2, DEAD ROUTE, RECOVERY×2`,
  `X`: a sane, placed root ghost's meaning is what its step shows, then the
  stepped node's.
- **`within-step`** (Stepper) — FALSITY, `REFUTED×2`, `X`: a sane, placed root
  ghost's step leaves its parts placed.
- **`gapped-past`** (Gapped) — FALSITY, `REFUTED`: a node in order under every
  rest has a gapped one's meaning past its skips.
- **`stepped-deep`** (Gapped) — FALSITY, `NO EVIDENCE`: what a sane, placed
  root ghost skips to is in order under every rest; reads what neither holds.
- **`gapped-sane`** (Gapped) — FALSITY, `NO EVIDENCE`: a node gapped from a
  sane one is sane.
- **`gapped-placed`** (Gapped) — FALSITY, `NO EVIDENCE`: a node gapped from a
  placed one is placed.
- **`lane-settles`** (Climbs) — FALSITY, `NO EVIDENCE`: a freed slot's settle
  tests the ghost's lane end: done flag the outer gone, count the lanes.
- **`calling-open`** (Climbs) — FALSITY, `NO EVIDENCE`: a climbing signal's
  path reads open.
- **`begin-path`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane begun runs to its
  inner subscribed under `ix 1`: counted, cut, listed, the rest weakened.
- **`bg-ghost`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane begun: the ghost's
  admit, the lane planted pending in the grown tree.
- **`bg-code`** (Climbs) — FALSITY, `NO EVIDENCE`: a begun lane's run is its
  inner compiled at the lane's env.
- **`bg-owned`** (Climbs) — FALSITY, `NO EVIDENCE`: `Owned` holds in the grown
  tree with a lane begun.
- **`bg-holds`, `bg-gated`, `bg-spent`, `bg-fed`** (Climbs) — FALSITY,
  `NO EVIDENCE`: the begun flatMap's own clauses, the count and list written,
  its lane pending.
- **`bg-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no sooner
  than the run one level down.
- **`lanes-counted`** (Climbs) — FALSITY, `NO EVIDENCE`: a climbing outer value
  reads the count as the live lanes; a fact of the call, not a kernel.
- **`outer-switch`** (Climbs) — FALSITY, `NO EVIDENCE`: a switch kills its
  lanes, their rests the pool's, and begins one.
- **`outer-queued`** (Climbs) — FALSITY, `NO EVIDENCE`: a full bounded merge
  queues the value, the ghost past the skip.
- **`outer-drop`** (Climbs) — FALSITY, `NO EVIDENCE`: a busy exhaust drops the
  value, the ghost past the skip.
- **`active-lanes`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's count reads
  zero exactly when no lane is live.
- **`fr-holds`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's kernel holds
  with a lane ended and the count down.
- **`fr-gated`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's gate holds with
  a lane ended.
- **`fr-fed`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's feeds hold with a
  lane ended.
- **`fr-spent`** (Climbs) — FALSITY, `NO EVIDENCE`: a flatMap's spent holds
  with a lane's cut and the count written.
- **`take1-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a held takeWhile's
  completion begun under its failing value, its cut the frame's rest.
- **`take1-void`** (Climbs) — FALSITY, `NO EVIDENCE`: a hidden takeWhile's
  completion, the ghost what the hidden part's rest shows.
- **`last-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a held open spent `of`'s
  completion begun at its end.
- **`last-void`** (Climbs) — FALSITY, `NO EVIDENCE`: a hidden open spent `of`'s
  end climbs to its guard, as a hidden value does.
- **`fin-enter`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's feed of its
  source's end, nothing left or the next subscriber's completion begun.
- **`note-least`** (Lift) — FALSITY, `NO EVIDENCE`: a note records the least
  value the ghost holds.
- **`turn-dry`** (Lift) — FALSITY, `NO EVIDENCE`: nothing held and no timer
  queued, the ghost shows nothing.
- **`spread-held`** (Lift) — FALSITY, `NO EVIDENCE`: held or hidden, no sibling
  an open `of`'s path to a held part passes heads under its base.
- **`behind-fire`** (Lift) — FALSITY, `NO EVIDENCE`: a timer popped at the
  turn, its fired cold heads no earlier than the run.
- **`shut-step`** (Lift) — FALSITY, `NO EVIDENCE`: a connect past its source's
  end, an `of` in its body: the body shut steps as it does, shut after.
- **`emit-run`** (Lift) — FALSITY, `NO EVIDENCE`: an open `of`'s value handed
  on under its scope, the climb starts aloft.
- **`end-ghost`** (Climbs) — FALSITY, `DEAD ROUTE`: the tree with a take
  restaged `ending` has a sane, placed part meaning what the ghost did.
- **`out-behind`** (Climbs) — FALSITY, `NO EVIDENCE`: every part heads no
  sooner than the run under `ix 0` with a take restaged `ending`.
- **`void-site`** (Lift) — FALSITY, `DEAD ROUTE`: an `of` the ghost does not
  hold sits under a held pool, ended source's rest or `ending` take, or the
  root has no part.
- **`pooled-pin`** (Lift) — FALSITY, `NO EVIDENCE`: at a pool over a hidden
  `of`, what the flatMap's ended parts left running pins next under the run.
- **`pool-off`** (Lift) — FALSITY, `DEAD ROUTE`: at a pool over a hidden `of`,
  neither the flatMap's outer nor any lane it holds heads under the run.
- **`pool-land`** (Lift) — FALSITY, `NO EVIDENCE`: the pool's pin lifted is the
  ghost's step: the run dies at its guard, the ghost past that pin.
- **`left-pin`** (Lift) — FALSITY, `NO EVIDENCE`: at a held connect over a
  hidden `of` in its ended source, what the source left running pins next under
  the run.
- **`rest-body`** (Lift) — FALSITY, `NO EVIDENCE`: there, the body shut at the
  source's end steps after that pin.
- **`rest-land`** (Lift) — FALSITY, `NO EVIDENCE`: the rest's pin lifted is the
  ghost's step: the rest a pin on, the ghost past it.
- **`close-lingers`** (Climbs) — FALSITY, `NO EVIDENCE`: an outer's end, its
  pool taking the outer's last ghost rested, keeps every tie.
- **`settle-lingers`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane's end, its
  pool taking the lane's last ghost rested, keeps every tie.
- **`next-lingers`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane's end with a
  value queued, the queue's head taken, keeps every tie.
- **`bg-lingers`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane begun in the grown
  world keeps every tie.
- **`fire-lingers`** (Lift) — FALSITY, `NO EVIDENCE`: a timer fired keeps every
  tie.
- **`torn-lingers`** (Lift) — FALSITY, `NO EVIDENCE`: what a teardown reached
  keeps every tie.
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
- **`src-idle`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's source signals
  its subject only with no feed under way.
- **`fed-part`** (Climbs) — FALSITY, `NO EVIDENCE`: the retagged body is the
  body's part fed the value, gapped up to the feed.
- **`fin-ghost`** (Climbs) — FALSITY, `DEAD ROUTE`: the tree with a finish
  staged has a sane, placed part, the ghost past the source's skip.
- **`emit-shut`** (Lift) — FALSITY, `NO EVIDENCE`: an `of` whose observer path
  is closed skips its value or its end.
- **`sub-cold`** (Lift) — FALSITY, `NO EVIDENCE`: a cold begun registers its
  sink and starts its timeline.
- **`of-owned`** (Restages) — FALSITY, `NO EVIDENCE`: an `of` planted where it
  was pending (an `empty` a spent one) owes its values and continuation as the
  agenda's calls.
- **`grow-stack`, `grow-alone`, `grow-ticked`** (Weaken) — FALSITY,
  `NO EVIDENCE`: the stack, its sources and its ticks carried across a
  weakening.
- **`grow-owned`, `grow-holds`, `grow-joined`** (Weaken) — FALSITY,
  `NO EVIDENCE`: the calls, the registered callbacks and the silenced
  subscribers read along a growth as the weakened kernels' — the kernels' code
  natural in the world.
- **`untake`** (Taken) — FALSITY, `NO EVIDENCE`: a source heads no earlier than
  the take over it.
- **`grew-store`** (Connected) — FALSITY, `NO EVIDENCE`: a store into a cell
  the growth made past its old names keeps the run as it read.
- **`walk-kont-sub`** (Names) — FALSITY, `NO EVIDENCE`: a walk's continuation
  reads alike on alike subscriptions.
- **`flat-wk-here`** (Flatted) — FALSITY, `RECOVERY`: a flatMap kit's admit,
  settle and dequeue weakened read as the node's over its compiled inners.
- **`unflat`** (Flatted) — FALSITY, `NO EVIDENCE`: an outer heads no earlier
  than the flatMap over it, no lane begun.
- **`connect-owned`** (Connected) — FALSITY, `NO EVIDENCE`: `Owned` holds of a
  connect planted at its body, its source owed under `ix 1`.
- **`connect-behind`** (Connected) — FALSITY, `NO EVIDENCE`: every part heads
  no sooner than the run with a connect planted at its body.
- **`sub-joined`** (Lift) — FALSITY, `NO EVIDENCE`: a joiner begun registers on
  its subject, or completes on a closed one.
- **`sub-defer`** (Lift) — FALSITY, `NO EVIDENCE`: a defer begun begins its
  body one level down, the ghost past its skip.
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
- **`ended-past`** (Frame) — FALSITY, `NO EVIDENCE`: a connect held past its
  source's end holds no source part, at every call under way.
- **`heads-flat`** (Shift) — FALSITY, `NO EVIDENCE`: a flatMap's merged part
  heads no sooner than `q` whenever its outer's and its lanes' do.
- **`untold-shut`** (Shift) — FALSITY, `NO EVIDENCE`: shutting a body's head
  input leaves what it has not told every other input.
- **`rest-sourced`** (Shift) — FALSITY, `NO EVIDENCE`: a connect's leftover
  over a source running on either side, pinned as its source's.
- **`rehome`** (Replant) — FALSITY, `NO EVIDENCE`: a call aimed anywhere in the
  tree aimed alike after a kin replanted.
- **`recold`** (Replant) — FALSITY, `NO EVIDENCE`: a cold reached in the tree
  reached alike after a kin replanted.
- **`owned-run`** (Replant) — FALSITY, `NO EVIDENCE`: the kin's own call ahead
  of the run's carries `Owned` across the replant.
- **`pool-idling`** (Climbs) — FALSITY, `NO EVIDENCE`: a pool joined with an
  idle one ties what it tied.
- **`close-heading`** (Climbs) — FALSITY, `NO EVIDENCE`: an outer closed, the
  pool's heads where the outer's were.
- **`fr-heading`** (Climbs) — FALSITY, `NO EVIDENCE`: a lane freed keeps the
  flatMap's heads.
- **`settle-heading`** (Climbs) — FALSITY, `NO EVIDENCE`: the pool taking what
  a lane ran heads where the lane did.
- **`next-heading`** (Climbs) — FALSITY, `NO EVIDENCE`: the queue's head taken
  off, the flatMap heads as it did.
- **`fed-heading`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's feed
  restaged keeps its own heads, the joiners retold.
- **`fed-lingering`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's feed
  restaged keeps its own ties.
- **`fin-heading`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's finish
  staged keeps its own heads.
- **`fin-lingering`** (Climbs) — FALSITY, `NO EVIDENCE`: a connect's finish
  staged keeps its own ties.
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
