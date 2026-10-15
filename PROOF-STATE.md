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
is `reachedᴿ`. Sortedness rides SCOPED positions: `under l m k` runs `m` at
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

- **THE ORDER.** `owned-flat`, `steady-sub`, `ordered-flat` and
  `ordered-rejoin`: a flatMap shows only what it keys, over sorted
  sources alien to it is steady, and a flatMap and a join of steady
  parts keep order. Ruled out: a join of a run merely in order, a
  flatMap of any outer in order (a joiner told a value and a skip at
  one position), lanes placed wherever they subscribe, and sources
  merely clear of a flatMap's subtree (one tagged under its join).
  Decides whether any operator shows a source's position untagged, and
  whether every operator keeps `Steady`.
- **THE DEFER.** `ordered-defer` and `within-defer`: a defer over sorted,
  alien sources is in order, and its program, fed, is placed within.
  Decides whether a defer's notices keep its sources steady when
  replayed, which `within-defer` would follow from as a feed.
- **THE OPERATORS.** `go-skips`, `take-first`, `join-quiet` and
  `defer-after`: a flatMap's meaning is what its step shows, a cut step
  comes first when the uncut did, an untold joiner fed nothing under
  silent sources shows nothing, a defer is its program subscribed. Ruled
  out: a stepper `≃` short of strong agreement, every operator respecting
  it and a source's step tied with the body's skips commuting. Decides whether `join-quiet` needs its
  sources' silence carried further than `First`.
- **THE MACHINE SIDE.** `note-least`, `note-onward`, `turn-pops`,
  `turn-dry`, `sub-onward` and `burst-onward`: a note records the least
  value the ghost holds, a popped timer's frame is the ghost's frames node,
  a drained run's ghost shows nothing, and a subscription or a burst runs
  silently to the next re-entry state. Decides whether "least" is paid
  once as a field of `Carried`, and whether the ghost's timers need an
  order of their own or `WellQueue`'s.
- **THE PROGRESS.** `reachedᴿ` as a body: induction on `Ahead`, carrying
  `Inner`, over one leaf, a re-entry hop steps the ghost or lowers a
  machine measure. A burst's steps, a lane admit and a defer step the
  ghost; a popped timer, a poll, a spent burst dropped, a burst over and
  owed todos paid leave it in place, each finitely often per frame. Ruled
  out: a meaning skip at a timer pop, at the frame's root (a hot's rekey
  sorts it after the burst, oracle) or tied with the burst's first step
  (an `out` must rise past it, `placing`). Decides whether those five are a
  measure on the pure driver alone, or need a ghost-only marker in the
  shared machine, as `here` is, which the IO runtime ignores.
### The ledger

- **`ordered-flat`** (Placed) — FALSITY, `REFUTED`: a flatMap merges its outer
  and lanes in order, over sources sorted and alien to where it subscribes.
- **`ordered-defer`** (Placed) — FALSITY, `NO EVIDENCE`: a defer's run, over
  sources sorted and alien to where it subscribes, is in order.
- **`steady-sub`** (Placed) — FALSITY, `NO EVIDENCE`: a subscription over
  sorted, alien sources never steps inside its last position nor ties an out.
- **`owned-flat`** (Placed) — FALSITY, `NO EVIDENCE`: a flatMap shows only
  positions keyed strictly under it, its merge minting none of its own.
- **`owned-connect`** (Placed) — FALSITY, `NO EVIDENCE`: a connect shows only
  positions keyed strictly under it, its source's steps and end just past them.
- **`owned-defer`** (Placed) — FALSITY, `NO EVIDENCE`: a defer shows only
  positions keyed strictly under it, its program read by the fold's meaning.
- **`alien-sub`** (Placed) — FALSITY, `NO EVIDENCE`: a connect's source,
  subscribed at its `ix 1`, keys nothing under its `ix 0`.
- **`ordered-beside`** (Placed) — FALSITY, `NO EVIDENCE`: a connect's source
  steps merge into its body in order.
- **`ordered-rejoin`** (Placed) — FALSITY, `REFUTED`: a join keeps a steady
  source's order.
- **`ordered-take`** (Placed) — FALSITY, `NO EVIDENCE`: a cut keeps the order.
- **`ordered-start`** (Placed) — FALSITY, `NO EVIDENCE`: a cold's run is in
  order.
- **`ordered-of`** (Placed) — FALSITY, `NO EVIDENCE`: a list's run is in order.
- **`within-defer`** (Stepper) — FALSITY, `NO EVIDENCE`: a defer's program,
  subscribed and fed, is placed within.
- **`lags-flat`** (Stepper) — FALSITY, `NO EVIDENCE`: a flatMap's meaning shows
  nothing before a body's event that comes first, its sources a step past.
- **`leads-flat`** (Stepper) — FALSITY, `NO EVIDENCE`: a flatMap's meaning
  shows only skips at a step coming before its own and its sources'.
- **`go-skips`** (Stepper) — FALSITY, `NO EVIDENCE`: a flatMap's meaning is
  what its step shows, each lane showing its own.
- **`join-quiet`** (Stepper) — FALSITY, `NO EVIDENCE`: an untold joiner fed
  nothing under silent sources shows nothing.
- **`take-first`** (Stepper) — FALSITY, `NO EVIDENCE`: a cut step comes first
  when the uncut one did.
- **`defer-after`** (Stepper) — FALSITY, `NO EVIDENCE`: a defer's meaning is
  one skip, then its program subscribed.
- **`note-least`** (Content) — FALSITY, `NO EVIDENCE`: a note records the least
  value the ghost holds.
- **`note-onward`** (Content) — FALSITY, `NO EVIDENCE`: past a note the run
  runs the stepped ghost.
- **`turn-pops`** (Content) — FALSITY, `NO EVIDENCE`: a popped timer's frame is
  the ghost's frames node at its tick.
- **`turn-dry`** (Content) — FALSITY, `NO EVIDENCE`: nothing held and no timer
  queued, the ghost shows nothing.
- **`sub-onward`** (Content) — FALSITY, `NO EVIDENCE`: a subscription begun
  runs silently to the next re-entry state.
- **`burst-onward`** (Content) — FALSITY, `NO EVIDENCE`: a burst's frame steps
  silently to the next re-entry state.
- **`placing`** (Adequacy) — FALSITY, `NO EVIDENCE`: an ascending record alike
  a program's events as a set is placed against them.
- **`reachedᴿ`** (Adequacy) — FALSITY, `NO EVIDENCE`: every item the meaning's
  events reach, some prefix reaches.
- **`ticks-up`** (Adequacy) — FALSITY, `RECOVERY`: the meaning's ticks never
  fall.

## Tier 2 — the simultaneous spec

**THE STATEMENT.** Define the new "simultaneous" spec over the denotation,
adapted from the old `agda/` tree's statement modules (reference only). No
rows until the statements exist; each lands as a postulate here.

## Tier 3 — the simultaneous spec, proven

**THE PROOF.** Discharge Tier 2's statements using the denotation and
`adequacy`. No rows until Tier 2 states them.
