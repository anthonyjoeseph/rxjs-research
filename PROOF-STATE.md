# PROOF-STATE — the roadmap

**What this file is.** The ordered worklist for the one goal: discharging
`agda/src/Verify-Batch-Simultaneous/The-Proof.agda` — no postulates, everything
typechecks. This file holds the SCHEDULE — each tier's next three legs — over a
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
  and not a region, but the chunk this session intends to land next. So the
  three are the next three COMMITS, and legs two and three may aim at the very
  same postulates as the first; what the trio owes is a coherent vision for
  reducing the most risk, cut at commit boundaries. Pick the risk order first,
  then cut — never pick three topics and hope each is commit-sized.
  **SO THE FILE MOVES WITH EVERY COMMIT, and `make roadmap-moved` fails when it
  does not.** Three outcomes. The leg landed: retire it, promote the other two,
  write a new third. It did not finish: **rewrite the first leg as the work that
  remains**, the only record of what it turned out to cost. Or its ROUTE DIED:
  **discard it** — a refuted framing rewritten smaller is still steering, so the
  finding goes to the header of the statement it constrains and the leg that
  replaces it is written from the risk as it now stands.
  **THE THREE LEGS DO NOT HAVE TO COVER THE TIER (Anthony).** They are the NEXT
  three, not a partition of the remaining work — the coverage rule is the
  LEDGER's job, and the rows already discharge it. Work beyond the third leg is
  left unnamed on purpose: it will be re-grouped by what the first three find,
  so naming it now writes a plan that ages before it is read.
  **Pick up the top LEG, not the top row.** Reading straight down the ledger
  works exactly one postulate at a time, and the expensive part of this
  campaign is never the clause — it is discovering, after the clause is ground,
  that the statement's neighbours had to move with it.
  **`make roadmap-check` ENFORCES THE COUNT AND A PROSE BUDGET PER LEG.** Three,
  unless the tier has fewer than three live postulates to plan over — fewer is a
  tier planning one leg ahead, more is a backlog, and the rows already are the
  backlog. The budget is several times a row's, because a leg carries its own
  reasoning and a group has no header to send research to; past it, the leg has
  stopped saying why this group is next and started proving it.
- **A TIER MAY OPEN AN `### Open questions` SECTION, AND IT IS NOT A SECOND
  ROADMAP (Anthony).** A question is what the tier does not yet KNOW that
  several of its FALSITY rows are all waiting on — the thing a row cannot
  say, because a row is about one statement and the uncertainty is shared.
  So it names at least two, and answering one moves all of them at once.
  It is capped at three for the roadmap's reason: past that the entries are
  rows wearing headings, or two phrasings of one question.
  **BUT IT IS NOT REQUIRED TO MOVE, AND NOT REQUIRED AT ALL.** A leg is a
  commit, so it moves with every commit; a question outlives many, and
  forcing one to change per commit would produce a rewritten question rather
  than an answered one. Nor is the section mandatory per tier — a required
  question is a filler question, exactly as a required `TWIN:` is filler,
  and filler here is worse than blank because it reads as research.
  **WHAT IS HELD INSTEAD IS THE `relevant:` LINE, and `make roadmap-check`
  enforces it.** Every name on it must still be a LIVE postulate, must be a
  row of that same tier, and must still be FALSITY. Nothing else would
  notice this section aging, so that list is the one thing kept current: a
  name off the ledger means the question is answered or its row was
  restated, and a row that has come down out of FALSITY means the
  uncertainty is settled there. When nothing risky is left under a question,
  the question goes. The list is FREE of the prose budget, so a question is
  never shortened by dropping a postulate from it — the same asymmetry the
  rows carry, for the same reason.
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
formal-verification-batchSimultaneous    The-Proof.agda — REAL, module postulate-free
 ├─ batch-agreement                      proven
 └─ evaluate-well-formed                 Verify-Well-Formed/ — tier 2
     ├─ budget-sufficient                Caps-Bridge.agda — a REAL BODY over:
     │   ├─ burst-dry/-bounded ┐ all three are projections of ONE
     │   ├─ burst-caps         ┘ subscribeE-wet-via-caps call (burst-all)
     │   │                                ← subscribeE-wet ← wet-landing-lift
     │   │                                  ← subscribeE-walk-level   proven
     │   └─ drain-dry   ← cascade-wet-via-caps     proven
     └─ the well-formedness branch       its own postulates — tier 2

  every tier above is stated over Rx.Exp's syntax  MergeAll-Laws.agda — closed
```

The caps route does not replace the wet contract — it rests on it: both
branches of `budget-sufficient` read `subscribeE-wet`'s `hasDry`/`INV?`
conjuncts, and both of those routes are real definitions — `subscribeE-wet`,
`wet-landing-lift`, `subscribeE-walk-level` and `cascade-wet-via-caps` all the
way down, with the `walkFace` family ground on every clause and the whole
Walk-Level tree holding no live postulate.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 1 — `budget-sufficient`

**The tier is ONE statement, not a directory.** `budget-sufficient`
(Caps-Bridge) says `hasDry (evaluate fuel e ins) ≡ false`, and it is the only
CLAIM the `Verify-Budget-Sufficient` tree exports: every module in the tree
sits in Caps-Bridge's import cone, bar a program corpus that reaches Main
through `Harness.Main`.

**IT IS ALSO THE TREE'S ONLY DOOR.** `Verify-Well-Formed` draws
`mint-install-survives` (Node-Fresh) by name, and that is the one real
cross-tier claim into this tree.

**"A REAL BODY" IS NOT "POSTULATE-FREE".** `budget-sufficient` is a definition
rather than a postulate; the rows below are the leaves still under it. Reading
a real body as a discharged cone is how a row gets mis-ranked, and a row whose
OBSTACLE is written down is not thereby a row whose STATEMENT is right.

**THE `subscribeE-nest-*` ROWS ARE ONE STATEMENT, NOT ONE PER HEAD.** They all
instantiate `NestAt`, whose grant now shrinks with the term and whose store
half is a join; why it is shaped that way is in its own header. A head that
does not fit is a finding about the shared statement, not about the head.



### Big picture tier roadmap

- **WALKING AN ADMITTED CHAIN AT THE LEVEL IT WAS REGISTERED AT, which
  is the one door the pricing leaves open.** Both ends are closed by
  arithmetic now, and `fan-regsSz`'s header carries which: the fan can
  reach neither the entry-cap receipt nor the stepped one. What
  neither end touches is the fan's own choice to re-enter a chain from
  the instant's TOP. A chain re-entered at the level it was registered
  at needs exactly the receipt `register-caps` left behind. The commit
  asks what the walk must carry for that to be stateable, and whether
  the depth measure still decreases when a chain is entered below the
  top — the mechanism question the currency search stood in for.

- **RE-MEASURING WHAT IS LEFT OF THE OVER-BUDGET LIST, now that the
  cause of one reading is known and it was not the module.** A dev
  check charges a consumer for its imports' CONTENTS, so a new
  module-graph edge into a widely imported module raises the cost of
  everything downstream: measured at sixty-three seconds against over
  eight minutes for one edge into the module defining the path
  predicates, with the bodies unchanged. That is a third cause
  beside the cold cone and the genuine SCC, and it is the one a shape
  reading cannot see. The commit re-runs the remaining floors
  bottom-up on a coherent cache, attributes each to cone, edge or
  block, and deletes the findings resting on the ones that fall.

- **A HYPOTHESIS WRITTEN INLINE IS NOT A DECLARATION, AND THE COPIES
  ARE NOT ONLY OF NAMED TYPES.** Naming the face hypothesis types was
  supposed to end the shape where a premise added to the real lemma
  must be added again by hand at every site. Threading the entry
  reading has found three survivors, and the third widens the
  criterion: a `-core` whose applied form restates the core's telescope
  inline rather than naming it, so one premise is typed three times in
  one file and the miss reports at a consumer. `dup-check` reads
  declarations and an inline `∀ … → Σ …` is not one. The commit
  replaces every hand-written copy of a named telescope, and decides
  whether the sweep is a check.

### Open questions

- **CAN A PREDICATE OVER THE PATH SEE WHAT LIVES IN THE STORE?** Six rows
  fail in one place: the statement reads a PATH or a chain, and the quantity
  it must bound is a cell in the STORE. A `scan-f` carries a `NodeId`, so
  the value it folds against is not in the syntax at all and no reading of
  the term reaches it. The standing ruling says a missing invariant goes in
  the RECORD and never in a signature — but a conjunct there must survive
  `stepFrame`, and that is exactly where two of these are refuted. So the
  question is not whether to add it; it is whether ANY store conjunct is
  preserved by the step, or whether the step is where the reading has to be
  re-established rather than transported.
  relevant: `walk-strat-step`, `step-frame-store≤`, `share-fold-store≤`, `subscribeE-sz-store-scan`, `pushBurst-sz-store-outer`, `subscribeSharedSlot-sz-store`

- **IS THERE A COMPUTABLE SHADOW OF THE SEALED FACES?** Three rows say in
  their own headers that they cannot be instantiated — the cap does not
  return, the climb bound is sealed, the fold's doubling closes the
  conclusion. That sealing is what makes the tower checkable, so it is not
  removable per row. It leaves a block of this tier whose class evidence can
  only RAISE and never lower: a refutation still lands, a probe cannot be
  written. The question is whether a weaker family exists that REDUCES and
  whose truth would imply these, because absent one they reach a proof only
  by being proven, and nothing de-risks them first.
  relevant: `walk-frame-drain-entries`, `subscribeE-sz`, `share-fold-fit`

- **WHAT PRICES A REGISTERED CHAIN, AND WHERE IS THE RECEIPT OWED?** Five
  closed routes under `fan-regsSz` name one residue: no cap prices a
  registered chain, and the stratified climb counts hops where the receipt
  counts frames. Two siblings reach the same place from the other side —
  each dies in its free form at one `register`, so each is owed AT THE MINT
  rather than along the walk. The question is what the factor can be
  denominated in when neither a cap nor the telescope will pay it, and
  whether the answer is a denomination at all or a mechanism that
  establishes the receipt where the chain is created.
  relevant: `fan-regsSz`, `sink-fan-sink`, `walk-share-strat`

### The ledger

- **`walk-strat-step`** (Part7/Walk-Sink) — FALSITY, `NO EVIDENCE`: what a hop
  does to the chain's stratification reading, the one reading a walk cannot
  transport. A `scan-f` folds against a value in the STORE, which no path
  predicate reaches and the premised state receipt does not yet read.
- **`pop-head-strat-sink`** (Caps-Bridge) — FALSITY, `REFUTED`: where the
  arrival's own value sits against every chain that will receive it, asked only
  below the root. It wants a fact relating a source's pending values to the
  floors registered against it, and only where a floor drops.
- **`walk-frame-drain-entries`** (Part7/Walk-Sink) — FALSITY,
  `REFUTED×2, DEAD ROUTE, TWIN, PROBED×2`: the per-entry tuple the `from-inner`
  drain owes, the wrapper's ceiling now minted from the frame's own room. Both
  denominations stay closed to instantiation — the cap does not return, the
  climb bound is sealed — so evidence can raise this class, never lower it.
- **`subscribeE-sz`** (Regs-Nest-Walk) — FALSITY, `REFUTED, PROBED`: what ONE
  subscription delivers, in its charge plus its telescope. The WHOLE value side
  is a body over it. A max is refuted at a chain of eleven; a slot named twice
  is free; the delivery block clears ONE nesting and no deeper level computes.
- **`pushBurst-sz-store-outer`** (Regs-Nest-Walk) — FALSITY,
  `REFUTED, DEAD ROUTE, PROBED, RECOVERY`: the burst a crossing door pushes
  back through itself, keyed on the source program since an arbitrary burst is
  unbounded. A duplication chain buys no rung; the climb rows say no second
  block is owed, read in rungs rather than through the charge.
- **`subscribeE-sz-store-scan`** (Regs-Nest-Walk) — FALSITY,
  `REFUTED, DEAD ROUTE, PROBED×4`: the reified seed and the cell each arrival
  rewrites. The arrival count REFUTED the depth-only denomination — a wrapping
  step doubles the cell where unfoldings and layers hold fixed — and the charge
  now buys a delivery block at the SIZE bound.
- **`subscribeSharedSlot-sz-store`** (Regs-Nest-Walk) — FALSITY,
  `DEAD ROUTE, PROBED×2`: the definition behind a reference, whose entire climb
  is the telescope summand — `input` charges nought, so no program reading
  reaches it. The summand is owed the connect's TRANSITIVE reach; sum against
  maximum is closed to instantiation.
- **`sink-fan-sink`** (Part7/Depth-Fit) — FALSITY, `REFUTED, DEAD ROUTE`: the
  potential at an admitted chain that ends at a SECOND hand-over. Its
  escalation is PROGRAM-bounded: hops climb the stratified telescope. The chain
  now arrives carrying its `sinkAbove?` reading, so what is open is the MINT.
- **`walk-share-strat`** (Part7/Depth-Fit) — FALSITY, `REFUTED`: every
  registered chain ends strictly ABOVE the input it was minted subscribing. The
  only receipt here naming no cap, which is what makes it carryable; the free
  form dies at one `register`, so it is owed at the mint.
- **`fan-regsSz`** (Part7/Depth-Fit) — FALSITY, `REFUTED, DEAD ROUTE×5`: the
  registry's own size receipt at the PROGRAM's cap. `register-caps` prices a
  mint at one frame step, so the reading sits above the cap the conclusion
  names and the connect puts a mint inside every fan. Open: the Φ arithmetic at
  one step, not a currency.
- **`walk-share-nestOK`** (Part7/Depth-Fit) — FALSITY, `DEAD ROUTE×4`: the
  instant's nest predicate at the state the fan reads the registry. The door
  has it and the walk carries no nest conjunct at all; threading it down is
  refused by the store's own growth toward the NEXT cap.
- **`share-fold-fit`** (Part7/Arrival-Caps) — FALSITY, `NO EVIDENCE`: one
  admitted registration's path, descended at the delivered-marked state. THE
  ONE LEAF INHERITING THE BARRIER — it is `depthFold` again, so the doubling
  recorded at `depthShareGo` closes its conclusion to instantiation exactly as
  the parent's was.
- **`share-fold-store≤`** (Part7/Arrival-Caps) — FALSITY, `REFUTED, TWIN`: the
  store across one `foldPath`, PRICED against the round's grant rather than
  preserved. A `scan-f` at an obs-typed accumulator crossed the preservation,
  and the grant is sealed — so the repair closes the region to instantiation on
  both sides at once.
- **`step-frame-vals≤`** (Part7/Arrival-Caps) — FALSITY, `REFUTED, TWIN`: what
  one `stepFrame` leaves in the delivered values, at that same grant. This is
  the axis the frame moves and the fold does not — a scan emits the accumulator
  it just wrote — so the trade the old ceiling permitted ran one way only.
- **`step-frame-store≤`** (Part7/Arrival-Caps) — FALSITY, `REFUTED, TWIN`: the
  store half of that step, carried APART from the values half so that no
  ceiling has to cross a step at all; the position's ceiling is rebuilt from
  the two ingredients where it is spent.
- **`shareAdmit-strat`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: what a
  share hands the chains it admitted, and THE ONE PLACE THE REGISTRY READING IS
  SPENT rather than established. The chain half rides the admission filter,
  which drops entries and rewrites none; the value half widens off the slot.
- **`chainsOf-strat`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: that same
  chain reading arriving from the CASCADE's face. The two filters are keyed by
  a slot and by an arrival's source, so neither rearranges into the other and
  the entry reading is owed once per face.
- **`subscribeE-burstStrat`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`:
  what a subscribe EMITS, read at the chain it was subscribed under. Every push
  in this development pushes a burst whose payloads the frame will subscribe
  again, and the caps receipt carries no reading of them.
- **`stepFrame-valsStrat`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: what
  a frame hands the rest of its chain. The walk re-enters on the tail with an
  output the caps receipt prices but does not read; the floor does not move
  across a frame, which is what lets one statement cover the walk.
- **`framePark-step`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: the
  frame-keyed park reading across one step. The push re-steps the SAME frame,
  so the reading is asked of a state the previous emit produced, where the
  frame is a variable and no clause reduces.
- **`frame-parkStrat`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: the
  frame's queue read at the floor its tail is read at, off the caps invariant
  alone. That invariant prices a node's queue for size and for width and reads
  no floor, so the conjunct it would project out of is not there.
- **`pathPark-step`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: that same
  reading lifted off one frame onto the tail the walk is about to enter. Not a
  corollary of the frame-keyed form: what must survive is a reading of nodes
  the step did not name.
- **`shareAdmit-park`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: the park
  reading over the admitted chains at the LATCHED state the fan-out starts
  from — stated after the close, because that is where the fan reads the
  registry.
- **`foldPath-park`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: the same
  reading again once a SIBLING chain has folded. It is about a state the walk
  PRODUCED rather than one it was handed, which is why the latched form does
  not cover it.
- **`cascade-admit-park`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: the
  latched park reading arriving from the CASCADE's face. Its filter is keyed by
  an arrival's source and the share's by a slot, so neither rearranges into the
  other and the entry reading is owed once per face.
- **`chainStep-park`** (Part7/Strat-Leaves) — FALSITY, `NO EVIDENCE`: the
  cascade's fold-through, where the tail's chains are read at the state the
  HEAD chain's step produced. The chains that must survive are not the one that
  stepped, which is what keeps it off the share's form.
- **`scanΦ-fit`** (Part7/Depth-Fit) — SHAPE, `DEAD ROUTE`: the producing side
  of the fold's grant. THE MECHANISM IS DEAD, NOT A DENOMINATION: a flat
  per-instant potential cannot dominate a count exponential in itself; the one
  affording ceiling is the store's exit-index factor, priced in a refuted
  width.
- **`innerΦ-quiet-fit`** (Part7/Depth-Fit) — SHAPE, `REFUTED×2`: the charge at
  width zero, refuted at one installed cell — it reads the node table and no
  premise of it bounds the table. Owed as a carried store predicate, with the
  drain arm.
- **`innerΦ-drain-fit`** (Part7/Depth-Fit) — SHAPE, `DEAD ROUTE`: the same
  charge at the queue's own `drainW`. Its extra premise pins the cell's
  CONSTRUCTOR, not its depth, so a parked program runs the store term away here
  too; the width is walk-denominated besides.
- **`frame-depth-fit`** (Part7/Arrival-Caps) — DIFFICULTY, `PROBED`: one
  frame's own spend under the position's ceiling. Map, scan and take charge
  nothing, and BOTH arms that do are now instantiated — the react at a walked
  edge, the walk at an assembled one. The residue is the state axis, not an
  arm.
- **`stepFrame-nest-nodes-inner`** (Nodes-Nest-Walk) — DIFFICULTY,
  `PROBED, RECOVERY`: what the drain writes at the nodes map. The pop shrinks,
  and the park its subscribe makes lands one layer under the term popped — so
  the entry table covers it with the budget unspent, gate honoured.
- **`stepFrame-nest-regs-inner`** (Regs-Nest-Walk) — DIFFICULTY,
  `REFUTED, PROBED, RECOVERY`: what the drain registers. The premise alone was
  refuted by an empty burst; the grant pays EXACTLY, the mint being the node's
  own reading, at margin zero on three rungs.
- **`stepFrame-nest-nodes-outer`** (Nodes-Nest-Walk) — DIFFICULTY, `PROBED`:
  what the outer frame mints at the nodes map. NOT the fresh `*All` cell, which
  the install is proven to price at zero — the write is a full merge PARKING an
  arrival in its queue, so the grant owed is the arriving value itself.
- **`stepFrame-nest-regs-outer`** (Regs-Nest-Walk) — DIFFICULTY, `PROBED`: what
  the outer frame registers — the subscribed value's frames over the REST of
  the path, which is the potential exactly. A ladder where the mint climbs and
  the entry registry stands still clears the premise's own floor by a constant
  one.
- **`burst-out`** (Desc-Ceil) — DIFFICULTY, `PROBED`: one subscribe frame emits
  no more payloads than its term syntactically carries. Seven tight rows tied,
  the scan head and the share chain among them; every region a row could refute
  in is now read, and the refold cannot.
- **`sight-thru-val`** (Depth-Sighted) — DIFFICULTY, `REFUTED, PROBED`: what
  ONE emitted inner costs the outer frame to subscribe. All three conjuncts are
  now instantiated where they move — the store at the PARKING branch, tight to
  equality — and the subscribing branch is blocked rather than uncovered.

- **`subscribeE-fit`** (Sighted-Fit) — DIFFICULTY, `REFUTED×3, PROBED×2`: what
  ANY subscription's emitted VALUES cost, in the `nestB` currency against a
  `descW` bound. The family that kills the width-free form holds here at and
  past its crossing; every head but the `scanᵉ` one is uncovered.
- **`sight-all-walk`** (Depth-Sighted) — DIFFICULTY, `PROBED`: the drain's WALK
  half, one leaf for all three `*All` heads — they delegate to the same family
  and wrap the subject in one level each. It reads the fit the fold carries,
  which is what a value list quantified freely could not give it.
- **`subscribeE-burst-nestL`** (Nest-Walk) — DIFFICULTY,
  `REFUTED×2, DEAD ROUTE×5, PROBED×2, RECOVERY×2`: the admissibility boolean
  over any subscription's whole burst, reporting the level it needs as an
  increment off the entry base. The increment is measured FLAT in substitution
  depth, so what is left is the induction.
- **`evalWith-nest-sync`** (Nest-Subst) — DIFFICULTY, `TWIN, PROBED`: the
  substitution walk's sync-denominated charge at an arbitrary environment; the
  one-entry instances are probed where the currencies split, the wider
  environments and the closed seed are not.
- **`thruFit-arr-merge`, `thruFit-arr-switch`, `thruFit-arr-exhaust`**
  (Nest-Walk) — DIFFICULTY, `PROBED×6`: the emit-by-emit fit at the arr key,
  all the three boundary heads still owe — the recursion and the push around it
  are checked. The cap-keyed route to a fit does not transport to a key that is
  not a `nestB`.
- **`subscribeE-nest-arr-scan`** (Nest-Walk) — DIFFICULTY, `REFUTED, PROBED×2`:
  the fold multiplies the depth per value while the key gains only the value's
  written size, so the grant is read over `suc W` copies of the key; measured,
  that puts the width in the exponent and the margin's sign comes right.
- **`pushVals-caps-burstW`** (Nest-Walk) — DIFFICULTY, `PROBED`: the last
  stream leaf — the walk over it is a proven body, so what remains per instant
  is the frame widths, which are sealed and taken as a quantified premise
  wherever a row reads them.
- **`burst-regs-split`** (Caps-Bridge) — DIFFICULTY, `REFUTED, PROBED×3`: the
  registry after the subscribe frame, split between the program's unit and the
  node table. A chain SUMS its two kinds of frame, so neither source alone pays
  and neither does their join; the sum is what is left, tight where they
  compose.
- **`subscribeE-nest-scan`** (Nest-Walk) — DIFFICULTY,
  `REFUTED, DEAD ROUTE, PROBED`: `NestAt` now carries the pointwise store
  conjunct this head's accumulator read demanded, so the shape is settled; what
  remains is the fold arithmetic at the sync-keyed grant and the seed's
  `evalTm-nest-sync` spend.
- **`arr-chains-nest-syn`** (Part7/Cascade-Nest) — DIFFICULTY,
  `REFUTED, PROBED`: the selection's paths and the arrival's payload land
  inside one unit — the fact that ties the walk's charge back to the program.
  Free-list form refuted; tied at the entry arrival, cap premises unasked.
- **`cascadeGo-nest-regs`** (Part7/Cascade-Nest) — DIFFICULTY, `PROBED`: the
  walk's registry paths under the same width. Registration adds the one frame
  the path measure charges nothing for; the component reads zero, so the tie is
  degenerate on the increment.
- **`subscribeE-Ψ`** (Burst-Walk) — DIFFICULTY, `TWIN`, large: the Ψ reading of
  the clique its header mirrors, clause for clause at a different measure. The
  cost is that the induction covers every clause; nothing in it is undecided.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `budget-sufficient`, so proving anything here while tier 1 is open
bets on ground a `Verify-Budget-Sufficient` failure would move.

**THE TIER IS ONE STATEMENT.** `The-Proof` draws `evaluate-well-formed`
(Part13) and nothing else from this tree, and every `Verify-Well-Formed` module
sits in its cone.

**MERGE COHERENCE IS UNSTATED** — the branch's own design question. What a
statement owes, and why it would inherit no evidence from the probe that is the
predicate's only consumer, is recorded on `Part4.root-mergeAllCache`.

In rough order for when the tier opens — statement repairs first, then grinds:

### Big picture tier roadmap

- **instantiate FoldOut before any arm is ground** — `mid-readoff`. FoldOut is
  a six-field record validated at exactly one clause and five further rows are
  readoffs from it, so the risk is the record and not the arms: if it is
  wrong, all six are. This commit is the probe alone — the record at canonical
  programs, saying which fields the rows reach and which they do not — and
  whatever the probe forces on the record's own statement.
- **the map push, as an ASSEMBLY** — `map-nodry-push`. Every ingredient is
  already PROVEN and the route is complete, so this is a body over leaves
  rather than a grind, and it is one commit. It is taken before its six
  siblings because assembling it tests the shape they will all be written to,
  and a shape found wrong here costs one row instead of seven.
- **the two frame readoffs the record's probe unblocks** —
  `foldPath-frame-out`, `foldPath-share-out`. They share the record, the
  clause it is validated at and the fold they are read off, so once the first
  commit says what the record actually carries they are one shelf of
  mechanical work. Held behind that commit deliberately: a readoff ground
  against a record that then moves is ground twice.

### The ledger

- **`root-entry-sunk`** (Part4) — FALSITY, `NO EVIDENCE`: the per-entry residue
  of `root-done-plumbed`. Its load-bearing region was NOT reached by probe, so
  the class stands — but it is a statement about ONE surviving entry, a size a
  counterexample can be built at. Coverage boundary in its header.
- **`mid-readoff`** (Part11) — FALSITY, `NO EVIDENCE`: the FoldOut readoff, and
  FoldOut is a 6-field invariant validated at exactly one clause.
- **`dispatchShare-wf`** (Part9) — FALSITY, `NO EVIDENCE`: the share arm's run
  equation, `foldPath-wf`'s third clause. Nothing has been instantiated at the
  diamond's owed accounting — a handoff bump repaid across a per-registration
  fan-out — and its FoldOut half belongs to `foldPath-share-out`.
- **`foldPath-frame-out` / `foldPath-share-out`** (Part11) — FALSITY,
  `NO EVIDENCE`: `foldPath-out`'s two undischarged arms, each the FoldOut
  readoff only. FoldOut is a new record and nothing has been instantiated at
  either arm — the frame arm's shadow fields under a `stepFrame` call, the
  share arm's net-zero owed across the diamond.
- **`mid-fold-certs`** (Part11) — FALSITY, `NO EVIDENCE`: one case split on
  `Arrival.isLast a` off `Mid.done-plumbed`, which is a record field and not a
  precedent. The unreached corner is the flip: `allShareSunk` after the source
  is dropped, from a conditional hypothesis.
- **`scan-nodry-push`** (Part3) — FALSITY, `NO EVIDENCE`: no
  `pushBurst-scan-char` counterpart of the map characterisation exists, so the
  route is a direct induction and the twin its header names is itself a
  postulate. Nothing in the dry family has been instantiated at a scan push.
- **`subscribeSharedSlot-wf`** (Part3) — FALSITY, `NO EVIDENCE`, blocked:
  `sharedConnect` recurses into `subscribeE`, so this arm cannot close outside
  the mutual block holding `subscribeE-wf`, two files down — and the connect
  branch, which grows both registry and shares, is unreached.
- **`subscribeE-defer-wf`** (Part3) — FALSITY, `NO EVIDENCE`, well-scoped:
  three BurstInv conjuncts fall out at once; the whole residue is `liveTypeOK?`
  at the minted source, whose tail needs a mintSource-freshness lemma the repo
  does not have and nothing has instantiated.
- **`cut-owed`** (Part9) — FALSITY, `NO EVIDENCE`: independent of every
  blocker, but its own header calls the owed-shape obligation "genuinely
  semantic" and names no precedent. The unreached region is the ledger after
  `cutThrough`'s close list is applied — zeroExcept and UniqueOwed out.
- **`stepFrame-wf-inner-mergeAll`** (Part9) — FALSITY, `NO EVIDENCE`: the drain
  grows the registry; re-establish FoldInv. It is the ONE `stepFrame` clause
  that is not registry-monotone, and nothing has been instantiated there.
  Independent of the cert.
- **`mergeAll-nodry-push` / `mergeAll-valsLast-push`** (Part3) — FALSITY,
  `TWIN×2`: carry the dry premise in and `valsLast?` out through the wrap
  frame. The map and scan pushes they read against are postulates too, so the
  whole push family stands on nothing at any operator.
- **`map-nodry-push`** (Part3) — FALSITY, `NO EVIDENCE`: every ingredient is
  PROVEN — `pushBurst-map-char` (.Part5) and the dry family `splitEvents-nodry`
  / `retagEvents-dry` / `mapValue-dry` / `any-dry-++` (.Walk-Level) — so the
  ROUTE is complete and the STATEMENT is still uninstantiated. Assemble it:
  Part3 already reaches that cone through Caps-Bridge.
- **`input-hot-spent-wf`** (Part3) — FALSITY, `NO EVIDENCE`: `oneShotBurst-wf`
  is the same balance at a FRESHLY MINTED source and its own header says it
  does not donate this arm — a spent source re-emitting init is the unreached
  case, and `live-matches` there is what nothing has checked.
- **`take-nodry-push`** (Part3) — FALSITY, `NO EVIDENCE`, and NOT by the scan
  twin its header names, which is a postulate: `cutThrough` emits only `close
  src cut`/`cutPending` while `dryEvent` fires on `dried` alone, so the route
  is structural — and the cut case is what nothing has instantiated.
- **`subscribeE-dying`** (Part8) — FALSITY, `NO EVIDENCE`, large: `subscribeE`
  never writes `dying` — two writers, neither reachable from it, both named in
  its header. The claim rests on that enumeration being exhaustive, which is
  exactly what no instantiation has tested.
- **`HotLive`'s preservation leaves** (Part2) — FALSITY, `NO EVIDENCE`, four of
  the five: `sched-init-hot-live`, `mintSource-hot-live`,
  `subscribeE-hot-live`, `cascadeFinish-hot-live`. Each header states a
  slots-untouched / prepend-only route and no more; the family's one worked
  body sweeps where these three build, prepend and split.
- **`subscribeE-{switch,exhaust}All-wf`** (Part3) — SHAPE, `TWIN×2`: written
  against a coherence whose statement is still open (the cert sketch in Part8's
  establishment block). The mergeAll face is no longer among them: it is a real
  clause, and its leaves are the five rows below.
- **`stepFrame-wf-outer`** (Part9) — SHAPE, `NO EVIDENCE`, on a ROUTE claim
  rather than the statement: discharging it means enriching `stepFrame-wf` to
  carry FoldOut out, restating this family. GRIND it after
  `stepFrame-wf-inner-mergeAll`, which it strictly contains — a work-order
  dependency only.
- **`map-valsLast-push` / `scan-valsLast-push`** (Part3) — SHAPE,
  `NO EVIDENCE`: each papers over a recorded mismatch (the proven sub-lemmas
  don't return `valsLast?`).
- **`cutThrough-close-bound-dying` / `cutThrough-live-dying`** (Part7) — SHAPE,
  `REFUTED`: both REFUTED (`Refuted.Cut-Through`), `L₁` free at exactly the
  sources the conclusions speak about. Restate over the (LAG) ledger; header
  carries the repair and why it was not ground here.
- **`input-cold-async-wf`** (Part3) — SHAPE, `NO EVIDENCE`: its one named
  precedent `initReg-wf` is ruled out in the header — that lemma's emit is
  `init src ∷ []` while this ships the sync prefix in the same emit — and the
  `reg-typed` conjunct needs a self-typing certificate no hypothesis carries.
- **`mergeAll-node-shape`** (Part3) — DIFFICULTY, `TWIN`: the wrap's node is
  still a `mergeAll-st` at the type it was installed at, whatever the burst did
  to it. Limit-blind, which is what lets the queue claim be a separate fact
  rather than a conjunct only one limit can honour.
- **`subscribeE-mergeAll-push`** (Part3) — DIFFICULTY, `TWIN`: the wrap's push
  half, protocol run and invariant back out through `thru-outer`, over the
  inner's receipt plus the FINISHED wrap's node.
- **`root-mergeAllCache`** (Part4) — DIFFICULTY, `DEAD ROUTE, PROBED`: the
  per-node residue of `root-caches`, split to the mergeAll clause alone and
  probed non-vacuously in assembled form. Header carries the DEAD ROUTE through
  `mergeAllCertAt` and the MISSING INVARIANT it leaves owed.
- **`mergeAll-binv-adapt`** (Part3) — DIFFICULTY, `TWIN`: mint and install
  touch neither registry nor live, so every BurstInv field survives, and the
  mirror's argument never reads which node state is installed.
- **`sched-next-hot-live`** (Part2) — DIFFICULTY, `TWIN`: the fifth leaf, split
  out because it is the only one with a mirror — a per-entry `liveTypeOK?`
  carried across this very pop, proven.

## Tier 3 — the top-line semantic claims (parked behind tier 2)

The second ledger: claims Main asserts beside the main theorem, off its
critical path.

### Big picture tier roadmap

- **probe the `readme-*` family** — the `readme-*` rows. Nothing has ever
  instantiated them and they are stated over defined machinery, so they are
  probeable today and the whole family shares one harness: one context, many
  similar obligations. One commit for the sweep and its receipts. A refutation
  here is SPEC-level — surface it, do not patch it.
- **probe the two inheritance claims** — `id-inheritance`, `batch-online`.
  Separated from the family above because they are stated over the batching
  pipeline rather than the readme's programs, so they need their own harness;
  same shape of commit, and unprobed is unprobed whatever the statement reads.
- **draft the abstractions and ASK** — `locality`, `non-interference`,
  `timing-invariance`, `causality`, `μ-guarded`, `defer-shift`, over `Node`,
  `NodeSt`, `Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`, `retime`,
  `truncateIn`, `emittedBefore`. De-risking any of these means DEFINING the
  abstraction under it, which is claim authoring and Anthony's call. The
  commit is the drafted definition set and the question, not a discharge.

### The ledger

- **`id-inheritance`, `batch-online`, `readme-*`** — FALSITY, `NO EVIDENCE`:
  the twelve top-line claims nothing has ever instantiated. A refutation of a
  `readme-*` claim is SPEC-level: surface to Anthony, do not patch.
- **Vacuous-by-abstraction — VACUITY**, `NO EVIDENCE` — `locality`,
  `non-interference`, `timing-invariance`, `causality`, `μ-guarded`,
  `defer-shift` (the one allowlisted honest gap). De-risking these means
  DEFINING the abstractions: claim authoring that needs Anthony. **Not
  GRINDABLE and never will be** — no precedent can make them mechanical,
  because nothing is stated yet.
- **The abstractions those claims quantify over — VACUITY**, `NO EVIDENCE` —
  `Node`, `NodeSt`, `Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`,
  `retime`, `truncateIn`, `emittedBefore`. Named individually because they are
  what makes the row above vacuous, and a collective phrase is invisible to the
  coverage check.
- **`μ-unfold`, `fuel-coherent`** (Evaluator-Theorems) — DIFFICULTY,
  `PROBED×2`: the two evaluator laws a spent battery instantiated at every
  canonical program without refuting. Split from the twelve below, which have
  no receipt at all.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.

