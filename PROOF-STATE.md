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
 └─ evaluate-well-formed                 Verify-Well-Formed/Part13 — tier 2
     ├─ rank-sufficient                  Verify-Rank-Sufficient.agda — tier 1
     └─ the well-formedness branch       its own postulates — tier 2

  every tier above is stated over Rx.Exp's syntax
```

The descent `rank-sufficient` guards is the evaluator's own and is stated
nowhere else: `Acc _≺_` over a lexicographic triple — unconnected shares, hop
rank, `syncSizeᵉ` — seeded at every entry from outside the machine and dropped
at three guarded peels, each a proven body. No quantity above `Rx.Evaluator` mentions it, which is what
lets one statement close the whole descent.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 1 — the descent never goes dry

**THE TIER IS ONE STATEMENT, AND IT IS THE WHOLE COST OF THE DESCENT.**
`rank-sufficient` (Verify-Rank-Sufficient) says no run of any program emits the
dry marker. It is a real body: `evaluate` is a root subscribe followed by a
drain, and the rows below are that split plus the fit the drain half stands on.

**WHAT ORDERS THE ROWS IS THE DIRECTION THE DEPTH TRAVELS.** Every route that
seeded the rank from outside is refuted, because a value deepens on the way OUT
and re-enters on the caller's witness. `Rx.Hop-Depth` reads the quantity off
the value instead, so a bound on it is carried by the induction that builds the
value rather than asserted about it.

**A FAILING GUARD IS NOT AN ERROR, AND THAT IS WHY THE TIER IS PROBEABLE.** A
guarded clause returns a `dry` emit and the run continues, so both sides
compute at every program — `hopFits` included, which is why its rows spend a
decision procedure rather than a pin.

### Open questions

- **WHAT BOUNDS THE REFOLD COUNT, NOW THAT NOTHING ELSE IS UNTIED?** The
  two-currency half is settled: the entry's rank IS the hop reading, each
  flattener's drop is a definitional `suc`, and no counter is left to exhaust.
  What the reading buys that in exchange for is one premise — that a scan
  refolds at most STORE-BOUND times — argued from the accumulator being stored.
  A run's bound is the fuel it was given and fuel counts ARRIVALS, so a cascade
  landing entirely inside one subscribe frame refolds once per literal and
  consumes none. Measured: four programs differing in literals alone read the
  SAME rank while their depth multiplies by three per literal. Both rows are
  open on exactly that region.
  relevant: `drain-dry-free`, `dry-operator`

### Big picture tier roadmap

- **PAY FOR `k ≤ V`, OR ESTABLISH THAT IT CANNOT BE PAID.** The reading's scan
  clause charges a store-bound-th power on the premise that a scan refolds at
  most bound-many times, and `Rx.Hop-Depth`'s header carries why nothing pays
  for it. The family that shows the gap is built and measured in
  `Probed.Operator-Root`, and its root is a flattener, so every layer it grows
  is a layer the run enters. This is the only open leg that can still refute the
  measure the other two are built on, which is why it goes first and why its
  outcome may be a restatement rather than a discharge.

- **CARRY THE BOUND OUT OF THE WALK RATHER THAN ASSERTING IT ABOUT THE VALUE.**
  Every dead route asked the emitter's rank to dominate a value it had not
  produced yet; the measure inverts that, since the three `*All` nodes each add
  one, so a carrier's own reading already sits strictly under the rank its
  emitter entered on. The leg is the strengthened return type: the burst walk
  reports its emissions' hop content alongside them, invariant in the motive,
  and the hop edge spends that report instead of a fact about an arbitrary
  inner. Ordinary induction, and `entry-hop-fits` is its base case.

- **MOVE THE BUG CACHE OFF THE TYPECHECKER (Anthony).** Every stored case pins a
  whole run by `refl`, so the gate normalises the evaluator once per case and
  the file is append-only: two cases already cost minutes, and the larger one
  took the gate down twice. The two predicates a case pins — agreement and
  well-formedness — are the two `QuickCheck.agda` already evaluates COMPILED, so
  the leg is a corpus and a `main` reading it rather than new machinery; compare
  the BOOLEANS, and hold every row to BOTH, which the per-case cost forbade.
  This narrows no question. It is what makes the other two affordable to probe:
  every rank measurement they need pays the cache's cost on the way to CI.

### The ledger

- **`drain-dry-free`** (Verify-Rank-Sufficient) — FALSITY,
  `REFUTED×2, PROBED×4`: every arrival after the root frame, conditioned on
  `hopFits` at the schedule's own slot reading and not one the caller picks.
  The fit holds flat across twelve drain states and is TIGHT at the plainest,
  so the rows sit where it is closest to false.

- **`dry-operator`** (Verify-Rank-Sufficient.Dry) — SHAPE,
  `REFUTED×2, DEAD ROUTE, PROBED, RECOVERY`: the THREE FLATTENERS' dry-freedom
  under the entry invariant read at the schedule's own store bound. First
  coverage at a root `opShape` admits, and the rank it is entered against was
  measured there NOT to move with the source the run folds over.

- **`entry-hop-fits`** (Verify-Rank-Sufficient) — DIFFICULTY, `PROBED`: the fit
  at the door, where the chain really is the one the root subscribe built out
  of `e`. Probed at three shapes including a share holding a recursion, each
  witnessed by the decision procedure rather than a pin.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `rank-sufficient`, so proving anything here while tier 1 is open bets
on ground a refutation of the descent would move.

**THE TIER IS ONE STATEMENT.** `The-Proof` draws `evaluate-well-formed`
(Part13) and nothing else from this tree, and every `Verify-Well-Formed` module
sits in its cone. `Verify-Support`'s three leaves are here rather than in a tier
of their own: nothing but Part3 consumes any of them.

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
- **`mint-install-survives`** (Node-Fresh) — DIFFICULTY, `RECOVERY`: a minted
  node survives the body subscribing under it. The statement is unchanged from
  the proven form its header recovers; what moved is the recursion the
  freshness ring was matched against.
- **`subscribeE-qd` / `pushBurst-qd`** (Queue-Dead) — DIFFICULTY, `RECOVERY×2`:
  two members of that same ring — an empty queue below the watermark stays
  empty across a subscribe and across a push. Same recovery, same blocker.
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

