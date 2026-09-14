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
  row of that same tier, and must still be FALSITY or SHAPE. Nothing else
  would notice this section aging, so that list is the one thing kept
  current: a name off the ledger means the question is answered or its row
  was restated. SHAPE counts because a question's rows convert FALSITY →
  SHAPE as it is ANSWERED — that is what a half-answer leaves behind, and
  holding the list to FALSITY retired a question at the very moment the
  narrowing it exists to record had happened. When nothing risky is left,
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
 └─ evaluate-well-formed                 Verify-Well-Formed.agda — tier 2
     ├─ rank-sufficient                  Verify-Rank-Sufficient.agda — tier 1
     └─ burst-drain-well-formed          one postulate — tier 2

  every tier above is stated over Rx.Exp's syntax
```

The descent `rank-sufficient` guards is the evaluator's own and is stated
nowhere else: `Acc _≺_` over a lexicographic triple — unconnected shares,
`obsDepthᵉ` joined with what the store holds, `syncSizeᵉ` — seeded at every entry
from outside the machine and dropped at three guarded peels, each a proven body.
No quantity above `Rx.Evaluator` mentions it, which is what lets one statement
close the whole descent.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 1 — the descent never goes dry

**THE TIER IS ONE STATEMENT AND IT IS CURRENTLY FALSE.** `rank-sufficient`
(Verify-Rank-Sufficient) says no run emits the dry marker; `Refuted.Dry-Wrap`
kills it three times against the evaluator as it stands. It is seven bodies
over seven leaves: both cycles' totality is a real induction now, and the risk
each held fell onto the clauses that read a component of the entry against the
term — the slot subscribe's share connect, and the walk's consume, where the
hop lives.

**AND THE MEASURE IS HELD BY SOMETHING NO STATEMENT MENTIONS: THE RUN HAS TO
COMPUTE IT.** Three non-structural edges TEST a reading and emit dry on the
negative answer, so an inadequate figure is a WRONG ANSWER rather than an open
obligation, and every syntactic candidate died that way. The relation lifts
that — inhabitation is a PROOF obligation, free to use a measure the machine
cannot compute — and the other two leaves carry no arithmetic at all.

### Big picture tier roadmap

- **MAKE THE HOP'S PREMISE TRUE: `burst-carries`, STATED OVER THE RELATION.**
  The hop is closed: `subscribeInner!` is a body, the cycle's seven members are
  one mutual block, and the descent it spends is `hop-guard` applied to a report
  that travels with the value from the burst that produced it. That report is
  `burst-carries` — a subscribe entered at τ hands back a burst whose every
  observable is shallower than τ's rank. Stated over `subscribeE⇓` and over no
  function, which keeps it out of the cycle it is about, and it REPLACED a
  five-frame carried shelf: the push cycle splits one `All` emit by emit rather
  than re-deriving a bound per frame. Riskiest because everything above it is
  now a body — if it is false the door comes back.

- **PRICE THE TEMPLATE, NOT THE INPUT: STATE THE SUBSTITUTION LEMMA (Anthony).**
  Six refutations stand at the door and every one of them refutes a price stated
  in what a frame was HANDED — which is the convergence test's spiral signal,
  whose prescribed response is to change the mechanism. The change is a change
  of CURRENCY: what a template emits is a substitution instance of a subterm of
  it, and substituting DATA moves no `strmᵗ`, so
  `obsDepthᵉ (applyFn fn v) < obsDepthᵗ fn` strictly, read off the program with
  no machine state in it. `Rx.Obs-Depth.Substitution` sketches it against its
  proven twin `obsDepth-elimG`; `Probed.Template-Depth` holds the rows, one of
  which REFUTES the unconditioned form. It is the hop's own premise, so the leg
  above hands it its only remaining customer.

- **THE THREE LEAVES OUTSIDE THE CYCLE, AND ONLY THEN THE RE-POINTING.**
  `subscribeE!-input` is the slot subscribe — six arms and the share connect's
  `unconn` guard, the other place an entry component is read against the
  program. `drain!` is fuel induction and carries no guard. `mergeAllDrain!` is
  the leg above's finding: the ONE subscription site a burst never reaches,
  since its observables were queued when the lane limit was full and come back
  out of the STORE, so what it is owed is a field on the invariant record and
  not a premise. These three and NOT the leg above's leaf are what the
  re-pointing waits on: a run steps through them, while the carried report is
  only ever projected and handed to a constructor.

- **THEN THE LEAVES BOTH CYCLES LEFT, AND REFUTE EACH BEFORE GRINDING IT.**
  Both cycles are bodies now and their list plumbing is closed, so what is open
  is `subscribeE⇓-input-total` (the slot subscribe, six arms, the share
  connect's `unconn` guard), the two the push cycle localised the hop onto —
  `thruConsume⇓-total`
  (`∀ … (ac : Acc _≺_ τ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t) (id : Id) (now : Tick) (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) → thruConsume⇓ op nid κ id now o sched st (thruConsume ac op nid κ id now o sched st)`,
  where `subscribeInner`'s rank test lives) and `innerReact⇓-total`, which
  reaches the same edge through the flattener's bookkeeping rather than a fresh
  value — and `subscribeAll⇓-total`, which is the two cycles composed and falls
  out of them. Each is stated unconditionally on purpose: a witness is what says
  which conjunct `EntryOK` grows, and the leg above is where the growing
  happens.

- **AND `drain⇓-total`, WHICH IS ORDINARY FUEL INDUCTION ONCE ITS SIBLING
  EXISTS.** `drain⇓ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) → drain⇓ {e = e} fuel id sched st (drain fuel id sched st)`,
  three arms matching `drain`'s own — out of fuel, empty schedule, and a
  cascade followed by the recursive call at `suc nextId`. It carries no guard
  at all; what it needs is the cascade's own totality, which re-enters the
  subscribe cycle and so takes the leg above as a premise rather than
  repeating it. Separated for that reason and not by size.

- **`subscribeE⇓-nodry` AS A BODY, WHICH IS A SHELF AND NOT A DESIGN.** Twelve
  subscribe-cycle families, one arm per constructor, each reading dryness off
  the emit that clause BUILDS — `init`, a value, a `close … exhausted`, a
  plumbing retag. The shelf this consumes was cut back to `hasDry-++` when the
  tower went and comes back a lemma at a time, one per shape:
  `git show 234074e:agda/src/Verify-Rank-Sufficient/Dry-Emits.agda`. No triple,
  no rank and no order appears anywhere in it, which is exactly what the
  relation bought — an arithmetic obligation became a list induction.

- **AND THE UNREACHABILITY CLAIM LAST, WHICH IS WHAT `rank-sufficient`
  BECOMES.** With the arm gone the marker is unemittable because nothing that
  could emit it is in the module — so the theorem stops being about numbers and
  is the observation that no constructor of the relation builds a dry emit,
  which `evaluate⇓-nodry` already proves of every derivation. `Refuted.Dry-Wrap`
  goes red at that commit and is deleted with it: `make refuted` going red IS
  the signal, and its three witnesses are what made the claim false until then.
  Last because every leg above is what makes it true rather than something it
  waits on.

### The ledger

- **`subscribeE⇓-input-total`** (Verify-Rank-Sufficient) — FALSITY, `PROBED`: a
  derivation at a slot subscription's own output. Six arms, and the share one's
  connect reads the unconnected count against the entry's first component, so
  this is refutable exactly as its parent was. Builder half
  `subscribeE!-input`; connect arithmetic `connect-drops`.

- **`innerReact⇓-total`** (Verify-Rank-Sufficient) — FALSITY, `PROBED`: the
  same edge reached through the flattener's own bookkeeping rather than a fresh
  value, so it carries no rank test and inherits the store the walk left.
  Builder leaf `mergeAllDrain!`, whose queue comes out of the store and not out
  of a burst.

- **`subscribeAll⇓-total`** (Verify-Rank-Sufficient) — FALSITY, `PROBED`: the
  flatteners' wrapper, a node install between the two cycles above. It adds no
  guard of its own and inherits both halves' falsity; the three operators
  differ only in a state no clause reads.

- **`drain⇓-total`** (Verify-Rank-Sufficient) — FALSITY, `PROBED`: the same
  over the arrival cycle. It carries no guard itself; its cascade arm re-enters
  the subscribe cycle, so it inherits that leaf's falsity rather than adding
  one. Its builder half is `drain!`.

- **`thruConsume⇓-total`** (Verify-Rank-Sufficient) — FALSITY,
  `REFUTED, PROBED`: the one clause taking a value and subscribing it,
  customer of both shelves. Builder `subscribeInner!`. Open: the enqueue arm,
  two operators on another node state, and the hop `subscribeInner⇓-total`.
  Substitution: `obsDepth-eval-open`, `obsDepth-wkTm`, `applyFn-strict`,
  `syncSize-applyFn`, `eval-case`, `eval-if`, `data-of`, `dataSize`,
  `+-dataˡ`, `+-dataʳ`, `×-dataˡ`, `×-dataʳ`. Carried: `applyFn-ok-×`,
  `applyFn-ok-+`, `map-frame-carried-obs`, `scan-frame-carried`,
  `take-frame-carried`, `thru-outer-frame-carried`, `from-inner-carried`,
  `subscribe-carried-schedule`, `burst-handed`, `burst-widen`, `payOf`,
  `rankOf`, `source-carried`, `of-carried`, `all-carried`, `burst-carries`.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `rank-sufficient`, so proving anything here while tier 1 is open bets
on ground a refutation of the descent would move.

**THE TIER IS ONE STATEMENT OVER ONE LEAF.** `The-Proof` draws
`evaluate-well-formed` and nothing else from this face. That name is a real
body: it splits the descent's dry-freeness across the subscribe frame and the
drain, and hands the two halves to the leaf. The split is what CONSUMES tier 1
— a leaf handed `rank-sufficient` directly would assert its sufficiency without
ever checking it, which is the shape the leaf law refuses.

**AND THE BOOKKEEPING IS DELIBERATELY UNCARVED.** The protocol argument's shape
is a function of a recursion tier 1 may still restate, so pieces cut against
today's machine are inventory and not progress. One leaf at full strength; carve
it when the descent under it settles.

### Big picture tier roadmap

- **instantiate the leaf before carving it** — `burst-drain-well-formed`. Both
  its hypotheses and its conclusion compute at a closed program, so the whole
  statement is decidable by `refl` at canonical shapes — and nothing has ever
  run the protocol automaton over an evaluator emit stream, at any program. The
  commit is the probe alone: which operators the rows reach, which they do not,
  and whatever a red row forces on the statement. It is taken first because
  every way of carving this face into pieces is a bet on the leaf being true,
  and a leaf refuted after the carve costs the carve as well.

### The ledger

- **`burst-drain-well-formed`** (Verify-Well-Formed) — FALSITY, `NO EVIDENCE`:
  everything the protocol argument owes about a run whose subscribe frame and
  whose drain are each dry-free. Never instantiated at any program, and the
  automaton it asserts acceptance under is defined, so the whole statement
  computes.

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

