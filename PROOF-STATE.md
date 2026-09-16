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
formal-verification-batchSimultaneous    The-Proof.agda — REAL, module postulate-free
 ├─ batch-agreement                      proven
 └─ evaluate-well-formed                 Verify-Well-Formed.agda — REAL, one match
     └─ burst-drain-well-formed          one postulate — tier 2

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

## Tier 1 — `take-bounds-values`

**THE TIER IS ONE STATEMENT AND IT IS ALREADY A BODY.** A program whose
outermost node is `take k` emits at most k values — the smallest claim here
about the EVALUATOR's own bookkeeping rather than about a correspondence: no
spec, no batching, no second run to compare against, and no need for the run
relation to be a function before it means anything.

**IT IS FIRST BECAUSE IT IS THE REHEARSAL (Anthony).** What it exercises is the
induction over the drain that every tier below also owes, with none of their
apparatus in the way. A run splits definitionally into its subscribe frame and
its drain, and the take node's remaining budget is the only thing crossing
between them, so the statement carves at exactly the seam the well-formedness
face has to carve at — and the pieces here are arithmetic rather than an
automaton.

### The monster

`take-burst-bound-suc` — the frame's half at a positive budget, and the
deepest thing here that can be false on its own: the node's decrement happens at the dispatch while the cut is
emitted from the frame, so a path that delivers before it spends parts from
this inequality and from nothing else. Its falsity takes the tier's statement
with it, because the budget it LEAVES is what the drain's half is denominated
in — a frame that hands on too much satisfies its sibling and fails the claim.
The sibling is admitted below rather than climbed over: the tier's own subject
has the whole tier for a cone and would decide nothing.

also: `take-bounds-values` — the tier's subject. Admitted only because this branch is the one that CARVED it: the assembly and its glue arrive here as added lines. It retires when the branch lands, and while it stands the cone decides nothing — which is the cost of the carve, paid once.
also: `take-drain-bound` — the tier's other leaf, whose cone is its own arithmetic and excludes the frame's; the two are ground together and neither is reachable from the other.
also: `burst-drain-well-formed` — tier 2's monster. Admitted because the branch that carved this tier out of that one carries that face's seam and its two leaves, and the check reads the branch rather than the commit.
also: `evaluate-deterministic` — tier 3's monster, whose statement and leaves are already declared, on the same branch and for the same reason.

### Big picture tier roadmap

- **THE FRAME'S ARITHMETIC, AT A POSITIVE BUDGET.** The split on `k` is done
  and the zero arm is a theorem: the walk's transport lifts off the triple, so
  the arm that mints no node computes off an abstract subterm. What remains is
  `take-burst-bound-suc`, where a node IS minted and the decrement at the
  dispatch has to agree with the cut at the frame. Under it is one mechanical
  fact the tree does not have: what `takeVals` passes through plus what it
  reports remaining is EXACTLY its budget, an equality rather than the
  inequality the consumer needs. Land that equality and stand the arm on it
  through the dispatch.

- **THEN THE DRAIN'S CARRY, WHICH IS THE INDUCTION.** `take-drain-bound` says
  the drain emits no more than the budget it was left. The drain re-enters
  itself and the budget is state it threads, so the motive is the node's own
  reading and the grind is an induction over the drain — the same shape both
  seam leaves of the tier below owe. One row reaches it today, at a cut
  spanning two arrivals where the frame emits nothing at all, so the whole
  bound is decided in the drain.

- **THEN PUSH THE ROWS PAST THE COVERAGE BOUNDARY THE PROBE DECLARES.** Three
  shapes are unreached and each is where a budget argument is least likely to
  be uniform: a take nested under another take, where two nodes' budgets are
  live at once; a budget that is not a literal, so `evalTm` is a real step; and
  any flattening program, where the inner subscribes mint nodes between the
  frame and the drain. A refutation at any of the three is worth more than
  either grind above it.

### The ledger

- **`take-burst-bound-suc`** (Verify-Take-Bounds) — FALSITY, `PROBED`: what the
  subscribe frame emits plus what it leaves in the node is within `k`, at a
  positive budget. One row reaches it; the decrement at the dispatch and the
  cut at the frame are the two points that can disagree. The zero arm is
  proven.

- **`take-drain-bound`** (Verify-Take-Bounds) — FALSITY, `PROBED`: the drain
  emits no more than the budget the subscribe frame left in the take node. The
  rehearsal's inductive half; one row reaches it, at a cut spanning two
  arrivals.

## Tier 2 — `evaluate-well-formed` (parked behind tier 1)

Built on the run's own derivation, which is now a body the whole tower
descends through. Parked behind the rehearsal, which exercises this face's
drain induction with none of its apparatus in the way.

**THE TIER IS ONE STATEMENT, NOW CARVED AT ITS SEAM.** `The-Proof` draws
`evaluate-well-formed` and nothing else from this face, and everything from
that name down to the two leaves is a body: the run's constructor splits the
burst from the drain, the automaton's state between them is named, and the two
halves are composed by a proven fold law rather than by assumption.

**SO WHAT IS OPEN IS TWO PRESERVATION CLAIMS AND THE RELATION THEY MEET IN.**
Both are born without evidence — the sweep that covered the old fused leaf
computed the concatenation's verdict and never the seam — and the seam is the
first thing on this face a program can be run against directly.

### The monster

`burst-drain-well-formed` — the DEEPEST node here whose cone still holds the
work that kills it. Below it are two leaves and the seam relation they are
denominated in, each with a cone of its own vocabulary, so naming one would
forbid its sibling; above it sits a wrapper supplying derivations. It can be
FALSE, not merely unproven: a run the automaton rejects kills both leaves, the
seam, and the WellFormed quantification `The-Proof` draws from here.


### Big picture tier roadmap

- **THEN RUN A CLOSE, WHICH IS THE ONE FIELD NO ROW HAS CONDITIONED.** The drain's
  step is reached: a hot slot firing at tick zero delivers, the emit count is
  pinned so the row cannot be the exit again, and the fold now runs over
  envelopes the drain minted. What that leaves is the shadow field's
  HYPOTHESIS. It is conditioned on `dying` because the all-sources form is
  false — a victim carrying its own exhausted close parts the two counts — and
  `dying` is populated by the CUT chain, which nothing here runs: the one close
  the rows reach is `exhausted`, so every row discharges the condition
  vacuously rather than exercising it. A `take` cutting a live source is the
  cheapest shape that could still refute either leaf.

- **THEN CARRY THE INVARIANT ACROSS THE DRAIN'S OWN RECURSION.** `drain-wf` is
  generic in the seam state precisely so it can re-enter itself, which means
  the grind is an induction over the drain with the relation as its motive —
  and the fields the burst form deliberately omits (node-counter coherence,
  the after-completion plumbing claim) are re-established once at the frame's
  exit rather than threaded. That exit is where the second invariant record
  and its heavier vocabulary land, and not before: carving it now would be
  inventory against an assembly nothing has written.

- **THEN REACH THE FRAGMENT THE GENERATOR CANNOT WRITE.** The sweep's coverage
  boundary survives the carve and is not decoration: a context other than two
  nat slots, a slot holding an observable rather than data, and any fuel but
  its own. The first two are where the protocol automaton's sharing and
  connect rules live, which is exactly where a bookkeeping argument is least
  likely to be uniform. Extend the harness rather than the argument.

- **AND THE BASE CASE LANDS WITH THE ROOT HALF'S BODY, NOT BEFORE.** The
  initial schedule and state do satisfy the seam relation against the
  automaton's initial state and the proof is five projections — but its only
  use today would be as an argument to the very leaf it is meant to start,
  which the leaf law refuses. It is written down as a finding in the
  relation's own module and lands in the commit that turns that leaf into a
  body.

### The ledger

- **`subscribeE-root-wf`** (Verify-Well-Formed) — FALSITY, `PROBED`: the root
  subscribe frame's burst drives the automaton to a state standing in the seam
  relation to the evaluator's. Computable at concrete programs and
  uninstantiated; it also owes its own base case.

- **`drain-wf`** (Verify-Well-Formed) — FALSITY, `PROBED`: from any state in
  the seam relation, the drain's emits drive the automaton to a state that is
  paid up. Generic so its induction can re-enter itself; nothing has run a
  drain against it.

## Tier 3 — `evaluate-deterministic`

The determinacy face, parked behind both dedicated tiers above. Nothing open
depends on it: the tiers below are stated over the ONE output the
builder produces, so an inequality or a verdict about that output means what it
says whether or not a second derivation could have produced another. What
determinacy buys is the STRENGTHENING — a leaf quantified over an arbitrary
derivation becomes a fact about the machine rather than about the builder — and
a strengthening is worth exactly nothing until the weak form is proven.

### The monster

`subscribeE-det` — the subscribe relation itself, which is where determinacy
can actually fail. Its falsity would be a fact about the EVALUATOR rather than
about a claim: a frame admitting two outputs at one set of indices means the
machine is not a function, and then every face's quantification over
derivations is over a set nobody has characterised. It is the deepest node
whose falsity takes the whole tier. A leaf's cone is its statement's
vocabulary, so it reaches neither its sibling nor the assembly consuming both —
those are admitted below, where the admission is read with the roadmap.

also: `drain-det` — the other half of the same assembly, off the frame's cone and ground alongside it.
also: `evaluate-deterministic` — the tier's subject, which consumes both leaves and is unreachable from either.

### Big picture tier roadmap

- **INSTANTIATE THE RING BEFORE GRINDING ANY OF IT.** The subscribe relation is
  twenty families and nothing has ever run two derivations at one set of
  indices. A refutation at a single arm is worth far more than a partial
  induction over all of them, and it is cheap: build two derivations of the
  same frame by taking the builder's and one arm's alternative, and ask for the
  `refl`. The arms that do not follow from the head constructor are the target;
  the rest are decided by pattern matching and cannot refute.

- **THEN GRIND `subscribeE-det`, ARM BY ARM.** What separates the arms is
  EQUATION PREMISES rather than constructors, which is why this is not a
  mechanical induction: two arms can agree on the head and be told apart only
  by a derived equality on the schedule or the state. Each such pair is a
  lemma, and the lemmas are what the leg delivers — the induction over them is
  the cheap half.

- **THEN `drain-det`, AND THE ASSEMBLY'S BODY.** The drain's determinacy is an
  induction whose motive is the subscribe result, so it lands second by
  necessity rather than by choice. When both leaves are bodies the assembly
  stops being a claim over postulates and becomes what its name says, and the
  faces below can be restated over an arbitrary derivation in whatever order
  their own schedules reach.

### The ledger

- **`subscribeE-det`, `drain-det`** (Verify-Determinacy) — FALSITY,
  `NO EVIDENCE`: each family admits one output at its own indices. Nothing has
  instantiated either, and the arms that do not follow from the head
  constructor are separated by equation premises — unwalked.
## Tier 4 — misc: the top-line semantic claims

The MISC tier, and the only one not dedicated to a single definition: claims
Main asserts beside the main theorem, off its critical path. They share a
ledger because none of them is on any other tier's route, not because they
share a subject.

### The monster

`readme-batch-order-is-delivery-order` — the flagship law, and the deepest node
here whose cone still holds the work that kills it. Below it is the SPEC, which
cannot move, so the descent bottoms out at the lowest claim rather than at a
leaf. Every other row is stated over values in delivery order, so if batching
reorders or drops, the seven instances and the take law go with it and the two
that survive assert something about a stream nobody should trust. It can be
FALSE at a program with a flattener, which is exactly the region no row has
reached.

### Big picture tier roadmap

- **re-probe the three universal laws at a program that has a SOURCE** —
  `readme-batch-order-is-delivery-order`, `readme-take-counts-values`,
  `readme-one-subscribe-one-batch`. Their rows stand at a closed literal in an
  empty slot table, so every one of them is decided inside the subscribe frame
  and nothing arrival-driven has ever been instantiated: the flagship law is
  about batching ACROSS instants and no row has reached a second one. A
  scripted hot slot does, on the harness `Probed.Pipeline-Claims` already
  carries. A refutation here is SPEC-level — surface it, do not patch it.
- **the seven instance claims are UNBLOCKED, and that IS the leg** —
  `readme-diamond`, `readme-each-next-own-instant`, `readme-cascades-inherit`,
  `readme-completion-cascades`, `readme-share-connect-no-replay`,
  `readme-late-join-growth`, `readme-serial-joins-mirror-rxjs`. Every one is
  hard-wired to a flattener, and while the descent was stuck at one no `refl`
  row could be written for any of them at any program. It is not stuck: the
  corpus runs a self-referential μ through every flattener. Re-run the
  recovered predecessor battery and let the rows say which of the seven hold
  as stated. A refutation here is SPEC-level — surface it, do not patch it.
- **draft the abstractions and ASK** — `locality`, `non-interference`,
  `timing-invariance`, `causality`, `μ-guarded`, `defer-shift`, over `Node`,
  `NodeSt`, `Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`, `retime`,
  `truncateIn`, `emittedBefore`. De-risking any of these means DEFINING the
  abstraction under it, which is claim authoring and Anthony's call. The
  commit is the drafted definition set and the question, not a discharge.

### The ledger

- **`readme-diamond`, `readme-each-next-own-instant`,
  `readme-cascades-inherit`, `readme-completion-cascades`,
  `readme-share-connect-no-replay`, `readme-late-join-growth`,
  `readme-serial-joins-mirror-rxjs`** — FALSITY, `NO EVIDENCE`: every one names
  a flattening program, and nothing has instantiated any of them. Probeable now
  that the evaluator computes through a flattener. A refutation is SPEC-level:
  surface to Anthony, do not patch.
- **`readme-batch-order-is-delivery-order`, `readme-take-counts-values`,
  `readme-one-subscribe-one-batch`, `id-inheritance`** — FALSITY, `PROBED×3`:
  instantiated now, but every row sits at a program with no flattener, which is
  where each statement's risk actually lives. Still FALSITY for that reason,
  not for want of a row.
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
- **`batch-online`** — DIFFICULTY, `PROBED`: the restated form, instantiated at
  the very split that refuted the unqualified one — a left side closing one
  instant and leaving a second open, whose terminal flush was the old
  statement's counterexample.
- **`μ-unfold`, `fuel-coherent`** (Evaluator-Theorems) — DIFFICULTY,
  `PROBED×2`: the two evaluator laws a spent battery instantiated at every
  canonical program without refuting. Separated from the rows above because
  their receipt is a sweep rather than a point.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.

