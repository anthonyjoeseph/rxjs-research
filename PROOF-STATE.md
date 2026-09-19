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
formal-verification-batchSimultaneous    The-Proof.agda — a BARE POSTULATE
                                          while the machine is rewritten — tier 2
 └─ batch-agreement                      proven, and claimed by Main in its
                                          own right rather than through the top

batch-online                              claimed by Main in its own right —
                                          nothing above consumes it — tier 3

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

## Tier 1 — the unique primitive, and the two trees that ride on it

**THE ENTANGLEMENT, PLAINLY: the plain tree is rxjs, and must not know what an
envelope is (Anthony).** TypeScript has two layers — plain rxjs, the published
library, and an `InstEmit`-carrying one over it called srxjs — while Agda has
one tree doing both jobs, which is why the evaluator mints envelopes it has no
business knowing about. The tier splits them: a plain tree and evaluator
mirroring ordinary rxjs, and a simul mirror tree whose formers are the
envelope-carrying operators, elaborated down by `toPlain`. What the proofs
above then quantify over is a program written in the SIMUL palette — which is
the restriction on the input type that nothing here could state before, and the
reason the split is worth a whole tier.

### The monster

(no monster) — the tier declares no statement. What it lands are DEFINITIONS,
one type constructor and a second tree, which cannot be false, only wrong; what
catches one wrong is the oracle disagreeing before any of it reaches Agda, and
then the existing proofs failing to typecheck over the split. A cone cannot aim
at either, and one drawn here would forbid the wide refactor that IS the tier.

### Big picture tier roadmap

- **THEN THE CYCLE'S FIVE, WHICH ARE WHAT THE STORE STEPS ARE FOR.** The
  nine step readings are proven and the setNode lemmas under them are
  general, so what is left is the induction those nine feed: the same
  eleven-armed walk over the delivery relations the count's half already
  took, read for the parked total, where each arm is either a step
  reading already in hand or a recursive call. Six arms are minted with
  it, as clauses rather than as leaves.

- **THEN THE DRAIN AS A BODY, WHICH IS WHAT THE WHOLE PAIR WAS FOR.** It
  is the only statement in the builder standing on nothing, and the only
  one that can spend the disjunction: a pop drops the parked total
  outright, and the one thing that can put items back needs a connect,
  which drops the count the descent is ordered by.

- **THEN THE FLATTENERS AND `takeᵖ`, AND NO FORMER IS OWED AFTER ALL
  (Anthony: "the flattens, mergeAll etc, _are_ the primitives … they can
  be implemented however you want, just so long as they … mirror exactly
  what rxjs would do").** The recorded ask — a multicast inside an
  expression — was an envelope obligation smuggled into a plain question:
  in rxjs every outer emit of a `mergeAll` IS an observable, so nothing
  owes an output emit without a lane. `takeᵖ`'s behaviour is measured
  rather than inferred and the plain `takeᵉ` already has all three facts.

- **THEN THE DERIVATION-LEVEL OBLIGATIONS THE ARRIVAL SPINE STILL OWES.**
  The delivery cycle's eleven relations now carry the count, and the
  spine above them — a chain step, a cascade, a drain — does not. It is
  the same induction one level up, over relations whose every arm is a
  cycle member already discharged, and it is what a `Below` handed to
  `evaluate!` will be spending. Small, and it closes the layer rather
  than opening one.

- **THEN THE REST OF THE SIMUL OPERATORS MIRRORED IN `Tm`/`Ty` (Anthony).**
  Each TS simul operator mirrored as an Agda definition in the value
  language, in the same fashion, so the correspondence is readable rather
  than asserted. The first thing tested is the SEEDED channel the share
  reads at subscribe time, a further ask than a plain channel which `Tm`
  may not have. `batchSyncᵉ` is already one, at the index Anthony has
  ruled on. **AND IF THE LANGUAGE CANNOT SAY ONE, STOP AND REPORT
  (Anthony).** A new `Ty` constructor or `Tm` former changes what a
  program can SAY, so it decides what every theorem above quantifies
  over — the same reason the spec is not an agent's to move.

### The ledger

- **`drainQueue!`** (Rx.Evaluator.Builder.Frames) — FALSITY, `DEAD ROUTE`: the
  builder's one remaining cut cycle, a parked lane's backlog spent under the
  frame whose closing side runs the drain. Not instantiated.

- **`{mergeAll,switchAll,exhaustAll}ᵖ`** (Rx.Elaborate) — SHAPE,
  `DEAD ROUTE×4`: the elaboration's per-former plumbing, after the two sources
  came out of it. The outer's bookkeeping needs no plain home — it rides the
  lane — so what is left is the compile of an envelope stream into a stream.
- **`red-{scanned,flushed}`** (Rx.Evaluator.Reducible) — DIFFICULTY,
  `DEAD ROUTE×4`: a value handed back out of the store arrives without the
  candidate it went in with. True through the term face, which the walk that
  spends them cannot call.
- **`takeᵖ`** (Rx.Elaborate) — DIFFICULTY, `DEAD ROUTE`: the author cuts on
  VALUES and a plain `takeᵉ` above the envelope cuts on BATCHES, so the
  elaboration owes a count that crosses the level and closes at the cut.

- **`queued-{emit,close,emits,subs,drain}`** (Rx.Evaluator.Unconnected) —
  GRINDABLE, `TWIN×5`: the delivery cycle read for the parked total instead of
  the count, where a park forces a disjunction.

## Tier 2 — the proof statement, once there are two trees to state it over

**WHY THIS IS DEFERRED RATHER THAN SKIPPED (Anthony: "it will be easier to
communicate my ideas once the syntax trees and working eval are in place").**
Tier 1 lands the syntax and a working evaluator, and nothing above can be
restated until both exist — settling the statement first argues a design in the
abstract, against trees nobody has run. So the order is trees, then statement.
What makes it a tier rather than a leg of tier 1 is the kind of failure
available to each: tier 1 lands DEFINITIONS, which can only be wrong, and these
are STATEMENTS, which can be false.

### The monster

(no monster) — a monster is a NAME, and this tier's statements are not written
yet. The top line standing today is a bare postulate over the machine tier 1 is
replacing, so it is the thing to be restated rather than a thing to aim at. The
tier takes a monster at the commit that first states the restatement; until
then tier 1 is the lowest open tier and holds the cone.

### Big picture tier roadmap

- **THE TOP LINE, RESTATED AND POSTULATED THROUGH (Anthony: "just make it
  typecheck for now and postulate out all the details").** The theorem
  quantified over a SIMUL tree, elaborated by `toPlain` and run on the plain
  evaluator, with `spec-batchSimultaneous` and its mirror at
  `instEmitᵗ uniqᵗ a` — no bridge. The impl becomes a `Tm` carrying a free
  variable of the stream type, `Ty` having no arrows; the spec stays an Agda
  function over `Val`, being the mathematical statement rather than a library
  one. Everything between is a leaf postulate. What the leg buys is a tower
  that TYPECHECKS over the new trees, which is what makes the legs below it
  arguable from code instead of from prose.

- **THEN WHATEVER LEGALITY THE TOP LINE NEEDS, STATED OVER THE TABLE AND NOT
  OVER THE RUN.** The old leaf claimed the automaton rejects no emit of a
  canonical run, and it was false: a slot is writable at the envelope type and
  elaboration passes an `input` through untouched, so a table naming an instant
  past the counter reaches the output without entering a clause. The route that
  split that claim over the syntax died with it. What is owed instead is a
  predicate on the SLOTS — and the first question it answers is whether it is
  per-slot or per-table, since a shared slot is read at several sites.

- **THEN THE PURITY RULING, WHICH DECIDES WHETHER THE TOP LINE CARRIES A
  HYPOTHESIS AT ALL.** A simul tree's non-observable positions take an author's
  own terms and a unique is reachable from there, so a mapping function can
  forge an envelope at any instant it likes. Either a predicate on the tree,
  discharged per program by a decision procedure, or a restriction on the TYPES
  at those positions in the mould of `isData`, making the forgery
  unrepresentable. The precedent sits in the tree already — guardedness here is
  not a predicate but a context gate, synchronous self-reference being a type
  error. The leg is the ruling and the churn it causes.

- **THEN REDUCIBILITY'S SECOND HALF, AND IT IS WHERE THE RED LINE IS TESTED.**
  The existing candidate is about a FRESH subscribe and says nothing about a
  cascade, which resumes stored machinery. Its standing argument that no state
  invariant is owed rests on a fan-out carrying no PAYLOAD — and protocol
  traffic is precisely what a fan-out does carry, so the argument does not
  transfer. The soundness half therefore wants its own invariant on the
  evaluator's state, seeded at the root and preserved per cascade, leaving the
  guard measure and the accessibility argument untouched. It holds, or the leg
  reports.

- **AND THE README'S TWO SEMANTIC LAWS COME BACK HERE, DELETED FOR NOW
  (Anthony).** `readme-batch-order-is-delivery-order` and
  `readme-one-subscribe-one-batch` were stated over the machine tier 1 is
  deleting, so porting them twice buys nothing.  They are gone from `src` and
  unwired from Main; `git show 5ade0b38:agda/src/Readme-Theorems.agda` restores
  both statements and the header recording that every probe row sat at a
  program with no flattener — which is where their risk actually lives, and the
  first thing a restatement owes.

### The ledger

- **`formal-verification-batchSimultaneous`** (The-Proof) — FALSITY,
  `RECOVERY`: the top line, bare while the machine under it is rewritten. It
  was a body over one leaf; that leaf was refuted by a slot table scripted at
  the envelope type, and its subject is the envelope the evaluator no longer
  mints.

## Tier 3 — what Main asserts beside the main theorem

**THE MISC TIER, AND IT IS NOW ONE ROW PLUS A DEBT.** It held ten claims about
the machine — determinacy, fuel coherence, the μ laws, run monotonicity and the
three timing claims. Every one was stated over the evaluator tier 1 is
rewriting, so they were deleted with recovery shas rather than transported: a
claim about the wrong semantics is not evidence about the right one, and none
of them blocked anything below. What is left standing is the one claim read off
the batcher rather than the machine.

**SO THE TIER'S REAL CONTENT IS A DEBT, AND IT IS NAMED RATHER THAN CARRIED.**
Main asserts less than it did, and that is honest only while the restatement is
scheduled — which is what the legs below are. They cannot start until the new
machine computes, so this tier stays last for the reason it always was.

### The monster

`batch-online` — the only live statement here, and the only one a concrete
program still decides. It says the batcher's answer on a prefix is the prefix
of its answer, which is what makes a streaming reading of the spec legitimate
at all; its unqualified form was refuted by a split closing one instant and
leaving a second open, so the form standing today is the repaired one and the
repair is exactly where it could still be wrong. A leaf's cone is its
statement's vocabulary.

### Big picture tier roadmap

- **RESTATE DETERMINACY OVER THE NEW MACHINE, AND INSTANTIATE IT BEFORE
  GRINDING ANY OF IT.** The old ring quantified over a subscribe relation of
  twenty families and nothing ever ran two derivations at one set of indices;
  the relation went with its evaluator and the ring went with it. What is owed
  again is the same fact about whatever machine lands — a frame admitting two
  outputs at one set of indices means the machine is not a function. The leg is
  to state it, then refute at a single arm before inducting over all of them,
  which is the cheap order and was never taken.

- **THEN THE FUEL AND UNFOLDING LAWS, WHICH ARE THE ONES A PROGRAM DECIDES.**
  Fuel coherence, `μ-unfold`, and more fuel extending a run rather than
  rewriting it: three statements the old machine carried with a sweep and three
  rows behind them. They are cheap to restate and cheap to probe, and the
  region the old receipts never reached — a program entering a flattening node,
  a source firing past one tick — is the region the rewrite most changes. The
  leg's product is rows there, or a refutation.

- **THEN THE TIMING CLAIMS, WHICH NEED AUTHORING RATHER THAN PROOF.** Locality,
  non-interference and timing invariance were stated over nine postulated
  abstractions and asserted close to nothing; `causality` was satisfiable by an
  empty helper and `defer-shift` was ⊤-typed outright. Restating them means
  DEFINING the abstractions, which is claim authoring and needs Anthony. **Not
  GRINDABLE and never will be** — no precedent makes them mechanical, because
  nothing is stated yet.

- **AND `batch-online` IS THE ONE LEG THAT CAN RUN TODAY.** It reads the
  batcher and not the machine, so the rewrite does not touch it and nothing
  above it waits. Its receipt sits at the very split that refuted the
  unqualified form; what it has never been run against is a prefix cut INSIDE a
  flattened instant, which is the shape the new machine will start producing.

### The ledger

- **`batch-online`** — DIFFICULTY, `PROBED`: the restated form, instantiated at
  the very split that refuted the unqualified one — a left side closing one
  instant and leaving a second open, whose terminal flush was the old
  statement's counterexample.
- **The claims Main no longer makes — a DEBT, not a row.** Determinacy, fuel
  coherence, the two μ laws, run monotonicity and the three timing claims are
  deleted, not discharged; `git show b5601783` restores all four modules and
  the three rows that were the only instantiation any of them had. They are
  uncounted here deliberately, because a postulate ledger counts statements
  `agda/src` makes and `agda/src` no longer makes these.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.
