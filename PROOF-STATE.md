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
 └─ evaluate-well-formed                 Verify-Well-Formed.agda — REAL, a body
     ├─ evaluate-accepted                no emit of a run is rejected — tier 3
     └─ evaluate-settled                 the run stops settled — tier 3

adequacy / saturation / run-monotone      claimed by Main in their own right —
                                          nothing above consumes them — tier 2

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

## Tier 1 — `InstEmit` off the syntax tree

**THE ENTANGLEMENT, PLAINLY: the syntax tree carries the emit metadata the
implementation needs, and the spec's tree should not.** TypeScript has two
layers — a plain rxjs pipeline and an `InstEmit`-carrying one over it — and
Agda has one, which is why every statement about the language drags the
implementation's bookkeeping through it.

**THE SHAPE IS A MIRROR TREE AND AN ERASURE, NEVER A SECOND EVALUATOR.** A
second evaluator means duplicating the reducibility candidate and its
termination argument, which is the most expensive artifact in this repo, and
`dup-check` would be right to fire. With the mirror erased into the existing
tree, every theorem already proven applies verbatim to the erasure.

### The monster

(no monster) — this tier declares no statement either, and with one extra
thing worth saying: the erasure is where a mistake here would live, and an
erasure is a DEFINITION. It cannot be false, only wrong, and what catches it
wrong is the batching proof restated over the mirror failing to typecheck —
which is the tier's own third leg rather than a claim a cone could aim at.

### Big picture tier roadmap

- **DEFINE THE MIRROR AND THE ERASURE, AND NOTHING ELSE.** One tree carrying
  the plain-rxjs formers, one function into `Rx.Exp`'s tree, and the clause per
  former that says which existing node each mirror node erases to. Land it with
  no consumer: the tree and the erasure typecheck on their own, and a mirror
  whose erasure does not is a mirror with the wrong formers.

- **THEN RESTATE THE BATCHING PROOF OVER THE MIRROR.** `The-Proof` and
  `Batch-Theorems` are stated at `Closed`, so the restatement is a composition
  with the erasure and its content is whether the mirror's formers suffice to
  say what the batching claim says. This is the leg that decides the tree: a
  claim that cannot be restated names a former the mirror is missing.

- **THEN THREAD IT UNTIL IT TYPECHECKS.** The evaluator, `Reducible` and the
  CLI all read the old tree; whatever of them should read the mirror instead is
  discovered here, not designed in advance. It is deliberately last, because
  the two legs above are what say which side of the boundary each consumer
  belongs on.

## Tier 2 — the denotation, adequacy, and the take bound

**WHAT THIS FACE BUYS: an object that is not the machine.** Every statement in
the repo today is read off `evaluate↓`, so the machine's own bookkeeping — node
ids, arrival ordinals, the drain counter — is visible in every answer. A
denotation says what a PROGRAM means rather than what one run does.

**AND NOTHING OUTSIDE IT CONSUMES IT.** The well-formedness face was the one
consumer and no longer is, so the pair below is its own only consumer and nothing
constrains the domain's shape. Whether it earns its place is the open question
here, not how to define it — the finding is on `Beh` and `observe`.

**AND THE TAKE FACE IS HERE AS THE GUINEA PIG (Anthony).** The pair is false
without a restriction to programs that SATURATE, and `take-bounds-values` is
the one emission bound this repo states uniform in fuel. A candidate is tested
by whether that face satisfies it and whether that face's machinery proves it.

### The monster

`adequacy` — the soundness half, and the deepest node here whose cone holds the
work that kills it: it reaches the observation of a closed program, hence
`denote` and `observe`, and it reaches `evaluate↓`. Its falsity is the
retroactive kind, since it is what every later restatement of a machine-level
claim into a denotational one would be transported along — and the tier above
now transports one along it for real.

also: `saturation` — the other half of the pair, off `adequacy`'s cone because its statement quantifies over a prefix the soundness half never mentions.
also: `run-monotone` — a fact about the machine alone, which is why it survives every restatement of the domain and why nothing in the domain reaches it.
also: `take-bounds-values` — the take face, which is here to be measured against and shares no vocabulary with the domain.

### Big picture tier roadmap

- **STATE THE SATURATION RESTRICTION, BECAUSE THE PAIR IS FALSE WITHOUT ONE.**
  A guarded fixpoint with no `takeᵉ` above it emits one envelope per unit of
  fuel, so no finite `Stream` bounds its runs and there is no `meaning` at that
  program whatever the domain turns out to be. The leg's product is the
  predicate the two claims are quantified over — every program the bug cache
  carries already satisfies it, so the restriction costs the corpus nothing —
  plus the machine proof that the unbounded program falsifies the unrestricted
  form, which is a refutation rather than a receipt. It is first because it
  decides whether the domain below it is finite at all.

- **THEN RUN THE CANDIDATE AGAINST THE TAKE FACE, WHICH IS WHY IT IS IN THIS
  TIER (Anthony).** `take-bounds-values` is the one emission bound already
  stated uniform in fuel, so it is the worked instance a restriction has to
  admit — and the first question about any candidate is not whether it reads
  well but whether that face SATISFIES it and whether that face's own drain
  induction proves it does. A candidate the take face cannot discharge is
  discarded on the spot; one it discharges cheaply is a candidate whose
  machinery already exists. Expect several rounds: the product is a predicate
  that survived a real consumer, not the first one written down.

- **DEFINE `Beh` FOR THE FIRST-ORDER FORMERS AND EARN THE EQUATIONS.**
  `ofᵉ`, `emptyᵉ`, `mapᵉ`, `takeᵉ` and `scanᵉ` denote without any of the
  machinery the flatteners need, so this is where the domain's shape is
  actually decided and where a compositionality equation can first be stated at
  all. The leg's product is the domain plus one equation per former, not a
  proof of adequacy — and the equations are what the tier above inducts over,
  so a former whose equation cannot be stated is a former whose well-formedness
  clause will not be writable either. Every remaining row here is unprobeable
  until `denote` computes, which is a dead route recorded on the domain itself.

- **THEN FIX WHAT `observe` HANDS BACK, BECAUSE THAT IS THE BOUNDARY THE TIER
  ABOVE IS STATED ACROSS.** The protocol automaton reads an emit list and asks
  whether it is settled; a `Beh` that cannot say where its instants end has an
  observation nothing can be demanded of at a cut point. So the observation's
  shape is decided by a requirement from outside this face, and it is worth a
  leg of its own rather than a clause of the one above: getting it wrong is not
  an inelegant domain, it is a tier above that cannot state its own subject.

- **THEN THE FORMERS THAT MAKE IT HARD: the flatteners, `μᵉ` and `deferᵉ`.**
  These are the three edges no structural reading reaches, and they are why the
  evaluator needed a reducibility candidate. The denotation owes the same
  descent in its own currency, so this leg either finds the domain wants a
  fixpoint structure the first-order half did not need, or finds the candidate
  transports — and which of those it is decides whether adequacy is a grind or
  a restatement.

### The ledger

- **`run-monotone`** (Verify-Adequacy) — FALSITY, `PROBED`: more fuel only
  extends a run. Nothing postulated in it; it is the tier's one row a concrete
  program decides.
- **`adequacy`, `saturation`** (Verify-Adequacy) — FALSITY, `DEAD ROUTE×2`: the
  pair pinning the denotation to the machine's limit. False as stated — a
  finite `Stream` cannot bound a fixpoint that emits one envelope per unit of
  fuel; the finding and the two available repairs are in the header.
- **`take-bounds-values`** (Verify-Take-Bounds) — FALSITY, `PROBED, RECOVERY`:
  a program headed by `take k` emits at most k values, at every fuel. Bare, and
  the one emission bound stated uniformly in fuel — which is what a saturation
  restriction is measured against.
- **`Beh`, `denote`, `observe`** (Verify-Adequacy) — VACUITY, `DEAD ROUTE×3`:
  the domain the pair above quantifies over, and what makes it vacuous. Named
  in the head rather than described, so the row can carry its own evidence
  field.

## Tier 3 — well-formedness, split where the predicate divides

**THE TIER IS TWO LEAVES, AND THE STATEMENT ABOVE THEM IS A BODY.** `The-Proof`
draws `evaluate-well-formed` from here and that name is a definition: it hands
the run to `evaluate-accepted` and `evaluate-settled` through `Rx.Protocol`'s
own recomposition, and those two are the whole of the tier's debt.

**THE SPLIT IS WHERE `WellFormed` ALREADY DIVIDES, NOT A NEW PREDICATE.** It is
`checkFinal` of `runProtocol`, and only the second is prefix-closed — the first
reads the LAST state. `runProtocol-prefix` and `wellFormed-settled` are proven,
so the automaton half travels down a truncation for free and the only thing a
cut point owes is that it is settled.

**AND BOTH LEAVES ARE ABOUT THE RUN, WHICH IS WHAT MAKES THEM PROBEABLE.**
`runProtocol protocol-init (evaluate↓ fuel e ins)` reduces at a concrete
program. The single statement they replace was stated over `meaning` and reduced
at none, so nothing could instantiate it — the tier's risk was unmeasurable by
construction and is now the ordinary kind.

### The monster

`evaluate-settled` — a run stops on an instant boundary with every obligation
paid. Deepest of the two and the likelier false: it is an off-by-one between the
point a budget is spent and the point a cut is emitted, reachable at a scripted
slot, while its sibling is a conjunction of clauses the evaluator asserts as it
builds. Its cone reaches `evaluate↓` and the automaton, which is the machinery
either leaf is discharged out of, so it admits the work that kills it.

also: `evaluate-accepted` — the other half, off the monster's cone because it is a
statement about every emit rather than about the stopping point.

### Big picture tier roadmap

- **INSTANTIATE BOTH LEAVES, WHICH IS NOW POSSIBLE AND WAS NOT.** Each is a
  computation over a run, so a probe walks fuel across an instant boundary and
  asks the automaton directly — and `evaluate-settled` is the one to aim at,
  since a cut landing mid-instant refutes the tier outright. The sampling sweep
  recorded in the body's own block reached the CONCLUSION and so constrains the
  pair only jointly; rows against the leaves separately are what say which half
  carries the risk.

- **THEN RESTATE WHAT CONSUMES WELL-FORMEDNESS, WHICH IS WHAT SAYS THE
  PREDICATE IS THE RIGHT ONE.** `The-Proof` quantifies the batcher over
  WellFormed streams, so the split has to reach that quantification rather than
  merely sit beside it. A predicate the batching claim cannot be stated against
  is one nobody will ever spend, however structural it reads — the same test the
  mirror tier applies to its own erasure.

- **THEN DECIDE WHAT DISCHARGES THE AUTOMATON HALF, WHICH IS THE TIER'S ONE
  DESIGN QUESTION.** Two routes: a seam invariant relating the eval state to
  `ProtocolSt`, recoverable from the face's header; or an induction on fuel over
  `run-monotone`, which says a longer run EXTENDS a shorter one and so asks only
  that an appended segment keeps the automaton happy. The second is the cheaper
  bet and needs no domain; the leg's product is which, decided by reading the
  evaluator's step structure rather than by preference.

- **AND THE SETTLEDNESS HALF IS WHERE A SEAM INVARIANT IS OWED WHATEVER THAT
  DECIDES.** `evaluate-settled` is a fact about where the machine may CUT, so no
  reorganisation of the other half removes it. That is the argument for pricing
  the seam invariant before committing to any route that claims to avoid it: it
  is owed once already, and a route avoiding it for one half still pays it here.

### The ledger

- **`evaluate-settled`** (Verify-Well-Formed) — FALSITY, `NO EVIDENCE`: a run's
  last protocol state has every obligation paid. The tier's monster, and the
  half a cut landing mid-instant refutes outright.
- **`evaluate-accepted`** (Verify-Well-Formed) — FALSITY, `DEAD ROUTE`: no emit
  of a run is rejected by the automaton. Every clause the automaton checks is a
  promise the evaluator makes while building the stream, so it is structural in
  the run.

## Tier 4 — determinacy and the top-line semantic claims

**THE MISC TIER, AND THE ONLY ONE NOT DEDICATED TO A SINGLE STATEMENT.** Two
faces share it because neither is on any other tier's route, not because they
share a subject: the run relation being a function, and the claims Main asserts
beside the main theorem.

**NONE OF THEM BLOCKS ANYTHING BELOW, WHICH IS WHY THEY ARE LAST.** The tiers
above are stated over the ONE output the builder produces, so a verdict about
that output means what it says whether or not a second derivation exists; what
determinacy buys is the STRENGTHENING, and a strengthening is worth nothing
until the weak form is proven.

### The monster

`subscribeE-det` — the subscribe relation itself, and the deepest node in the
tier whose falsity takes the rest of it. It would be a fact about the
EVALUATOR rather than about a claim: a frame admitting two outputs at one set
of indices means the machine is not a function, and then every face's
quantification over derivations is over a set nobody has characterised. A
leaf's cone is its statement's vocabulary, so it reaches neither its sibling
nor the assembly consuming both — those are admitted below.

also: `drain-det` — the other half of the same assembly, off the frame's cone and ground alongside it.
also: `evaluate-deterministic` — the determinacy subject, which consumes both leaves and is unreachable from either.
also: `readme-batch-order-is-delivery-order` — the flagship semantic law, and with it the instance claims and the abstractions the timing claims quantify over.

### Big picture tier roadmap

- **THEN INSTANTIATE THE DETERMINACY RING BEFORE GRINDING ANY OF IT.** The
  subscribe relation is twenty families and nothing has ever run two
  derivations at one set of indices. A refutation at a single arm is worth far
  more than a partial induction over all of them, and it is cheap: build two
  derivations of one frame by taking the builder's and one arm's alternative,
  and ask for the `refl`. The arms that do not follow from the head constructor
  are the target; the rest are decided by pattern matching and cannot refute.

- **THEN `subscribeE-det` ARM BY ARM, THEN `drain-det` AND THE ASSEMBLY.** What
  separates the arms is EQUATION PREMISES rather than constructors, so two arms
  can agree on the head and be told apart only by a derived equality on the
  schedule or the state; each such pair is a lemma and the lemmas are the
  product. The drain's determinacy is an induction whose motive is the
  subscribe result, so it lands second by necessity rather than by choice.

- **AND THE SEVEN INSTANCE CLAIMS ARE UNBLOCKED, WHICH IS A LEG BY ITSELF.**
  Every one of `readme-diamond`, `readme-each-next-own-instant`,
  `readme-cascades-inherit`, `readme-completion-cascades`,
  `readme-share-connect-no-replay`, `readme-late-join-growth` and
  `readme-serial-joins-mirror-rxjs` is hard-wired to a flattener, and while the
  descent was stuck at one no row could be written for any of them at any
  program. It is not stuck. Re-run the recovered battery, and re-probe the
  three universal laws at a program with a SOURCE while the harness is open. A
  refutation here is SPEC-level — surface it, do not patch it.

### The ledger

- **`subscribeE-det`, `drain-det`** (Verify-Determinacy) — FALSITY,
  `NO EVIDENCE`: each family admits one output at its own indices. Nothing has
  instantiated either, and the arms that do not follow from the head
  constructor are separated by equation premises — unwalked.
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
