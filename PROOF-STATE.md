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

run-monotone                              claimed by Main in its own right —
                                          nothing above consumes it — tier 2

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

- **THE ENVELOPE IN `Ty`'s OWN VOCABULARY, WITH THE TAG FORKED TO ANTHONY.**
  `instEmitᵗ`, `instEventᵗ`, `emitKindᵗ` and `closeReasonᵗ` are DEFINED over
  `unitᵗ`, `_+ᵗ_`, `_×ᵗ_` and `listᵗ` rather than added to `Ty`, parameterised
  over their uniq type, so a simul slot declared at `instEmitᵗ unitᵗ a` admits
  only `tt` where a uniq goes. That half is unblocked and is what lands here.
  The tag is not: a `uniqᵗ` with NO introduction form cannot be built, since
  `reify` is total over `Ty` and each clause owes a CLOSED term — its header
  carries the reasoning. Two horns, both deciding what a program may SAY, so
  neither is an agent's: drop the tag (`uniqᵗ = natᵗ`), or keep it with an
  intro form and rest unforgeability on the simul palette, where the
  shipped-formers framing already puts it.

- **THEN DEMOTE THE ENVELOPE OUT OF THE EVALUATOR.** Target:
  `evaluate : … → List (Val Γ t)`. The mentions split three ways and only one
  is work — plumbing vanishes with the return type, a claim's statement
  restates mechanically, and what is left is BEHAVIOUR, every place the
  machine reads a field of its own envelope to decide something. Each of those
  moves UP into a simul former, which is what makes this a demotion rather
  than an extraction: the plain tree's `take` and `defer` are already protocol
  formers by the pairing map's own role column, and they stop being that here.

- **THEN THE SIMUL TREE AND `toPlain`.** A second `Exp` whose formers are the
  envelope-carrying operators, and one elaboration into the plain tree. It is
  where the demoted behaviour lands, so it cannot be written before the leg
  above, and it is the leg that decides whether the split was real: a demoted
  behaviour with no simul former to move into means the two trees are one tree
  with extra steps.

- **THEN THE TYPESCRIPT SIMUL OPERATORS, `lift` INCLUDED (Anthony).** Written
  over plain rxjs, ES6 array operations and conditionals only. `lift`, `take`,
  `map` and the batcher already are; `share`, `defer` and the three flatteners
  are not, and each needs a synchronous subscribe frame captured as a unit,
  which plain combinators cannot observe. Whether the three quarantined escape
  hatches count as permitted vocabulary is the question the leg opens with,
  and it is Anthony's.

- **THEN THE SAME OPERATORS IN `Tm`/`Ty`, AND TIER 1 IS COMPLETE (Anthony).**
  Each TS simul operator mirrored as an Agda definition in the value language,
  in the same fashion, so the correspondence is readable rather than asserted.
  **AND IF THE LANGUAGE CANNOT SAY ONE, STOP AND REPORT (Anthony).** A missing
  former is never repaired by inventing one: a new `Ty` constructor or `Tm`
  former changes what a program can SAY, so it decides what every theorem
  above quantifies over — the same reason the spec is not an agent's to move.

## Tier 2 — the machine's own fuel

**WHAT THIS FACE BUYS: the one claim about the evaluator that no correspondence
carries.** It is read off `evaluate↓` alone — no spec, no batching, no second
run to compare against — and a concrete program decides it. That is the whole
tier: what this repo asserts about its own machine, standing on nothing else.

**AND THE RISK IS THE FLATTENERS.** The row carries a probe whose receipt names
the region it does NOT reach — no program whose evaluation enters a flattening
node, and no source firing at more than one tick. So what is instantiated is the
first-order half of the statement, and the region where it could still be false
is named rather than guessed at.

### The monster

`run-monotone` — the cheapest thing here that can be false. It says more fuel
EXTENDS a run and never rewrites what a shorter one emitted, which is two
properties in one equation, and the second is the one a machine violates
quietly: a drain resuming from a different arrival ordinal, an instant
renumbered under the larger fuel, a burst reordered. Every face above reads its
own fuel off its own hypotheses, so nothing yet forces the equation — which is
why a restatement is cheap now and ruinous once a consumer exists.

### Big picture tier roadmap

- **PROBE THROUGH A FLATTENER, BECAUSE THAT IS THE ONE REGION THE RECEIPT DOES
  NOT REACH.** The probe stops at that boundary and says so, so the tier's whole
  remaining doubt sits in one shape: a longer fuel enters an inner subscribe at
  a different point, and what the shorter run emitted is rewritten rather than
  extended. The leg's product is rows at `mergeAll`/`switchAll`/`exhaustAll`
  programs, or a refutation — and a refutation is the cheap outcome here, since
  the statement has no consumer yet and restating it costs nothing above it.

- **THEN PAST ONE TICK, AND OFF A COLD SOURCE.** Every existing row scripts a
  hot source firing once, so every arrival lands at tick zero and no row spans
  two deliveries. That leaves the prefix property untested exactly where a run
  carries state between ticks, which is where a drain counter could resume
  differently. The leg adds rows at a source firing twice and at a cold source,
  and its product is whether the equation survives a run with more than one
  arrival ordinal in it.

- **THEN MINT THE LEAVES, IN WHATEVER CURRENCY THE FIRST TWO LEAVE STANDING.**
  The row is a BARE postulate on purpose: what the induction is over — the
  drain's own step, the frame's concatenation, the arrival ordinal — is what the
  flattener and multi-tick rows decide, and minting ahead of them is a
  hypothesis about the route rather than a decomposition. So this leg is last by
  construction, and its own product is the split, not a proof of it.

### The ledger

- **`run-monotone`** (Verify-Run-Monotone) — FALSITY, `PROBED`: more fuel only
  extends a run. Nothing postulated in it, and a concrete program decides it.

## Tier 3 — the automaton half, and it is the only half

**THE TIER IS TWO LEAVES, ONE PER SEGMENT KIND.** `The-Proof` draws
`evaluate-accepted` from here and nothing else: no emit of a canonical run is
rejected by the protocol automaton. That is a body now, over `Sound i j xs` —
acceptance with both endpoints removed and indexed by the watermarks a segment
runs between — so what is left to prove is one claim about a cascade and one
about the root subscribe.

**THE INDEXING IS WHAT MAKES IT DECOMPOSE.** An instant id is an absolute
arrival position, so a predicate quantified over every sane state is satisfied
by no segment that emits anything. The entry bound repairs that, the exit bound
is what the next segment spends, and a run is their concatenation.

**AND IT IS PREFIX-CLOSED, WHICH IS WHAT TIER 2 NEEDS.** `runProtocol`
short-circuits on rejection, so acceptance travels down a truncation for free.

### The monster

`evaluate-sound` — a canonical run takes the automaton from watermark zero to
the fuel's successor. Not a postulate, and that is the point: it is the body
the drain induction assembles, which is where a wrong decomposition lives while
every leaf under it reads as reasonable. Chosen above its own leaves because
its cone is what the per-former grind has to land in, and the cascade relation
alone reaches neither the builder nor the reducibility candidate.

also: `evaluate-accepted` — the tier's export, which CONSUMES the monster and
so sits above it rather than inside its cone. Nothing else is admitted.

### Big picture tier roadmap

- **GRIND THE CASCADE LEAF, ONE FORMER AT A TIME, WIDENING THE ROWS AHEAD OF
  EACH.** Its clause count is the tree's former count, which is what Tier 1's
  collapse shrinks first. The rows covering it today reach a synchronous source
  and a slot at the seed watermark only, so each clause is probed at its own
  former before it is ground — the flatteners and `μᵉ` first, where an
  instant's obligations are hardest to keep inside one cascade, and a cascade
  emitting nothing, where the exit bound is the whole claim.

- **THEN THE SUBSCRIBE LEAF, WHICH THE COLLAPSE HAS MADE SMALLER.** It is an
  induction over the subscribe relation, so its clause count is the former
  count too. Taking it second is not deferral: ground before the collapse, most
  of its clauses would be ground twice.

- **THEN SETTLE WHETHER THE HARNESS'S QUESTION IS STILL THE RIGHT ONE.**
  `wellFormed?` decides a conjunction this face no longer claims, so QuickCheck
  rejects streams the theorem accepts. That is a harness stricter than the
  claim, which costs coverage silently: every program whose run stops
  mid-instant is dropped before it is compared. The leg's product is whether
  the decision procedure drops its final check, and what the sweep then reaches
  that it did not.

### The ledger

- **`sound-cascade`** (Verify-Well-Formed) — FALSITY, `PROBED`: one cascade's
  emits take the automaton from the instant it opens to the next, from any sane
  state at the entry watermark. The exit bound is the risky half — a cascade
  that leaves an instant open exceeds it.

- **`sound-subscribe`** (Verify-Well-Formed) — FALSITY, `PROBED`: the root
  subscribe's burst is the zeroth instant and nothing more. Its clause count is
  the tree's former count, which is what Tier 1 is for.

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
