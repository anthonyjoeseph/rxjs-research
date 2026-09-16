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
 └─ evaluate-well-formed                 Verify-Well-Formed.agda — REAL, one match
     └─ burst-drain-well-formed          one postulate — tier 1

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

## Tier 1 — Verify-Well-Formed

Built on the run's own derivation, which is now a body the whole tower
descends through.

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
work that kills it. Below it the tier is two leaves and the seam relation they
are denominated in, each with a cone of its own vocabulary only, so naming one
would forbid touching its sibling; above it sits a wrapper supplying
derivations. The tier bottoms out near its own top because it is two levels
deep, not because the top was defaulted to. It can be FALSE, not merely
unproven: a run whose emit stream the automaton rejects kills both leaves, the
seam, and the WellFormed quantification `The-Proof` draws from this face.

also: `evaluate-deterministic` — a tier-2 statement worked here on Anthony's
direction, because the coverage axis it closes is this face's and no schedule
of tier-1 work reaches it.

### Big picture tier roadmap

- **RUN A CLOSE, WHICH IS THE ONE FIELD NO ROW HAS CONDITIONED.** The drain's
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

## Tier 2 — the top-line semantic claims (parked behind tier 1)

The second ledger: claims Main asserts beside the main theorem, off its
critical path.

### The monster

`evaluate-deterministic` — `subscribeE-det` is likelier false and is deeper,
and it is below the FLOOR: a leaf's cone is its statement's vocabulary, so
naming it would put `drain-det` and the assembly itself off-tree and forbid the
grind that kills it. This is the deepest node whose cone IS the work, and it
still sits far below the tier's semantic top line. Its falsity would be a fact
about the EVALUATOR rather than about a claim: a subscribe frame admitting two
outputs at one set of indices means the machine is not a function, which moves
the tier below as well.

### Big picture tier roadmap

- **DECIDE WHETHER THE RUN RELATION IS A FUNCTION** — `subscribeE-det`,
  `drain-det`, under the assembly `evaluate-deterministic` that Main now
  claims. The body typechecks, so what is open is the two leaves and nothing
  about the shape. It is first because it is the only row here whose answer
  changes another tier: the protocol face's leaf quantifies over any subscribe
  and any drain derivation while every sampled program exercised the builder's,
  and this is the fact that makes those the same set. Instantiate before
  grinding — the ring is twenty families, so a refutation at one arm is worth
  far more than a partial induction over all of them.
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

