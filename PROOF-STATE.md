# PROOF-STATE — the roadmap

**What this file is.** The ordered worklist for the one goal: discharging
`agda/src/Verify-Batch-Simultaneous/The-Proof.agda` — no postulates, everything
typechecks. This file holds the ORDER and a one-line hook per item; everything
else lives in the code.

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
- **EVERY TIER IS SORTED RISKIEST-FIRST, AND THE SORT IS AN INVARIANT —
  NOT A ONE-TIME TIDY.** Within a tier, rows appear
  in risk-class order: FALSITY, then SHAPE, then VACUITY, then DIFFICULTY,
  then GRINDABLE. **Re-sort in the SAME commit as any edit that could move a
  row** — a class raised or lowered, a postulate added, discharged, split, or
  renamed. A split is the easy one to miss: it can put a SHAPE child in a
  parent's GRINDABLE slot.
  **Why it is an invariant and not cosmetics:** this file's order is the only
  thing that says what to work on, so a stale sort silently re-aims the next
  session — and it re-aims it toward the SAFE end, because grinding is what
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
file only ASSIGNS them. Read that section
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

  every tier above is stated over Rx.Exp's syntax  Flatten-Laws.agda — tier 0
```

The caps route does not replace the wet contract — it rests on it: both
branches of `budget-sufficient` read `subscribeE-wet`'s `hasDry`/`INV?`
conjuncts, and both of those routes are real definitions — `subscribeE-wet`,
`wet-landing-lift`, `subscribeE-walk-level` and `cascade-wet-via-caps` all the
way down, with the `walkFace` family ground on every clause and the whole
Walk-Level tree holding no live postulate.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 0 — the anchor: `flattenᵉ` and bounded concurrency

**Re-opened because the syntax moved.** `mergeAllᵉ` and `concatAllᵉ` are gone,
replaced by ONE `flattenᵉ` carrying rxjs's `concurrent` argument, and every
tier below is stated over that syntax. What is genuinely new is the DRAIN
GATE, and `Rx.Flatten-Laws` is the door it is stated behind.

**ONE ROW LEFT, AND IT IS THE ONLY NON-LOCAL ONE.** Both un-rowed obligations
are closed — the two trees no longer name the removed constructors, and the wf
ledger's four-way *All split is one flatten face. Three of the four
gate laws went with them: the drain scrutinises the GATE and nothing else, so
saturation, the lane bound and shrinkage are one walk each, and the caps face
had already proven the third under its own name. What is left is the claim
about a node the inner's own burst can re-enter, which no hypothesis bounds.
Its consumer exists — the flatten wrap is a real clause — but the leaf that
would spend it is postulated, so the route home is a burst induction.

- **`unbounded-never-parks`** (Flatten-Laws) — SHAPE: the conclusion is a
  predicate on a node LOOKUP rather than an equation, because `NodeState` holds
  the queue's element type existentially; whether consumers can use it in that
  form is the open question. Statement and its shape argument in its header.

## Tier 1 — `budget-sufficient` (parked behind tier 0)

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



- **`cascadeGo-depth-perDeliv`** (Caps-Face/Part7) — DIFFICULTY: one arrival's
  cascade descent, one `nestSyn` per delivery off the evaluator's own ledger.
  The mirror's pre-step tail kills the inductive route and not the statement —
  measured deep into the skip branch, at six phantom chains of ten.
- **`depth-nest-compositional`** (Caps-Bridge) — DIFFICULTY: the subscribe-side
  depth induction, width-denominated. Its one-`nestSyn` form is machine-refuted
  at a fold depth of five; this form clears the same family by three orders of
  magnitude. Nineteen mutual members, every level paid by a path term but one.
- **`cascadeGo-nest-perDeliv`** (Caps-Face/Part7) — DIFFICULTY: the chain walk's
  induction, one `nestSyn` per delivery off the evaluator's ledger. Measured
  tight — the overshoot is a constant per delivery on both axes. Residue: a
  step that stores without delivering.
- **`cascadeGo-deliv-real`** (Caps-Face/Part7) — DIFFICULTY: the walk's delivery
  count under the real width; the STORE face spends it. Measures safe with wide
  slack, but the proven counter is cap-denominated INSIDE its walk module, so
  this wants new machinery — two dead routes recorded.
- **`nest-height`** (Nest-Store, inside the seal) — DIFFICULTY: the arithmetic
  both depth rows spend, and no evaluator in it. One tower height for the
  currency's sum, one story below the caps height; the `blowH` conversion and
  the recurrence's own base are now proven around it.
- **`init-nestOK?`** (Caps-Bridge) — DIFFICULTY: the entry state's nesting
  receipt. `init-capsOK?` is its route, but a scripted slot's obs-freeness only
  reduces at a concrete type, so an `isData` inversion is owed first.
- **`burst-nest`** (Caps-Bridge) — DIFFICULTY: the subscribe frame's nesting
  receipt at instant 1, and the one place the currency is really bet — every
  cascade instance is slack. `burst-caps` is the shape, but `burst-all`
  produces no nesting conjunct yet, so the producing lemma is owed first.
- **`storeNest-finish`** (Nest-Store) — GRINDABLE: the far end of a cascade only
  shortens lists, and every summand of the store measure is a `⊔`-fold over one.
  Its header names the proven twin at the same two branches.
- **`pop-nest`, `pop-head-nest`** (Caps-Bridge) — GRINDABLE: the pop mirrors,
  clause for clause against the proven `pop-caps` and `pop-head-valCaps`.
- **`chainsNest≤store`** (Caps-Face/Part7) — GRINDABLE: a `⊔`-fold dominates the
  selection it folds; `chainsOf-caps` is the same recursion at a size.
- **`subscribeE-Ψ`** (Burst-Walk) — GRINDABLE, large: the Ψ mirror of the PROVEN
  `subscribeE-caps` clique over the PROVEN `subscribeInner-Ψ` descent; the
  clause-by-clause sketch in its header names no undecided index.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `budget-sufficient`, so proving anything here while tier 1 is open
bets on ground a `Verify-Budget-Sufficient` failure would move.

**THE TIER IS ONE STATEMENT.** `The-Proof` draws `evaluate-well-formed`
(Part13) and nothing else from this tree, and every `Verify-Well-Formed` module
sits in its cone.

**MERGE COHERENCE IS UNSTATED** — the branch's own design question. What a
statement owes, and why it would inherit no evidence from the probe that is the
predicate's only consumer, is recorded on `Part4.root-flattenCache`.

In rough order for when the tier opens — statement repairs first, then grinds:

- **`root-entry-sunk`** (Part4) — FALSITY: the per-entry residue of
  `root-done-plumbed`. Its load-bearing region was NOT reached by probe, so the
  class stands — but it is a statement about ONE surviving entry, a size a
  counterexample can be built at. Coverage boundary in its header.
- **`mid-readoff`** (Part11) — FALSITY: the FoldOut readoff, and FoldOut is a
  6-field invariant validated at exactly one clause.
- **`subscribeE-{switch,exhaust}All-wf`** (Part3) — SHAPE: written against a
  coherence whose statement is still open (the cert sketch in Part8's
  establishment block). The flatten face is no longer among them: it is a real
  clause, and its leaves are the five rows below.
- **`stepFrame-wf-outer`** (Part9) — SHAPE, on a ROUTE claim rather than the
  statement: discharging it means enriching `stepFrame-wf` to carry FoldOut out,
  restating this family. GRIND it after `stepFrame-wf-inner-flatten`, which it
  strictly contains — a work-order dependency only.
- **`map-valsLast-push` / `scan-valsLast-push`** (Part3) — SHAPE: each papers
  over a recorded mismatch (the proven sub-lemmas don't return `valsLast?`).
- **`cutThrough-close-bound-dying` / `cutThrough-live-dying`** (Part7) — SHAPE:
  both REFUTED (`Refuted.Cut-Through`), `L₁` free at exactly the sources the
  conclusions speak about. Restate over the (LAG) ledger; header carries the
  repair and why it was not ground here.
- **`flatten-node`** (Part3) — DIFFICULTY: the node the wrap's inner burst
  leaves, and the only one of the five the limit reaches. Its queue conjunct at
  an unbounded limit is `unbounded-never-parks` iterated over the burst, which
  is what gives that claim a consumer once this is a body.
- **`subscribeE-flatten-push`** (Part3) — DIFFICULTY: the wrap's push half,
  protocol run and invariant back out through `thru-outer`. Twin: the scan
  face's `subscribeE-scan-wf`, same joint, and that one is proven.
- **`dispatchShare-wf`** (Part9) — DIFFICULTY: the share arm's run equation,
  `foldPath-wf`'s third clause. Its FoldOut half belongs to
  `foldPath-share-out`, so the statement as written is what `foldPath-out`
  spends.
- **`root-flattenCache`** (Part4) — DIFFICULTY: the per-node residue of
  `root-caches`, split to the flatten clause alone and probed non-vacuously in
  assembled form. Header carries the DEAD ROUTE through `flattenCertAt` and
  the MISSING INVARIANT it leaves owed.
- **`foldPath-frame-out` / `foldPath-share-out`** (Part11) — DIFFICULTY:
  `foldPath-out`'s two undischarged arms, each the FoldOut readoff only (the
  run's `S′` and equation come in from the PROVEN `foldPath-wf`). The frame arm
  wants `stepFrame-wf` enriched to carry FoldOut out; the share arm is the
  diamond's net-zero owed and additionally waits on `dispatchShare-wf`.
- **`mid-fold-certs`** (Part11) — DIFFICULTY: one case split on
  `Arrival.isLast a` off `Mid.done-plumbed`; the blueprint's GUARD applies to
  its flip conjunct.
- **`scan-nodry-push`** (Part3) — DIFFICULTY: no `pushBurst-scan-char`
  counterpart of the map characterisation exists, so the dry-preservation route
  is a direct induction over `pushBurst` rather than a rewrite.
- **`subscribeSharedSlot-wf`** (Part3) — DIFFICULTY, blocked: `sharedConnect`
  recurses into `subscribeE`, so this arm cannot close outside the mutual block
  holding `subscribeE-wf`, two files down.
- **`input-cold-async-wf`** (Part3) — DIFFICULTY: its one named precedent
  `initReg-wf` is ruled out in the header — that lemma's emit is `init src ∷ []`
  while this ships the sync prefix in the same emit.
- **`subscribeE-defer-wf`** (Part3) — DIFFICULTY, well-scoped: three BurstInv
  conjuncts fall out at once (hasDry vacuous, valsLast? by computation, hot-live
  definitional); the whole residue is `liveTypeOK?` at the minted source, whose
  tail needs a mintSource-freshness lemma the repo does not have.
- **`cut-owed`** (Part9) — DIFFICULTY: independent of every blocker, but its own
  header calls the owed-shape obligation "genuinely semantic" and names no
  precedent, so being unblocked is not the same as being mechanical.
- **`stepFrame-wf-inner-flatten`** (Part9) — DIFFICULTY: the drain grows the
  registry; re-establish FoldInv. Independent of the cert.
- **`flatten-binv-adapt`** (Part3) — GRINDABLE: mint and install touch neither
  registry nor live, so every BurstInv field survives. The scan twin is proven
  at the same two operations.
- **`flatten-nodry-push` / `flatten-valsLast-push`** (Part3) — GRINDABLE: carry
  the dry premise in and `valsLast?` out through the wrap frame, clause for
  clause against the map and scan pushes at the same frame shape.
- **`map-nodry-push`** (Part3) — GRINDABLE: every ingredient is PROVEN —
  `pushBurst-map-char` (.Part5) and the dry family `splitEvents-nodry` /
  `retagEvents-dry` / `mapValue-dry` / `any-dry-++` (.Walk-Level). Only import
  wiring remains, and Part3 already reaches that cone through Caps-Bridge.
- **`input-hot-spent-wf`** (Part3) — GRINDABLE: the PROVEN `oneShotBurst-wf`
  (.Part2) is the same init/close/complete balance one source-state over, and
  the header carries the whole argument with nothing left open.
- **`take-nodry-push`** (Part3) — GRINDABLE, and NOT by the scan twin its header
  names: `cutThrough` emits only `close src cut`/`cutPending` while `dryEvent`
  fires on `dried` alone, so dryness is structural, and `retagEvents-dry`
  (.Walk-Level) is proven. `ecEq` comes from the outer pushBurst's node lookup.
- **`subscribeE-dying`** (Part8) — GRINDABLE, large: `subscribeE` never writes
  `dying` — two writers, neither reachable from it, both named in its header.
  Nothing undecided; the cost is that the induction covers every clause.
- **`HotLive`'s preservation leaves** (Part2) — GRINDABLE, all five:
  `sched-init-hot-live`, `mintSource-hot-live`, `subscribeE-hot-live`,
  `cascadeFinish-hot-live`, `sched-next-hot-live`. Every header states a
  slots-untouched / prepend-only route with nothing undecided; `sched-next`'s
  twin `regTyped?-pop-sched` is PROVEN, and `cutSched-hot-live` (.Part6) is the
  family's worked body over the PROVEN `liveTypeOK?-sweepLive`.

## Tier 3 — the top-line semantic claims (parked behind tier 2)

The second ledger: claims Main asserts beside the main theorem, off its
critical path.

- **Vacuous-by-abstraction — VACUITY** — `locality`, `non-interference`,
  `timing-invariance`, `causality`, `μ-guarded`, `defer-shift` (the one
  allowlisted honest gap). De-risking these means DEFINING the abstractions:
  claim authoring that needs Anthony. **Not GRINDABLE and never will be** — no
  precedent can make them mechanical, because nothing is stated yet.
- **The abstractions those claims quantify over — VACUITY** — `Node`, `NodeSt`,
  `Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`, `retime`, `truncateIn`,
  `emittedBefore`. Named individually because they are what makes the row above
  vacuous, and a collective phrase is invisible to the coverage check.
- **Real, probed, awaiting proof — DIFFICULTY** — `μ-unfold`, `fuel-coherent`,
  `id-inheritance`, `batch-online`, and the ten `readme-*` claims. Probe
  receipts and residual risks live in the module headers. A refutation of a
  `readme-*` claim is SPEC-level: surface to Anthony, do not patch. None is
  demoted — the precedent audit waits on this tier being reached.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.
