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
```

The caps route does not replace the wet contract — it rests on it: both
branches of `budget-sufficient` read `subscribeE-wet`'s `hasDry`/`INV?`
conjuncts, and both of those routes are real definitions — `subscribeE-wet`,
`wet-landing-lift`, `subscribeE-walk-level` and `cascade-wet-via-caps` all the
way down, with the `walkFace` family ground on every clause and the whole
Walk-Level tree holding no live postulate.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 1 — `budget-sufficient` (the lowest open tier)

**The tier is ONE statement, not a directory.** `budget-sufficient`
(Caps-Bridge) says `hasDry (evaluate fuel e ins) ≡ false`, and it is the only
CLAIM the `Verify-Budget-Sufficient` tree exports: 41 of the tree's 42 modules
sit in Caps-Bridge's import cone, and the one that does not is `Demand-Programs`,
a program corpus reaching Main through `Harness.Main`.  The tree's two probes
used to sit outside that cone as well; both expired with their targets and are
deleted, and a live probe now lives in `agda/evidence/probed` instead.

**AND THE COUNT WENT DOWN BY DELETION, WHICH IS WHAT THE CONE IS FOR.** `Wet`
Parts 4 and 5 and most of Part 3 were the W11 width walk — 1820 proven lines
whose consuming face, the ledger walk, was retired. It reached Main through a
`public` re-export in Wet/Part6 and nothing else, so a mutual cluster consuming
itself read as wired; reachability was the only check that could see it. The
`ofW` measures stay, spent by the successor face (`Walk-Level`), which is what
distinguishes a superseded predecessor from a missing wire.

**IT IS ALSO THE TREE'S ONLY DOOR NOW, and what closed the others was a
module, not a cleanup.** `Verify-Well-Formed` still draws `mint-install-survives`
(Node-Fresh) by name — one real cross-tier claim. What used to sit beside it was
`Node-Table`'s utility lemmas crossing two tier boundaries into `The-Proof`,
which cited `≡ᵇ→≡` and `≡ᵇ-refl` at a module defining neither. Those were never
claims on this tier; they were arithmetic with no home, so they had accreted a
copy per tree. They now live in `Decide` below both trees, and `The-Proof`
reaches into the trees for exactly `evaluate-well-formed` and this door.

**"A REAL BODY" IS NOT "POSTULATE-FREE".** `budget-sufficient` is a definition
rather than a postulate; the rows below are the leaves still under it. Reading
a real body as a discharged cone is how a row gets mis-ranked — the census that
mis-classed `subscribeE-inner-nodry-inv` read conclusions and never asked what
its named suppliers needed.

Labour MOSTLY, and the qualifier has been earned four times here, twice at an
ASSEMBLY rather than a leaf. The connect leaf admitted instances its caller
cannot make; `depth-compositional` was refuted at a nine-slot program because
the measure under it took a max where connects CHAIN; then the one shape
`depth-all-bound`'s own receipt named as untested refuted the whole face — a
`scanᵉ` whose step wraps its accumulator gains nesting PER TICK, so `depthE`
grows in `wraps × ticks` while every syntactic right-hand side grew in
`wraps + ticks`; and the interface above it fell to the same product at seven
wraps over twenty-nine ticks, 204 against 201, every hypothesis satisfied and
`capsOK?` by `refl`. A real body's own conclusion is no safer than a
postulate's, and a row whose OBSTACLE is written down is not thereby a row whose
STATEMENT is right.

THE FACE IS NOW RESTATED, over a measure derived from the evaluator and pinned
by `Probed.Nest-Depth`: one `suc` per `*All` layer, and a `scanᵉ` worth its
source's payload count times its step function's layers. It EQUALS `depthE` —
not merely dominates it — at three programs, the third a scan nested inside
another scan's step function, which says the product COMPOUNDS: one factor per
nested scan, so the measure is exponential in the program and no fixed-degree
product of caps fields could have replaced it. `depthCap`,
`depth-compositional`, `depth-all-burst` and `slotNest` all carry it now, and a
shared slot pays its def's nesting.

AND THE CAP IS NOW READ OFF NESTING ALONE, its size term gone and `pathLen`
replaced by a measure charging only the SPENDING ARC. That is what the `*All`
face's recorded dead route asked for: an emitted inner can be arbitrarily larger
than its emitter but never more deeply nested, so the size currency was what
blocked the burst arm — and it was measured slack, the μ probe reading caps of 7
and 12 against depths of 1 and 2 where the tightened cap reads 1 and 2 on the
nose. Every clause got shorter: the three structural descents need no arithmetic
step, the μ clause's two caps became one term, and the connect now over-pays.
Both remaining leaves are strengthened by it, and `Probed.Nest-Depth`'s rows now
pin the cap itself as an EQUALITY with the depth.

AND THE CURRENCY IS NOW ONE THROUGHOUT, which the first half of that tightening
left owed and the burst arm forced. `slotNest` charged a def's size beside its
nesting and `nodeNestMax` charged a queued inner's size alone, so a
`concatAllᵉ` that queues an emitted inner put a SIZE into a cap that no longer
reads one — the same mismatch one level down, and unfixable by any cleverer
proof. Both now charge `nestDᵉ`, `nodeNestMax` taking the `Slots` it needs to,
and the one leaf that covers the emitted inner covers the queued one with it.
Two of the three consumers got smaller: the slot half of the tower bound is
`nestD-tower` with a level to spare rather than a two-summand `sum2H`, and the
connect's payment is an equality again. The probe rows moved with the measure —
a nine-link chain's store reads 9 where it read 60, against a depth of 5, so
what margin is left is of the same order as the thing it bounds.

WHAT THAT COST IS THE WHOLE CAPS-CONDITIONED ROUTE. `Depth-Bound` is deleted:
`depth-capped`, its `3 · cSize` conclusion, the `storeNestMax`-under-`capsOK?`
inversion, and `three-size≤capsH` with the pool-lower chain that proved it.
`depth-compositional` reaches the root directly, where `pathLen root` is 0,
`st-init`'s nodes are empty and `Sched.slots (sched-init e ins)` is `ins` — so
the remaining obligation carries NO state hypothesis, which is exactly what made
the old statement false: `capsOK?` was checked at the entry state and the
conclusion was about a depth reached much later. Three dead routes are recorded
where they were tried: bound the depth by the GAS (true, and `budgetAt-gs-pad`
puts the budget a full capsH-step the wrong side of the goal), bound it by the
WIDTH family (its exponential's base is 1, since a wrap layer's `outWⱽ`
multiplies by one and adds nothing — refuted against the max of all four
measures at once), and take a fixed-degree product of caps fields.

- **`depth-all-burst-gs`** (Depth-Compositional) — DIFFICULTY, all that is left of
  the `*All` face. The arm is a real body split on its gas and the `g0` half is
  discharged, which checks the claim that the GAS is what the route descends on.
  One leaf left: an emitted inner's nesting is bounded by its emitter's.
- **`cascade-depth-capsH`** (Caps-Face/Part7) — DIFFICULTY, NOT demotable: both
  twins are proven, but its header rules out repackaging — the delivery machinery
  sits wholly outside `depthE`'s induction. Conditioned on `capsOK?` because the
  unconditional form is false.
- **`depth-subst-guarded`** (Depth-Compositional) — GRINDABLE: the `deferᵉ` clause
  is `z≤n` and the rest is the structural recursion the assembly above it already
  performs, on `body` rather than on its unfolding; the guardedness is a property
  of the syntax. Strengthened with the cap; the μ probe crosses it with no slack.
- **`subscribeE-Ψ`** (Burst-Walk) — GRINDABLE, large: the Ψ mirror of the PROVEN
  `subscribeE-caps` clique over the PROVEN `subscribeInner-Ψ` descent; the
  clause-by-clause sketch in its header names no undecided index.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `budget-sufficient`, so proving anything here while tier 1 is open
bets on ground a `Verify-Budget-Sufficient` failure would move.

**THE TIER IS ONE STATEMENT.** `The-Proof` draws `evaluate-well-formed` (Part13)
and nothing else from this tree, and all fourteen `Verify-Well-Formed` modules
sit in its cone. The four utility names it also used to draw are in `Decide`
now, so the count is a fact about the import graph rather than about which
lemmas happened to be re-exported.

The branch's own design question is **merge coherence, and it is UNSTATED**: the
decidable predicate a statement would be about lives with the probe that is its
only consumer (`Probed.Root`, moved there when the probes left `MODULE_ROOTS`),
so a restatement here states its own and does not inherit evidence earned
against that one. The coherence owes a statement, a mid-fold FoldInv form, and
the consumer rewrites that spend it. The ALIVE-vs-PRESENT gap any statement has
to close is recorded on `Part4.root-mergeCache`.

In rough order for when the tier opens — statement repairs first, then grinds:

- **`root-entry-sunk`** (Part4) — FALSITY: the per-entry residue of
  `root-done-plumbed`. Its load-bearing region was NOT reached by probe, so the
  class stands — but it is a statement about ONE surviving entry, a size a
  counterexample can be built at. Coverage boundary in its header.
- **`mid-readoff`** (Part11) — FALSITY: the FoldOut readoff, and FoldOut is a
  6-field invariant validated at exactly one clause.
- **`subscribeE-{merge,concat,switch,exhaust}All-wf`** (Part3) — SHAPE:
  written against a merge coherence whose statement is still open (the
  merge-cert sketch in Part8's establishment block).
- **`stepFrame-wf-outer`** (Part9) — SHAPE, on a ROUTE claim rather than the
  statement: discharging it means enriching `stepFrame-wf` to carry FoldOut out,
  restating this family. GRIND it after `stepFrame-wf-inner-concat`, which it
  strictly contains — a work-order dependency only.
- **`map-valsLast-push` / `scan-valsLast-push`** (Part3) — SHAPE: each papers
  over a recorded mismatch (the proven sub-lemmas don't return `valsLast?`).
- **`cutThrough-close-bound-dying` / `cutThrough-live-dying`** (Part7) — SHAPE:
  both REFUTED (`Refuted.Cut-Through`), `L₁` free at exactly the sources the
  conclusions speak about. Restate over the (LAG) ledger; header carries the
  repair and why it was not ground here.
- **`dispatchShare-wf`** (Part9) — DIFFICULTY: the share arm's run equation,
  `foldPath-wf`'s third clause. Its FoldOut half belongs to
  `foldPath-share-out`, so the statement as written is what `foldPath-out`
  spends.
- **`root-mergeCache`** (Part4) — DIFFICULTY: the per-node residue of
  `root-caches`, split to the merge clause alone and probed non-vacuously in
  assembled form. Header carries the DEAD ROUTE through `mergeCertAt` and
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
- **`stepFrame-wf-inner-concat`** (Part9) — DIFFICULTY: concat's drain grows
  the registry; re-establish FoldInv. Independent of merge-cert.
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
