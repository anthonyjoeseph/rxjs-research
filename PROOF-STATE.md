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
- **Completed items are DELETED, not marked complete.** No ~~strikethrough~~,
  no "✅ DONE" rows, no discharged-count bookkeeping in tier headings. The
  deletion happens in the same commit as the discharge, and the commit
  message carries what was proven. A completed row left in place is the seed
  of the dated-narrative rot this file was once lost to.
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
- **One line per item: name + risk class + hook.** The hook says where
  the risk lives and where the full story is (always a source header) —
  it does not TELL the story. An entry that has grown sentences of
  mechanism, receipts, or history is a header that leaked; move it to the
  postulate's header and cut the entry back to its line.
- **The ledger is the source of truth, not this file.** `make postulates` lists
  every live postulate by name; every one of them appears in exactly one tier
  below, and a name here that no longer greps is a bug in this file — fix on
  sight.
- **There is no second roadmap.** Not a session task list, not a worker's
  notes, not a scratch file. A parallel list is outside the repo, so no gate
  and no `grep` can see it rot — one ran beside this file for weeks, kept
  every completed row, and outlived this file's rewrite by a commit. The tell
  is citing work by a NUMBER: names come from here and from the ledger,
  numbers come from somewhere that should not exist. Find it and delete it.

**The tier law and the risk classes are DEFINED IN CLAUDE.md** — tier 0 finishes
first, then 1, then 2, then 3, strictly; classes worst-first are FALSITY, SHAPE,
VACUITY, DIFFICULTY, GRINDABLE. This file only ASSIGNS them. Read that section
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
     ├─ budget-sufficient                Caps-Bridge.agda — PROVEN from:
     │   ├─ burst-dry/-bounded ┐ all three are projections of ONE
     │   ├─ burst-caps         ┘ subscribeE-wet-via-caps call (burst-all)
     │   │                                ← subscribeE-wet ← wet-landing-lift
     │   │                                  ← subscribeE-walk-level   [tier 0]
     │   └─ drain-dry   ← cascade-wet-via-caps     [tier 0: subscribeE-inner-nodry]
     └─ the well-formedness branch       its own postulates — tier 2
```

The caps route does not replace the wet contract — it rests on it: both
branches of `budget-sufficient` read `subscribeE-wet`'s `hasDry`/`INV?`
conjuncts, so no amount of caps work retires tier 0.

## Tier 0 — THE ANCHOR CHAIN (everything else waits on this)

Work top to bottom. Every full route, receipt, and ruling lives in the
named postulate's own header.

The three DIFFICULTY rows head the tier and are the design session's own
work; the GRINDABLE rows below them do NOT block on those three — every
row in a tier is available to its siblings as a postulate, so the
mechanical ones can be ground in parallel by a worker. Top-to-bottom is
the order attention is OWED, not a bar on running the bottom concurrently.

- **`input-wet-shared`** (Walk-Level) — DIFFICULTY: the CONNECTING half, and
  the only one that recurses. Its eight ingredients are PROVEN and the walk
  face now reaches it, but the caps twin `sharedSlot-caps` has no recursion
  where this has one, so the induction is still to be designed. The Ψ axis is
  closed by PROVEN `caseW-subΘ` + `fnCap-subΘᵉ`; evidence and the hop
  disanalogy in its header.
- **`input-wet-scripted`** (Walk-Level) — GRINDABLE: takes NO walk face, so
  nothing recurses and no induction has to be designed. Its header carries a
  full census — four slot shapes × the wet five against the PROVEN
  clause-for-clause twin `subscribeE-input-caps` — naming a proven ingredient
  for every conjunct, with one 5-line gap (`register-regsLen`) written out and
  dev-checked green. The routes marked "by computation" are read off the
  evaluator, not yet typechecked.
- **`slotHop-cap`** (Measures) — DIFFICULTY: Demand-Probe series S reaches
  the amplifier-chain region and measures the margin widening. Route and
  coverage in its header.
- **`walk-{of,empty,map,take,scan,defer}`** (Walk-Level) — DIFFICULTY.
  The walk face's one-shot and chain clauses; scan exercises the
  Ŝ-ceiling growth, defer mints the registry entry.
- **`subscribeE-inner-nodry-inv`** (Burst-Walk) — GRINDABLE: the repaired
  statement; its header names a proven source for every remaining conjunct, one
  of which (`regsB?-of-parts`) sits downstream and must relocate or inline.
- **`subscribeE-inner-nodry-{pBO,depth}`** (Burst-Walk) — GRINDABLE.
  Path-extension and depth-mirror plumbing for the inner call.
- **`concatDrain-nodry-vb` / `-nestBud` / `-dep` / `-cl` / `-loop` / `-nestRec`**
  (Burst-Walk) — GRINDABLE. Per-element context for concat's drain: each
  re-establishes one hypothesis of `subscribeInner-nodry` after the previous
  element has moved the state, and the shared header names the caps face
  (`.Subscribe-Face`) as the worked twin at the same indices. `-cl` is the
  hardest of the six — its opIterD/fLvlD arithmetic is the reason it is a leaf.
- **`thruConsume-nodry-vb` / `-nestBud` / `-dep` / `-loop`, `thruWalk-nodry-dep`,
  `VbB-tail`, `switchKill-context`** (Burst-Walk) — GRINDABLE. The same
  per-element context on the thru-outer side against the same twin, plus
  switchKill's OKB/regP transport. `VbB-tail` carries a phantom `{e}` its
  statement never mentions.

## Tier 1 — Verify-Budget-Sufficient (parked behind tier 0)

Labour, not risk: nothing here can discover a design failure, and an anchor
failure would move the ground under all of it.

- **`subscribeE-Ψ`** (Burst-Walk) — GRINDABLE, large: the Ψ mirror of the PROVEN
  `subscribeE-caps` clique over the PROVEN `subscribeInner-Ψ` descent; the
  clause-by-clause sketch in its header names no undecided index.
- **`depth-compositional`'s residue** (Depth-Compositional) — DIFFICULTY, and the
  module header buckets it BLOCKED: `depth-conn-storeNest`, `depth-all-bound`,
  `depth-μ-bound`, `installScan-depth-bound`. No worked precedent among them, and
  `depth-μ-bound`'s size IH is refuted in its own header. Obstacles and routes there.
- **`cascade-depth-capsH`** (Caps-Face/Part7) — DIFFICULTY, NOT demotable: both
  twins are proven, but its header rules out repackaging — the delivery machinery
  sits wholly outside `depthE`'s induction. Conditioned on `capsOK?` because the
  unconditional form is false.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `budget-sufficient`, so proving anything here while tier 0 is open
bets on ground an anchor failure would move. The branch's own design question
is **merge coherence** — UNSTATED again as of 2026-08-18. The `merge-cert`
postulate was retired when the two root-exit assemblies became real bodies and
showed it does not close even their `k ≡ 0` case: `mergeCertAt` rules out ALIVE
from-inner instances while `countLiveInners` counts PRESENT ones. The decidable
predicate and its probe evidence survive (`mergeCertAt`, Root-Probe); what is
parked is the corrected statement, its mid-fold FoldInv form, and the six
consumer rewrites. Full finding on `Part4.root-mergeCache`.

In rough order for when the tier opens — statement repairs first, then grinds:

- **`dispatchShare-wf`** (Part9) — DIFFICULTY: the share arm's run equation,
  `foldPath-wf`'s third clause. Its FoldOut half belongs to
  `foldPath-share-out`, so the statement as written is what `foldPath-out`
  spends.
- **`root-entry-sunk`** (Part4) — FALSITY: the per-entry residue of
  `root-done-plumbed`, now a real body. The load-bearing region (`done` with a
  live registry) was NOT reached by probe, so the class stands — but it is now
  a statement about ONE surviving entry, which is a size a counterexample can
  be built at. Coverage boundary in its header.
- **`root-mergeCache`** (Part4) — DIFFICULTY: the per-node residue of
  `root-caches`, now a real body, split to the merge clause alone. Probed
  non-vacuously in assembled form over all four *All node kinds and the
  take-cut edge. Carries a DEAD ROUTE: merge-cert does not close even its
  k ≡ 0 case (alive-vs-present), which is why that postulate is gone. The
  blocker it leaves is a MISSING INVARIANT — no dead-but-present from-inner
  instance survives in the root-exit registry — which the repo does not have.
- **`subscribeE-{merge,concat,switch,exhaust}All-wf`** (Part3) — SHAPE:
  written against a merge coherence whose statement is still open (the
  merge-cert sketch in Part8's establishment block, no longer a postulate).
- **`stepFrame-wf-outer`** (Part9) — SHAPE, on a ROUTE claim rather than the
  statement: `foldPath-frame-out`'s header says discharging it means enriching
  `stepFrame-wf` to carry FoldOut out, which would restate this family. A route
  is not evidence, so the class holds until that route is walked or replaced.
  Order it AFTER `stepFrame-wf-inner-concat`, which it strictly contains — its
  header now derives why from the evaluator.
- **`mid-readoff`** (Part11) — FALSITY: the FoldOut readoff, and FoldOut is a
  6-field invariant validated at exactly one clause.
- **`foldPath-frame-out` / `foldPath-share-out`** (Part11) — DIFFICULTY:
  `foldPath-out`'s two undischarged arms, each the FoldOut readoff only (the
  run's `S′` and equation come in from the PROVEN `foldPath-wf`). The frame arm
  wants `stepFrame-wf` enriched to carry FoldOut out; the share arm is the
  diamond's net-zero owed and additionally waits on `dispatchShare-wf`.
- **`mid-fold-certs`** (Part11) — DIFFICULTY: one case split on
  `Arrival.isLast a` off `Mid.done-plumbed`; the blueprint's GUARD applies to
  its flip conjunct.
- **`map-valsLast-push` / `scan-valsLast-push`** (Part3) — SHAPE: each papers
  over a recorded mismatch (the proven sub-lemmas don't return `valsLast?`).
- **`map-nodry-push`** (Part3) — GRINDABLE: every ingredient is PROVEN —
  `pushBurst-map-char` (.Part5) and the dry family `splitEvents-nodry` /
  `retagEvents-dry` / `mapValue-dry` / `any-dry-++` (.Walk-Level). Only import
  wiring remains, and Part3 already reaches that cone through Caps-Bridge.
- **`scan-nodry-push`, `scan-nodeP`** (Part3) — DIFFICULTY: no
  `pushBurst-scan-char` counterpart of the map characterisation exists, and
  `-nodeP` additionally wants an unproven "inner `subscribeE` never overwrites a
  pre-existing nid" induction — `subscribeE-keeps` tracks slots, not the node
  table.
- **`input-hot-spent-wf`** (Part3) — GRINDABLE: the PROVEN `oneShotBurst-wf`
  (.Part2) is the same init/close/complete balance one source-state over, and
  the header carries the whole argument with nothing left open.
- **`subscribeSharedSlot-wf`** (Part3) — DIFFICULTY, blocked: `sharedConnect`
  recurses into `subscribeE`, so this arm cannot close outside the mutual block
  holding `subscribeE-wf`, two files down.
- **`input-cold-async-wf`** (Part3) — DIFFICULTY: its one named precedent
  `initReg-wf` is ruled out in the header — that lemma's emit is `init src ∷ []`
  while this ships the sync prefix in the same emit.
- **`subscribeE-defer-wf`** (Part3) — DIFFICULTY, now well-scoped: three BurstInv
  conjuncts fall out at once (hasDry vacuous, valsLast? by computation, hot-live
  definitional); the whole residue is `liveTypeOK?` at the minted source, whose
  tail needs a mintSource-freshness lemma the repo does not have.
- **`take-nodry-push`** (Part3) — GRINDABLE, and NOT by the scan twin its header
  names: `cutThrough` emits only `close src cut`/`cutPending` while `dryEvent`
  fires on `dried` alone, so dryness is structural, and `retagEvents-dry`
  (.Walk-Level) is proven. `ecEq` comes from the outer pushBurst's node lookup.
- **`take-nodeP`** (Part3) — DIFFICULTY: strictly stronger than `scan-nodeP`
  (exact kCount, not mere presence), so it inherits that row's missing induction
  and adds count bookkeeping over cutThrough's closes.
- **`cutThrough-close-bound-dying` / `cutThrough-live-dying`** (Part7) — SHAPE:
  both REFUTED (`Refuted.Cut-Through`), `L₁` free at exactly the sources the
  conclusions speak about. Restate over the (LAG) ledger; header carries the
  repair and why it was not ground here.
- **`subscribeE-dying`** (Part8) — GRINDABLE, large: `subscribeE` never writes
  `dying` — two writers, neither reachable from it, both named in its header.
  Nothing undecided; the cost is that the induction covers every clause.
- **`HotLive`'s preservation leaves** (Part2) — GRINDABLE, all five:
  `sched-init-hot-live`, `mintSource-hot-live`, `subscribeE-hot-live`,
  `cascadeFinish-hot-live`, `sched-next-hot-live`. Every header states a
  slots-untouched / prepend-only route with nothing undecided; `sched-next`'s
  twin `regTyped?-pop-sched` is PROVEN, and `cutSched-hot-live` (.Part6) is the
  family's worked body over the PROVEN `liveTypeOK?-sweepLive`.
- **`cut-owed`** (Part9) — DIFFICULTY: independent of every blocker, but its own
  header calls the owed-shape obligation "genuinely semantic" and names no
  precedent, so being unblocked is not the same as being mechanical.
- **`stepFrame-wf-inner-concat`** (Part9) — DIFFICULTY: concat's drain grows
  the registry; re-establish FoldInv. Independent of merge-cert.

## Tier 3 — the top-line semantic claims (parked behind tier 2)

The second ledger: claims Main asserts beside the main theorem, off its
critical path.

- **Vacuous-by-abstraction — VACUITY** — `locality`, `non-interference`,
  `timing-invariance` (Rx/Time-Theorems, over nine postulated abstractions),
  `causality` (postulated `truncateIn`/`emittedBefore`), `μ-guarded` (type
  identical to `μ-unfold`'s), `defer-shift` (⊤ on purpose — the one allowlisted
  honest gap). De-risking these means DEFINING the abstractions — claim
  authoring that needs Anthony, not a grind. **Not GRINDABLE and never will
  be**: no precedent can make them mechanical, because nothing is stated yet.
- **Real, probed, awaiting proof — DIFFICULTY** — `μ-unfold` (residual risk: a
  program near the `gs`-level boundary), `fuel-coherent`, `id-inheritance`,
  `batch-online` (restated pre-flush over `foldBatch-no-flush`), and the ten
  `readme-*` claims. Probe receipts live in the module headers. A refutation
  of a `readme-*` claim is SPEC-level: surface to Anthony, do not patch.
  None has been header-audited for a worked precedent, so none is demoted;
  the audit is worth doing only if this tier is ever reached.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.
