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
- **The ledger is the source of truth, not this file.** `make wiring` lists
  every live postulate; every one of them appears in exactly one tier below,
  and a name here that no longer greps is a bug in this file — fix on sight.
- **There is no second roadmap.** Not a session task list, not a worker's
  notes, not a scratch file. A parallel list is outside the repo, so no gate
  and no `grep` can see it rot — one ran beside this file for weeks, kept
  every completed row, and outlived this file's rewrite by a commit. The tell
  is citing work by a NUMBER: names come from here and from the ledger,
  numbers come from somewhere that should not exist. Find it and delete it.

**The tier law and the risk classes are DEFINED IN CLAUDE.md** — tier 0 finishes
first, then 1, then 2, then 3, strictly; classes worst-first are FALSITY, SHAPE,
VACUITY, DIFFICULTY. This file only ASSIGNS them. Read that section before
re-classifying anything: what counts as evidence for lowering a class, and the
convergence test for whether a spawned FALSITY is progress, both live there.

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
     │   └─ drain-dry   ← cascade-wet-via-caps     [tier 0: subscribeE-inner-nodry, dry-tick-core]
     └─ the well-formedness branch       its own postulates — tier 2
```

The caps route does not replace the wet contract — it rests on it: both
branches of `budget-sufficient` read `subscribeE-wet`'s `hasDry`/`INV?`
conjuncts, so no amount of caps work retires tier 0.

## Tier −1 — THE LEAF-ONLY MIGRATION (ahead of tier 0)

The postulates that still take PROVEN LEMMAS as arguments, in violation of the
leaf-only rule (defined in CLAUDE.md). Each migrates by **INSTANTIATE, DON'T
PASS**: replace `P = P-core l₁ … lₖ` with a real body that APPLIES each `lᵢ` at
this site's own arguments, postulating only the residue. Applying is what pays
each lemma's premises, and paying them is the point — a passed lemma has never
had its FIT tested, so nothing checks that its type is the one the parent needs.

**THE FIRST ONE LANDED, AND IT PAID BOTH WAYS.** `subscribeE-input-wf` is a real
body now. Applying `initReg-wf` is what surfaced the missing `ltok` — a whole
absent schedule invariant, now the `hot-live` field — and it also RETIRED an arm
the `-core` had absorbed silently: the cold/no-async arm is `oneShotBurst`
verbatim, closed outright by the proven `oneShotBurst-wf`. Expect both outcomes
from the rest; neither is visible while the lemma is merely passed.

**AND THE THIRD OUTCOME IS A STOP, WHICH IS A FINDING AND NOT A DISCHARGE.**
`subscribeE-takeᵉ-wf-core` stays a parent: applying its lemma exposed a premise
that is FALSE at the only call site, so the row, the `DEFERRED.txt` line and the
leaf-only violation all stay live until the repair lands. A stopped migration
still pays — it converts an unexamined premise into a machine refutation — but it
does not close its row.

**AND A STOP CAN BE RESUMED BY A RULING.** `BurstInv.live-matches` is now keyed
off `EvalSt.dying st` (Anthony, 2026-08-18), which unblocked that stop: the
refuted `dyF` premise is not re-keyed but GONE from `cut-head-joint`,
`pushBurst-take-{cut-,}joint` and `subscribeE-take-wf`'s conjunct list. The
migration's own blocker is cleared; the row stays until the body actually lands.

**TIER MEMBERSHIP EXEMPTS NOTHING HERE (Anthony, 2026-08-15).** The migration is
not scheduled against the tier order and does not defer to it: a lemma whose type
was never checked against its parent's need is wasted work at every tier, so the
fit test is worth more the earlier it runs — which is why the nominally-tier-2
`mid-step-core` was migrated here rather than parked.

The residue `P-rest` may remain a postulate — that is what makes this a migration
rather than a proof, and it is the FLOOR, not a ceiling. Where the parent falls
out fully once its lemmas are actually applied, take it. **A landed migration's
residue leaves move to their own tier**, not this one: they take no proven lemma,
so they are ordinary work and this tier stays the migration worklist.

`agda/DEFERRED.txt` is the grandfather list and shrinks as these land. Cheapest
first, so the single-lemma parents establish the pattern:

- **`subscribeE-takeᵉ-wf-core`** (Part3) — one lemma (`subscribeE-take-wf`).
  **UNBLOCKED 2026-08-18, NOT YET LANDED**: the `dyF` survivor is gone with the
  A′ re-keying of `BurstInv.live-matches`, so every arm is now payable (the zero
  arm falls to `oneShotBurst-wf` outright). Remaining: write the body over
  `ec`/`ecEq` as ordinary arguments (the with-abstraction dodge its header
  records), with `take-binv-adapt`, `take-nodry-push`, `take-nodeP` as residue.
- **`dry-tick-core`** (Caps-Bridge) — NINE lemmas, the largest, and eight of them
  are not ingredients: `cascadeFinish` emits nothing (pinned), so the conclusion is
  `cascadeGo-nodry`'s verbatim. The INV?-without-capsOK? refutation IS NOW BUILT
  (pin beside the postulate; the gap is the concat queue's LENGTH, not a width), so
  restating `dry-tick` over the `capsOK?` its sole caller already holds is
  UNBLOCKED. Remaining: do that restatement, and re-home the eight onto
  `cascade-wet-via-caps`'s other two conjuncts. Finding in its header. Tier-0 parent.

## Tier 0 — THE ANCHOR CHAIN (everything else waits on this)

Work top to bottom. Every full route, receipt, and ruling lives in the
named postulate's own header.

- **`input-wet`** (Walk-Level) — DIFFICULTY, lowered from FALSITY: the Ψ
  axis is closed by PROVEN `caseW-subΘ` + `fnCap-subΘᵉ`, the refuted hop
  conjunct's repair is proven, and every conjunct has non-degenerate
  coverage. Mutual landing done; the three-clause induction is the work.
  Evidence, the hop disanalogy and the landing in its header.
- **`slotHop-cap`** (Measures) — DIFFICULTY, lowered from FALSITY by
  Demand-Probe series S, which reached the amplifier-chain region and
  measured the margin widening. Route and coverage in its header.
- **`mu-lvl-desc`** (Walk-Level) — DIFFICULTY, low. The μ edge's L̂
  transport, and its header names a route over FOUR PROVEN lemmas
  (op-step-mu, inner-desc, opIterD-mono, sLvlD-suc) — the caps side does
  not donate the statement, but it does donate all the machinery.
- **`fnCap-unfoldμ`** (Walk-Level) — DIFFICULTY, low: the fnCap sibling
  of the proven shellSize-/syncSize-/size-unfoldμ inductions.
- **`walk-{of,empty,map,take,scan,defer}`** (Walk-Level) — DIFFICULTY.
  The walk face's one-shot and chain clauses; scan exercises the
  Ŝ-ceiling growth, defer mints the registry entry.
- **`subscribeE-inner-nodry-inv`** (Burst-Walk) — DIFFICULTY, reclassified
  from FALSITY: it was SHAPE, and the repair is landed. Finding in its
  header.
- **`subscribeE-inner-nodry-{pBO,depth}`** (Burst-Walk) — DIFFICULTY.
  Path-extension and depth-mirror plumbing for the inner call.
- **`entry-slotsCaps` / `entry-slotsSize` / `capsOK⇒regsLen` /
  `regsLen?-mono`** (Walk-Level) — DIFFICULTY. Entry plumbing for the
  outer assembly; each self-contained, none level-indexed.
- **`INV?-install`** (Walk-Level) — DIFFICULTY. Node-install plumbing
  the *All body consumes; conjunct-by-conjunct route in its header.
  (Its former row-mate pathB?-mono-B is GONE — it duplicated the proven
  pathB?-widen, .Measures, found by a name clash; grep before stating.)
- **`innerReact-nodry-slFc` / `thruOuter-nodry-slFc`** (Burst-Walk) — DIFFICULTY,
  parked. The static `slotsFnCap sl ≤ Ψ` both nodry bodies need; wants INV?
  threading that `stepFrame-nodry`'s hypotheses do not yet carry. The first
  carries NO depth premise — dropped as a non-ingredient the fit test exposed,
  which STRENGTHENS it; its twin still carries one, pending Anthony's ruling.
  Reasoning in the first's header.
- **`concatDrain-nodry-vb` / `-nestBud` / `-dep` / `-cl` / `-loop` / `-nestRec`**
  (Burst-Walk) — DIFFICULTY, parked. Per-element context for concat's drain:
  each re-establishes one hypothesis of `subscribeInner-nodry` after the
  previous element has moved the state.
- **`thruConsume-nodry-vb` / `-nestBud` / `-dep` / `-loop`, `thruWalk-nodry-dep`,
  `VbB-tail`, `switchKill-context`** (Burst-Walk) — DIFFICULTY, parked. The same
  per-element context on the thru-outer side, plus switchKill's OKB/regP
  transport. `VbB-tail` carries a phantom `{e}` its statement never mentions.
- **`dry-tick-core`** (Caps-Bridge) — DIFFICULTY. Latch/finish bookkeeping
  plus the Deliveries counts. Last in the tier, never first.

## Tier 1 — Verify-Budget-Sufficient (parked behind tier 0)

Labour, not risk: nothing here can discover a design failure, and an anchor
failure would move the ground under all of it.

- **`subscribeE-demand`** (Anchor-Dry) — DIFFICULTY. The subscribe-side burst
  face; the same gap as the walk faces, and whichever of it /
  `stepFrame-burst-face`'s wet leaves is discharged first absorbs the other.
- **`subscribeE-Ψ`** (Burst-Walk) — DIFFICULTY. The Ψ face of subscribeE;
  proof sketch in its header, mirror of the proven caps clique.
- **`depth-compositional`'s residue** (Depth-Compositional) — DIFFICULTY.
  `depth-conn-storeNest`, `depth-all-bound`, `depth-μ-bound`,
  `installScan-depth-bound`; each blocker's obstacle and route in its header.
- **`cascade-depth-capsH`** (Caps-Face/Part7) — DIFFICULTY. The delivery-side
  depth bound, twin of the proven root bound; conditioned on `capsOK?`
  deliberately.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on `budget-sufficient`, so proving anything here while tier 0 is open
bets on ground an anchor failure would move. The branch's own design question
is **merge-cert** — now STATED (`merge-cert`, Part4, with the reachability
mechanism and coverage residue in its header); what stays parked is its
mid-fold FoldInv form and the six consumer rewrites.

In rough order for when the tier opens — statement repairs first, then grinds:

- **`dispatchShare-wf`** (Part9) — **SHAPE, known too weak**: its conclusion
  carries no FoldInv/FoldOut out, so it cannot feed `mid-step` as stated. A
  guaranteed restatement, cascading into the stepFrame family — do it first.
- **`root-done-plumbed-core` / `root-caches-core`** (Part4) — FALSITY,
  blocked on merge-cert's mid-fold form; the merge-coherence content itself.
- **`subscribeE-{merge,concat,switch,exhaust}All-wf`** (Part3) — SHAPE:
  written against a merge-cert form that may still gain hypotheses.
- **`stepFrame-wf-outer`** (Part9) — SHAPE, same cluster plus the FoldOut
  question.
- **`mid-readoff`** (Part11) — FALSITY, inherited from the retired
  `mid-step-core`: the FoldOut readoff, and FoldOut is a 6-field invariant
  validated at exactly one clause.
- **`foldPath-frame-out` / `foldPath-share-out`** (Part11) — DIFFICULTY:
  `foldPath-out`'s two undischarged arms. The frame arm wants `stepFrame-wf`
  enriched to carry FoldOut out; the share arm is the diamond's net-zero owed.
- **`mid-fold-certs`** (Part11) — DIFFICULTY: one case split on
  `Arrival.isLast a` off `Mid.done-plumbed`; the blueprint's GUARD applies to
  its flip conjunct.
- **`map-valsLast-push` / `scan-valsLast-push`** (Part3) — SHAPE: each papers
  over a recorded mismatch (the proven sub-lemmas don't return `valsLast?`).
- **`map-nodry-push`, `scan-nodry-push`, `scan-nodeP`** (Part3) — DIFFICULTY,
  probed non-vacuously (receipts in headers).
- **`subscribeSharedSlot-wf` / `input-hot-spent-wf` / `input-cold-async-wf`**
  (Part3) — DIFFICULTY: the input clause's three surviving arms, each stated at
  its own burst. The first is mutual with `subscribeE-wf` via `sharedConnect`;
  the other two are register/init balances of a shape proven twice over.
- **`subscribeE-defer-wf`** (Part3) — DIFFICULTY: a per-clause receipt of a
  pattern already proven three times over.
- **`subscribeE-takeᵉ-wf-core`** (Part3) — DIFFICULTY, lowered from SHAPE: the
  restatement it was waiting on landed (A′, `BurstInv.live-matches` keyed off
  `dying`), and what remains is writing the body. Tier −1 carries it.
- **`cutThrough-close-bound-dying` / `cutThrough-live-dying`** (Part7) — FALSITY,
  A′'s residue and the honest cost of it: at a dying source the live list lags the
  registry by the already-delivered entries, and neither leaf can be proven until
  that lag is an invariant. The exact ledger, and why adding it as a `BurstInv`
  field spirals into the registry's id discipline, are in their shared header.
- **`subscribeE-dying`** (Part8) — DIFFICULTY, low: `subscribeE` never writes
  `dying` (two writers, neither reachable from it). An induction over its clause
  set; the route is in its header.
- **`HotLive`'s preservation leaves** (Part2) — DIFFICULTY, the `hot-live` field's
  own cost and the first migration's residue: `sched-init-hot-live` (base, from
  `mkHot`), `mintSource-hot-live`, `subscribeE-hot-live`, `cascadeFinish-hot-live`,
  `sched-next-hot-live`. Each is a schedule-transition fact; routes in their shared
  header. `cutSched`'s case is already a real body over the proven
  `liveTypeOK?-sweepLive`, so it is not among them.
- **`cut-owed`** (Part9) — DIFFICULTY, low: self-contained Owed-table algebra,
  independent of every blocker; the easiest real proof in the branch.
- **`stepFrame-wf-inner-concat`** (Part9) — DIFFICULTY: concat's drain grows
  the registry; re-establish FoldInv. Independent of merge-cert.

## Tier 3 — the top-line semantic claims (parked behind tier 2)

The second ledger: claims Main asserts beside the main theorem, off its
critical path.

- **Vacuous-by-abstraction** — `locality`, `non-interference`,
  `timing-invariance` (Rx/Time-Theorems, over nine postulated abstractions),
  `causality` (postulated `truncateIn`/`emittedBefore`), `μ-guarded` (type
  identical to `μ-unfold`'s), `defer-shift` (⊤ on purpose — the one allowlisted
  honest gap). De-risking these means DEFINING the abstractions — claim
  authoring that needs Anthony, not a grind.
- **Real, probed, awaiting proof** — `μ-unfold` (residual risk: a program near
  the `gs`-level boundary), `fuel-coherent`, `id-inheritance`,
  `batch-online` (restated pre-flush over `foldBatch-no-flush`), and the ten
  `readme-*` claims. Probe receipts live in the module headers. A refutation
  of a `readme-*` claim is SPEC-level: surface to Anthony, do not patch.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.
