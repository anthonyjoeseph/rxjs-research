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
  finding that reorders it.
- **The ledger is the source of truth, not this file.** `make wiring` lists
  every live postulate; every one of them appears in exactly one tier below,
  and a name here that no longer greps is a bug in this file — fix on sight.
- **There is no second roadmap.** Not a session task list, not a worker's
  notes, not a scratch file. A parallel list is outside the repo, so no gate
  and no `grep` can see it rot — one ran beside this file for weeks, kept
  every completed row, and outlived this file's rewrite by a commit. The tell
  is citing work by a NUMBER: names come from here and from the ledger,
  numbers come from somewhere that should not exist. Find it and delete it.

**The tier law (CLAUDE.md):** tier 0 finishes first, then 1, then 2, then 3 —
strictly; the one carve-out is answering a design question. Risk classes,
worst first: **FALSITY** (the statement may be false — everything ground above
it is then wasted), **SHAPE** (wrong statement, a guaranteed restatement),
**VACUITY** (typechecks but asserts nothing), **DIFFICULTY** (true and
correctly stated; the proof is just hard).

## The theorem chain (top → leaves)

```
formal-verification-batchSimultaneous    The-Proof.agda — REAL, module postulate-free
 ├─ batch-agreement                      proven
 └─ evaluate-well-formed                 Verify-Well-Formed/ — tier 2
     ├─ budget-sufficient                Caps-Bridge.agda — PROVEN from:
     │   ├─ burst-wet   ← subscribeE-wet           [tier 0/1: subscribeE-wet-core + walk residue]
     │   ├─ burst-caps  ← subscribeE-wet-via-caps  [proven, but reads subscribeE-wet's conjuncts]
     │   └─ drain-dry   ← cascade-wet-via-caps     [tier 0: cascadeGo-nodry, dry-tick-core]
     └─ the well-formedness branch       its own postulates — tier 2
```

The caps route does not replace the wet contract — it rests on it: both
branches of `budget-sufficient` read `subscribeE-wet`'s `hasDry`/`INV?`
conjuncts, so no amount of caps work retires tier 0.

## Tier 0 — THE ANCHOR (everything else waits on this)

The three postulates form a chain; work them top to bottom. Full routes,
probe-coverage receipts, and the recovery pointer are in their headers.
The mirror census (2026-08-12, ruling in `cascadeGo-nodry`'s header) found
the old anchor's INV? half already proven at `cascade-wet-via-caps` and
deleted it; the anchor is now dry-only.

- **`cascadeGo-nodry`** (Burst-Walk § 8) — **FALSITY, the anchor.** The
  cascade's dry half, all that remains of the old two-conjunct core;
  unprobeable (the abstract Gas family blocks every probe out of the risky
  region), so symbolic-or-nothing. Route from its header: extend the Walk's
  two-flavour ledger with a nodry conjunct (mechanical), landing the content
  in `stepFrame-burst-face`'s dry conjunct — which is `subscribeE-demand`'s
  territory, seeded-budget-covers-demand, the class `caps-fuel-root` already
  proved at the root.
- **`subscribeE-wet-core`** (Wet/Part6) — FALSITY, conditional on the anchor.
  The outer instantiation; its named unverified step is the INV?/capᴱ flavour
  conversion; maximal blast radius (both branches of `budget-sufficient`).
  The census does NOT shrink this one: the subscribe side has no caps-level
  charge (GAP 4's named companion), so both its conjuncts stay.
- **`dry-tick-core`** (Caps-Bridge) — DIFFICULTY, risk inherited from
  `cascadeGo-nodry` (its first hypothesis IS that postulate). Latch/finish
  bookkeeping plus the Deliveries counts. Last of the three, never first.

## Tier 1 — Verify-Budget-Sufficient (parked behind tier 0)

Labour, not risk: nothing here can discover a design failure, and an anchor
failure would move the ground under all of it.

- **`subscribeE-walk-core`'s residue** (Measures) — DIFFICULTY. 20 named
  sub-postulates in three shapes: 14 clause faces (worker-shaped,
  parallelisable), 5 μ-specific (the `syncSize-unfoldμ` pattern), and
  `walkCap-mono-d`. Grind tips in the section header above them.
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
- **`mid-step-core`** (Part11) — FALSITY, moderate: rests on FoldOut, a
  6-field invariant validated at exactly one clause.
- **`map-valsLast-push` / `scan-valsLast-push`** (Part3) — SHAPE: each papers
  over a recorded mismatch (the proven sub-lemmas don't return `valsLast?`).
- **`map-nodry-push`, `scan-nodry-push`, `scan-nodeP`** (Part3) — DIFFICULTY,
  probed non-vacuously (receipts in headers).
- **`subscribeE-input-wf-core`, `subscribeE-defer-wf`,
  `subscribeE-takeᵉ-wf-core`** (Part3) — DIFFICULTY: per-clause receipts of a
  pattern already proven three times over.
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
