# PROOF-STATE — the canonical design-state index

**Read this first, every session, before any proof work.** Update it in the same
commit as every ruling, every postulate added or discharged, every gap opened or
closed. Detailed records stay in source comments — this file is pointers, not
copies. If a pointer and its source comment disagree, the source comment wins;
fix the pointer.

Why this file exists: the design state used to live only in scattered
mega-comments (Wet.agda's GAP 4 block, Caps-Face:6087, probe headers). Sessions
that didn't re-read them paid a rediscovery tax — re-refuting the sync-μ
adversary, "discovering" caps-tick has no consumer, reading GAP 4's REFUTED as
news. Every one of those was already written down. This index is the fix.

## The theorem chain (top → leaves)

```
formal-verification-batchSimultaneous          The-Proof.agda:1098 — REAL, module postulate-free
 ├─ batch-agreement                            proven
 └─ evaluate-well-formed                       Verify-Well-Formed.agda:5328
     └─ budget-sufficient                      Wet.agda — PROVEN from:
         ├─ burst-wet    ← subscribeE-wet      [P1]
         ├─ cascade-dry  ← cascadeGo-wet       [P2]
         └─ drain-dry                          proven
```

So the entire campaign reduces to the postulate ledger below. Nothing else
stands between the repo and the finish line.

## Postulate ledger (critical path: 5)

| # | Name | Where | Blocked by |
|---|------|-------|-----------|
| P1 | `subscribeE-wet` | Wet.agda:4294 | GAP 4 (a) + (b) |
| P2 | `cascadeGo-wet` | Wet.agda:4335 | GAP 4 (b); decomposed into S1-S4 + bridge lemmas, `Caps-Bridge.agda` — `cascade-wet-via-caps` is the real replacement, not yet wired as P2's consumer |
| P3 | `innerFinish-concat-face` | Caps-Face.agda:6233 | GAP 4 (a) — same hole, seen from the caps side |
| P4 | `thruOuter-face` | Caps-Face.agda:6248 | GAP 4 (a) — same hole |
| P5 | `subscribeE-walk` | Measures.agda:6173 | none named; internal mid-instant walk. Its receipt CANNOT supply P1's landing (that composition is refuted — see GAP 4) |

Off the critical path: `batch-online` (Batch-Theorems.agda:9) — extrinsic
no-lookahead property, reachable from Main.agda but not consumed by The-Proof.

## Named gaps and rulings (the full deck)

**GAP 4** — Wet.agda:4125–4199. THE central design fact. The ledger-receipt
route from P5's conclusion to P1's landing is **REFUTED** (wet-ceiling-absurd —
a route, NOT the theorem: "It does not refute subscribeE-wet"). The one
surviving route is the **caps face**, whose delivery half is already ground
(`caps-tick`, Caps-Face:6752, PROVEN: `capsOK?` at `id` → `capsOK?` at `suc id`
across a whole cascade). Two blockers stand, both statement-level:

- **(a) No subscribe-level charge.** `subscribeE-caps` reports at
  `frameStep (j + j′) c` with `j′` unbounded; nothing budgets a bare
  subscribe's growth index. The missing companion is NOT a closed form
  (Sub-Charge-Probe: subscribe and frame charges are mutually recursive) —
  it needs recursion on a **nesting budget**. The Caps-Depth mirror + the
  `dpt` threading through Subscribe-Face (Unit 3, landed, postulate-free)
  IS that budget. P3/P4 wait on this same companion.
- **(b) `capsOK?` is not `INV?`.** They share `stBounded?` and nothing else;
  `INV?` adds `fnCapBounded?`, `regsB?`, `slotsFnCap`, and reads registry
  cardinality at `cSize` where `capsOK?` reads `cReg`. Four wet conjuncts have
  no caps-side counterpart. The bridge is the most uncertain open piece.

**Sync-μ escape: CLOSED BY TYPING.** `deferᵉ` is the sole gate moving `Δᵍ`
into `Δ`, so a μ's self-reference costs a tick; synchronous self-subscription
is not writable. Recorded at Wet.agda:4186 and Caps-Face:6087. Do not
re-refute this.

**Depth obligation must be conditioned.** `depthE ≤ capsBase` is FALSE
(machine-refuted, `agda/probe/Depth-Blowup-Probe.agda`: scan accumulators
deepen per fold while capsBase gains +1 per arrival). Unconditionally,
`depthE ≤ capsH` is also indefensible (an adversarial stored state defeats
any entry-computable bound). The honest statement conditions on `capsOK?` —
which bounds stored value sizes via `stBounded?` and is already in scope at
`caps-tick`, the only site that spends the fuel.

**Fold-threading (2026-07-20, standing).** P2 does not decompose into a
per-chainStep contract at fixed bounds (caps-frame-boundary-absurd). The
honest decomposition threads per-cascade growth, which the caps face's `j`
index does.

## Supplier → consumer map

| Supplier (proven) | Feeds | Status |
|---|---|---|
| `caps-tick` (Caps-Face:6752) | `cascade-wet-via-caps` (Caps-Bridge.agda) | assembled; INV? closed conjunct-by-conjunct |
| Caps-Depth mirror + Subscribe-Face `dpt` threading | `sub-charge` (Caps-Bridge.agda), GAP 4 (a)'s nesting budget | PROVEN — no misalignment, no postulate needed |
| `subscribeE-walkS` family (Wet:1367) | the internal walk under P1's grind | ground |
| `chainsOf-B` (Wet:4270) | P2's chain-bound hypothesis | done, wired |

A proven fact with no consumer here is speculative inventory — flag it.

## Active tasks → gaps

- Task #16 (assembly skeleton) → DONE: `agda/src/Verify-Budget-Sufficient/Caps-Bridge.agda`.
  Bridge lemmas B1 (`Caps.cSize (capsAt e sl id) ≡ sizeCapAt e sl id`, PROVEN by
  refl) and B2 (`cReg ≤ cSize` at a level, postulated — base case holds, the
  frameBlowup-iteration case needs a joint induction nobody has done). Four
  postulated suppliers stated: S1 `fn-tick` (fn face + Ψ-half of regsB?
  preserved across a cascade), S2 `slots-tick` (stated as the STRONGER raw
  `Sched.slots` equality across a cascade — structurally true, no `slots =`
  update anywhere in Rx.Evaluator's mutual delivery clique, but unproven at
  this layer), S3 `dry-tick` (P2's unchanged dry half). S4 `sub-charge` needed
  NO postulate and NO misalignment: `subscribeE-caps` already carries
  `depthE ≤ dep` and concludes `j+j′ ≤ opIterD(...)`, and `depthE`'s argument
  list already matches subscribeE-caps' call site exactly. The real assembly
  `cascade-wet-via-caps` closes INV? conjunct-by-conjunct (no `inv-assemble`
  fallback needed) via B1/B2 + S1 + S2 + `caps-tick`, plus a new Ψ-only
  predicate family (`frameBΨ?`/`pathBΨ?`/`regsBΨ?`) and its recombination
  with capsOK?'s `regsSz?` into the real `regsB?`. NEXT: prove S1/S2/B2 for
  real, then state `subscribeE-wet-via-caps` (P1's analogue) now that S4 is
  clear, then wire `cascade-wet-via-caps` as `cascade-dry`/`burst-wet`'s
  supplier in place of `cascadeGo-wet`.
- Task #13 (depth obligation statement) → GAP 4 (a)'s nesting budget, stated
  conditionally on `capsOK?`.
- Task #4 (P3 + P4) → GAP 4 (a). Do not start before the charge companion is
  stated.
- Task #5 (P5) → independent of GAP 4; safe parallel work.
- Task #6 (P1 + P2) → GAP 4 (a) + (b); the endgame, last.
