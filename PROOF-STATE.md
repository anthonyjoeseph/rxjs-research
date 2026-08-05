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

## Postulate ledger (critical path: 4, plus 1 orphan)

| # | Name | Where | Blocked by |
|---|------|-------|-----------|
| P1 | `subscribeE-wet` | Wet.agda:4294 | the SUBSCRIBE-side bridge (unstated) + its dry half (gas axis). GAP 4 (a) is CLOSED. |
| P2 | `cascadeGo-wet` | Wet.agda:4335 | `dry-tick` only. `cascade-wet-via-caps` (Caps-Bridge) is the real replacement and its other three suppliers are now PROVEN; not yet wired as P2's consumer |
| P3 | `innerFinish-concat-face` | Caps-Face.agda:6233 | nothing named — GAP 4 (a)'s companion is PROVEN (`sub-charge`). Expect grind, not design. **Genuinely consumed** at Caps-Face:6336 |
| P4 | `thruOuter-face` | Caps-Face.agda:6248 | same as P3. **Genuinely consumed** at Caps-Face:6522 |
| P5 | `subscribeE-walk` | Measures.agda:6204 | **ORPHANED — ZERO CONSUMERS.** See below. |

**P5 IS NOT ON THE CRITICAL PATH, and is a deletion candidate.** Verified
2026-08-05 by grep: its only occurrence in all of `agda/src` is its own
declaration (one prose mention in Wet's GAP 4 comment aside). Nothing consumes
it. That is consistent with what it IS — the ledger receipt whose composition to
P1's landing GAP 4 *refuted* — so it looks like weight left behind when that
route died. Note it is distinct from `subscribeE-walkS` (Wet:1367), the PROVEN
family that is genuinely used. Deleting an unused postulate is strictly sound:
it removes an assumption and cannot break a proof. **Ruling needed:** confirm no
future consumer is intended, then delete for a free 4 → 3 on the ledger. Do not
spend proof effort on it before that ruling.

**THE CAPS CHAIN DEPENDS ON P3 + P4.** `caps-tick` is described as "ground", and
it is — *modulo* the two faces above, which are real call sites inside the caps
clique, not decoration. Since `cascade-wet-via-caps` rests on `caps-tick`, P2's
replacement transitively needs P3 and P4 too. Earlier versions of this table
hid that; it is the third time this index read more optimistically than the
tree (see also `caps-tick`'s missing consumer and P5). **When in doubt, grep for
consumers before believing a status here.**

Off the critical path: `batch-online` (Batch-Theorems.agda:9) — extrinsic
no-lookahead property, reachable from Main.agda but not consumed by The-Proof.

**Decomposition postulates** (the named small pieces the monoliths reduce to —
these are progress, but they count; discharging one of P1–P5 by assembly means
these become the ledger):

| Name | Where | Content |
|---|---|---|
| S3 `dry-tick` | Caps-Bridge.agda | P2's dry half. **Its arithmetic is ALREADY PROVEN** — see "The gas axis" below. Expected to be a wiring job, the cheapest remaining win. |
| `depth-compositional` | Depth-Bound.agda | `depthE ≤ sizeᵉ b + pathLen κ + storeNestMax` (structural induction over the mirror). CENSUSED 2026-08-05: scope is 16 heads, not 19 (the delivery family — depthFold/depthDisp/depthShareGo/depthChain — is out of scope). The real remaining work is a state-growth conjunct, not a lemma about the mirror itself — every clause feeds `depthBurst` the state from the REAL `subscribeE` run, while the bound's RHS reads the entry state, so the induction needs `storeNestMax` at the evolved state dominated by the entry's bound. Details, including the ruling to prove this as a second conjunct of the same induction rather than a separate family, are in Depth-Bound.agda's header. |

(B2, S1 `fn-tick`, S2 `slots-tick`, and `storeNest-capped` are PROVEN — landed
in Caps-Bridge.agda and Depth-Bound.agda respectively, no longer postulates.)

## Named gaps and rulings (the full deck)

**GAP 4** — Wet.agda:4125–4199. THE central design fact. The ledger-receipt
route from P5's conclusion to P1's landing is **REFUTED** (wet-ceiling-absurd —
a route, NOT the theorem: "It does not refute subscribeE-wet"). The one
surviving route is the **caps face**, whose delivery half is already ground
(`caps-tick`, Caps-Face:6752, PROVEN: `capsOK?` at `id` → `capsOK?` at `suc id`
across a whole cascade). Two blockers stand, both statement-level:

- **(a) No subscribe-level charge — CLOSED 2026-08-05.** The companion is
  `sub-charge` (Caps-Bridge.agda), and it needed no postulate: Unit 3's `dpt`
  threading had already put `depthE … ≤ dep` into `subscribeE-caps`, whose
  conclusion already bounds `j + j′`. The debt did not vanish, it MOVED — the
  bound is stated in terms of `depthE`, so it is now `depth-compositional`'s
  (Depth-Bound.agda). P3/P4 no longer wait on a design question.
- **(b) `capsOK?` is not `INV?`.** They share `stBounded?` and nothing else;
  `INV?` adds `fnCapBounded?`, `regsB?`, `slotsFnCap`, and reads registry
  cardinality at `cSize` where `capsOK?` reads `cReg`. Four wet conjuncts have
  no caps-side counterpart. **The DELIVERY side is now bridged** —
  `cascade-wet-via-caps` assembles all six conjuncts, no fallback postulate.
  The SUBSCRIBE side (P1's analogue) is still unstated and is the untested half.

**GAP 4's obstruction does NOT apply to Ψ-only faces (2026-08-05, from
`fn-tick`'s proof).** `fn-tick` is proven by reusing `cascadeGo-walk` — the very
interior fold P2 is stuck on. P2 is stuck only on relating that fold's final
ledger bound back to a fixed cap, which is the refuted composition; but a
conclusion that is Ψ-indexed only does not read the numeric bound, so *any*
bound the fold lands at suffices. **Template: face by face, whatever does not
read the numeric bound can cross the ledger gap today.** Worth trying on other
faces before assuming GAP 4 blocks them.

**THE GAS AXIS IS PROVEN, AND ORPHANED (censused + design-verified
2026-08-05).** It had been assumed the largest remaining risk, on the grounds
that nobody had attempted it. That was wrong, and the correction matters for
planning:

- **Exactly three decrement edges**, confirmed by enumerating every clause of
  the subscribe clique (`Rx/Evaluator.agda:939-1477`), and stated by the
  machine's own comment at `Evaluator.agda:340-344`: the μ unfold
  (`Evaluator.agda:1456`), the share connect (`sharedConnect`, 1348), and the
  inner-value subscribe (`subscribeInner`, 1009). Every other recursion threads
  gas UNCHANGED — the decrement is internal to those three functions, never at
  a caller's call site. No fourth edge exists.
- **All three edges' arithmetic is PROVEN**, in `Wet.agda:3867-4091` under its
  own heading ("THE THREE GAS EDGES, PACKAGED"): `mu-edge` (4032), `hop-edge`
  (4047), `connect-edge` (4060), plus `unconn-keeps` (4079) for U between
  edges, and `hop-step-gives`/`hop-step-needs` (3873/3879) which characterise a
  hop's slack in BOTH directions — the bound is tight, not merely sufficient.
  Verified as real proof bodies with no postulate block in range.
- **`caps-fuel-root`** (`Wet.agda:4530`) is proven AND wired, as `burst-wet`'s
  fuel witness. It also confirms the tower relationship as a theorem rather than
  folklore: gas sits exactly three tower stories above the caps level.
- **Zero corners are vacuous, not holes.** At `r = 0` / `U = 0` / `s = 0` the
  corresponding edge cannot fire (its `_<_` hypothesis is uninhabited), so the
  obligation disappears with the edge. Already named and dismissed at
  `Wet.agda:4152-4155`.
- **But the whole package has ZERO consumers** — grep finds only the
  definitions. `dry-tick`'s own comment says why: it is "not touched by the
  caps/INV? bridging problem at all". So the gas axis is solved and merely
  unwired.

**Consequence for the risk ranking:** fuel sufficiency is NOT the risk. The
remaining risk is concentrated in GAP 4 (b) — the `capsOK?` ↔ `INV?` bridge on
the SUBSCRIBE side — and in `depth-compositional`'s state-growth conjunct.

**One caution flagged during the census, unresolved:** `walk-hyps-round3b`
(`Measures.agda:6510`) is a proven Σ-receipt showing the edge constraints are
jointly satisfiable at ONE entry point. Per CLAUDE.md's Σ-receipt rule, that is
not the same as an end-to-end induction, and its own comment (6199) says so. Do
not read it as "the walk is basically done."

**Look one layer down before writing anything (2026-08-05).** FOUR separate
facts this session turned out to be already proven beneath where they were
needed: `sub-charge`'s hypothesis (in `subscribeE-caps`), `slots-tick` (in
`Keeps-Ring:952` + `Caps-Face:3690+` + `Measures:493` — a worker had drafted a
21-lemma mutual mirror before finding it), `fn-tick`'s fold (`cascadeGo-walk`),
and the entire gas axis (above). Grep for the fact before planning its proof.

**THE STANDING LESSON, four instances deep.** This campaign's dominant failure
mode is not wrong proofs — it is *not knowing what it already has*. Orphaned
proven work (`caps-tick`, P5, the three gas edges) and already-satisfied
hypotheses have each cost more than any refutation did. Two habits follow, and
they are cheap: **grep for a fact before planning its proof**, and **grep for a
proven lemma's consumers before believing its status here**. A proven lemma with
no consumer is either a missing wire or dead weight; both are findings.

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
| `caps-tick` (Caps-Face:6752) | `cascade-wet-via-caps` (Caps-Bridge.agda) | assembled; INV? closed conjunct-by-conjunct. Rests on P3 + P4 |
| Caps-Depth mirror + Subscribe-Face `dpt` threading | `sub-charge` (Caps-Bridge.agda), GAP 4 (a)'s nesting budget | PROVEN — no misalignment, no postulate needed |
| `sub-charge` (Caps-Bridge.agda) | `depth-capped` (Depth-Bound.agda) | PROVEN; spends `depthE`, so it is what makes `depth-compositional` load-bearing |
| `storeNest-capped`, `B2`, `fn-tick`, `slots-tick` | `cascade-wet-via-caps` / `depth-capped` | PROVEN 2026-08-05, all four wired |
| `cascadeGo-walk` (Wet:2145) | `fn-tick` | PROVEN; the Ψ-only crossing of GAP 4's gap |
| `chainsOf-B` (Wet:4270) | P2's chain-bound hypothesis | done, wired |
| `subscribeE-walkS` family (Wet:1367) | the internal walk under P1's grind | ground |

A proven fact with no consumer here is speculative inventory — flag it. (This
is how `caps-tick`'s orphaning and P5's were both caught.)

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
- Task #13 (depth obligation) → STATED:
  `agda/src/Verify-Budget-Sufficient/Depth-Bound.agda`. The probe-validated
  measure (`storeNestMax` = slot shared defs ⊔ boundedNode's two live clauses)
  is now a src definition; two postulates with their consumer written first:
  `depth-compositional` (`depthE ≤ sizeᵉ b + pathLen κ + storeNestMax`, C = 0
  per the probe; proof route = structural induction over the depth mirror's
  clauses, one channel each) and `storeNest-capped` (`capsOK?` +
  `slotsSize ≤ cSize` → `storeNestMax ≤ cSize`; an inversion of stBounded? +
  the slots chain). The assembly `depth-capped` is a REAL definition:
  `depthE ≤ 3·cSize c` under exactly `sub-charge`'s hypothesis list — the
  entry-computable cap that makes `opIterD … depthE …` spendable, tower-free.
  Probe evidence (`agda/probe/Depth-Compositional-Probe.agda`): VALIDATED
  C = 0, k = 1-4, N ≤ 10, plus three targeted refutation attempts (large
  static shared def, 30-deep κ, concat-st queue of nested observables) — all
  hold, slack positive and non-shrinking. NOT reached: k ≥ 6 / N ≥ 13-22
  (measured computability wall in the probe's real-run extraction, ~×1.5 per
  unit k — an infrastructure limit, not a finding either way); that zone is
  covered by the structural shape of `depth-compositional`'s eventual proof,
  not by rows.
- Task #4 (P3 + P4) → GAP 4 (a). Do not start before the charge companion is
  stated.
- Task #5 (P5) → independent of GAP 4; safe parallel work.
- Task #6 (P1 + P2) → GAP 4 (a) + (b); the endgame, last.
