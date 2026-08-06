# PROOF-STATE — the canonical design-state index

**Read this first, every session, before any proof work.** Update it in the same
commit as every ruling, every postulate added or discharged, every gap opened or
closed. Detailed records stay in source comments — this file is pointers, not
copies. If a pointer and its source comment disagree, the source comment wins;
fix the pointer.

> **THE WIRING LAW GOVERNS EVERYTHING BELOW — see CLAUDE.md § "The wiring law:
> NEVER LEAVE A PROOF HANGING".** Every gap is a typed postulate; every
> definition and postulate is consumed, transitively, by a top-level theorem.
> `make wiring` is the acceptance test. **The wiring pass is COMPLETE**
> (zero orphans, zero unreachable modules, every postulate consumed) — which is
> what makes the risk accounting below meaningful: the postulate ledger now IS
> the total remaining uncertainty, with nothing hiding outside it.

> **CURRENT OPERATING MODE (Anthony, 2026-08-06): DE-RISK FIRST.** Every
> postulate carries a probability of being FALSE or EMPTY, and the proof's total
> risk is the SUM over the ledger — so the work is ordered by risk reduced per
> unit effort, not by proof-progress optics. Two consequences:
>
> - **A machine refutation of a postulate is as valuable as a proof of one.**
>   Cheaper, usually. A false postulate found NOW costs a restatement; found
>   after the towers above it are ground, it costs the towers.
> - **The truth-audit prohibition from the wiring pass is LIFTED** (it was
>   scoped "during the wiring pass" and the pass is done). Auditing statements
>   for truth — especially by machine probe — is now the priority, not a
>   distraction. The SHORTCUT MANDATE's other half stands: never weaken a
>   statement to make it typecheck, and postulate rather than grind when a gap
>   is real mathematics.

## The theorem chain (top → leaves)

```
formal-verification-batchSimultaneous       The-Proof.agda:1098 — REAL, module postulate-free
 ├─ batch-agreement                         proven
 └─ evaluate-well-formed                    Verify-Well-Formed.agda
     ├─ budget-sufficient                   Caps-Bridge.agda — PROVEN from:
     │   ├─ burst-wet   ← subscribeE-wet            [T1 risk: walk-core, wet-core]
     │   ├─ burst-caps  ← subscribeE-wet-via-caps   [T1 risk: lift-core, opIterD-core, init-capsOK?]
     │   └─ drain-dry   ← cascade-wet-via-caps      [T1 risk: dry-tick-core, cascadeGo-wet-core, P3, P4]
     └─ THE WELL-FORMEDNESS BRANCH          its own 21 postulates    [T2]
```

**THE CAPS ROUTE DOES NOT REPLACE P1 — IT RESTS ON IT.** Both branches of
`budget-sufficient` route through `subscribeE-wet`: `burst-wet` directly, and
`burst-caps` because `subscribeE-wet-via-caps` takes its `hasDry` and `INV?`
conjuncts straight out of it. No amount of caps work retires the wet contract.

---

## THE RISK LEDGER — every postulate, ranked (2026-08-06 accounting)

Live names and counts come from `make wiring`; this section ranks them. Four
risk classes, worst first:

- **FALSITY** — the statement may simply be false. The worst class: everything
  ground above a false statement is wasted, and the restatement cascades.
- **SHAPE** — the statement is probably true of the right thing but is known or
  suspected to be the WRONG STATEMENT (too weak to consume, wrong hypothesis
  set, imprecise) — a guaranteed future restatement, i.e. deferred falsity.
- **VACUITY** — the statement typechecks but asserts nothing (abstract-helper
  quantification, duplicate types, `⊤`). Zero falsity risk, zero content; the
  risk is REPORTING — it reads as a claim and is not one.
- **DIFFICULTY** — believed true and correctly stated; the risk is only that
  the proof is hard. The cheapest class to carry.

**PROBEABLE means machine-checkable today**: the statement is an equation or
decidable bound over COMPUTABLE functions (`evaluate`, `capsOK?`, `opIterD`,
`depthE`, `spec-batchSimultaneous` …), so concrete instances check by `refl`
exactly like the bug cache. QuickCheck/oracle only ever tested impl≡spec —
**no postulate in this ledger has ever been probed**; that is the standing
blind spot the roadmap's Phase 0 closes.

### Tier 1 — Verify-Budget-Sufficient (12 postulates)

| # | Postulate | Where | Class | Why it ranks here |
|---|-----------|-------|-------|-------------------|
| 1 | `subscribeE-walk-core` | Measures.agda:5750 | **FALSITY, critical** | The single riskiest statement in the repo. Nine conjuncts over the whole subscribeE mutual clique; its three predecessor statements were each MACHINE-REFUTED (`walk-hyps-absurd`, `hop-anchor-absurd`, `round3-old-ell-absurd`, `round3-anchor-indexed-absurd` — the base rate on this face is bad); its hypotheses (a one-entry-point Σ-receipt + arithmetic) contain NO induction; and it assumes exactly what THE ANCHOR PROBLEM (below) says is unestablished — that Ŝ/R̂/F can be sourced from reachability. Its own comment concedes: "Frame-Work-Probe is the evidence, not a proof." |
| 2 | `cascadeGo-wet-core` | Wet.agda:4499 | **FALSITY, critical** | P2's entire content (its only hypotheses are two stBounded? preservation facts). The anchor problem on the cascade axis. The naive per-chainStep decomposition is machine-refuted (`caps-frame-boundary-absurd`), so the fold-threaded statement's truth is genuinely open, not merely unproven. |
| 3 | `subscribeE-wet-core` | Wet.agda:4311 | FALSITY, conditional | Given the walk it is "the outer instantiation" — but the instantiation must manufacture the walk's G/ℓ/Ω entry data from `INV?` alone, and the INV?/capᴱ flavor conversion is unchecked. Moderate incremental risk over #1, with maximal blast radius (both branches of budget-sufficient). |
| 4 | `sub-charge-capsOK-lift-core` | Caps-Bridge.agda:1182 | **SHAPE** | Its hypothesis carries only the ROOT instance `opIterD≤capsH-root` while its conclusion quantifies over ARBITRARY mid-run `sched`/`st`/`id`; its own route comment says "via a GENERAL form of opIterD≤sizeCount-root" — which is unstated and unknown. The `-core` will need a generalized hypothesis at proof time, and whether the general mid-state bound even HOLDS is open. |
| 5 | `depth-compositional` | Depth-Bound.agda:153 | FALSITY — **probeable** | Its own census (source comment, point 4) says the induction needs `storeNestMax` at the EVOLVED state dominated by the entry bound — an unproven strengthening. If an evolved state can escape it, the statement is false. Both sides compute: probe it. |
| 6 | `opIterD≤sizeCount-root-core` | Caps-Bridge.agda:1090 | FALSITY — **probeable** | "The genuinely new mathematics"; the direction is novel (an UPPER bound on a budget everything else lower-bounds). Nobody has checked the numbers. Both sides compute at concrete `e`/`ins`: probe before grinding. |
| 7 | `init-capsOK?-base-core` | Caps-Bridge.agda:978 | FALSITY — **probeable** | The unverified premise under the depth-capped RULING (below): `stBounded?` and the `widLive` sweep at the small caps c₀ are INFERRED from what the fields mean, never checked. `capsOK?` is a boolean on concrete states — decidable outright. If it fails, c₀ grows and the #17 arithmetic re-runs. This is task #19. |
| 8 | `init-capsOK?` | Caps-Bridge.agda:918 | FALSITY — **probeable** | Same fact at the blown-up caps; should eventually be DERIVED from #7 via `capsOK?-mono` + `cSize≤frameBlowup`, retiring one of the two. Probe alongside #7. |
| 9 | `thruOuter-face-core` (P4) | Caps-Face.agda:6317 | SHAPE | Its own header doubts itself: receipt "(a) is the SECOND number … `subscribeE-caps` bounds its j′ by nothing whatever" and "(a) may not fit `fCharge` as stated." Statement-level work before grind. |
| 10 | `innerFinish-concat-face-core` (P3) | Caps-Face.agda:6253 | DIFFICULTY | The one from-inner clause that is not j′=0 (concatDrain's width sum). Expect grind, not design; the toolkit hypotheses are the right kit. |
| 11 | `dry-tick-core` | Caps-Bridge.agda:439 | DIFFICULTY | Given `cascadeGo-wet` (its first hypothesis) it is latch/finish bookkeeping plus the Deliveries counts. Nearly all its risk is inherited from #2, not its own. |
| 12 | `three-size≤capsH-core` | Caps-Bridge.agda:1021 | DIFFICULTY, low | The `poolCount` lower-bound chain is already rehearsed step-by-step in `agda/probe/Pool-Lower-Probe.agda`. Upgrade to proof when convenient. |

### Tier 2 — the main proof branch (Verify-Well-Formed, 21; plus batch-online)

| # | Postulate | Where | Class | Why it ranks here |
|---|-----------|-------|-------|-------------------|
| 1 | `burst-done-false` | VWF:1109 | **FALSITY — own SUSPECT marker** | The repo's single most-likely-false statement: its own comment says "true only at the right walk position, not from BurstInv alone." The cheapest high-value refutation target anywhere in the ledger — one adversarial BurstInv inhabitant kills it, and the fix (a walk-position hypothesis) is known in advance. |
| 2 | `root-done-plumbed` | VWF:1423 | FALSITY, blocked on merge-cert | The merge-coherence content. Candidate invariant #1 was machine-refuted by THREE counterexamples (VWF:3410–3429); route #2 is marked STRUCTURALLY DEAD (:3498); the corrected statement is OPEN (:3459–3497). Stated at the settled root exit — the one case the refutations do not touch — so plausibly true, but nobody knows the invariant that proves it. |
| 3 | `root-caches` | VWF:1438 | FALSITY, blocked on merge-cert | Same content, same blocker, same settled-state plausibility. Discharges together with #2. |
| 4–7 | `subscribeE-{merge,concat,switch,exhaust}All-wf` | VWF:1235–1268 | SHAPE | The four wrap-clause receipts, written against a merge-cert whose correct statement is UNKNOWN. Until it exists, the `valsLast?`/BurstInv conjuncts through a merge are conjecture — the statements may need hypotheses nobody has named yet. |
| 8 | `stepFrame-wf-outer` | VWF:4046 | SHAPE | The thru-outer wrap; same cluster, plus it inherits the FoldOut question. |
| 9 | `dispatchShare-wf` | VWF:4058 | **SHAPE — known too weak** | Its conclusion is only `Σ S′ → runProtocol … ≡ just S′` — no FoldInv/FoldOut carried out, so it CANNOT feed `mid-step` as stated (old W7 finding, still true). A guaranteed restatement, cascading into the stepFrame family. Wired, consumed, and wrong-shaped. |
| 10 | `mid-step-core` | VWF:4907 | FALSITY, moderate | Rests on `FoldOut` — a genuinely new 6-field invariant validated at exactly ONE clause (`foldPath-root-out`). If FoldOut's shape is wrong, this and the root proof both move. |
| 11 | `batch-online` | Batch-Theorems:12 | **SHAPE — self-flagged imprecise** | Its own `nb:` says to "state precisely as pre-flush" — as literally written (comparing full outputs, flushed open tail included) it is likely FALSE. Off the critical path, trivially probeable, and the restatement is already prescribed by its own comment. |
| 12 | `map-valsLast-push`, `scan-valsLast-push` | VWF:1124/1154 | SHAPE | Each papers over a recorded "REAL SHAPE MISMATCH" (the proven sub-lemmas don't return `valsLast?`). Plausible truths standing in for a missing conjunct in the proven work. |
| 13 | `map-nodry-push`, `scan-nodry-push`, `scan-nodeP`, `scan-binv-adapt` | VWF:1115–1174 | DIFFICULTY — probeable | Computational propagation/survival facts about specific subscribeE clauses; `scan-binv-adapt`'s comment even says "provable inline as record { … }". Concrete instances compute. |
| 14 | `subscribeE-input-wf-core`, `subscribeE-defer-wf`, `subscribeE-takeᵉ-wf-core` | VWF:1195/1218/1294 | DIFFICULTY | Per-clause receipts of the pattern already PROVEN three times over (map/scan/take clause proofs exist). Low statement risk. |
| 15 | `cut-owed` | VWF:4017 | DIFFICULTY, low | Self-contained Owed-table algebra, independent of every blocker. The easiest real proof in the branch. |
| 16 | `stepFrame-wf-inner-concat` | VWF:4037 | DIFFICULTY | concat's drain grows the registry; re-establish FoldInv. Independent of merge-cert. |

### Tier 3 — all the other theorems (~25)

Three buckets, in risk order:

**(a) VACUOUS BY ABSTRACTION — asserts ~nothing today; risk is reporting, not
falsity.** `Rx.Time-Theorems` entire: 9 abstract helpers (`Node`, `NodeSt`,
`Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`, `retime`) under
`locality` / `non-interference` / `timing-invariance` — each claim is
satisfiable by trivial instantiation (`retime ρ = id` makes timing-invariance
free), so as stated they are close to vacuous, exactly as Main's CAUTION
records. Same class: `causality` (its `truncateIn`/`emittedBefore` are
postulated functions; `emittedBefore k = []` satisfies it), `μ-guarded` (its
type is IDENTICAL to `μ-unfold`'s — a duplicate asserting nothing new), and
`defer-shift` (`⊤` on purpose; the honest-gap exemption). **De-risking these
means DEFINING the abstractions — claim-authoring work that needs Anthony, not
a grind.** Until then they are parked, with the Main caution as the label.
NOTE for ledger readers: the wiring report shows `NodeSt`/`cascade` at
Rx/Evaluator.agda lines — that is the checker's known same-name merge
(Evaluator's REAL definitions colliding with Time-Theorems' abstractions), not
a postulate inside the evaluator.

**(b) REAL AND PROBEABLE — genuine claims about computable functions, zero
probe coverage today.** The 10 `readme-*` theorems (the spec's public
personality; 7 are closed-form equalities on concrete programs — bug-cache
shaped), `μ-unfold` (strict `≡` across a μ-unfolding — MODERATE suspicion,
since defer-shift's own comment records that unfolding re-mints ids;
if ids differ the strict equality dies), `fuel-coherent` (prefix property),
`id-inheritance` (ids ⊆ horizon — real-typed now, testable). A refutation of
`μ-unfold` or a readme claim would be a SPEC-level finding: surface to Anthony,
do not patch.

**(c) FFI, zero proof risk.** `_>>=_`, `getContents`, `putStr` (CLI/IO),
`randFold`, `natMod` (QuickCheck) — GHC bindings for the two extracted
binaries, off every proof path. Carried, not counted.

### Where the risk actually is — the concentration facts

1. **Two design questions carry most of tiers 1–2:** THE ANCHOR PROBLEM
   (tier 1 ranks 1–3, 11) and MERGE-CERT (tier 2 ranks 2–8). Solving either
   moves a whole block; grinding around them moves nothing.
2. **Three postulates are suspected wrong by their own comments:**
   `burst-done-false` (SUSPECT: false as stated), `batch-online` (imprecise as
   stated), `dispatchShare-wf` (too weak as stated). Cheapest wins in the repo.
3. **A third of the ledger is machine-probeable today** and none of it has
   ever been probed. The QuickCheck/oracle harness only ever compared impl to
   spec; every postulate ABOUT the spec/evaluator is untested territory.

---

## THE ROADMAP — reduce uncertainty first, grind last

Ordered so that each phase's findings can still cheaply change the phases after
it. Do not reorder: grinding before probing risks proving towers over false
ground, which is this campaign's most expensive possible mistake.

### Phase 0 — THE FALSIFICATION SWEEP (workers, parallel, days not weeks)

Build the **postulate probe battery**: `agda/probe/Battery-*.agda` modules of
bug-cache-style `refl` checks instantiating each probeable postulate at
concrete programs (reuse the canonical/README programs; adversarial shapes
where a comment names one). Every probe ends in exactly one of two states —
a refutation (STOP-grade for that statement: record, restate, re-rank) or a
confidence receipt (note it in the postulate's header: `-- PROBED 2026-08-…`).

- **0a. `burst-done-false` refutation attempt** — the SUSPECT. Aim the probe at
  a wrong-walk-position BurstInv inhabitant, per its own comment.
- **0b. `batch-online` restatement + probe** — apply its own `nb:` (pre-flush
  prefix), then probe the corrected form.
- **0c. Caps arithmetic battery** — `init-capsOK?-base` (+ `init-capsOK?`;
  this IS task #19), `opIterD≤sizeCount-root`, `depth-compositional`,
  `three-size≤capsH`. All decidable on concrete `e`/`ins`; sweep the canonical
  program set, nested/adversarial shapes included.
- **0d. Evaluator-law battery** — `μ-unfold` (ids across the unfold — the
  suspicious one), `fuel-coherent`, `id-inheritance`.
- **0e. README battery** — the 10 `readme-*` claims at concrete instances.
  Spec-level: a failure here is a STOP, not a fix.
- **0f. VWF propagation battery** — `map/scan-nodry-push`, `scan-nodeP`,
  the two `valsLast-push` mismatch postulates.

### Phase 1 — THE TWO DESIGN QUESTIONS (design session; the real risk mass)

- **1a. MERGE-CERT first — it is the cheaper experiment and already scoped:**
  probe the corrected one-directional, liveness-aware statement
  (VWF:3483–3486) against the three adversarial shapes that killed candidate
  one (multi-source inner; inner-completes-before-outer; cut-through on an
  inner), in the style of `agda/probe/Cut-Caches-Probe.agda`. Survives → state
  it as the postulate the four `*All` wraps and the two root-exit postulates
  are rewritten over. Dies → this branch needs a design ruling before tier 2's
  top eight can move at all.
- **1b. THE ANCHOR PROBLEM (below, unchanged and still the campaign's center):**
  state the reachability-sourced dry family (`chainStep-dry` /
  `foldPath-dry` / `subscribeInner-dry`) that sources Ŝ/R̂/F from reachability —
  the ONE route the two absurd proofs leave alive. Deliverable is a STATEMENT
  that typechecks against the walk's actual call sites, probed on
  Frame-Work-Probe's shapes — or a third refutation, which is STOP-grade:
  it would mean tier 1's top three postulates have no surviving proof route.

### Phase 2 — STATEMENT REPAIRS (design session; before any grind above them)

Every known-wrong-shape statement gets restated BEFORE work lands on top of it:

- `dispatchShare-wf` → FoldOut-carrying conclusion (cascades into the
  stepFrame family signatures — change the signatures first, per the law).
- `sub-charge-capsOK-lift-core` → general mid-state `opIterD` hypothesis
  (or a recorded ruling for why root-only suffices at its one consumer).
- `burst-done-false` → walk-position hypothesis (shape known; do it even if
  Phase 0a somehow fails to refute).
- P4 `thruOuter-face-core` → resolve the "(a) may not fit fCharge" doubt at
  the statement level.
- Phase 0's refutation fallout, whatever it is.

### Phase 3 — THE GRIND (workers; only over probed or repaired ground)

Conditional-risk order: cheapest-and-safest first, anchor-dependent mass last.

1. `cut-owed`, `three-size≤capsH-core`, `scan-binv-adapt`, and the Phase-0f
   propagation lemmas — no blockers, low statement risk.
2. The per-clause WF receipts (`input-core`, `defer`, `takeᵉ-core`) — pattern
   proven three times already.
3. `stepFrame-wf-inner-concat`, P3 — real grind, no design blocker.
4. `init-capsOK?-base-core` + `opIterD≤sizeCount-root-core` — after 0c
   confirms the numbers.
5. The merge-cert cluster — after 1a lands its statement.
6. The anchor cluster (`subscribeE-walk-core` → `subscribeE-wet-core` →
   `cascadeGo-wet-core` → `dry-tick-core`, then `mid-step-core`'s FoldOut
   threading) — after 1b. This is the endgame, and it stays LAST because it
   is where a design failure costs the most reground work.

**Tier 3 policy:** bucket (b) is Phase 0e/0d worker fodder. Bucket (a) is
parked until Anthony authors the abstractions' definitions — flag, don't grind.
Bucket (c) is permanent trusted FFI.

---

## THE ANCHOR PROBLEM — the campaign's one central open question

`hop-edge` (and `connect-edge`) reset their demand to an anchor `Ŝ`, and
discharging one requires `sizeᵛ o ≤ Ŝ` for a value `o` arising **mid-walk /
mid-cascade**. There are exactly two ways to source `Ŝ`, and **the repo has
already proven both impossible**:

- **A fixed, entry-computable cap** — refuted by `caps-frame-boundary-absurd`
  (`Caps-Face.agda`, proven): for any cap `C ≥ 1`, `sizeStep C C ≤ C → ⊥`.
  One more frame-crossing always escapes the cap, *uniformly in the cap*.
- **A ledger/walk-position-tied ceiling** — refuted by
  `round3b-ledger-reset-absurd` (`Measures.agda`, proven): tying the anchor
  to the walk's own growing ceiling is circular.

The one surviving option is the repo's own stated plan — source `Ŝ`, `R̂`, `F`
from **reachability** (`Measures.agda:6199-6203`) — and it **is not established
anywhere.** No `chainStep-dry`/`foldPath-dry`/`subscribeInner-dry` family
exists, and every proven `-wet` delivery lemma is size-axis only — none carries
a `Gas` hypothesis or concludes `hasDry ≡ false`.

**This unifies what looked like separate problems.** GAP 4(b), `dry-tick`, and
P1's subscribe side are the SAME question on different axes: *can a mid-walk
value's size be bounded from reachability, rather than from a fixed cap or from
the ledger?* Answer it and tier 1's top block falls together; leave it and none
of it moves.

**Σ-receipt caution, standing:** `walk-hyps-round3b` (Measures) is a proven
receipt showing the edge constraints are jointly satisfiable at ONE entry
point. Per CLAUDE.md's Σ-receipt rule that is not an end-to-end induction, and
its own comment says so. Do not read it as "the walk is basically done."

## MERGE-CERT — the well-formedness branch's own anchor-shaped blocker

Blocks the `*All` wrap receipts, `root-done-plumbed`, `root-caches`,
`stepFrame-wf-outer`. Candidate invariant #1
(`merge-st k at nid ⇒ k ≡ countRegsUnder nid registry`) is **machine-refuted by
three independent counterexamples** (VWF:3410–3429); the "derive from
`Inv.done-plumbed`" route is **STRUCTURALLY DEAD** (VWF:3498 — its premise is
vacuous exactly when the obligation is needed). The corrected route — a
one-directional, liveness-aware statement — is identified but OPEN
(VWF:3459–3497); its exact statement is the remaining design point, and
Phase 1a is its experiment.

**FoldOut, the second statement-level debt in this branch:** a genuinely new
invariant (what a PARTIAL chain fold preserves of the live↔registry shadow),
stated as a 6-field record and validated at exactly one clause
(`foldPath-root-out`). `mid-step-core` consumes it; `foldPath-wf`'s signature
does not yet thread it, and restating W5/W6/W7 over it is Phase 2 work.

---

## Standing rulings (each one prevents a specific dead route — keep)

**RULING: `depth-capped` must be spent at the SMALL caps `c₀`
(`baseCaps e ins`), never at `capsAt e ins 0`.** The blown-up caps' `cSize` is
`sizeStep` iterated `sizeCount`-many times, and closing the gap to `capsH`
demands a cross-`M` growth-rate argument that exists nowhere in the repo;
`capsAt-tower` points the wrong way. At the root, three of `capsOK?`'s five
conjuncts are vacuous on the empty initial state and the two live ones are
syntax-ceiling-shaped — which is what `c₀`'s fields ARE. Full reasoning in
`Caps-Bridge.agda` above `init-capsOK?-base-core`; arithmetic chain rehearsed
in `agda/probe/Pool-Lower-Probe.agda`. **The unverified premise — the two live
conjuncts actually holding at c₀ — is Phase 0c / task #19.** If either fails,
c₀ grows and the arithmetic re-runs at whatever it grows to.

**Depth obligation must be conditioned.** Unconditional `depthE ≤ capsBase` is
FALSE (machine-refuted, `agda/probe/Depth-Blowup-Probe.agda`), and
unconditional `depthE ≤ capsH` is indefensible against adversarial stored
state. The honest statement conditions on `capsOK?` — already in scope at every
consumer.

**Fold-threading (standing).** P2 does not decompose into a per-chainStep
contract at fixed bounds (`caps-frame-boundary-absurd`). The honest
decomposition threads per-cascade growth, which the caps face's `j` index does
and any eventual `chainStep-wet` must mirror.

**Sync-μ escape: CLOSED BY TYPING.** `deferᵉ` is the sole gate moving `Δᵍ`
into `Δ`, so a μ's self-reference costs a tick; synchronous self-subscription
is not writable. Recorded at Wet.agda:4186 and Caps-Face:6087. Do not
re-refute this.

**THE GAS AXIS IS PROVEN AND WIRED.** Exactly three decrement edges (μ unfold,
share connect, inner-value subscribe — enumerated against every clause of the
subscribe clique), all three packaged and proven in Wet ("THE THREE GAS EDGES,
PACKAGED"), now consumed as `subscribeE-wet-core` hypotheses. Zero corners are
vacuous, not holes. What is NOT proven is SPENDING the edges mid-walk — that is
the anchor problem, not a gas gap.

**Ψ-only faces cross the ledger gap today** (`fn-tick`'s template): a
conclusion that does not read the numeric bound can reuse `cascadeGo-walk`
directly. Worth trying face-by-face before assuming the anchor blocks one.

**MAIN IS THE TOP-LINE PROOF.** Whatever Main imports sticks around; Main
names individual definitions, never a bare `open import`; Main is never touched
without Anthony's explicit approval. `make wiring` roots its exempt set there.

**The standing lesson.** This campaign's dominant failure mode is not wrong
proofs — it is not knowing what it already has. Grep for a fact before planning
its proof; grep for a lemma's consumers before believing any status written
here — including in this file.

## Debts on next touch (cheap, fold into a pass that dirties the file anyway)

- **Prose that outlived its code:** eight comment references to `measureE` and
  two to `rank-lt-pow` survive in Keeps-Ring (:149,179,267,332,404),
  Wet (:2211,:2273), Rx/Slots (:32), Rx/Hop-Depth (:4), Measures (:1866).
  Keep the reasoning, mark the names retired. Not worth a solo ~45-min rebuild.
- **Two lying comments:** Caps-Face:4175 credits a recursion to Deliveries § D
  lemmas the live code never calls; Subscribe-Face's header lists
  `chainStep-caps` as a caller into the clique when nothing calls it.
- **`dry-tick-core`'s header** still claims independence from the caps/INV?
  bridging problem — WRONG (the anchor problem is exactly where it sits); fix
  when next editing Caps-Bridge.

## RECOVERY SHA: the retired multiset measure — `11a34db`

`git show 11a34db` restores the Dershowitz–Manna apparatus (524 lines: `_≺ᵛ_`,
`≺ᵛ-wf`, `rank`, `shells`, descent lemmas), deleted under the freeze's
source-retires-it exemption. **The scenario that brings it back:** the ANCHOR
PROBLEM resolution wants a well-founded multiset order — the classical
instrument for exactly that descent class. Restore from the SHA rather than
re-deriving `≺ᵛ-wf`.

## WRITING AN ASSEMBLY — the postulate-to-assembly conversion (the method)

For a parent postulate `P` with proven pieces `o₁…oₖ`, `P`'s type `T` is
unchanged; it becomes

```agda
postulate P-core : <type of o₁> → … → <type of oₖ> → T
P : T
P = P-core (λ {a} {b} → o₁ {a} {b}) … oₖ
```

`P-core` is equivalent to `P` exactly when every hypothesis is a PROOF. A
*function*-valued piece must be wired by its DEFINING EQUATION instead (`ΩAt`
in `.Measures` is the worked example) — passing the function type quantifies
over every inhabitant and makes the core strictly STRONGER.

Four rules, each of which otherwise costs a full build to rediscover:

1. **EXTRACT hypothesis types from source; never retype them.**
   `scripts/check-wiring.py`'s `signature_text` does it exactly.
2. **Pass every lemma ETA-EXPANDED with explicit implicits** —
   `(λ {n} {Γ} → f {n} {Γ})`. When a statement reduces away its own implicit
   (`share-live-novals` computes on a literal list), bare arguments give
   `Unsolved metas`; the eta form always works.
3. **Copied signatures drag in VOCABULARY the parent module does not import.**
   Collect the names in one pass; Agda stops at the FIRST scope error.
4. **ORDERING: a postulate cannot reference a definition below it.** `-core`
   sits where the postulate was; the definition sits after the last piece it
   consumes. `make wiring` section B3 reports violations — do not learn this
   from a failed typecheck.

## Build-cost rules (unchanged)

- Iterate in `agda/probe/` with minimal imports (~6 s loops against cached
  interfaces); land probe-green bodies in batches.
- At most TWO heavyweight checks at once (Subscribe-Face/Wet class, multi-GB).
- Never let two workers edit the same module.
- Detach long builds with `EXIT=$?` logs; pin the working directory in every
  build command; verify the run actually ran (`Checking` lines, not just exit
  codes).

## Active tasks → phases

Live list is the session task tool; this maps the standing ones onto the
roadmap: **#19** (capsOK? at c₀) IS Phase 0c's core probe. **#17**
(opIterD≤sizeCount-root + sub-charge-capsOK-lift) is Phase 0c + Phase 2's
generalization repair, THEN Phase 3.4. **#4** (P3+P4) is Phase 2 (P4's
statement doubt) + Phase 3.3 (P3's grind).
