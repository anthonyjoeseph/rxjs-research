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
| 7 | `init-capsOK?-base-core` | Caps-Bridge.agda:978 | FALSITY — **probeable, STILL UNCOVERED** | The unverified premise under the depth-capped RULING (below): `stBounded?` and the `widLive` sweep at c₀ are INFERRED from what the fields mean, never checked. Task #19. **2026-08-06: first probe pass FAILED TO COVER IT.** `capsOK?` (Caps-Face:297) is five conjuncts; at `st-init` the registry and nodes are empty so (2) `regsSz?`, (4) `widNode`, (5) `length ≤ᵇ cReg` are true by `all _ []`. Those are the known-vacuous three. The probe's two programs left the two LIVE conjuncts vacuous too — `emptyᵉ` has empty `live`, and the `input` row had `pending = []` so `widLive` returned true vacuously. **A non-vacuous row needs slots carrying real, WIDE scripted values**, since `baseCaps` is a syntax-derived ceiling and the inputs are where it can be outrun. |
| 8 | `init-capsOK?` | Caps-Bridge.agda:918 | **BLOCKED — cause identified** | Not probeable: `capsAt e ins id` unfolds through `sizeCount`, which is `abstract` (Caps.agda:369), so it never reduces to a numeral. **The derivation route is now fully scoped**: `capsOK?-mono` (Caps-Face:365, proven) lifts #7 to #8 given `baseCaps ⊑ᶜ capsAt`, which needs three sub-lemmas — `capsAt-base-size` and `capsAt-base-wid` EXIST, and the sole missing one is `capsAt-base-reg : suc (sizeᵉ e + slotsSize ins) ≤ Caps.cReg (capsAt e ins id)`. State that and this postulate retires. |
| 9 | `thruOuter-face-core` (P4) | Caps-Face.agda:6317 | SHAPE | Its own header doubts itself: receipt "(a) is the SECOND number … `subscribeE-caps` bounds its j′ by nothing whatever" and "(a) may not fit `fCharge` as stated." Statement-level work before grind. |
| 10 | `innerFinish-concat-face-core` (P3) | Caps-Face.agda:6253 | DIFFICULTY | The one from-inner clause that is not j′=0 (concatDrain's width sum). Expect grind, not design; the toolkit hypotheses are the right kit. |
| 11 | `dry-tick-core` | Caps-Bridge.agda:439 | DIFFICULTY | Given `cascadeGo-wet` (its first hypothesis) it is latch/finish bookkeeping plus the Deliveries counts. Nearly all its risk is inherited from #2, not its own. |
| 12 | `three-size≤capsH-core` | Caps-Bridge.agda:1021 | DIFFICULTY, low — **likely PROMOTABLE** | The `poolCount` chain is rehearsed in `agda/probe/Pool-Lower-Probe.agda`, and 2026-08-06's probe found `three-size-le-blowH` (:77) unifies with the goal DIRECTLY at concrete instances, with the reduction `capsH e ins 0 = capsHgo (capsBase e ins) 0 = blowH (capsBase e ins)` definitional (neither is `abstract`). So this likely wants PROMOTING, not probing: move that lemma into `src` and discharge. Its side condition `2 ≤ 3 + X + suc E` looks free. |

### Tier 2 — the main proof branch (Verify-Well-Formed, 21; plus batch-online)

| # | Postulate | Where | Class | Why it ranks here |
|---|-----------|-------|-------|-------------------|
| 1 | `burst-done-false` | VWF:1109 | **REFUTED 2026-08-06 — FALSE** | **Machine-refuted**, `agda/probe/Battery-Burst-Done.agda` (`burst-done-false-absurd`, a proven `→ ⊥`). `BurstInv`'s four fields never mention `done`, so `S = record { live = [] ; horizon = 0 ; current = nothing ; done = true }` inhabits it at `st-init`/`sched-init` and forces `true ≡ false`. Structural, hence shape-invariant over all `n`/`Γ`/`e`. **The source already knew**: VWF:876–882 says `done ≡ false` is a subscribe-TIME fact and "BurstInv cannot carry it; it must come from the walk order" — the postulate asserted what its own neighbour calls impossible. Repair is a SIGNATURE change, not a restatement — see Phase 2. |
| 2 | `root-done-plumbed` | VWF:1423 | FALSITY, blocked on merge-cert | The merge-coherence content. Candidate invariant #1 was machine-refuted by THREE counterexamples (VWF:3771–3800); route #2 is marked STRUCTURALLY DEAD (:3859); the corrected statement is OPEN (:3820–3858). Stated at the settled root exit — the one case the refutations do not touch — so plausibly true, but nobody knows the invariant that proves it. |
| 3 | `root-caches` | VWF:1438 | FALSITY, blocked on merge-cert | Same content, same blocker, same settled-state plausibility. Discharges together with #2. |
| 4–7 | `subscribeE-{merge,concat,switch,exhaust}All-wf` | VWF:1235–1268 | SHAPE | The four wrap-clause receipts, written against a merge-cert whose correct statement is UNKNOWN. Until it exists, the `valsLast?`/BurstInv conjuncts through a merge are conjecture — the statements may need hypotheses nobody has named yet. |
| 8 | `stepFrame-wf-outer` | VWF:4046 | SHAPE | The thru-outer wrap; same cluster, plus it inherits the FoldOut question. |
| 9 | `dispatchShare-wf` | VWF:4058 | **SHAPE — known too weak** | Its conclusion is only `Σ S′ → runProtocol … ≡ just S′` — no FoldInv/FoldOut carried out, so it CANNOT feed `mid-step` as stated (old W7 finding, still true). A guaranteed restatement, cascading into the stepFrame family. Wired, consumed, and wrong-shaped. |
| 10 | `mid-step-core` | VWF:4907 | FALSITY, moderate | Rests on `FoldOut` — a genuinely new 6-field invariant validated at exactly ONE clause (`foldPath-root-out`). If FoldOut's shape is wrong, this and the root proof both move. |
| 11 | `batch-online` | Batch-Theorems:12 | **REFUTED 2026-08-06 — FALSE** | Machine-refuted, `agda/probe/Battery-Batch-Online.agda` (`batch-online-refuted`, a proven `¬`). `impl-batchSimultaneous [em1,em2]` flushes an OPEN batch to `value [1]`, while on `[em1,em2,em3]` that batch closes as `value [1,2]` — the first elements differ, so no prefix relation holds. Exactly the failure its own `nb:` predicted. **Restatement drafted, NEEDS ANTHONY'S RULING** — see below. |
| 12 | `map-valsLast-push`, `scan-valsLast-push` | VWF:1124/1154 | SHAPE | Each papers over a recorded "REAL SHAPE MISMATCH" (the proven sub-lemmas don't return `valsLast?`). Plausible truths standing in for a missing conjunct in the proven work. |
| 13 | `map-nodry-push`, `scan-nodry-push`, `scan-nodeP` | VWF:1115–1141 | DIFFICULTY — **PROBED 2026-08-06** | `agda/probe/Battery-VWF-Prop.agda`: all three hold at concrete instances, non-vacuously (premise AND conclusion both live, not an empty-premise pass). `scan-nodeP`'s mechanism is that `ofᵉ` ignores its path argument and returns state unchanged, so the installed node survives at its seed. Coverage is ONE program each — thin, but the class is low-risk. |
| — | **`scan-binv-adapt`** | VWF:1168 | **DISCHARGEABLE — proof in hand** | Its comment was right: the proof is `record { live-matches = BurstInv.live-matches binv ; … }`, four fields passed straight through, verified in `agda/probe/Battery-VWF-Prop.agda`. It works because `installNode` touches only `nodes` and `mintNode` only `nextNode`, so `registry` and `live` are unchanged and record eta closes it with no rewrites. **Land it BUNDLED with the `burst-done-false` repair** — both edit VWF, and one ~40-min gate should carry both. |
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

**THREE WAYS A PROBE LIES GREEN — all three observed on 2026-08-06's first
sweep, all three in the direction of false comfort. Check every probe report
against them before believing a PROBED-GREEN.**

1. **VACUOUS ROWS.** The rows pass because the quantifier is empty, not because
   the bound holds — `all _ [] = true`, `0 ≤ᵇ _`, a sweep over an empty list.
   `capsOK?` at `st-init` has THREE of five conjuncts vacuous by construction,
   so a green row there is evidence about nothing unless the shape was built to
   make the LIVE conjuncts do work. **Name the covered conjuncts, not the
   covered programs.**
2. **HAND-BUILT STATES.** A state written as `record (st-init e) { … }` is not
   a state the evaluator can reach, and a predicate checked only against states
   its own author invented is confirmation with the inputs chosen by the thing
   under test. **Reach states by RUNNING** (`evaluate` / subscribe / cascade);
   one reached row outweighs a table of constructed ones. Corollary: a
   constructed state where the predicate FAILS is not a "non-vacuity witness"
   to be noted and passed over — it is a refutation candidate, and its
   reachability is the finding.
3. **READING AN ASSEMBLY BACKWARDS.** `P = P-core o₁ … oₖ` proves **P from the
   postulated core**; it does NOT prove the core. The `oᵢ` are the core's
   HYPOTHESES. Mistaking this makes every `-core` in the repo look discharged —
   and every remaining tier-1 gap is a `-core`.

### Phase 1 — THE TWO DESIGN QUESTIONS (design session; the real risk mass)

- **1a. MERGE-CERT first — it is the cheaper experiment and already scoped:**
  probe the corrected one-directional, liveness-aware statement
  (VWF:3844–3847) against the three adversarial shapes that killed candidate
  one (multi-source inner; inner-completes-before-outer; lingering regs after
  `finish mergeᵒ`), in the style of `agda/probe/Cut-Caches-Probe.agda`. Survives → state
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

- **`batch-online` → pre-flush form. NEEDS ANTHONY'S RULING BEFORE LANDING.**
  REFUTED 2026-08-06 (above). The restatement is prescribed by the postulate's
  own `nb:` and is drafted + concretely checked in
  `agda/probe/Battery-Batch-Online.agda`: compare `foldBatch-no-flush` (the same
  fold with `[] ↦ []` instead of `[] ↦ flushBatch st`) against the full
  `impl-batchSimultaneous` of the extension. **Why it is not landed under the
  standing autonomy grant:** `batch-online` is one of Main's named claims, so
  changing what it ASSERTS changes Main's claim set — while leaving Main.agda
  byte-identical. That is precisely the silent change Main's rule 3 exists to
  prevent, so it gets drafted and asked rather than assumed. Cost note: the edit
  is cheap (Batch-Theorems + Main recheck; The-Proof does not import it).
  Second point for the ruling: `foldBatch-no-flush` differs from `foldBatch`
  (Implementation:119) in ONE clause, so it is a near-duplicate — acceptable as
  the honest online projection, but worth a nod given the no-fat rule.
- `dispatchShare-wf` → FoldOut-carrying conclusion (cascades into the
  stepFrame family signatures — change the signatures first, per the law).
- `sub-charge-capsOK-lift-core` → general mid-state `opIterD` hypothesis
  (or a recorded ruling for why root-only suffices at its one consumer).
- **`burst-done-false` → DELETE IT; give `subscribeE-wf` the premise instead.**
  REFUTED 2026-08-06 (above), so this one is no longer optional. Two plausible
  cheap fixes are both FALSE and each costs a build to rediscover: the
  consumers do NOT already supply `done ≡ false` (they are the ofᵉ/emptyᵉ
  clauses, and the postulate exists precisely because they have nothing to hand
  `oneShotBurst-wf`'s `deq`), and `nodry` does NOT supply it (`hasDry ≡ false`
  is a different proposition — the dry-burst flag, not the completion latch).
  The repair: `subscribeE-wf` TAKES `ProtocolSt.done S ≡ false` and threads it.
  **Soundness rests on the SPINE ARGUMENT** — mapᵉ/scanᵉ/takeᵉ/deferᵉ/μᵉ each
  recurse into ONE child with `S` unchanged, and there is no binary static merge
  (VWF:3823), so `S` is untouched from walk entry to the single base burst. This
  matters because `oneShotBurst-run` LATCHES `done ≡ true`: if one walk could
  subscribe two bases in sequence, the threaded premise would itself be false.
  **CALLERS: ANSWERED — the repair is sound.** There is exactly ONE external
  caller, `subscribe-wf` (VWF:1457), and it passes `S = protocol-init` whose
  `done` field is literally `false` (Rx/Protocol.agda:75), so `refl` discharges
  the premise. Every other call site is internal recursion carrying `S`
  unchanged. **Rehearsed green** in `agda/probe/Battery-Done-Thread.agda`: all
  12 clauses with the amended signature, calling the REAL `oneShotBurst-wf`, so
  `deq` is checked against the actual lemma rather than a stub.
  **PATCH IS WRITTEN AND READY TO LAND — 13 hunks**, listed in that probe's
  header: 7 postulate signatures (`input-wf-core`, `defer-wf`, four `*All-wf`,
  `takeᵉ-wf-core` outer), 3 declared signatures (`input-wf`, `subscribeE-wf`,
  `takeᵉ-wf`), all 12 body clauses gain `deq`, `subscribe-wf` gains `refl`, and
  `burst-done-false` is deleted. The two pointfree definitions eta-expand
  unchanged; `takeᵉ-wf-core`'s INNER receipt does not change.
  **SCOPE CAVEAT, do not overstate the result:** the spine is verified only
  where recursion is VISIBLE CODE (mapᵉ/scanᵉ/takeᵉ/μᵉ + the two bases). The
  four `*All` clauses and `input`/`deferᵉ` delegate to postulates, so threading
  `deq` RELOCATES the obligation into them rather than proving it — and four are
  also blocked on merge-cert. Whoever proves an `*All` receipt must honour it.
  **HELD, not blocked:** landing it edits VWF, which invalidates the cached
  interface that concurrently-running probe workers import. Land it when no
  VWF-importing worker is live — the design session owns that gate (~40 min:
  VWF + The-Proof + Main; the V-B-S tower is upstream and stays cached).
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
three independent counterexamples** (VWF:3771–3800 — the outer's own
`thru-outer` threads nid; a multi-source inner registers two chains under one
`bump`; `finish mergeᵒ` decrements `k` without dropping the registry). The
"derive from `Inv.done-plumbed`" route is **STRUCTURALLY DEAD** (VWF:3859 — its
premise is vacuous exactly when the obligation is needed). The corrected route
is identified but OPEN (VWF:3820–3858): one-directional and liveness-aware,

```
merge-cert : (merge-st k _ at nid) ⇒ k ≡ 0 ⇒ no aliveThrough inner
             INSTANCE under nid survives
```

keyed on the `from-inner allNid ≡ nid` frame only (dodges refutation 1), deduped
by `inst` (dodges 2), and excluding spent registrations (dodges 3). **Do not
generalise it to a global node↔registry theory, and not onto `dispatchShare`**
(standing, VWF:3800).

**PHASE 1a RESULT (2026-08-06): SURVIVES THE DECISIVE TEST — STATE IT AND
UNBLOCK THE SIX.** `agda/probe/Battery-Merge-Cert.agda` gives merge-cert a
computable form (`mergeCertAt`, over `innerInstsP` + `aliveThroughᶠ`), and
`k ≡ 0 ⇒ none` **IS seed-provable** (`merge-st 0`, empty registry, by `refl`).

**THE MECHANISM — this is the real deliverable, more than any row.** The probe's
own Shape B (`merge-st 0` with a from-inner registration where `dying`,
`delivered`, `cancelled` are all empty) is a state where merge-cert is FALSE, so
the whole question was its REACHABILITY — exactly where refutation R3 pointed.
The cascade ordering answers it:

- `cascadeLatch` (Evaluator:1617–1622) fires FIRST, setting `dying = [arrSource a]`
  **before any chain is processed**;
- `cascadeGo` (Evaluator:1633–1641) adds `rid` to `delivered` **before** calling
  `chainStep`;
- so by the time `innerFinish` decrements `k` to 0, `src ∈ dying` AND
  `rid ∈ delivered` both hold, making `aliveThroughᶠ ≡ false` for the spent
  registration.

The "both" is load-bearing — `aliveThroughᶠ` stays TRUE if only one holds — and
the ordering supplies both. **Shape B is unreachable by this path.**

**REACHED rows** (not constructed — the earlier pass's rows were all hand-built
and are retained only as a behaviour table): `mergeAll(of([slot0]))`, slot 0 hot
at tick 1, driven through `subscribeE` → `cascadeLatch` → `cascadeGo`. Mid-cascade
(`merge-st 0`, reg still in the registry, `dying=[0]`, `delivered=[0]`) → `true`;
post-`cascadeFinish` → `true`. The mid-cascade row is the decisive one.

**STILL UNCOVERED, and worth stating before anyone over-reads this:** ONE program
was reached, the R1/R3 shape. **R2 (multi-source inner) is covered only at
hand-built states**, as are concat/switch/exhaust and nested `*All`. And the
ordering argument covers the *cascade* route to `k ≡ 0` — **the CUT route is
untested**, though R3's own note says registrations are dropped "only at
cut/cascadeFinish", so a take-cut reaching `k ≡ 0` is a distinct path.

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
