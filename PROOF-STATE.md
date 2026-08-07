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
decidable bound over COMPUTABLE functions (`evaluate`, `capsOK?`, `depthE`,
`storeNestMax`, `spec-batchSimultaneous` …), so concrete instances check by
`refl` exactly like the bug cache.

> **CORRECTION (2026-08-06) — THE CAPS AXIS IS NOT PROBEABLE, BY DESIGN.** This
> ledger's first draft listed `opIterD` and the caps arithmetic as probeable.
> That was WRONG. Four symbols on that axis sit in `abstract` blocks —
> `opIterD` (Evaluator:727), `blowH` (Evaluator:898), `sizeCount` (Caps:368),
> and `capsAt` through `sizeCount` — so they never reduce to numerals and no
> `refl` row can ever be written about them. The opacity is DELIBERATE and
> load-bearing: Caps.agda:365 says outright that "whether `.Wet` normalises or
> runs for an hour is decided by whether this symbol stays stuck." On top of
> that, `blowH m = 6 + m + 2 * poolCount (towerℕ m) m` is a tower-of-towers, so
> even unsealed it would not terminate.
>
> **The consequence for the roadmap: Phase 0 cannot reduce the caps axis's risk
> at all.** Those postulates are reachable only by PROOF. But there is a working
> substitute, and it is proven, not speculative: attack them **SYMBOLICALLY** —
> state the full type at symbolic `e`/`ins` in a probe and close it with a lemma
> that never reduces the sealed symbol. That is exactly how
> `three-size≤capsH-core` went from "unprobed postulate" to "one-line proof"
> (#12 below). **Symbolic rehearsal is the caps axis's Phase 0.**

QuickCheck/oracle only ever tested impl≡spec — before 2026-08-06 **no postulate
in this ledger had ever been probed**; closing that blind spot is Phase 0.

### Tier 1 — Verify-Budget-Sufficient (12 postulates)

| # | Postulate | Where | Class | Why it ranks here |
|---|-----------|-------|-------|-------------------|
| 1 | `subscribeE-walk-core` | Measures.agda:5750 | **FALSITY, critical** | The single riskiest statement in the repo. Nine conjuncts over the whole subscribeE mutual clique; its three predecessor statements were each MACHINE-REFUTED (`walk-hyps-absurd`, `hop-anchor-absurd`, `round3-old-ell-absurd`, `round3-anchor-indexed-absurd` — the base rate on this face is bad); its hypotheses (a one-entry-point Σ-receipt + arithmetic) contain NO induction; and it assumes exactly what THE ANCHOR PROBLEM (below) says is unestablished — that Ŝ/R̂/F can be sourced from reachability. Its own comment concedes: "Frame-Work-Probe is the evidence, not a proof." |
| 2 | `cascadeGo-wet-core` | Wet.agda:4499 | **FALSITY, critical** | P2's entire content (its only hypotheses are two stBounded? preservation facts). The anchor problem on the cascade axis. The naive per-chainStep decomposition is machine-refuted (`caps-frame-boundary-absurd`), so the fold-threaded statement's truth is genuinely open, not merely unproven. |
| 3 | `subscribeE-wet-core` | Wet.agda:4311 | FALSITY, conditional | Given the walk it is "the outer instantiation" — but the instantiation must manufacture the walk's G/ℓ/Ω entry data from `INV?` alone, and the INV?/capᴱ flavor conversion is unchecked. Moderate incremental risk over #1, with maximal blast radius (both branches of budget-sufficient). |
| 4 | `sub-charge-capsOK-lift-core` | Caps-Bridge.agda | **RE-SHAPED 2026-08-06 (`df2bb71`, `2d4b899`) — ruling made, general-id depth bound now the residual** | The recorded doubt was right and worse than recorded: the root-only hypothesis `opIterD≤capsH-root` could not support a conclusion quantified over arbitrary mid-run `b`/`id`/`sched`/`st`, and **TWO** counting facts were missing, not one — `nest b sl cs ≤ cSize (capsAt e sl id)` AND `suc (sizeᵉ b) ≤ cSize (capsAt e sl id)`. Both went through at the root only because `b = e` there. **RULING (rejected two cheaper options).** Narrowing the statement to root-only was rejected: its sole caller `burst-caps` does pass `id = 0`, but shaping a statement to today's only consumer means its shape is never checked against the general use Phase 3 needs. Indexing the bound at `suc id` — the tight consequence of `iterSize-doubles` — was rejected because it OVERSHOOTS: the consumer needs `capsOK?` at `capsAt e sl (suc id)` and the shift delivers `suc (suc id)`. So: hypothesis 5 replaced by `opIterD-dominated`, the two counting bounds threaded as explicit premises, discharged at `burst-caps` from `capsAt-base-size` + `nest≤`. **RESIDUAL, and it is a NEW design question:** the general-id depth bound. `depth-capped` + `three-size≤capsH` compose only at the ROOT; at general `id` the composition is FALSE, because `cSize (capsAt e sl id)` is tower-SIZED while `capsH e sl id` is the tower's INDEX (`capsAt-tower`), so `3 · cSize ≤ capsH` is absurd there. The root chain is wired as `depth-bound-root`; the general chain needs a different mechanism (likely `sizeCount` monotonicity, not the `capsH` route). |
| 5 | `depth-compositional` | Depth-Bound.agda:153 | **PROBED-GREEN 2026-08-06, evolved states included** | Its census (source comment, point 4) needs `storeNestMax` at the EVOLVED state dominated by the entry bound. **That direction was actually tested**, not dodged: `Depth-Compositional-Probe` drains N real cascades through the evaluator (k ≤ 4, N ≤ 10) and reads `depthE` off the extracted scan accumulator — evolved states, all rows hold. `agda/probe/Battery-Depth-Iter.agda` adds two things: the `switch-st`/`exhaust-st` branch of `depthAll`, which **no prior depth probe had ever exercised** (4 programs, green), and the preservation step `storeNestMax(post-subscribeE) ≤ sizeᵉ e + storeNestMax(pre)` — census point 4's exact inductive step — confirmed at N=1. Thin at N=1, but this is the one tier-1 axis where probing works, and it held. |
| 6 | `opIterD-budget-core` (was `opIterD-budget`, was `opIterD≤sizeCount-root-core`) | Op-Dominance.agda | **REFUTED AND REPAIRED 2026-08-06 (`7a82c6c`, `7e077e2`, `df2bb71`)** | **The statement was FALSE.** Machine-refuted in `probe/OpIterD-Budget-Probe.agda` §1 (`opIterD-budget-R0-false`, a proven `→ ⊥`): at `R = 0` the registry walk is empty (`regAt S 0 J = 0 * suc (J * S) = 0`), so `cDel (caps S W 0) d = 0` and the RHS collapses to `lvls S W d 0 0 = 0` — while the LHS is a `dLvl` application and `2≤dLvl` holds unconditionally. The claim read `2 ≤ 0`. The missing hypothesis is `1 ≤ R`, now carried by both `opIterD-budget-core` and `opIterD-dominated`, and **the refutation is recorded in the postulate's own header so the weaker form cannot be re-derived by accident.** Discharge cost nothing: `1≤capsAt-reg` already existed (`Caps.agda:929`). Since converted to a `-core` over the SEVEN expression-level lemmas (`entry-to-index`, `nest≤`, `residAt-connected`, `share-step-resid`, `mu-1≤k`, `mu-step-le`, `k-raise`) — the kit its own header had always named as the consumer, orphaned when the root chain was deleted and rewired here rather than thrown away. **Still open, and still the genuinely new mathematics:** the residual-budget induction on `m` (mutual with `sLvlD`'s k-descent). It cannot be probed into confidence — `widAt 2 1 10` is a ten-story tower, so concrete evaluation is infeasible. The route step it rests on (`fIterD-lvls`, ‹bound in n› = n) IS proven. |
| 7 | `init-capsOK?-base-core` | Caps-Bridge.agda:978 | **PROBED + STRUCTURALLY ARGUED 2026-08-06 — risk sharply down; task #19 answered** | `capsOK?` (Caps-Face:297) is five conjuncts; at `st-init` the registry and nodes are empty, so (2) `regsSz?`, (4) `widNode`, (5) `length ≤ᵇ cReg` pass by `all _ []` — the known-vacuous three. The first probe pass left the two LIVE conjuncts vacuous as well (empty `live`; `pending = []`), which is why it did not count. **The second pass covers them non-vacuously** (`agda/probe/Battery-Caps-Init.agda`, programs C and D: one and three pending scripted values) — green — and, better than rows, gives a REASON refutation is impossible at `baseCaps`: (3) `widLive` cannot fail because `scripted` requires `T (isData t)` and every data type has `pWᵛ ≡ 0` (Frame-Width:294–299), so the check is `0 ≤ᵇ cWid`; (1) `stBounded?` cannot fail because each pending `v` has `sizeᵛ t v < cSize = 2 + sizeᵉ e + slotsSize ins` by construction. **Those two arguments are the proof sketch** — this looks provable, not merely probable. Residual gap: the argument covers `scripted` slots; non-scripted entries in `Sched.live` at init are not analysed. |
| 8 | `init-capsOK?-suc` (was `init-capsOK?`) | Caps-Bridge.agda | **SPLIT 2026-08-06 (`df2bb71`) — `id = 0` is now PROVEN** | The blocker stands for the general case (`capsAt e ins id` unfolds through `sizeCount`, which is `abstract` at `Caps.agda:369`, so it never reduces to a numeral). But the postulate has been split rather than left monolithic: `init-capsOK?-0` is a REAL definition lifting `init-capsOK?-base` (tier-1 #7) through the proven `capsOK?-mono` via `capsAt-base-size`/`capsAt-base-wid`/`m≤m*n`, and `init-capsOK?-suc` is the specific remaining postulate at `id ≥ 1`. This also wires #7's `init-capsOK?-base`, which was stranded when the root chain was deleted. **The predicted route worked exactly as scoped** — the sole missing sub-lemma named in the old entry (`capsAt-base-reg`) had already been proven as `capsAt-reg` in Tick-Headroom. |
| 9 | `thruOuter-face-core` (P4) | Caps-Face.agda:6317 | SHAPE | Its own header doubts itself: receipt "(a) is the SECOND number … `subscribeE-caps` bounds its j′ by nothing whatever" and "(a) may not fit `fCharge` as stated." Statement-level work before grind. |
| 10 | `innerFinish-concat-face-core` (P3) | Caps-Face.agda:6253 | DIFFICULTY | The one from-inner clause that is not j′=0 (concatDrain's width sum). Expect grind, not design; the toolkit hypotheses are the right kit. |
| 11 | `dry-tick-core` | Caps-Bridge.agda:439 | DIFFICULTY | Given `cascadeGo-wet` (its first hypothesis) it is latch/finish bookkeeping plus the Deliveries counts. Nearly all its risk is inherited from #2, not its own. |
| 12 | ~~`three-size≤capsH-core`~~ | — | **DISCHARGED 2026-08-06 (`559780a`), then re-shaped (`2d4b899`)** | `three-size-le-blowH` + a 7-lemma support chain landed in `Caps.agda`; the postulate is gone and `three-size≤capsH` is a real definition. `S≤sizeStep` was deleted with it (its sole consumer was the replaced hypothesis slot). **Then it nearly died twice by accident** — a worker deleting the superseded root chain stranded `three-size-le-blowH`, and a second worker proposed deleting THAT. Both times the orphan report was right and the ruling was wrong: it is one half of the depth composition (`depth-capped` gives `depthE ≤ 3·cSize`, this gives `3·cSize(base) ≤ blowH`), and the two chain to `depthE ≤ capsH e ins 0`. Now wired root-first: `three-size≤capsH` → `depthE≤capsH-root` → hypothesis of `sub-charge-capsOK-lift-core`. **The lesson is general: a consumer-count sweep cannot tell a dead lemma from an unconnected half of a composition. Read what an orphan SAYS before ruling on it.** |

### Tier 2 — the main proof branch (Verify-Well-Formed, 21; plus batch-online)

> **PARKED behind tier 1** — see THE TIER ORDERING LAW in the roadmap below.
> Tier 2 is built ON `budget-sufficient`, so proving anything here while tier 1's
> anchor question is open bets on ground a tier-1 design failure would move. The
> ranking is kept current; the WORK waits. Sole carve-out: merge-cert's
> STATEMENT (a design deliverable, not a proof).

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

> **PARKED behind tier 2** — see THE TIER ORDERING LAW. Bucket (b) is already
> probed, so there is nothing cheap left here anyway; bucket (a) needs Anthony to
> author definitions before it asserts anything at all.

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

**(b) REAL AND PROBEABLE — ALL PROBED 2026-08-06, no refutation found.**
`agda/probe/Battery-Eval-Laws.agda` and `agda/probe/Battery-Readme.agda`. The
first pass on both was DEGENERATE throughout and was rejected; the second pass
carries an explicit **LOAD-BEARING / DEGENERATE label on every row plus a
"what would make this fail" line** — that labelling is the reusable part, and
new rows here should keep it.

- **`μ-unfold`** — the one under real suspicion (`defer-shift`'s comment says
  unfolding re-mints ids, which would kill a strict `≡`). Now has genuinely
  self-referential rows: `μbody₁ = deferᵉ (varᵉ (here refl))` at fuel 1 and 2,
  where drain steps actually fire and the compared output lists carry the
  `init`/`close` events **with their instants**, so ids ARE part of the
  comparison. The suspected asymmetry — LHS budgeted at `budgetAt (μᵉ e)` vs RHS
  at `budgetAt (unfoldμ e)`, which could make one side hit `g0`/dryBurst while
  the other unfolds — is addressed directly: both sizes are ≥ 3, so both budgets
  carry ≥ 8 `gs` levels and the difference cannot decide either site.
  **RESIDUAL:** that last step is an ARGUMENT, not a proof, and coverage is
  `noSlots` with fuel ≤ 2. A program sized near the `gs`-level boundary is where
  it would break if it breaks.
- **`fuel-coherent`, `id-inheritance`** — probed; first-pass rows were
  degenerate (fuel that changed nothing; singleton ⊆ singleton) and were
  relabelled/extended.
- **The 10 `readme-*` claims** — every row classified. Two were DEGENERATE and
  are now backed by load-bearing siblings (`emptyᵉ` rows where `concat [] ≡ []`
  or `0 ≤ 1` passes regardless; `cascades-inherit` at `ws ≡ []` fired no cascade
  at all, so a new `ws ≡ [varᵗ (here refl)]` row was added). Each load-bearing
  row now names its failure mode — e.g. `readme-diamond` would fail with
  `(3∷[])∷(3∷[])∷[]` if the two paths fired at different instants, which is
  exactly the property the README is about. A refutation here is SPEC-level:
  surface to Anthony, do not patch.

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

## THE ROADMAP

> ## THE TIER ORDERING LAW (Anthony, 2026-08-06)
>
> **TIER 1 IS FINISHED BEFORE ANY TIER 2 OR TIER 3 WORK RESUMES. STRICTLY.**
> Not "mostly", not "while we wait on a build" — tier 2 and tier 3 work
> *follows* tier 1 and does not interleave with it.
>
> **Why this is the right order, so nobody relaxes it for a plausible-sounding
> reason:** tier 1 (`Verify-Budget-Sufficient`) is what `budget-sufficient`
> rests on, and `evaluate-well-formed` — the whole of tier 2 — consumes
> `budget-sufficient`. So **tier 2 is built ON tier 1**. Every hour spent
> proving a tier-2 statement while tier 1's anchor question is open is an hour
> bet on ground that a tier-1 design failure would move. That is this
> campaign's most expensive class of mistake, and it has already been paid for
> once.
>
> **The one carve-out, and it is a DESIGN carve-out, not a grinding one:**
> answering a *design question* is cheap, is not the grind, and prevents the
> grind from being aimed wrongly. So MERGE-CERT's **statement** may land now
> even though its consumers are tier 2 — a statement is a one-line postulate
> plus a header, and having it settled costs nothing later. **What must NOT
> happen is the six rewrites and any tier-2 proof work built on it.** Those are
> parked behind tier 1 with everything else.
>
> **Practical test before starting any task:** if the postulate you are about
> to touch is NOT in the tier-1 table above, and the work is not one of the two
> design questions, it is parked. Say so and pick a tier-1 item instead.

Within tier 1, ordered so that each phase's findings can still cheaply change
the phases after it. Do not reorder: grinding before probing risks proving
towers over false ground.

### Phase 0 — THE FALSIFICATION SWEEP — ✅ COMPLETE (2026-08-06)

All seven targets resolved in one parallel sweep. Two REFUTED
(`burst-done-false`, `batch-online` — both had flagged themselves in comments),
two DISCHARGED (`scan-binv-adapt` landed; `three-size≤capsH-core` proven in one
line, landing pending), merge-cert SURVIVED its decisive reachability test,
`init-capsOK?-base` + `depth-compositional` probed with residuals recorded, and
`init-capsOK?` BLOCKED with its cause named. Detail per postulate is in the
ledger tables above. **The sweep's most valuable output was not a verdict but
the boxed CORRECTION on the caps axis: it is `abstract`-sealed and cannot be
probed at all**, which is why Phase 2 below is symbolic rather than numeric.

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

A fourth, from the same sweep: **a row that could not have failed is not a
row.** Label every probe row LOAD-BEARING or DEGENERATE and state what would
make it fail; the README and evaluator batteries carry the worked example.

### Phase 1 — THE TWO DESIGN QUESTIONS ← **YOU ARE HERE**

These are the campaign's real risk mass, and both are design work for the
design session, not worker grind.

- **1a. MERGE-CERT — SURVIVED (2026-08-06); land the STATEMENT only.**
  The corrected form has a computable shape, is seed-provable, and its
  reachability question is answered by the cascade ordering
  (`cascadeLatch` sets `dying` before any chain is processed; `cascadeGo` adds
  `rid` to `delivered` before `chainStep`; so `aliveThroughᶠ` is already false
  when `innerFinish` drops `k` to 0). Full detail and the uncovered residue are
  in the MERGE-CERT section below. **DO: state it in VWF with that mechanism in
  its header, citing the line numbers. DO NOT: rewrite the six consumers or
  prove anything over it — that is tier 2 and it is parked.**
- **1b. THE ANCHOR PROBLEM — the campaign's center, and now the critical path.**
  The 2026-08-06 probe round settled everything AROUND the anchor (see the
  section below), so this phase is no longer exploratory. It is four edits, in
  this order, and the order is the outside-in rule:

  1. **`Ŝ` ALREADY EXISTS — step 1 is FREE (found 2026-08-06, correcting this
     file).** The anchor is `sizeCapAt e sl (suc id)` (`Wet.agda:4109`,
     `= Caps.cSize (capsAt e sl id)`), a real definition, already threaded at
     the call site (`Caps-Bridge.agda:656`, `Ŝ = sizeCapAt e sl′ (suc id)`).
     `capsH e ins 0` was a PROBE CANDIDATE for a fresh anchor and is not
     needed — do not add a second one. Two facts already in hand come with it:
     `2≤sizeCapAt` (:4112) discharges `hop-edge`'s FIRST premise outright, and
     `sizeCapAt-mono` (:4118) lifts any bound at `id` to `suc id`.
  2. **STATE the dry family as POSTULATES** — `chainStep-dry` / `foldPath-dry` /
     `subscribeInner-dry`, each concluding that the observable reaching that
     site is `valB?`-bounded at the instant's own `B`. **The reachability source
     is `INV?`, and this is the round's second finding:** `INV? Ψ B sched st`
     already bounds every value the state holds by `B = sizeCapAt e sl id`
     (`valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)`,
     `Measures.agda:4875`). So `sizeᵛ o ≤ Ŝ` is NOT a fresh mystery — it is
     `valB?` at `id` composed with `sizeCapAt-mono`. **The whole remaining
     content is therefore ONE question: does the value ARRIVING at
     `subscribeInner` carry `valB?`, or is it freshly computed and outside
     `INV?`'s coverage?** That is what the three postulates assert, one per
     site, and it is the reachability induction in its smallest honest form.

     **DO NOT source it from the ledger.** `subscribeE-walk-core` concludes
     `burstB? (capᴱ W E′) Ψ …`, which looks like the bound wanted — but routing
     the anchor through `capᴱ W E′` is exactly the composition GAP 4 REFUTES
     (`walk-hyps-absurd`). The family sources from the CAPS face (`capsAt`,
     `caps-tick`), never from the receipt.

     ✅ **STATED AND GREEN, `02ffddc`** — `agda/probe/Anchor-Dry-Probe.agda`,
     three postulates plus `dry-hop`, the REAL (non-postulate) lemma closing
     `hop-edge`'s second premise from `valB?` and `sizeCapAt-mono`:
     `dry-hop B Ŝ Ψ o B≤Ŝ h = ≤-trans (valB-sz B Ψ _ o h) B≤Ŝ`. Telescopes
     match `Evaluator.agda:1592` / `:1542` / the `thruConsume` call sites
     (`:1109, 1121, 1130, 1140, 1196`). No `capᴱ` in any statement. Every
     hypothesis is caps-face (`INV?`, `capsOK?`, `valB?`, `pathB?`); every
     conclusion bounds the site's output at the FIXED `Ŝ = sizeCapAt e sl
     (suc id)` — fixed, so there is no Σ-witness to be upward-closed in.

     ⚠️ **THE RISK MOVED, IT DID NOT VANISH — AND THIS IS THE NEXT PROBE.**
     Each statement carries the growth of ONE INSTANT: inputs bounded at
     `B = sizeCapAt e sl id`, outputs at `Ŝ = sizeCapAt e sl (suc id)`, i.e.
     exactly one `frameBlowup` of headroom. But the adversarial doubling
     `scanᵉ` grows the accumulator by a FACTOR of ~2 per emission, and
     `syncSizeᵉ e` emissions can land in a single instant. So the headroom
     actually demanded is about `2^(syncSizeᵉ e)` — multiplicative in the
     emission count, not additive. `frameBlowup` is tower-shaped and very
     likely covers it, **but that is UNPROBED, and it is now the load-bearing
     arithmetic of the whole anchor.** If it fails, the three statements are
     FALSE as written and the repair is an anchor indexed by emission count
     within the instant rather than by instant alone. **Probe this BEFORE
     wiring the family into `subscribeE-wet-core`** — the wiring edit dirties
     `Wet.agda` (~14-18 min, plus everything above it), and grinding it over a
     false statement is the expensive mistake de-risk mode exists to prevent.

     ⚖️ **PROBED `f83186c` — HALF ESTABLISHED, AND THE OTHER HALF IS THE HALF
     THAT CARRIES THE RISK.** `agda/probe/Battery-Instant-Headroom.agda`
     (green) proves the CAPS side: `capsAt-covers-12pow`, i.e.
     `12 · 2^(sizeᵉ e + slotsSize sl) ≤ Caps.cSize (capsAt e sl id)` for any
     instant, over a proven chain (`capsAt-zero-size` by `refl`, `regAt-zero`
     via `*-identityʳ`, `i≤dWalkᶜ`, `J+n≤lvls`, `iterSize-le-capsAt`) plus two
     honestly-flagged postulates — `12·2^sz≤iterSize` (the real gap, verified
     by `refl` at sz = 1,2,3: `iterSize` = 129, 2340, 55555 against 24, 48, 96)
     and a trivial helper. Route 2 (numeric tables) is CONFIRMED DEAD:
     `sizeCount`, `cDel` and `blowH` are all `abstract`, so no numeral emerges
     from `sizeCapAt` — symbolic lower bounds are the only route, as the caps
     axis's `abstract` design already implied.

     **BUT THE COMPOSITION IS NOT PROVEN.** The growth is `12·2^k − 11` in the
     EMISSION COUNT `k`; the theorem bounds `12·2^sz` in the PROGRAM SIZE `sz`.
     Composing them needs **`k ≤ sz`**, and that step appears in the file only
     as prose (§6's "since max sizeᵛ ≤ 12·2^sz … see Battery-Obs-Growth"). It
     is exactly the repo's own lying-comment pattern: a qualification carrying
     the claim's weight, living where neither the typechecker nor `grep` can
     reach it. **It is also precisely the question the probe was sent to
     answer** — how many emissions land in ONE instant — so the receipt
     asserts its own open question as a premise.
     - **Half of the link is already proven and was not used**:
       `syncSize≤sizeᵉ` (`Measures.agda:698`), giving `syncSizeᵉ e ≤ sizeᵉ e`.
     - **The other half is measured but unstated**: `k ≤ syncSizeᵉ e`, i.e.
       emissions-per-instant is bounded by the sync measure. That is
       `Battery-Mu-Emissions`'s content, and it exists as measurements, not as
       a lemma. **State it, then the composition closes.**
     Until then this is a PARTIAL receipt: the caps ceiling is high enough for
     `12·2^sz`, and whether the growth stays under `12·2^sz` is still open.

     🔶 **`f04fb42` — THE GAP IS NOW NAMED RATHER THAN CLOSED, AND THE
     DISTINCTION MATTERS.** `obs-fits-headroom` typechecks the full chain
     `sizeᵉ o ≤ 12·2^k ≤ 12·2^(syncSizeᵉ e) ≤ 12·2^(sizeᵉ e) ≤ 12·2^sz ≤
     Caps.cSize (capsAt e sl id)`, correctly using the already-proven
     `syncSize≤sizeᵉ`. **But its hypothesis is UNINHABITABLE.** The step
     `k ≤ syncSizeᵉ e` was discharged by introducing
     `SyncCount : Closed Γ t → ℕ → Set` as a POSTULATED ABSTRACT PREDICATE
     with no definition and no introduction rule — so nothing in the repo can
     ever produce a `SyncCount e k` witness, `sync-count-bounded` is
     unfalsifiable (vacuously true if the family is empty), and the theorem
     cannot be instantiated at any program.
     - **This is CLAUDE.md's VACUOUS-BY-ABSTRACTION bucket** (Phase 5 (a)),
       arrived at from a new direction, and it is worth naming as a repeating
       failure mode: *an open step can be made to typecheck by promoting it to
       an undefined predicate, which looks like discharge and is not.*
     - **It IS progress, but only the wiring law's kind.** A prose
       qualification became a greppable, gated postulate — real, and preferred
       by the law. **The mathematical content is unchanged**, and the receipt
       must not be read as "the growth fits."
     - **THE REPAIR IS CONCRETE AND SHOULD NOT NEED A NEW ABSTRACTION.**
       `burstLen` (`Measures.agda:5654`) already counts emissions over the
       evaluator's REAL output stream, computably. State the bound over that —
       `burstLen (proj₁ (subscribeE …)) ≤ syncSizeᵉ e` at the right shape —
       and it becomes falsifiable, probeable by `refl` at concrete programs,
       and inhabitable at every call site. Delete `SyncCount` when it lands.

     ❌ **`2daa05b` — THAT REPAIR SHAPE IS REFUTED, AND THE ERROR WAS IN THE
     DIRECTIVE, NOT THE WORK.** `agda/probe/BurstLen-SyncSize-Probe.agda`
     (green, 7 `refl` checks) kills `burstLen (proj₁ (subscribeE …)) ≤
     syncSizeᵉ e` outright: at `deferᵉ emptyᵉ`, `burstLen ≡ 2` while
     `syncSizeᵉ ≡ 1`. `emptyᵉ` alone is worse (4 vs 1). Scan rows pass
     comfortably (5/6/7 against 14/15/16), so the failure is specific, not
     general.
     - **WHY IT FAILS — `burstLen` IS THE WRONG MEASURE.** It computes
       `sum (map (λ em → suc (length (InstEmit.events em))) b)`: one `suc` per
       `InstEmit` plus EVERY event, and `InstEvent` (`Rx/Prim.agda:107`) has
       `init`, `close`, `handoff` and `complete` beside `value`. The refuting
       burst carries one `init` and **zero `value` events** — so the number
       refuted is protocol bookkeeping, which a syntactic value-emission
       measure was never meant to bound. The mistake was naming `burstLen` in
       the directive; the probe did exactly the right thing with it.
     - **THE ANCHOR CLAIM IS UNTOUCHED.** Only `value` events feed a scan
       accumulator, so only they drive `12·2^k`. The measure needed is a
       VALUE-ONLY count over the same real stream — not yet defined anywhere,
       and a few lines to define.
     - **`SyncCount` correctly LEFT IN PLACE** for now: vacuous but not false,
       and deleting it before a correct replacement exists would strand
       `obs-fits-headroom`. Retire it when the value-count bound lands.
     - **STANDING LESSON, and it cost a round: name the measure by what it
       COUNTS, not by what it is called.** `burstLen` reads like "how many
       things did this burst emit" and is not that.

     🗼 **NESTING ESCALATES ONE EXPONENTIAL PER LEVEL — the per-instant
     headroom demanded is TOWER-shaped** (`agda/probe/Battery-Nesting-Escalation.agda`,
     green, all by `refl`). Two findings close steps 1–2 of the post-refutation
     plan:
     - **GAS IS NOT A COUNT BOUND, no run needed:** Battery-Value-Count's 30
       values ran on fuel of DEPTH 10. `subscribeInner` peels one `gs` per
       subscription and hands the same decremented fuel to every sibling —
       gas limits subscription DEPTH; breadth is free. The gas-sourced repair
       route is dead.
     - **THE ESCALATION LAW:** `nest src = mergeAllᵉ (scanᵉ step liveSeed src)`
       applies `v ↦ 2^(v+1) − 2` to the incoming per-instant count v — certified
       at v = 1..4 over `ofᵉ` sources and, the new fact, UNCHANGED at v = 2 when
       the source is itself a nested level (`nest²ᵃ ≡ 6`, instant 0). Composing
       from v = 1: 2, 6, 126, 2^127 − 2, … — a tower in nesting depth. Each level
       adds a CONSTANT to `sizeᵉ` while exponentiating the count, so **no fixed
       exponential in entry data bounds the per-instant count** — `12·2^sz`-class
       ceilings are dead for good, not just via `syncSizeᵉ`. (The v = 6 rows,
       predicted 126, exceeded a 10-min typecheck and are left uncertified in
       the file; coverage is honest there.)
     - **WHAT DECIDES THE DRY FAMILY NOW — step 3, the symbolic caps step.**
       (An earlier draft of this bullet said the cSize step "is one blowH
       application" — WRONG, that is the GAS height `capsHgo`. The real step,
       read off `capsAt-suc-full`: `Ŝ = iterSize B j B` with
       `j = sizeCount (capsAt e sl id) (capsH e sl id)`.)

     ⚖️ **STEP 3 DONE — THE RACE RESOLVES TO ONE NAMED INEQUALITY**
     (`agda/probe/Battery-Tick-Headroom.agda`, green). Proven, no postulates:
     `iterSize-doubles` (`sizeStep S s = S·(1+2s) ≥ 2s`, so one tick
     multiplies cSize by ≥ 2^j) and `headroom-arith` (`2^j·B` beats the
     instant's demand form `(2B+12)·towerℕ(suc sz)` as soon as
     `j ≥ 3 + towerℕ sz`, `sz = sizeᵉ e + slotsSize sl`). The assembly
     `tick-covers-instant` is a REAL definition typechecking against the
     actual `capsAt` recurrence.

     ✅ **`count-covers-tower` IS NOW PROVEN TOO — the headroom arithmetic
     is CLOSED, zero postulates in the file.** The recorded route executed
     as written: `fLvlD` is STRICTLY inflationary (`fLvl-pad` — both clauses
     factor through `fLvl + suc widAt`; the suc-d clause seeds `sIterD` with
     it via the existing `sIterD-zero≤`), so `iterL` advances by its budget
     (`iterL-plus`), `dLvl` climbs past `suc (sizeAt S J) + J` with
     `sizeAt S J ≥ 2^J`, hence `lvls 0 n` towers (`lvls-tower`, by induction
     with `pow2-mono`); and the count's budget `cDel ≥ cReg (capsAt) ≥
     2 + sz` (`dWalkᶜ-ge` — the walk visits `regAt S R 0 = R` positions,
     each adding ≥ 1 — plus `capsAt-reg`, cReg's base `suc sz` only ever
     multiplied up). Total: `sizeCount ≥ lvls 0 (2+sz) ≥ 3 + towerℕ sz`.
     **WIRING NOTE: `capsAt-reg` is the `capsAt-base-reg`-shaped sub-lemma
     tier-1 #8 names as its sole missing piece** (proven here at the
     stronger `2 + sz`); lift it into `Caps.agda` when #8 is picked up.
     **What remains open on the anchor is ONLY the demand model**
     (`a′ ≤ 2a + v + 11`, count ≤ towerℕ sz) — the dry family's own
       measured-not-proven content — that is what the
       three dry postulates assert.
  3. **TYPECHECK THE CONSUMER AGAINST THEM — ✅ DONE (2026-08-06), with one
     correction to this step's own wording.** The consumer is NOT
     `subscribeE-wet-core`: the dry family is `capsOK?`-conditioned and Wet
     deliberately reads NOTHING from the caps face (its own import comment),
     so the right layer is the caps↔wet bridge. Landed as:
     - `src/Verify-Budget-Sufficient/Tick-Headroom.agda` — the whole headroom
       chain, verbatim from the probe (deleted).
     - `src/Verify-Budget-Sufficient/Anchor-Dry.agda` — the dry family,
       FACTORED on landing: each dry statement is a real DEFINITION =
       demand postulate widened to `Ŝ` by `tick-covers-instant` (via
       `burstB?-widen`/`valsB?-widen`). The three `*-demand` postulates at
       the explicit form `(2·B + 12) · towerℕ (suc sz)` are now THE anchor's
       entire open surface, greppable.
     - `dry-tick-core` (Caps-Bridge) threads the family + `dry-hop` as four
       new hypotheses, supplied at `dry-tick` — the shape typechecks against
       the real recurrence; all four ledgered in DEFERRED.txt.
     If the demand form is wrong it now changes in one file, before any
     proof is ground over it.
  4. **THE UN-DEFERRING, ENFORCED IN `make wiring`** (Anthony, 2026-08-06) —
     ✅ **DONE, `bfa6b6e`.** `agda/DEFERRED.txt` holds 55 ledgered entries
     (≤152 →-slots); `make wiring-gate` ratchets against it. Verified by the
     design session, not merely reported: gate green at exit 0, and deleting
     `hop-edge`'s line fails it with the exact line to restore. `hop-edge`'s
     entry names the anchor premise as the worked example that motivated the
     ledger — so the debt this phase is about is now greppable from a file
     under version control. Design notes below are retained for the rationale.

  A third refutation here is still STOP-grade: it would mean tier 1's top three
  postulates have no surviving proof route.

  **THE UN-DEFERRING, AND WHY IT IS PART OF THIS PHASE.** Hoisting `sizeᵛ o ≤ Ŝ`
  out of `hop-edge`'s hypothesis position and into a named top-level postulate
  IS step 2 — the dry family and the un-deferring are the same edit seen from two
  sides. That makes this the right moment to close the hole that let the debt
  hide, because the fix and its first test case land together.

  **THE HOLE.** `make wiring` tracks NAMES, not OBLIGATIONS INSIDE TYPES. A
  proven lemma with unpaid premises, handed to a postulate as an argument, reads
  as fully wired: the name has a consumer, so no orphan, no gate failure — while
  its premises are never discharged by anything. That is how `hop-edge`'s size
  premise sat unexamined; the wiring law says every gap is a postulate with a
  real signature, and a premise buried in a hypothesis position is precisely a
  gap that is not.

  **THE FIX — promote (B4) from report to RATCHETED GATE.** (B4) already finds
  the passed-only lemmas (55 lemmas, ≤152 deferred →-slots at baseline). Make it
  bite:

  - **A checked-in ledger** (`agda/DEFERRED.txt` or equivalent) listing each
    passed-only lemma with the postulate that defers it. `make wiring-gate`
    EXITS 1 when the measured set is not the ledger's set.
  - **The ratchet runs one way.** A NEW passed-only lemma fails the gate until
    it is added to the ledger deliberately — so deferral becomes an explicit,
    reviewed act rather than a silent side effect of writing an assembly. A
    lemma LEAVING the set (its premises now discharged) requires deleting its
    ledger line, which is how the numbers come down and stay down.
  - **Ledger lines carry the reason**, one line each, naming what would have to
    exist to un-defer. Then "what debt is hidden in hypothesis positions?" is
    answered by a file under version control instead of by re-reading signatures.

  Baseline note for whoever lands it: (B4)'s →-slot count is an UPPER BOUND (it
  counts arrows, not distinct obligations), and it is textual — a lemma used only
  inside a `where` block can be misreported. The ledger inherits both caveats;
  record them in its header so the number is never read as exact.

### Phase 2 — TIER 1 STATEMENT REPAIRS + THE SYMBOLIC ATTACK

Tier-1 statements known to be wrong-shaped, and the caps axis's substitute for
probing. All of this is tier 1, so all of it precedes tier 2.

- `sub-charge-capsOK-lift-core` → general mid-state `opIterD` hypothesis (or a
  recorded ruling for why root-only suffices at its one consumer). Its own route
  comment calls for a general form that is unstated and unknown.
- P4 `thruOuter-face-core` → resolve the "(a) may not fit `fCharge`" doubt at
  the statement level, per its own header.
- **`opIterD≤sizeCount-root-core` → DONE as a reduction (2026-08-06); the
  assembly is READY TO LAND into Caps-Bridge.** `agda/probe/Battery-OpIter-Symbolic.agda`
  holds it. Three things worth carrying forward:
  - **HOW TO REASON THROUGH THE SEAL — reusable for the whole caps axis.** All
    three `sizeCount-body` call sites use the same move: it is a `≤-reflexive`
    wrapper around an existing `lvls` inequality. So prove the `lvls` form, then
    wrap with `≤-reflexive (sym (sizeCount-body c d))`. That is the pattern for
    every sealed-symbol obligation here; do not re-derive it.
  - **THE NAIVE COUNT IS FALSE, and the reason fixes the shape.**
    `opIterD S W d k m 0 ≤ lvls S W d 0 m` — same count `m` on both sides — does
    NOT hold. Each `opIterD` suc-step sets `J₀ = suc (suc (S)²)` then applies
    `suc (widAt S W J₂)` passes of `fLvlD` where `widAt` grows as a TOWER
    (`foldStep S w = S^(suc w)`), while one `dLvl` step from 0 applies only
    `suc S` passes. So the count MUST be `cDel c d` (doubly exponential in `S`),
    which is what the postulate already says — its shape is right.
  - **THE REMAINING MATHEMATICS, named at last.** `opIterD-dominated` wants
    induction on `m` with a residual-budget invariant tracking `J` and remaining
    `D`, and the suc case needs a lemma of the form
    `fIterD S W d k n J ≤ lvls S W d J (‹bound in n›)` — dominating `fIterD`'s
    n-step application by some number of `dLvl` steps. **Finding ‹bound in n› is
    the open question**; that is the irreducible core of "the genuinely new
    mathematics", and it is now one inequality over ℕ rather than a statement
    about the evaluator.
- **Land `three-size≤capsH-core`'s discharge**, moving `three-size-le-blowH` and
  its helper chain from `Pool-Lower-Probe` into `Caps.agda`. **Decide the
  `S≤sizeStep` orphan in the SAME commit** — the discharge strands it (its only
  consumer is the assembly being replaced).
- **State `capsAt-base-reg`**, the one missing sub-lemma that lets proven
  `capsOK?-mono` lift `init-capsOK?-base` to `init-capsOK?` and retire the
  latter.

### Phase 3 — THE TIER 1 GRIND (workers; only over probed or repaired ground)

Cheapest-and-safest first, anchor-dependent mass last.

1. `three-size≤capsH-core` (proof in hand), `init-capsOK?-base-core` (proof
   sketch in hand from the two structural arguments) — the two tier-1 items
   closest to done.
2. `dry-tick-core`'s own bookkeeping, to whatever depth `cascadeGo-wet` allows.
3. P3 `innerFinish-concat-face-core` — real grind, no design blocker.
4. `depth-compositional` — probed green including evolved states; the
   `storeNestMax` strengthening is the remaining work.
5. The anchor cluster (`subscribeE-walk-core` → `subscribeE-wet-core` →
   `cascadeGo-wet-core` → `dry-tick-core`) — after 1b. This is the endgame and
   it stays LAST, because it is where a design failure costs the most reground
   work.

**TIER 1 IS FINISHED when every postulate in the tier-1 table is discharged or
deleted.** That is the gate. Only then does the parked work below resume.

### Phase 4 — TIER 2, PARKED BEHIND TIER 1

Ready-to-go work deliberately NOT being done, so it is not lost:

- The six merge-cert consumers rewritten over 1a's statement
  (`subscribeE-{merge,concat,switch,exhaust}All-wf`, `root-done-plumbed`,
  `root-caches`, `stepFrame-wf-outer`).
- `dispatchShare-wf` → FoldOut-carrying conclusion (cascades into the stepFrame
  family signatures — change the signatures first, per the wiring law).
- `cut-owed`, `stepFrame-wf-inner-concat`, the per-clause WF receipts
  (`input-core`, `defer`, `takeᵉ-core`), `mid-step-core`'s FoldOut threading,
  and the two `valsLast-push` shape postulates.

### Phase 5 — TIER 3, PARKED BEHIND TIER 2

- Bucket (a) VACUOUS-BY-ABSTRACTION (all of `Rx.Time-Theorems`, `causality`,
  `μ-guarded`, `defer-shift`): de-risking these means **defining** the nine
  postulated abstractions, which is claim-authoring and needs Anthony. Flag,
  do not grind.
- Bucket (b) is PROBED (2026-08-06) with residuals recorded; proofs are Phase 5.
- Bucket (c) FFI is permanently trusted, not counted.


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

> ### ANCHOR STATUS AFTER 2026-08-06's PROBE ROUND — THE ROUTE IS ALIVE AND NARROWED TO ONE LEMMA
>
> Four probes ran against the surviving reachability route. **None refuted it, three
> retired a way it could have died, and the surrounding constraints are now verified
> satisfiable.** What remains is a single obligation.
>
> **1. The μ ESCAPE IS BLOCKED BY TYPING — so the emission count is entry-bounded.**
> (`agda/probe/Battery-Mu-Emissions.agda`.) `μᵉ` binds into the GUARDED context `Δᵍ`
> while `varᵉ` reads from `Δ`, and `deferᵉ` is the sole gate between them — so
> `μᵉ (varᵉ (here refl))` is a TYPE ERROR and synchronous self-subscription is not
> writable. Measured contrast across an unfold: `sizeᵉ` DOUBLES (10 → 20) while
> **`syncSizeᵉ` is STABLE (9 → 9)**. The load-bearing fact, now named:
> `syncSize-μ-invariant : syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body`.
>
> > ❌ **REFUTED 2026-08-06 — "per tick, emissions ≤ `syncSizeᵉ e`" IS FALSE, and
> > it was the cornerstone claim of this section.** `agda/probe/Battery-Value-Count.agda`
> > (green, every row by `refl`) measures VALUE emissions in ONE instant against
> > `syncSizeᵉ`, on a doubling `scanᵉ` over a **live** seed:
> >
> > | K | valueCount | `syncSizeᵉ` | holds? |
> > |---|---|---|---|
> > | 1 | 2  | 17 | ✓ |
> > | 2 | 6  | 18 | ✓ |
> > | 3 | 14 | 19 | ✓ |
> > | 4 | **30** | **20** | **✗ REFUTES** |
> >
> > `valueCount = 2^(K+1) − 2` (exponential in source length) against
> > `syncSizeᵉ = 16 + K` (linear); they cross at K = 4 and the gap widens.
> > `maxInstant ≡ 0` on the refuting burst, so this is genuinely PER-INSTANT.
> > **The mechanism:** `syncSizeᵉ (mergeAllᵉ e) = suc (syncSizeᵉ e)`
> > (`Exp.agda:509`) charges a bare `suc` for a merge, while a merge over a
> > doubling accumulator subscribes an exponentially large tree of live leaves
> > inside the one instant. A syntactic measure charging additively cannot bound
> > a multiplicative runtime effect.
> > **Why it was believed:** `Battery-Obs-Growth`'s scan uses `seed = strmᵗ emptyᵉ`,
> > so every accumulator is a tree of merges over EMPTY leaves — it grows in SIZE
> > while emitting nothing. Changing one token (`emptyᵉ` → `ofᵉ [0]`) makes the
> > leaves live and the counts explode. **A near-miss shape can look like a
> > covering shape; this one hid the refutation for four probe rounds.**
> > **What it kills:** every anchor route through emissions-bounded-by-syntax,
> > including `sync-count-bounded` in `Battery-Instant-Headroom.agda` (FALSE the
> > moment its abstract `SyncCount` is instantiated to the real count) and the
> > chain `sizeᵛ o ≤ 12·2^k ≤ 12·2^(syncSizeᵉ e)` built on it. Since `k` is
> > itself exponential in program size, **`sizeᵛ o` is DOUBLY exponential in
> > entry data — not `12·2^sz`** — so `capsAt-covers-12pow` is the wrong ceiling.
> > **What it does NOT kill:** the three dry postulates bound `sizeᵛ` at
> > `sizeCapAt e sl (suc id)`, which is tower-shaped and may still dominate a
> > doubly-exponential value. **That is the open question now, and it is a
> > different one.** The μ typing fact itself (`deferᵉ` gates `Δᵍ`→`Δ`) stands;
> > what falls is the inference from it to a syntactic emission bound.
>
> **2. BOTH CEILINGS FIT** (`agda/probe/Battery-Anchor-Fit.agda`), against the
> candidate `Ŝ-cand e ins = 12 · 2^(sizeᵉ e + slotsSize ins)`:
> - `Ŝ ≤ capsH e ins 0` — FITS, with one arithmetic gap `exp12≤blowH` (route:
>   `blowH m ≥ 2·poolCount (towerℕ m) m ≥ 2·towerℕ m ≥ 12·2^X` when `m ≥ 4 + X`,
>   via Pool-Lower-Probe's `capsBase-le-pool`).
> - **`dBound` at that `Ŝ` fits under `budgetAt e ins 0` — FULLY DERIVABLE, no new
>   postulates.** This was the failure mode most worth fearing: an anchor big enough
>   to bound the values could have blown the walk's own budget, killing the route
>   *even if the size bound were true*. It does not. The chain mirrors
>   `caps-fuel-root` in Wet.agda exactly.
>
> **3. THE LARGEST WORKABLE ANCHOR IS `capsH e ins 0` ITSELF** — ceiling 1 holds at
> equality and ceiling 2 by the same chain. **So `Ŝ` need not be a bespoke
> exponential; take `Ŝ := capsH e ins 0`** and both ceilings come for free. That is
> the design ruling this round buys.
>
> **4. HOP-EDGE'S THIRD PREMISE discharges from an existing walk conjunct** (below).
>
> **5. THE GROWTH RATE IS CAPPED AT EXPONENTIAL — the shape of `Ŝ` is settled**
> (`agda/probe/Battery-Reached-Sizes.agda`). Sizes REACHED through the evaluator's
> real `scanVals` path (Evaluator:1052–1056), which is what `thruWalk` hands to
> `subscribeInner`:
>
> | k | `sizeᵉ progₖ` | max `sizeᵛ` at `subscribeInner` |
> |---|---|---|
> | 1 | 15 | 13 |
> | 2 | 16 | 37 |
> | 3 | 17 | 85 |
> | 4 | 18 | 181 |
>
> Program size grows LINEARLY (+1 per source element); the observable grows
> EXPONENTIALLY. **A linear anchor is refuted by this table.** A tripling step was
> also built (`Aₖ₊₁ = 3·Aₖ + 15`, giving `1, 18, 69, 222`) — so the base is
> tunable. **But super-exponential is IMPOSSIBLE for a fixed step function:** an
> `Fn` of size `S` with branching factor `n` (occurrences of the accumulator in
> its output) yields `sizeᵛ accₖ = O(nᵏ)`, and `n ≤ S ≤ sizeᵉ e`. Growing `n` with
> `k` would take a non-fixed `Fn`, which is not writable. **So `Ŝ` is exponential
> with an entry-bounded base AND an entry-bounded exponent** (`k ≤ syncSizeᵉ e`
> per §1) — comfortably under `capsH`'s tower.
>
> **6. `connect-edge`'s BOUND IS FREE — only `hop-edge` is hard.** `slotSize
> (shared d) ≡ sizeᵉ d` (Slots.agda:61), so `sizeᵉ d ≤ slotsSize ins < capsBase
> e ins ≤ Ŝ`. Shared defs are fixed at program entry and cannot grow at runtime.
> That retires one of the two anchor edges outright.
>
> **WHAT REMAINS — one lemma, and it now looks PROVABLE.** Prove `sizeᵛ o ≤ Ŝ` for
> every observable `o` REACHABLE at `subscribeInner`. Everything around it is
> settled: the ceilings fit, `Ŝ := capsH` works, the descent premise discharges,
> `connect-edge` is free, emissions are entry-bounded, and growth is at most
> `O(nᵏ)` with both `n` and `k` entry-bounded. **The remaining content is the
> REACHABILITY INDUCTION** — that every `o` arriving at `subscribeInner` is
> produced by at most `k` applications of a fixed step function to entry syntax.
> That is what the dry family (`chainStep-dry` / `foldPath-dry` /
> `subscribeInner-dry`) has to say.

**WHAT THE DELIVERABLE ACTUALLY IS — it is CODE, not an argument.** `hop-edge`
and `connect-edge` are already PROVEN and already wired in as hypotheses of
`subscribeE-wet-core` (Wet.agda:4344, :4350). Nothing is missing from the descent
machinery. What is missing is the ability to discharge their PREMISES at the call
site, and that takes exactly ONE artifact — **the dry lemma family**
(`chainStep-dry` / `foldPath-dry` / `subscribeInner-dry`) proving the premises
for every `o` that actually reaches `subscribeInner`. **`Ŝ` itself is NOT
missing** (corrected 2026-08-06): it is `sizeCapAt e sl (suc id)`, defined at
`Wet.agda:4109` and already threaded at `Caps-Bridge.agda:656`. An earlier
reading of this file called for defining it; that would have added a second,
competing anchor. Discharging them unblocks tier 1 ranks 1, 2, 3 and 11 together.
Per the outside-in rule, (1) lands as a real definition and (2) as postulates
FIRST, with `subscribeE-wet-core`'s proof typechecking against them — so a wrong
`Ŝ` changes in one place instead of invalidating finished work.

**And (2) IS the un-deferring.** Stating the family hoists `sizeᵛ o ≤ Ŝ` out of
`hop-edge`'s hypothesis position — where `make wiring` cannot see it — into a
named postulate it can. Phase 1b step 4 makes that permanent by ratcheting (B4);
see the phase entry above.

**HOP-EDGE'S THIRD PREMISE — RESOLVED 2026-08-06, and it is NOT a second design
blocker.** `hop-edge`'s signature is `2 ≤ Ŝ → sizeᵛ (obs u) o ≤ Ŝ →
hopDᵛ Ŝ (obs u) o < r → …`. The campaign's anchor discussion is entirely about
the second premise, so the third — the DESCENT condition — was checked
(`agda/probe/Battery-Hop-Premise.agda`, green). It discharges in two lines from
material that already exists:

- at the `*All` frame, `r` IS `hopDᵉ Ŝ (mergeAllᵉ b) = suc (hopDᵉ Ŝ b)` —
  definitional, `Rx/Hop-Depth.agda:191`;
- `subscribeE-walk-core`'s conclusion already carries the conjunct
  `burstHopD? F (hopDᵉ F b) burst ≡ true` (Measures.agda:5810), labelled in
  source as "the hop edge's feed, at the index the child also reads", giving
  `hopDᵛ Ŝ u v ≤ hopDᵉ Ŝ b`;
- so `hopDᵛ Ŝ u v ≤ hopDᵉ Ŝ b < suc (hopDᵉ Ŝ b) = r`. Wet.agda:4046 said as much
  all along ("the r-drop is the emitted-value invariant (burstHopD?)").

**It is not free, though — it is ABSORBED into `subscribeE-walk-core`.** The
`burstHopD?` conjunct is part of that postulate's conclusion, so proving the walk
must prove it too. Classed DIFFICULTY, not FALSITY: its engine is proven
(`hopD-applyFn`, Measures:2765) as is its mapᵉ consumer (`hopD-map-emit`, :2780).

**The two premises share a failure mode**, which is the useful reduction: on the
adversarial doubling scan, `hopDᵉ V accₖ ≡ k` (LINEAR) while the parent
`hopDᵉ V (mergeAllᵉ (scanᵉ …)) ≡ suc (3^V)` (exponential in `V`) — at `V ≡ 4`,
`3` against `82`. So (iii) can only fail where (ii) already fails. **The anchor
problem remains the single design gate.**

**`connect-edge` has NO analog** — its descent energy comes from `U` dropping
strictly via `unconn-insert`, while `r`/`s` merely RESET (`reach-reset`), needing
no strictness. Its sole open obligation is the same anchor question,
`sizeᵉ d ≤ Ŝ` for a slot def.

**CORRECTION, and the standing lesson landing on this file itself:** the note this
replaces said the third premise "appears nowhere and has never been examined."
That was true of PROOF-STATE and FALSE of the repo —
`agda/probe/Hop-Descent-Probe.agda:202–230` was built for exactly this obligation
and measured it on three shapes. What today added is the adversarial `scanᵉ`
shape, which that probe explicitly did not cover ("no scanᵉ in any witness"). Grep
the repo before declaring a gap, including when the gap looks new.

**NEW CONSTRAINT ON `Ŝ`'s SHAPE (2026-08-06, machine-checked):
`Ŝ` CANNOT BE LINEAR IN `sizeᵉ e`.** `agda/probe/Battery-Obs-Growth.agda`
establishes, by `refl`:

- **`scanᵉ` carries NO `isData` restriction on its accumulator type** (Exp.agda:67;
  the guard exists only on `scripted` slots, Slots.agda:40, and
  `isData (obs _) ≡ false`). So the accumulator may be `obs u`-typed, and
  `strmᵗ` (Exp.agda:96) lets the step function return an observable built from
  its own input. The doubling step
  `strmᵗ (mergeAllᵉ (ofᵉ (acc ∷ acc ∷ [])))` typechecks with nothing to stop it.
- **Inner observable sizes then grow exponentially in the emission count**, on
  the recurrence `sizeᵛ accₖ = 11 + 2 · sizeᵛ accₖ₋₁`, closed form `12·2ᵏ − 11`:
  measured `1, 13, 37, 85` at `k = 0…3`.
- **The killer number: `sizeᵉ prog₃ ≡ 17` while its own max inner is `85`.** A
  17-symbol program reaches an inner observable 5× its own size, so any anchor
  derived LINEARLY from program size is refuted outright. `Ŝ` must be at least
  exponential in entry data.

**WHAT THIS DOES NOT ESTABLISH — the route is NOT dead.** The probe's source is
`ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])`, i.e. `k ≡ 3` is SYNTAX. A scripted slot's
values live in `ins`, which is entry data too, so `k ≤ slotsSize ins` and
`Ŝ ≈ 12·2ᵏ` stays entry-computable — merely exponential, not unbounded. And
`capsH = blowH (capsBase e ins)` is a TOWER in `m`, which dominates `12·2ᵐ`
comfortably. A first pass claimed the route dies for scripted sources via
`Ŝ > capsH`; that ASSUMED `Ŝ > capsH` rather than deriving it, and the refuting
program was never built.

**SO THE ANCHOR QUESTION IS NOW SHARPER, AND THIS IS ITS DECIDING FORM:**

> Can the number of emissions into a doubling `scanᵉ` within ONE anchor scope
> (one subscribe walk, or one cascade) exceed anything computable from `e` and
> `ins`?

The only generator that could do it is `μᵉ` — and **the standing sync-μ ruling is
what likely saves the route**: `deferᵉ` is the sole gate moving `Δᵍ` into `Δ`, so
a μ's self-reference costs a TICK and synchronous self-subscription is not
writable (see the ruling below). If that holds, per-instant emissions are
syntax-bounded, `Ŝ` is entry-computable-exponential, and it fits under the tower.
**Then the sync-μ ruling is not a side note — it is the load-bearing fact of the
anchor proof**, and should be cited as such wherever `Ŝ` is sourced.

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

Live list is the session task tool. Under THE TIER ORDERING LAW the standing
tasks split cleanly into ACTIVE (tier 1 + the two design questions) and PARKED
(everything tier 2 / tier 3), and the split is the schedule:

**ACTIVE — tier 1 and design:**
- **#30** THE ANCHOR PROBLEM — Phase 1b. The critical path; nothing in tier 1's
  top block moves until it is answered.
- **#17** `opIterD≤sizeCount-root` + `sub-charge-capsOK-lift` — Phase 2's
  symbolic attack and generalization repair, then Phase 3.
- **#4** P3 + P4 — Phase 2 for P4's statement doubt, Phase 3.3 for P3's grind.
- **#33 (PARTIAL)** merge-cert — the STATEMENT half only, as Phase 1a's design
  carve-out. Its six consumer rewrites are PARKED.

**PARKED behind tier 1 — recorded so it is not lost, not so it is picked up:**
- **#31** tier-2 statement repairs (`dispatchShare-wf`), and #33's six rewrites.
- Everything in roadmap Phase 4 and Phase 5.

**#19** and **#26** are COMPLETE (Phase 0). Note #19's answer — the two
structural arguments — doubles as `init-capsOK?-base-core`'s proof sketch.
