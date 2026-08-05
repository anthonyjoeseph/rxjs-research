# Formal Verification Campaign — Worker Handoff (updated 2026-08-05)

**Status:** Tier 1 item 4 (Step C) — Units 0–2 DONE and merged green to main. The level
conjunct is threaded across the clique and 18 of the 20 census sites are closed;
`level-TEMP` has TWO remaining sites (Subscribe-Face **1834**, **2280**), and both are the
SAME question — depth sufficiency, now scoped and **RULED** as Unit 3 below. Postulate
ledger: **5 real postulates** (Caps-Face 2, Measures 1, Wet 2) — unchanged by Step C,
which was TEMP-scaffolding work.

## ⚠ RESUME HERE

`origin/main` is GREEN through the input-edge commit ("the slot edge was never a ruling,
and the strict step it needed was already written"). Every commit was gated on
`make agda && make bug-cache` both exiting 0, read from the log's own `EXIT=` lines.

**The current work is: EXECUTE UNIT 3** (the ruling below). It closes the last two
`level-TEMP` sites, finishes Step C, and unblocks item 3 (the two Caps-Face faces).

History that used to fill this file — the 20-site census and its buckets, the keystone
pass, the budget rethreading, the profiling findings (Positivity is 78.5% of
Subscribe-Face's check, a whole-mutual-block cost; the module split was measured at ~7%
and deprioritized) — is in this file's git history. Where any memo and the tree disagree,
**the tree wins**.

---

## UNIT 3 — DEPTH SUFFICIENCY: THE RULING (2026-08-05, design session)

### The decision in one line

Add a depth-sufficiency hypothesis to the clique, exactly as `nest … ≤ bud` and
`suc (sizeᵉ b) ≤ ops` already sit there — and its currency is a **DEPTH MIRROR**: a family
of ℕ-valued functions, one per evaluator head on the subscribe path, defined
clause-for-clause on the evaluator's own recursion, returning the `⊔` (max) of its
callees' mirrors, with a `suc` at EXACTLY the two arcs where the caps proof spends `dep`.
Head X's hypothesis is `depthX ⟨X's own evaluator arguments⟩ ≤ dep`, argument name `dpt`.

The mirror is a function of the RUN, not of any syntax — it recomputes the evaluator's own
intermediates. That is what dissolves both historical refutations: the share edge reads
the same stored def the evaluator reads (no residue needed, unlike `bud`'s measure), and
scan-minted payloads are recomputed rather than approximated. It is also the WEAKEST
hypothesis that can close the clique — it is literally "the depth this very run reaches" —
so every future top-level discharge argument factors through it automatically.

### Why nothing simpler works — all three alternatives are dead, two by machine

1. **Bare positivity** (`1 ≤ dep`, descend-and-maintain) — machine-refuted,
   `Mu-Nest-Probe` § 1: the maintenance step at `dep = 1` demands `1 ≤ 0`.
2. **Any syntactic or value-derived measure** — machine-refuted twice. `Mu-Nest-Probe`
   § 2: the share edge's callee is a stored def structurally unrelated to the subscribed
   term. `Nest-Budget-Probe` § 3: a `scanᵉ` under an `*All` mints payloads whose nesting
   is the FOLD COUNT — the payload's walk descends deeper than any function of the payload
   or of the carrier's syntax. Depth demand is dynamic; no static measure dominates it.
   (Caps-derived measures fail separately: caps GROW down the walk, so nothing derived
   from them descends.)
3. **The gas** (`suc (gasHt g) ≤ dep`, offset by cycle position) — threads perfectly (the
   peel discipline, `Rx/Evaluator.agda:672-695`, was designed as this bridge) but is
   **FALSE at the intended instantiation**: `capsAt` runs at `d := capsH e sl id`, and the
   instant's gas sits one blowH story ABOVE that (`Rx/Evaluator.agda:710-717`, "a
   stratification, not a domination"). Threading a hypothesis known false at its only
   planned supply site is the proven-pieces-without-an-assembly anti-pattern. Do not
   re-propose it.

### The mirror, precisely

New module **`agda/src/Verify-Budget-Sufficient/Caps-Depth.agda`** — its own mutual block,
importing `Rx.Evaluator`; nothing imports it except `Subscribe-Face` (and later the face
chain). Definition rules:

- **R1 — one mirror head per evaluator head on the subscribe path**, taking the SAME
  argument list as the evaluator head, including value-style scrutinee arguments
  (`innerFinish`'s trailing `Maybe (NodeState Γ)` is the model).
- **R2 — each clause returns the `⊔` of the mirrors of every callee** the evaluator's
  clause invokes on the subscribe path, applied to the SAME expressions — recompute
  intermediate bursts and states by calling the real evaluator, exactly as the clause's
  own `let` does. Clauses with no subscribe-path callee return `0`.
- **R3 — `suc` in exactly two places**: `stepFrame`'s thru-outer clause
  (`suc (depthWalk fuel op nid κ id now vals sched st)`) and `innerFinish`'s
  concat/`yes refl` branch (`suc (depthDrain fuel allNid κ id now q sched st)`).
  **NOT** at `subscribeInner`'s gas peel, NOT at μ, NOT at `sharedConnect` — the mirror
  mirrors where the CAPS PROOF spends `dep` (the two arcs that fit a walk under
  `fLvlD S W (suc d) j`), not where the evaluator peels gas.
- **R4 — NO `with` anywhere in the mirror.** Where the evaluator dispatches by `with`,
  either (a) OVERAPPROXIMATE — ignore the test and return the spending branch's value or
  the max over branches, whenever the types allow (`innerReact`'s `aliveThroughᶠ` test,
  `concatDrain`'s `if done`); a too-big mirror is harmless, it only demands more depth.
  Or (b), when the dispatch is TYPE-FORCING (`innerFinish`'s `w ≟ᵗ s`, `subscribeE`'s
  `take` on `evalTm count`, the `input` clause on `Sched.slots sched i`), delegate to a
  helper head taking the scrutinee as a real argument and matching it as a pattern
  (`depthFinConcat … (w ≟ᵗ s)` with `yes refl` / `no _` clauses).
- **R5 — heads that never reach a subscribe have mirror 0** (map-f/scan-f/take-f frames;
  `ofᵉ`, `emptyᵉ`, `deferᵉ` — it PARKS, `varᵉ`, out-of-gas clauses); `retagEvents` and
  `evalTms` get no mirror head at all.
- **R6 — NOT `abstract`, at first**: the caps clauses need the clause equations to reduce
  definitionally in their pattern contexts. If Caps-Depth's or Subscribe-Face's check cost
  explodes, fall back to the transformer family's own pattern — `abstract` plus exported
  per-clause `≡`-equations (`Rx/Evaluator.agda:789-829` style) — and pay the rewrites.
- **R7 — termination is the evaluator's own**: the mirror's call graph is a subgraph of
  the evaluator's with identical argument shapes (gas descends at the same three edges;
  lists and expressions descend structurally; `dispatchShare`'s ℕ gas descends as there).
  If the checker balks, align the argument order with the evaluator's exactly.

Clause table — a TRANSCRIPTION GUIDE, not a substitute for reading the tree
(`Rx/Evaluator.agda:939-1600`); where they disagree, the tree wins:

| mirror head | of evaluator | shape |
|---|---|---|
| `depthE` | `subscribeE` | `input i` ↦ `depthSlot … (Sched.slots sched i)`; `of/empty/defer/var`, `μ` at `g0` ↦ 0; `mapᵉ` ↦ `depthE fuel b (map-f f ↠ κ) … ⊔ depthBurst fuel id now (map-f f) κ burst sched₁ st₁` with the clause's own lets (:1418-1420); `takeᵉ` ↦ `depthTake … (evalTm count)` (R4b; `zero` ↦ 0, `suc k` ↦ the map shape with `take-f nid`/`installNode` exactly as :1428-1433); `scanᵉ` ↦ same shape (:1435-1440); the four `*All` ↦ `depthAll …`; `μᵉ` at `gs fuel` ↦ `depthE fuel (unfoldμ body) …` |
| `depthSlot` | the `input` dispatch | `shared d` ↦ mirror of `subscribeSharedSlot`; `scripted` hot/cold ↦ 0 |
| `depthShSlot` | `subscribeSharedSlot` | mirrors its dispatch down to `sharedConnect` |
| `depthConn` | `sharedConnect` | `g0` ↦ 0; `gs fuel′` ↦ `depthE fuel′ d …` ⊔ the clause's burst-push mirrors (:1348+) |
| `depthAll` | `subscribeAll` | `depthE fuel b (thru-outer op nid ↠ κ) … ⊔ depthBurst … (thru-outer op nid) …` with the mint/install lets (:1314+) |
| `depthInner` | `subscribeInner` | `g0` ↦ 0; `gs fuel` ↦ `depthE fuel …` per :1009+ (the retag/split plumbing adds nothing) |
| `depthWalk` | `thruWalk` | `[]` ↦ 0; `o ∷ os` ↦ `depthConsume … o sched₀ st₀ ⊔ depthWalk … os sched₁ st₁` (post-state via the same let, :1153+) |
| `depthConsume` | `thruConsume` | each clause: the subscribing branch ↦ `depthInner …`, a parking branch ↦ 0 (R4b where its concat clauses dispatch) |
| `depthDrain` | `concatDrain` | `[]` ↦ 0; `o ∷ q` ↦ `depthInner fuel concatᵒ allNid κ id now o sched₀ st₀ ⊔ depthDrain … q sched₁ st₁` — overapproximate the `if done` (R4a) |
| `depthFin` | `innerFinish` | merge/switch/exhaust/catch-all ↦ 0; concat with `just (concat-st {w} q act od)` ↦ `depthFinConcat … (w ≟ᵗ s)` (R4b): `yes refl` ↦ **`suc (depthDrain fuel allNid κ id now q sched st)`**, `no _` ↦ 0 |
| `depthReact` | `innerReact` | `false` ↦ 0; `true` ↦ `depthFin … (lookupNode allNid (EvalSt.nodes st))` — ignore the `aliveThroughᶠ` test (R4a) |
| `depthFrame` | `stepFrame` | map-f/scan-f/take-f ↦ 0; from-inner ↦ `depthReact …`; thru-outer ↦ **`suc (depthWalk fuel op nid κ id now vals sched st)`** |
| `depthBurst` | `pushBurst` | `[]` ↦ 0; `em ∷ ems` ↦ `depthFrame … (proj₁ sp) (proj₂ (proj₂ sp)) sched st ⊔ depthBurst … ems sched₁ st₁` (the lets of :1298-1306) |
| `depthFold` / `depthDispatch` / `depthShareGo` / `depthChain` | `foldPath` / `dispatchShare` / `shareGo` / `chainStep` | mirror their bodies down to `depthFrame` (:1521-1600) — needed so the downstream caps heads can supply `stepFrame-caps` |

### The threading

Every caps head that transitively calls `stepFrame-caps` gains ONE hypothesis, placed
beside `nest … ≤ bud`: **`depthX ⟨its evaluator args⟩ ≤ dep`**, argument name `dpt`.
That is the 13-member clique (`subscribeE`, `subscribeAll`, `subscribeInner`, `thruWalk`,
`thruConsume`, `concatDrain`, `stepFrame`, `pushBurst`, `innerFinish`, `innerReact`,
`subscribeE-input`, `sharedSlot`, `sharedConnect`) plus the downstream four (`foldPath`,
`dispatchShare`, `shareGo`, `chainStep`). `retagEvents-caps` and `evalTms-caps` gain
nothing.

Supply mechanics — every call site is one of exactly three moves:

- **(a) PROJECTION** (nearly every site): the caller's `dpt` reduces definitionally (the
  mirror clause equation, in the caps clause's own pattern context) to a `⊔` of callee
  mirrors; project with `≤-trans (m≤m⊔n …) dpt` / `≤-trans (n≤m⊔n …) dpt`.
- **(b) THE TWO SPENDS**: `stepFrame-caps` thru-outer and `innerFinish-caps` concat case
  on `dep`. At `zero`, `dpt` is `suc … ≤ 0` — absurd; close the clause with it. At
  `suc dep′`, peel one `s≤s` off `dpt` and hand the callee `dep′` with the peeled proof.
- **(c) THROUGH A WITH**: when the caps clause `with`s a scrutinee the mirror
  value-dispatches on (the `w ≟ᵗ s`, take's count, input's slot), **add `dpt` to the
  `with` line** so its type refines along with the goal. This is the design's one
  elaboration risk — Probe A settles it before anything is ground.

### Closing the two sites — in the SAME pass as the threading; do not split it

- **2280** (`stepFrame-caps` thru-outer, `dep = zero`): becomes absurd by (b). DELETE the
  clause's body. The `suc dep′` clause at :2293-2309 is already green and untouched.
- **1834** (`innerFinish-caps` concat, `yes refl`): case `dep` by (b). In the `suc dep′`
  branch, call `concatDrain-caps` at `dep′` and the REFRESHED budget — the strict level
  `sizeAt (Caps.cSize c) (suc j)`, exactly as the thru-outer `suc` clause hands
  `thruWalk-caps`. The queue's mList bound needs a strict analog of `obsList→mList` —
  new lemma **`obsList→mList-strict`** in Caps-Face, same mechanism as
  `valsCaps→mList-strict`. Land the level conjunct by the same `frame-step` + `walk-index`
  dance as :2303-2309, with the queue's length conjunct (`wnLen`, already extracted at
  :1839) feeding `walk-index`. If `frame-step`'s premise shape does not meet the drain's
  report the way the thru-outer clause's met the walk's, **STOP and report the goal
  verbatim** — do not invent arithmetic.
- Then DELETE `level-TEMP` (the declaration AND its pass memo at ~855-896);
  `grep -rn "TEMP" agda/src` must return zero (the BARE word). **Step C is then done.**

### The faces (item 3 — the NEXT leg, not this one)

`innerFinish-concat-face` and `thruOuter-face` (Caps-Face ~6190) gain the same hypothesis
(`depthFin … ≤ d` resp. the thru-outer form `suc (depthWalk …) ≤ d`). They are postulates,
so amending their statements is free; their ground consumers (`innerFinish-face`,
`stepFrame-face`, `Walk-Hyps.sf-step`) thread it upward. The chain terminates at the
machinery feeding the postulated `subscribeE-walk` (Measures:6204, **zero use sites**) —
amend its statement too and stop there. With the hypothesis in place, the faces discharge
from the now-complete clique lemmas; that is item 3's brief.

### What the top will owe, later — record it, do not pay it now

`dep` remains instantiated NOWHERE after this unit. The hypothesis SURFACES the debt the
tree already recorded (`Rx/Evaluator.agda:710-718`: "the story index dominates the depth
the instant actually reaches … owed by the signature pass. Reported, not assumed"). When
items 2/1 wire an instantiation (`capsAt` reads `d := capsH e sl id`,
`Verify-Budget-Sufficient/Caps.agda:449-458`), the obligation lands as ONE named
statement, shaped

    depthE gas e κ id now sched st ≤ capsH e sl id     -- at the instant's actual entry args

State it as a postulate FIRST when that day comes (outside-in), then attack it. Two known
facts about it: (i) the gas bridge — `depthE … ≤ gas height`, provable by the peel
discipline (`Rx/Evaluator.agda:672-695`) — is NOT sufficient, because the gas sits one
blowH story above `capsH` (:710-717); (ii) any real proof must account for DELIVERIES, not
just static nesting (Nest-Count-Probe: stories per instant = deliveries × nesting).
**THE RISK OF THE WHOLE DESIGN LIVES HERE**: if `depthE ≤ capsH` is ever refuted, then
`capsAt`'s `d`-instantiation is wrong and the measure family's top wiring changes. That is
a STOP-AND-DISCUSS event, same severity as a spec question.

### Steps 1-4 are DONE and green (2026-08-05). Only the Subscribe-Face pass remains.

- **Probe A — `agda/probe/Depth-Mirror-Probe.agda`, green first try.** A mini-evaluator
  with a `Dec` dispatch and a `Maybe` scrutinee, its mirror per R1-R5, and a fake caps
  family exercising every supply move. Settles all four elaboration questions, including
  that the mirror's termination needs NO pragma and that `with scrutinee | dpt` refines
  `dpt`'s type in the branch.
- **`Verify-Budget-Sufficient/Caps-Depth.agda` — WRITTEN, green, 5.2 s cold.** 20 mirror
  heads, termination accepted with no pragma. Read its head comment before touching it.
- **`walk-room` in `Caps-Chain` — PROVEN.** This was the design's one open risk (the
  1834 closure needed one level MORE than `concatDrain-caps` reports). The room is the
  unused payload slot: the queue is bounded by `widAt S W j` while `frame-step`'s premise
  admits `suc (widAt S W j)` payloads, and one walk payload is worth ≥ one level
  (`sIterD-sadd` + `sLvlD-infl`). **The stop condition is cleared.**
- **`obsCaps→nest-strict` / `obsList→mList-strict` in `Caps-Face` — PROVEN** (the queue
  mirror of `valsCaps→mList-strict`). Caps-Face green.
- **Supply census — DONE**, and it found **no call-graph or call-argument mismatch**
  between the caps clique and the evaluator, and that all 17 heads reach
  `stepFrame-caps`. Every local `where` name a supply depends on was checked term-by-term
  against the mirror (`sp`, `sd₁`/`st₁`, `st₀`/`st₁`, `res`, `step`, `TC`): all match.

**WHY `dep` MUST STAY A UNIVERSALLY QUANTIFIED PARAMETER — do not "simplify" this.**
The tempting alternative is to delete the `dep` parameter and write each head's conjunct
at the computed `depthX <args>` directly; then the thru-outer clause's transformer is
literally `fLvlD S W (suc (depthWalk …)) j` and site 2280 vanishes with no case split at
all. It is worse. With a uniform opaque `dep` the transformer NEVER changes across a call,
so a supply is exactly one `⊔`-projection. With `dep` computed, the caller's transformer
sits at `depthX <caller args>` and the callee reports at `depthX <callee args>`, so every
one of the ~37 sites needs a `d`-monotonicity lift ON TOP OF the same projection. Strictly
more work, in the most expensive module. Recorded because the idea looks like a
simplification and is not.

### THE REMAINING WORK: the Subscribe-Face pass, in TWO stages

Staged deliberately. Stage A is ~100 mechanical edits with no new mathematics; stage B is
two clauses. If they go in together, a failure in either is debugged against a 44-minute
build with the other's diff in the way. Stage A leaves `level-TEMP` in place at its two
sites, which is safe here because the threading contains no descent for a weak hole to
hide — every supply below is an exact projection.

#### Stage A — thread `dpt`. Three mechanical parts.

**A1. Add ONE hypothesis to each of the 17 signatures**, as the LAST hypothesis,
immediately before the `let r = … in Σ …`. Argument name `dpt`. The hypothesis is
`depthX <the evaluator arguments that head's own `let r = …` passes> ≤ dep`:

| head | new hypothesis |
|---|---|
| `subscribeE-caps` | `depthE g b κ bid now sched st ≤ dep` |
| `subscribeAll-caps` | `depthAll g op ns b κ id now sched st ≤ dep` |
| `subscribeInner-caps` | `depthInner g op allNid κ id now o sched st ≤ dep` |
| `thruWalk-caps` | `depthWalk g op nid κ id now vals sched st ≤ dep` |
| `thruConsume-caps` | `depthConsume g op nid κ id now o sched st ≤ dep` |
| `concatDrain-caps` | `depthDrain g allNid κ id now q sched st ≤ dep` |
| `stepFrame-caps` | `depthFrame g id now f κ vals fin sched st ≤ dep` |
| `pushBurst-caps` | `depthBurst g id now f κ str sched st ≤ dep` |
| `innerFinish-caps` | `depthFin g op allNid inst κ id now vals sched st (lookupNode allNid (EvalSt.nodes st)) ≤ dep` |
| `innerReact-caps` | `depthReact g op allNid inst κ id now vals sched st fin ≤ dep` |
| `subscribeE-input-caps` | `depthE g (input i) κ id now sched st ≤ dep` |
| `sharedSlot-caps` | `depthShSlot g i d κ id now sched st ≤ dep` |
| `sharedConnect-caps` | `depthConn g i d κ id now sched st ≤ dep` |
| `foldPath-caps` | `depthFold sf gas id now envSrc path vals evs fin sched st ≤ dep` |
| `dispatchShare-caps` | `depthDisp sf gas id now i vals fin sched st ≤ dep` |
| `shareGo-caps` | `depthShareGo sf gas id now i vals fin ps sched st ≤ dep` |
| `chainStep-caps` | `depthChain id a path sched st ≤ dep` |

Import them: add `open import Verify-Budget-Sufficient.Caps-Depth` with those 17 names
plus nothing else (`Caps-Depth` imports `Rx.Evaluator` only, so there is no cycle).

**A2. Add a `dpt` binder to each of the 60 top-level clause LHSs.** `with`-continuation
clauses (`... | pat = ...`) take NO new binder — the binder comes from the parent LHS.
Put `dpt` last, in the same position as in the signature. The 60 lines are exactly the
output of

```bash
grep -n "^subscribeE-caps \|^subscribeAll-caps \|^subscribeInner-caps \|^thruWalk-caps \|^thruConsume-caps \|^concatDrain-caps \|^stepFrame-caps \|^pushBurst-caps \|^innerFinish-caps \|^innerReact-caps \|^subscribeE-input-caps \|^sharedSlot-caps \|^sharedConnect-caps \|^foldPath-caps \|^dispatchShare-caps \|^shareGo-caps \|^chainStep-caps " agda/src/Verify-Budget-Sufficient/Subscribe-Face.agda | grep -v " : ∀"
```

Note `sharedSlot-caps`'s zero clause already ends in an absurd pattern `()` — its `dpt`
goes BEFORE that `()`.

**A3. Supply `dpt` at the 37 call sites.** Verbatim `dpt` at 20 of them, one projection at
13, and four need the scrutinee refined. `PL = ≤-trans (m≤m⊔n _ _) dpt` (left of a `⊔`),
`PR = ≤-trans (m≤n⊔m _ _) dpt` (right). Note the stdlib name is `m≤n⊔m`, NOT `n≤m⊔n`.

| line | callee | supply |
|---|---|---|
| 1023 | `subscribeE-caps` | `dpt` |
| 1147, 1209 | `subscribeE-caps` | `dpt` |
| 1302 | `sharedConnect-caps` | `dpt` |
| 1341, 1381, 1507 | `subscribeInner-caps` | `dpt` (merge/concat/exhaust — the mirror ignores those node reads, R4a) |
| 1465 | `subscribeInner-caps` | **(c)** add `dpt` to the clause's existing `with lookupNode nid (EvalSt.nodes st)` line; in the `just (switch-st cur od)` branch the refined `dpt′` is verbatim |
| 1583 | `thruConsume-caps` | `PL` |
| 1590 | `thruWalk-caps` | `PR` |
| 1644 | `subscribeInner-caps` | `PL` |
| 1697 | `concatDrain-caps` | `PR` |
| 1842 | `concatDrain-caps` | **(c)** `dpt` onto the existing `with … | w ≟ᵗ s` line; then in `yes refl`, supply `≤-trans (n≤1+n _) dpt′` (stage A only — stage B replaces this) |
| 1956 | `sharedSlot-caps` | **(c)** `dpt` onto the existing `with Sched.slots sched i`; in the `shared d` branch `dpt′` is verbatim |
| 2158 | `innerFinish-caps` | `dpt` (the liveness `with` is overapproximated, R4a) |
| 2258 | `innerReact-caps` | `dpt` |
| 2282, 2313 | `thruWalk-caps` | `≤-trans (n≤1+n _) dpt` — the mirror's thru-outer arm is `suc (depthWalk …)`, so dropping the `suc` is the whole supply in stage A |
| 2428 | `stepFrame-caps` | `PL` |
| 2436 | `pushBurst-caps` | `PR` |
| 2612 | `subscribeE-caps` | `PL` |
| 2620 | `pushBurst-caps` | `PR` |
| 2689 | `subscribeE-input-caps` | `dpt` |
| 2812 | `subscribeE-caps` | `PL` |
| 2823 | `pushBurst-caps` | `PR` |
| 2895, 2906 | `subscribeE-caps`, `pushBurst-caps` | **(c)** `dpt` onto the existing `with evalTm cnt`; then `PL` / `PR` off the refined `dpt′` in the `suc k` branch |
| 2990 | `subscribeE-caps` | `PL` |
| 3002 | `pushBurst-caps` | `PR` |
| 3028, 3033, 3038, 3043 | `subscribeAll-caps` | `dpt` |
| 3096 | `subscribeE-caps` | `dpt` |
| 3272 | `dispatchShare-caps` | `dpt` |
| 3289 | `stepFrame-caps` | `PL` |
| 3296 | `foldPath-caps` | `PR` |
| 3327 | `shareGo-caps` | `dpt` |
| 3350 | `shareGo-caps` | `PL` (the mirror reports the cancelled tail as the FIRST of three, so this needs no `with`) |
| 3364 | `foldPath-caps` | `≤-trans (m≤m⊔n _ _) (≤-trans (m≤n⊔m _ _) dpt)` |
| 3370 | `shareGo-caps` | `≤-trans (m≤n⊔m _ _) (≤-trans (m≤n⊔m _ _) dpt)` |
| 3401 | `foldPath-caps` | `dpt` |

Then: detached `make agda && make bug-cache` (~44 min dirty), green, commit, push.

#### Stage B — close the two sites and delete `level-TEMP`.

- **2280** (`stepFrame-caps`, `dep = zero`, thru-outer): DELETE THE WHOLE CLAUSE. Its
  `dpt` is `suc (depthWalk …) ≤ zero`, uninhabited, so the clause is absurd — replace the
  `c zero bud j …` clause with nothing and let the (renamed) `suc dep′` clause be the only
  thru-outer clause, matching `c (suc dep′) …`. Coverage then requires the absurd clause
  to remain as `stepFrame-caps c zero bud j g id now (thru-outer op nid) κ vals fin sl
  sched st 2≤S 1≤R slEq slC slSz inv fS pS lC vC fb ()` — one line, no body.
- **1834** (`innerFinish-caps`, concat `yes refl`): case `dep`. **The mechanism is a
  NESTED with, verified in `Depth-Mirror-Probe` § 4** — the clause reaches `yes refl`
  through a `with` it already had, and `CD` (whose depth must descend) is bound in that
  branch's own `where`, so the split cannot be delegated to a helper head that matches
  `dep` in its LHS. Write `... | yes refl | dpt′ with dep | dpt′` and then
  `... | zero | ()` / `... | suc dp | s≤s dpt″ = …`; both scrutinees must be re-listed so
  the tail hypothesis refines. At `zero`, `dpt′` is `suc (depthDrain …) ≤ zero` — absurd,
  one line. At `suc dp`, call `concatDrain-caps`
  at `dep′` and at the REFRESHED budget `sizeAt (Caps.cSize c) (suc j)` (it reports at
  `suc bud`, and `frameBud c j` IS `suc (sizeAt (cSize c) (suc j))` definitionally, which
  is the budget `frame-step` demands), with the queue's mList bound from the new
  `obsList→mList-strict` in place of `mList?-widen … (obsList→mList …)`, and peel `dpt′`
  with `s≤s`. Then the level conjunct is

  ```agda
  frame-step (Caps.cSize c) (Caps.cWid c) dep′ j 0 (suc j′) 2≤S z≤n
    (subst (λ x → x + suc j′
                    ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep′
                        (frameBud c j) (suc (Caps.cWid (frameStep j c))) x)
           (sym (+-identityʳ j))
           (walk-room (Caps.cSize c) (Caps.cWid c) dep′ (frameBud c j)
                      (length q) j j′ 2≤S
                      (≤ᵇ⇒≤ (length q) (Caps.cWid (frameStep j c)) (T-to wnLen))
                      (proj₂ (proj₂ (proj₂ (proj₂ CD))))))
  ```

  `wnLen` is already extracted in that clause's `where` (the queue's length conjunct off
  `widNode`). `frame-step`'s conclusion is `j + (0 + suc j′)`, and `0 + suc j′` reduces to
  the reported witness `suc j′`.
- Then DELETE `level-TEMP` (declaration at ~896 AND its pass memo above it);
  `grep -rn "TEMP" agda/src` must return zero — the BARE word.
- `make agda && make bug-cache` green → commit → push → merge to main → **Step C DONE**,
  ledger still 5, item 3 next (its brief is the faces paragraph above).

### Refuted candidates — do not re-propose

Budget inheritance from entry size (`Nest-Budget-Probe` § 3); bare positivity
(`Mu-Nest-Probe` § 1); term-syntax measure without residue (`Mu-Nest-Probe` § 2);
gas-height hypothesis (undischargeable at `capsAt`'s `d` — `Rx/Evaluator.agda:710-717`,
this ruling); closing 2280 from the walk's report (`Dep0-Walk-Probe` § 1 — strict
overshoot, structural).

---

## The Goal & Structure

**Ultimate goal:** Fully machine-checked proof, `agda/src/Verify-Batch-Simultaneous/The-Proof.agda` discharged, **no postulates, everything typechecks**. The work is decomposed into three tiers:

### Tier 1: Postulate Ledger Discharge (5 remaining, originally ~50)
**Done:** cascadeGo-charge framework, full receipt/queue-length quantification apparatus, supply proofs, Unit 2 (all TEMP scaffolding deleted), Step C Units 0–2.

**Current (item 4):** Step C — Unit 3 (the depth ruling above) is the remaining work.

**Remaining after Step C:**
- **Item 3** — discharge the two Caps-Face faces (`innerFinish-concat-face`, `thruOuter-face`), taking the ledger from 5 to 3. Brief: the faces paragraph in Unit 3 above.
- **Item 2** — discharge subscribeE-walk postulate (Measures:6204; its own comment says it is blocked on a "reachability" bridging lemma, not a state invariant).
- **Item 1** — discharge subscribeE-wet + cascadeGo-wet + Wet.agda's remaining postulates. Both are proof-ASSEMBLY problems against machinery that already exists and is proven (`register-INV`, Wet:317-334); neither is blocked on the depth invariant (verified against their own comments, Wet:4276-4334).

**Tier 1 is the authorization boundary:** once ledger reaches 0, the design session has standing permission to delegate Tier 2 work with full autonomy (no more ruling/stop conditions, purely mechanical grinding).

### Tier 2: Verify-Well-Formed (8 postulates)
Depends on Tier 1. Batch-online also sits here. Begins after Tier 1 closes.

### Tier 3: Theorem Ring (30 postulates across 4 modules)
Readme, Time, Evaluator, Provenance. Depends on Tiers 1 and 2. Lowest priority.

---

## Container Resilience: Rollbacks & Usage Limits

**Observed failures (2026-08-04):**

1. **Container snapshot rollback (twice):** The execution environment rolled back to an August 1 snapshot mid-work, wiping the local repo and running processes. Recovery: immediate re-sync from GitHub (`git fetch origin; git checkout -B branch origin/branch`). **All work was safe on origin** — nothing was lost that had been pushed.

2. **Usage limits (twice):** weekly and session limits hit mid-work; a worker died with in-flight edits lost (never pushed).

**Standing practice:**
- **Push per green batch.** Unpushed work is at risk (rollback, usage limits).
- **Detect rollback via commit dates:** before any edit, `git log -1 --format=%ci`. If it's days old but the transcript claims recently-pushed commits, re-sync immediately.
- **Handle usage limits gracefully:** the error quotes a reset time; schedule a self-check-in 5 minutes after it rather than reviving immediately.

---

## The Probe-Before-Grind Law

Any syntax/elaboration question you haven't used in THIS file → write a ≤10-line probe in
`agda/probe/` BEFORE incorporating it into the big module. Probes are ephemeral (deleted
after the proof, not shipped), but they save hours of big-module rechecks. Proven
repeatedly: `with … in` binding, weak-vs-precise hole shapes, the chain-index currency,
and the Dep0 walk refutation — each settled in seconds what a Subscribe-Face recheck would
have charged 44 minutes for.

### Two cheap gates BEFORE you spend a real build slot

Both learned the expensive way on 2026-08-05, when Stage A's first build burned time on a
scope error and then on an inference failure:

1. **`agda --only-scope-checking <module>` — 11 s on Subscribe-Face.** Catches the entire
   scope class: not-in-scope, multiple-definitions, a missing `using` entry, and the trap
   that an **unsignatured `where` definition must textually PRECEDE its uses** (Agda has no
   forward reference for them). A `make agda` finds these too — 40 s in if you are lucky,
   or after the whole SCC if you are not. Run the gate first, every time.
   Afterwards **delete the module's `.agdai`** (`_build/…/<Module>.agdai`) before the real
   build, so a scope-only interface cannot be mistaken for a checked one.
2. **Solo-check the cheap module you just edited.** Caps-Depth is 5.4 s. If a lemma you are
   about to depend on does not compile alone, nothing downstream is worth starting.

And a reporting trap, not a gate: **the background-task notification reports the WRAPPER's
exit code, not the build's.** On 2026-08-05 a notification said "exit code 0" for a build
whose log read `MAKE_AGDA_EXIT=2`. Never believe a notification, a green-looking tail, or a
zero error-line count. Read the `EXIT=` line out of the log, every time.

---

## Standing Rules (Carry These Forward)

### Design & Proof Structure
- **Spec is gospel.** Impl ≠ spec → impl is wrong. Only touch spec after asking.
- **Outside-in assembly:** state full signatures and end goals first with postulate bodies, then prove leaves-first. Never prove pieces before their assembly exists.
- **Σ-witness law:** before adding a conjunct, check it is not upward-closed in the witness — if it is, it's vacuous.
- **Survey the whole hole-set before discharging any of it** (census → classify → prove; blocked bucket first).

### Editing Discipline
- **Hand-edit, no scripts.** Agda clause-LHS syntax cannot be parsed line-by-line.
- **Weak TEMP holes** (`∀ {x y} → x ≤ y`) unify; precise shapes may not.
- **Descent split only at the reporting clause** — the transformer families pass `k` through (family property).

### Commit & Push Protocol
- **Green `make agda && make bug-cache` before each commit.** No exceptions.
- **Push per green batch.**
- **Commit messages in repo voice.** No worker IDs, no meta-commentary.

### Stop Conditions
- **Two failed distinct attempts on one site → STOP with the goal type verbatim.**
- **Spec ambiguity → surface with a TypeScript rxjs example**, defer to naive plain rxjs semantics.
- **Impossibility pair discovered → STOP, report immediately. Do not act on it.**
- **`depthE ≤ capsH` refuted (Unit 3's deferred obligation) → STOP-AND-DISCUSS**, same severity as a spec question.

### Build & Environment
- Long Agda checks (>600 s) use the Bash tool's **`run_in_background: true`** (on this laptop `setsid` does not exist and detached writes under `/private/tmp` are denied). Write agda's own `$?` into the log (`agda … > log 2>&1; echo "AGDA_EXIT=$?" >> log`) and grep THAT — never trust a pipe's or wrapper's exit code.
- **Pin the working directory in every build command** — `cd agda/` for raw `agda`, repo root for `make`; guard with `ls Makefile &&` or `ls src/… &&`. Verify the run actually ran (`grep -c Checking` ≥ 1, no `Total 0ms`) before believing anything it says.
- **Interfaces are cached per module**: a green tree plus one new leaf module is ~1 min of `make agda`. The full 35–40 min applies when Subscribe-Face (~44 min dirty, ~6.9 GB) or Wet (~14–18 min) is dirty. At most TWO heavyweight checks at once.
- **`touch` does not dirty a module** (invalidation is by content); the build is `--safe`, so no check-disabling pragmas exist.

---

## Files of Interest

### Core Working Files (Tier 1, item 4 — Unit 3)
- **`agda/src/Verify-Budget-Sufficient/Subscribe-Face.agda`** — ~3305 lines, **~44 min and
  ~6.9 GB per dirty check**. Iterate in probes, land in verified batches, never guess a
  projection path. Holds 18 `-caps` definitions; the true SCC is THIRTEEN (the other five
  stratify out). The clique's signature block starts at `subscribeE-caps` (~899); the
  `level-TEMP` postulate and its pass memo sit at ~855-896. **Two `level-TEMP` sites
  remain: 1834 (innerFinish concat) and 2280 (stepFrame thru-outer at `dep = zero`)** —
  Unit 3's targets. The thru-outer `suc dep′` clause (:2293-2309) is the model for both
  closures.
- **`agda/src/Verify-Budget-Sufficient/Caps-Depth.agda`** — TO BE CREATED by Unit 3: the
  depth mirror (rules R1-R7 above).
- **`agda/src/Verify-Budget-Sufficient/Caps-Chain.agda`** — the composition gate: clause
  shapes (`walk-step`/`frame-step`/`op-step`/`op-step-eval`/`op-step-mu`, `inner-step`,
  `connect-step`, …), index conversions (`walk-index`, `index-mono`, …), `chain-desc`.
  Non-SCC, ~6 s solo — new non-mutual arithmetic goes here.
- **`agda/src/Verify-Budget-Sufficient/Caps-Nest.agda`** — the budget measure
  `nest e sl cs = syncSizeᵉ e + resid sl cs` and its per-constructor steps.
- **`agda/src/Verify-Budget-Sufficient/Caps-Sadd.agda`** — superadditivity family,
  `walk-step-lift`, `walk-step-suc`.
- **`agda/src/Verify-Budget-Sufficient/Caps-Face.agda`** — the two ledger postulates
  (`innerFinish-concat-face`, `thruOuter-face`, `postulate` block at ~6190) and the face
  machinery (`FrameFace` at 4578); `valsCaps→mList-strict` lives here and is the model for
  Unit 3's `obsList→mList-strict`.

### Key probes (all in `agda/probe/`)
- `Dep0-Walk-Probe.agda` — the machine refutation that forced Unit 3's ruling.
- `Mu-Nest-Probe.agda`, `Nest-Budget-Probe.agda` § 3, `Nest-Count-Probe.agda` — the
  refuted-candidate record cited by the ruling.
- `Chain-Index-Probe`, `Chain-Supply-Probe`, `Chain-Descent-Probe`, `Sub-Charge-Probe` § 5
  — Step C's settled shape decisions.

### Build & Test
- **`Makefile`:** `make agda` (full check), `make bug-cache` (type-level unit tests), `make test`.
- **`agda/src/Implementation/Unit-Test.agda`** via `make bug-cache`; append with `scripts/gen-unit-tests.sh`.

---

## Contact & Authority

**Design session:** reviews worker reports, merges green work to main, makes rulings,
launches the next leg. Anthony supervises the campaign. **Workers (Sonnet 4.6):** execute
the assigned leg, commit+push per green batch, report plainly (numbers including
failures), stop on the standing conditions. **Tier 1 completion** is the threshold for
full worker autonomy on Tier 2.
