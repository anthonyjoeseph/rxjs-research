# PROOF-STATE — the canonical design-state index

**Read this first, every session, before any proof work.** Update it in the same
commit as every ruling, every postulate added or discharged, every gap opened or
closed. Detailed records stay in source comments — this file is pointers, not
copies. If a pointer and its source comment disagree, the source comment wins;
fix the pointer.

> **THE WIRING LAW GOVERNS EVERYTHING BELOW — see CLAUDE.md § "The wiring law:
> NEVER LEAVE A PROOF HANGING".** Never prove something and leave it unwired.
> Extend the consuming assembly first (postulating its other gaps), land both in
> one commit, and change a signature rather than leaving a piece that will not
> plug in. Every gap is a typed postulate; every definition and postulate is
> consumed, transitively, by a top-level theorem. No invisible debt, no dead
> code, no gap that lives only in prose. `make wiring` is the acceptance test —
> zero orphans outside its two documented exempt families. This document's own
> history is the argument for the law: it has been wrong four times in one day,
> in the reassuring direction every time, and each error was a status claim no
> typechecker was enforcing.

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
     ├─ budget-sufficient                      Wet.agda — PROVEN from:
     │   ├─ burst-wet    ← subscribeE-wet      [P1]
     │   ├─ cascade-dry  ← cascadeGo-wet       [P2]
     │   └─ drain-dry                          proven
     └─ THE WELL-FORMEDNESS BRANCH             its OWN 5 postulates — see [W1-W5]
```

**THERE ARE TWO BRANCHES, NOT ONE.** An earlier version of this file said "the
entire campaign reduces to the postulate ledger below; nothing else stands
between the repo and the finish line", listing only the budget-sufficiency
postulates. **That was wrong.** `evaluate-well-formed` has its own postulate set
in `Verify-Well-Formed.agda`, every one of which is as load-bearing as P1/P2 —
they were simply never traced, because the chain diagram stopped at
`budget-sufficient`. Corrected 2026-08-05, by the same grep-for-consumers habit
this file preaches; the author of the claim was the one who broke it.

## The well-formedness branch (critical path, never assessed)

There are **EIGHT**, not five. (The design session's first count grepped only the
first declaration in each `postulate` block and missed three. Censused properly
2026-08-05.) Each has exactly one consumer — no orphaned postulates here.

| # | Name | Line | Bucket |
|---|------|------|--------|
| W1 | `subscribeE-wf` | 1093 | (d) partly — base/map/scan/take clauses ALREADY PROVEN (see below); `*All` wrap clauses blocked on `merge-cert`; `pushBurst-wf`/`stepFrame-burst` don't exist yet |
| W2 | `root-done-plumbed` | 1166 | (d) blocked on `merge-cert` |
| W3 | `root-caches` | 1181 | (d) blocked on `merge-cert` |
| W4 | `cut-owed` | 3656 | **(c) — the easiest thing in this branch.** Self-contained `Owed`-table algebra, independent of every blocker |
| W5 | `stepFrame-wf-inner-concat` | 3676 | (c) concat's drain grows the registry; re-establish `FoldInv`. Independent of `merge-cert` |
| W6 | `stepFrame-wf-outer` | 3685 | (d) blocked on `merge-cert` |
| W7 | `dispatchShare-wf` | 3697 | (c) share fan-out mutual recursion — but must be RE-STATED with a `FoldOut` conclusion before it can feed `mid-step` |
| W8 | `mid-step` | 4541 | (d) blocked on the `FoldOut` refactor below |

**BLOCKER A — `merge-cert` (a GAP-4-shaped dead end with NO existing rescue).**
Blocks W1's wrap clauses, W2, W3, W6. A first candidate invariant
(`merge-st k at nid ⇒ k ≡ countRegsUnder nid registry`) is **machine-refuted by
three independent counterexamples** (Verify-Well-Formed.agda:3410-3429); a second
route ("derive from `Inv.done-plumbed`") is marked **STRUCTURALLY DEAD** (3498) —
its premise is vacuous exactly when the obligation is needed. The corrected route
is identified but explicitly OPEN (3459-3497): a one-directional, liveness-aware
`merge-cert` whose *exact statement is the remaining design point*. Grepped for
`merge-cert`/`countRegsUnder`/`aliveThrough` repo-wide: **zero hits outside this
file.** Unlike the budget branch's rescues, this one is genuinely unsolved.

**BLOCKER B — the `FoldOut` refactor, and a LYING COMMENT.** Blocks W8.
`mid-step`'s header says `FoldOut` is "deliberately NOT yet stated" — **it IS
stated**, a full 6-field record at 3527-3597, and `foldPath-root-out` (4138) is a
real proof of it for the `root` path. But `foldPath-wf`'s actual signature
(3874-3882) still returns only `Σ ProtocolSt …` with **no `FoldOut`**, so the
plan to thread it lives only in prose. Consequences: `foldPath-root-out` is an
ORPHAN (instance 5 of the wiring-law failure), and W8 cannot be assembled until
`foldPath-wf`'s signature CHANGES — which cascades into re-*stating* W5, W6, W7.
Textbook case of the wiring law: change the signature first.

**Already proven but unwired here (instance 6):** `subscribeE-map-wf` (1916),
`subscribeE-scan-wf` (1999), `subscribeE-take-wf` (3056) — roughly half of W1's
case split is DONE. This one is *sanctioned* (the assembly was stated first, as a
postulate, per outside-in) but scope W1 knowing it.

**Cost:** the module is 5348 lines with no explicit `mutual` blocks — but that is
NOT a safety signal: Subscribe-Face also has none and costs ~44 min. Most of this
file's heavy obligations are still postulates, so today's cheap recheck is
**not** representative; expect a Subscribe-Face-shaped cost increase as they get
real bodies. It imports `budget-sufficient` one-way, so editing it does not
force a Wet/Subscribe-Face recheck.

**Cheapest de-risking experiment:** probe the corrected `merge-cert` statement
(3483-3486) against the three adversarial shapes that killed candidate one —
multi-source inner, inner-completes-before-outer, cut-through on an inner — in
the style of `agda/probe/Cut-Caches-Probe.agda`. If it survives those, it is
very likely the right statement; if not, this branch needs a design ruling
before W1/W2/W3/W6 can be attempted at all.

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
| S3 `dry-tick` | Caps-Bridge.agda | P2's dry half. **BLOCKED on THE ANCHOR PROBLEM** (below) — NOT a wiring job. Its own header comment claiming independence from GAP 4 is WRONG; fix it when next editing that file. |
| `depth-compositional` | Depth-Bound.agda | `depthE ≤ sizeᵉ b + pathLen κ + storeNestMax` (structural induction over the mirror). CENSUSED 2026-08-05: scope is 16 heads, not 19 (the delivery family — depthFold/depthDisp/depthShareGo/depthChain — is out of scope). The real remaining work is a state-growth conjunct, not a lemma about the mirror itself — every clause feeds `depthBurst` the state from the REAL `subscribeE` run, while the bound's RHS reads the entry state, so the induction needs `storeNestMax` at the evolved state dominated by the entry's bound. Details, including the ruling to prove this as a second conjunct of the same induction rather than a separate family, are in Depth-Bound.agda's header. |

(B2, S1 `fn-tick`, S2 `slots-tick`, and `storeNest-capped` are PROVEN — landed
in Caps-Bridge.agda and Depth-Bound.agda respectively, no longer postulates.)

## Wiring rulings (2026-08-05) — run `make wiring` for the live list

**PRIORITY (Anthony, 2026-08-05): deletion matters, but NOT ignoring usable work
matters more.** Read the clusters below as a RECOVERABLE-ASSETS list first and a
cleanup list second. 87 proven definitions sitting unused is 87 pieces of work
already paid for; the question to ask of each is "what would it take to spend
this, and what does spending it unblock" — not "should this go."

`scripts/check-wiring.py` mechanises CLAUDE.md's wiring law. Current numbers:
**55 postulates** (31 with consumers, 22 top-line claims, **2 truly orphaned**)
and **87 orphaned proven definitions**. Do not re-derive this list by hand or by
memory — run the target. Rulings by cluster, made by the design session after
four bad worker verdicts on exactly these calls (see the cautions below):

1. **EXEMPT — `*-absurd` refutation witnesses (7).** A machine-checked `… → ⊥`
   is the durable form of "this route is dead"; its consumer is the design
   process. Allowlisted by pattern in the script. **A worker classified these
   "archive, not live infrastructure" and was OVERRULED**: two of them
   (`caps-frame-boundary-absurd`, `round3b-ledger-reset-absurd`) are what proved
   the anchor problem real on 2026-08-05, saving a wasted grind.
2. **EXEMPT — top-line semantic claims (22)**, the `readme-*` family plus
   `Evaluator-/Provenance-/Time-/Batch-Theorems`. Nothing consumes them because
   they ARE the claims. **They are a SECOND LEDGER — unproven, off the critical
   path — not dead weight.** Still counted in the postulate total on purpose:
   excluding them made the headline number lie in the reassuring direction.
3. **MISSING WIRE — the anchor cluster.** `mu-edge`, `hop-edge`,
   `connect-edge`, `unconn-keeps`, `hop-step-gives/-needs`,
   `sharedConnect-unconn`, `obs-slot-shared`, `share-live-novals`,
   `share-spent-novals`. **KEEP ALL.** A worker called the Keeps-Ring half dead
   weight, reasoning "P5 is orphaned, so machinery targeting P5 is dead" —
   that conflates a dead ROUTE with dead CONTENT. Note
   `sharedConnect-unconn` is machine-level (quantifies over `Gas`/`Sched`/
   `EvalSt`) where `unconn-insert` is abstract list arithmetic; they are not
   interchangeable, and the machine-level one is exactly what wiring the connect
   edge to the evaluator will need.
4. **MISSING WIRE — the Caps-Bridge/Depth-Bound tower.** `sub-charge`,
   `depth-capped`, `cascade-wet-via-caps`, `B1-cSize≡sizeCapAt`. The named next
   step (wire `cascade-wet-via-caps` into `cascade-dry`).
5. **MISSING WIRE, and a CHEAP WIN — the proof is written TWICE.**
   `frameSz?-⊑`, `residAt-connected`, `prepend-fits`, `entry-to-index`,
   `shareGo-cons-N`, `cascadeGo-cons-N`, `foldPath-sink-N`, `shareGo-skip-N`,
   `cascadeGo-skip-N`. Each exists as a named lemma AND is re-derived inline at
   the site that needs it. Replacing the inline copy with a call *reduces* total
   proof text — the wiring law's cost made concrete and reversible.
6. **MISSING WIRE, sanctioned — WF pieces ahead of their assembly.**
   `oneShotBurst-wf`, `initReg-wf`, `subscribeE-map-/scan-/take-wf`,
   `foldPath-root-out`, `mid-seed`. The assembly was stated first as a
   postulate, per outside-in; these land under it. ~half of W1 is already done.
7. **DELETE — pending Anthony's confirmation (6).** `returnIO` (CLI/IO.agda:14,
   both entry points end in `putStr`), `subscribeE-walk` (Measures.agda:6204,
   P5 — the refuted ledger route's receipt), `share-step-resid` (superseded by
   `share-step`, comment says so), `mu-step-le` (its own comment says it no
   longer suffices; `mu-step` replaced it), `mu-1≤k` (superseded by a direct
   absurd pattern), `mid-enters` (superseded by `seed-enter-pay`). **Not
   executed. Verify the superseding lemma is genuinely called before removing
   any of these.**
8. **A REAL BUG — vacuous postulates.** `id-inheritance`
   (Provenance-Theorems.agda:20) and `defer-shift` (Evaluator-Theorems.agda:56)
   are typed `⊤`, with the actual claim only in a trailing comment. They
   typecheck trivially and assert NOTHING — worse than an honest postulate,
   because they look discharged. State their real types.
9. **LEAVE, revisit when the area is next touched.** The `refl`-facts relied on
   via silent unification (`frameStep-full`, `capsAt-suc-full`), and the genuine
   UNCLEARs (`⊑ᶜ-refl`, `k-raise`, `nest≤`, `enterInstant-idle/-held`,
   `paidUp-held`, `shareFinish-len`, `chainStep-caps`, `wkᵍ`, `Grouped`).
   Low cost either way; `Grouped` has a concrete fix (use it in the spec/impl
   signatures that spell out `List (InstEmit (List A))` by hand).

**Two more lying comments found, worth fixing on next touch:** Caps-Face:4175
claims a recursion "is proven, line for line, in .Deliveries § D" naming lemmas
the live code never calls; Subscribe-Face's header lists `chainStep-caps` as one
of four callers into the clique when nothing calls it.

**Process ruling: classification is the design session's, not a worker's.**
Fan out for the mechanical sweep and for evidence-gathering — that part was
excellent, and the script found four real bugs in its own first approach. But
verdicts depend on campaign context that lives in no source comment, and
delegating them produced four errors in two hours, in both directions (one
"we've solved it", three "delete it"). Workers gather; the design session rules.

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
  definitions.

**AND IT CANNOT BE WIRED YET. Attempting it (2026-08-05) produced the session's
most important structural finding — see THE ANCHOR PROBLEM.** An earlier version
of this section said the gas axis was "solved and merely unwired" and called
`dry-tick` the cheapest remaining win, quoting `dry-tick`'s own comment that it
is "not touched by the caps/INV? bridging problem at all". **Both that comment
and this file were wrong.** The edge ARITHMETIC is proven; SPENDING it is not.

## THE ANCHOR PROBLEM — the campaign's one central open question

`hop-edge` (and `connect-edge`) reset their demand to an anchor `Ŝ`, and
discharging one requires `sizeᵛ o ≤ Ŝ` for a value `o` arising **mid-walk /
mid-cascade**. There are exactly two ways to source `Ŝ`, and **the repo has
already proven both impossible**:

- **A fixed, entry-computable cap** — refuted by `caps-frame-boundary-absurd`
  (`Caps-Face.agda:6836`, proven): for any cap `C ≥ 1`, `sizeStep C C ≤ C → ⊥`.
  One more frame-crossing always escapes the cap, *uniformly in the cap*.
- **A ledger/walk-position-tied ceiling** — refuted by
  `round3b-ledger-reset-absurd` (`Measures.agda:6550`, proven): tying the anchor
  to the walk's own growing ceiling is circular.

The one surviving option is the repo's own stated plan — source `Ŝ`, `R̂`, `F`
from **reachability** (`Measures.agda:6199-6203`) — and it **is not established
anywhere.** Verified: no `chainStep-dry`/`foldPath-dry`/`subscribeInner-dry`
family exists, and every proven `-wet` delivery lemma (`chainStep-wet`,
`foldPath-wet`, `dispatchShare-wet`, `shareGo-wet`, `cascadeGo-walk`) is
**size-axis only** — none carries a `Gas` hypothesis or concludes `hasDry ≡ false`.

**This unifies what looked like separate problems.** GAP 4 (b), `dry-tick`, and
P1's subscribe-side bridge are all the SAME question on different axes: *can a
mid-walk value's size be bounded from reachability, rather than from a fixed cap
or from the ledger?* Answer it and several postulates fall together; leave it and
none of them move. **This is where design attention belongs.** A separate but
analogous anchor-shaped blocker (`merge-cert`, node↔live-instance coherence)
independently blocks the well-formedness branch — see that section.

**Consequence for the risk ranking:** the risk is NOT spread across the ledger.
It is one problem, named above, plus `depth-compositional`'s state-growth
conjunct and the well-formedness branch's `merge-cert`.

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

**THE WHOLE CAPS-BRIDGE / DEPTH-BOUND TOWER IS CURRENTLY UNWIRED (verified
2026-08-05 by grep).** `sub-charge`, `depth-capped`, and `cascade-wet-via-caps`
each have ZERO consumers outside their own defining module. The work is real and
green, but nothing above it spends it yet. Two consequences worth holding:

- **`cascade-wet-via-caps` must be wired into `cascade-dry`/`burst-wet` in place
  of `cascadeGo-wet`.** That is a Wet.agda edit (~14-18 min recheck) and is the
  step that actually retires P2. Until it happens, P2's "decomposed" status is
  potential, not realised.
- **`depth-compositional`'s urgency is currently UNKNOWN, and that is a finding.**
  It is needed by `depth-capped`, which is needed by nothing yet. Note
  `cascadeGo-caps` and `caps-tick` carry NO depth hypothesis (checked their
  signatures) — the delivery side is already depth-complete. So the depth tower
  exists for P1's subscribe-side route, which is still unstated. **State P1's
  analogue BEFORE grinding the 16-head induction**, or the induction may be
  proven against a consumer that never materialises — exactly the "pieces before
  their assembly" anti-pattern CLAUDE.md forbids.

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
