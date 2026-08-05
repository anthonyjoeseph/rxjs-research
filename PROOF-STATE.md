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
     ├─ budget-sufficient                      Caps-Bridge.agda — PROVEN from:
     │   ├─ burst-wet    ← subscribeE-wet      [P1]  (.Wet, unchanged)
     │   ├─ burst-caps   ← (postulated — see the RULING's EXECUTED note)
     │   └─ drain-dry    ← cascade-wet-via-caps       proven
     └─ THE WELL-FORMEDNESS BRANCH             its OWN 5 postulates — see [W1-W5]
```

MOVED 2026-08-05 (see the RULING below, now EXECUTED): `budget-sufficient` lives
in `Caps-Bridge.agda`, not `Wet.agda`; `cascadeGo-wet` [P2] is RETIRED BY
DELETION (orphaned, zero consumers) rather than by proof, since
`cascade-wet-via-caps` now supplies dryness+INV? instead.

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

### MAIN IS THE TOP-LINE PROOF — three rules (Anthony, 2026-08-05)

1. **Whatever Main imports STICKS AROUND.** `agda/src/Main.agda` is the
   deletion exemption, not a build convenience.
2. **Main names individual definitions — never a bare `open import`.** This is
   what makes rule 1 precise: the exempt set is exactly the names Main lists,
   and everything else must be transitively required by one of them.
3. **Main is NEVER touched without Anthony's explicit approval.**

**Two targets, and the gap between them is the debt.** Naming claims shrinks
what Agda compiles, because Agda compiles exactly what is transitively
imported. So:

| target | what it covers | meaning |
|---|---|---|
| `make agda` | the claim graph from Main | every claim's support compiles |
| `make agda-all` | every module under `src/`, reachable or not | rot-guard for unwired work |
| `make wiring` | the gap, itemised | the remaining work |

Ten V-B-S modules — **14,439 lines**, Caps-Face (6,923) and Subscribe-Face
(3,488) among them — are currently reachable from NO claim. `make agda-all`
exists only so they cannot rot while the wiring pass runs, and it is
**self-retiring**: when both targets cover the same set, the wiring law holds
by construction and the target is deleted. Do not "fix" the gap by re-adding a
bulk import to Main; that is the loophole, not the repair.

`scripts/check-wiring.py` mechanises CLAUDE.md's wiring law, rooting its
exempt set in Main's `using` clauses. Current numbers: **54 postulates** (30
with consumers, 20 top-line claims, **4 truly orphaned**) and **87 orphaned
proven definitions**. Do not re-derive this list by hand or by memory — run the
target. Two corrections landed with the Main change, both in the direction of
strictness:

- The exempt set was previously "any postulate in a `*-Theorems.agda` file" — a
  filename heuristic that exempted internal helpers (`truncateIn`,
  `emittedBefore`, `Node`, `δ`, `_≈ˢ_`, `_≈ᵍ_`) along with real claims. **A
  filename is not a claim; being named in Main is.** Orphaned postulates 2 → 4.
- Main is excluded as a **consumer**, so a claim cannot self-certify by being
  named. Without this the two ledgers collapse into one (30/20 → 50/0).

**NEW FINDING from the stricter check: `_≈ˢ_` and `_≈ᵍ_`
(Rx/Time-Theorems.agda:72–73) have ZERO consumers.** They are the equivalence
relations that module exists to state things up to, and `locality`,
`non-interference`, `timing-invariance` do not use them. That module is weaker
than "close to vacuous" — two of its own helpers are not wired into its own
claims.

### THE ORPHAN CENSUS (2026-08-05) — 87 items, 17 families, evidence not verdicts

A read-only sweep grouped all 87 and checked every family's import direction
with `grep '^open import'` before claiming any consumer. **Six findings that
were NOT already known.** (Cost ~276k tokens; the follow-up census should run
against the post-landing list, which is smaller.)

1. **THE MASTER STRUCTURAL FACT.** `Verify-Well-Formed.agda:43` imports
   **exactly one name** — `budget-sufficient` — from the entire
   Verify-Budget-Sufficient tower. That single edge is why a whole stratum of
   proven work can never reach a claim. Every "missing wire" below is
   downstream of it.
2. **A TENTH DUPLICATED PROOF, and its cause.**
   `Verify-Well-Formed.agda:4564–4573` states its own `cascadeGo-skip` with the
   identical case-split shape as `Deliveries.agda:868`'s `cascadeGo-skip-N` —
   **because Verify-Well-Formed cannot reach Deliveries.** The duplication is
   not carelessness; it is the import graph forcing a re-derivation. Fix the
   edge and the duplicate becomes deletable.
3. **THE RESET PAIR IS STATED THREE TIMES, and only the inline copy is ever
   called.** `connect-edge`'s body (Wet.agda:4066–4071) inlines exactly what
   `reach-resets` (Caps-Face:6917) bundles and what `connect-anchor`
   (Measures:1977) *also* bundles. Wet's own comments admit it — "reach-resets'
   first component, inlined" (4043) and "reach-resets' two components, again
   inlined" (4058). Three statements, one fact, zero of the named ones spent.

   **CORRECTION (design session, on inspecting all three): the three are NOT
   interchangeable, so "just call the existing one" is a wall, not a fix.**
   - `connect-edge`/`hop-edge` (Wet) are **generic in `Ŝ`** and take
     `sizeᵉ d ≤ Ŝ` as a hypothesis.
   - `reach-resets` (Caps-Face:6917) is the matching generic form —
     `2 ≤ C → sizeᵉ o ≤ C → (syncSizeᵉ o ≤ C) × (hopDᵉ C o ≤ hopR C)` — but
     **Caps-Face is Wet's SIBLING** (Wet → Caps; Caps-Face → Delivery-Walk →
     Caps), so Wet can never import it.
   - `connect-anchor` (Measures:1977) is **specialised** to
     `V = sizeBudgetAt e sl id` and derives the size bound internally from
     `slotDef-size`/`slots≤budget`. Calling it from `connect-edge` would force
     `Ŝ = sizeBudgetAt e sl id` and destroy the genericity.

   **THE ACTUAL FIX:** state the generic pair ONCE in `.Measures` — the lowest
   common point — since its two ingredients (`hopD-cap`, `syncSize≤sizeᵉ`) are
   already reachable from both Wet and Caps-Face. Then `connect-edge`,
   `hop-edge`, `reach-resets`, AND `connect-anchor` all delegate to it, and
   `reach-resets` becomes a one-line re-export (or goes). Four consumers for one
   three-line lemma. This is the general lesson again: **when the same fact is
   proven N times, the fix is usually to move it DOWN, not to pick a winner.**
4. **A WHOLE SUPERSEDED WELL-FOUNDEDNESS TOWER (7 items, Measures).** `≺ᵛ-wf`
   :536, `≺-embed`:2085, `unfoldμ-≺`:2151, `shells-unfoldμ-cap`:2165,
   `shells-drop`:2209, `rank-drop`:2224, `dBound-struct`:2237 — a
   Dershowitz–Manna multiset order over syntax, including its nontrivial
   well-foundedness proof. **Evidence it is superseded rather than merely
   unwired:** the measure actually wired, `dBound V R U r s = s + suc V * (r +
   suc R * U)` (Measures:2003), is closed-form ℕ arithmetic that never mentions
   `rank`, `shells`, or `≺ᵛ` at all. Two encodings of one termination
   argument; only the cheap one is spent. **Anthony's ruling needed** — this is
   the single largest block of recoverable-or-deletable work in the census.
5. **THREE LEMMAS UNWIRED PURELY BY A MISSING `using` CLAUSE** — the cheapest
   fix in the repo. `pmO≤ceil`:782, `pmI≤ceil`:787, `pWᵉ≤entryCeil`:831
   (Rx/Frame-Width.agda) are absent from the `using` lists that import
   Frame-Width into Caps-Face (:116–124) and Subscribe-Face (:102–110), while
   their siblings `slotsPW≤entryCeil`/`slotsIW≤entryCeil` ARE imported and ARE
   consumed (Caps-Face:4323,4325). The wired siblings bound the *slot
   telescope's* width; these three bound the *expression's own*. No cycle, no
   design question — one import line each.
6. **WRAPPERS BYPASSED BY THEIR OWN CALLER.** `enterInstant-fresh-aux`
   (Verify-Well-Formed:4010–4021) calls the field-unpacked `…-aux` internals
   directly, skipping `enterInstant-idle`:3965 / `enterInstant-held`:3982 /
   `paidUp-held`:4000 — wrappers written precisely to repack those calls. The
   wrapper came first, then the call site was written against the primitive
   form.

Also: **`Depth-Bound.agda:67–69` has the identical upside-down shape as
Caps-Bridge** (imports Wet AND Subscribe-Face), so the ruling above applies to
it too. And `sub-charge`/`cascade-wet-via-caps` were re-verified as
non-vacuous, taking concrete hypotheses rather than assuming the hard part —
checked by reading the signatures, not by trusting the memos.

**Priority order from the census, and it matches the ruling above:** delivery-
count tower (cheapest real win) → Caps-Bridge/Depth-Bound (biggest payoff,
retires P2) → Frame-Width/Rx one-liners → Verify-Well-Formed's `subscribeE-wf`
body → Caps-Face/Caps-Nest odds and ends → **the anchor cluster LAST (26 items,
the largest mass of proven work, genuinely blocked on the one open design
question — no further worker time there until it resolves).**

Rulings by cluster, made by the design session after
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
   `depth-capped`, `B1-cSize≡sizeCapAt`. **`cascade-wet-via-caps` is WIRED**
   (2026-08-05, phase 2 — see the RULING's EXECUTED note): it is `drain-dry`'s
   direct supplier now, `cascade-dry` having been retired rather than
   restated. `sub-charge` stays unwired for a recorded reason (see
   `burst-caps`'s header, `Caps-Bridge.agda`) — it is not the same open
   item this bullet originally named.
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

### RULING: Caps-Bridge was built UPSIDE DOWN (2026-08-05, phase 1)

**The module sits ABOVE `.Wet` and its header names `.Wet` as its consumer. That
can never happen** — `Caps-Bridge.agda:55` is `open import …Wet`, so a `.Wet →
.Caps-Bridge` edge is a cycle Agda rejects outright. The header's "CONSUMERS.
`cascade-dry` and `burst-wet` (.Wet) migrate to consume `cascade-wet-via-caps`
here" is a **lying comment** of exactly the forbidden kind: it describes a wiring
the import graph forbids. The design session wrote that header AND wrote the
phase-1 brief that inherited its error, sending a worker to build an impossible
edge. The worker was right to route around it and right to flag the cost.

**Why `open … public` hid this.** `Verify-Budget-Sufficient.agda:595` re-exports
Caps-Bridge `public`, so `make agda` typechecks it forever and it never rots —
but a re-export is not a consumer. Nothing downstream *needs* one line of it.
This is the loophole the wiring law closes, and it is why `make wiring` flagged
these while the build stayed green. **Re-export ≠ consumption; only `make wiring`
sees the difference.**

**The fix is to move the TOP of the tower UP, not the bridge DOWN.** Measured,
not guessed:
- Caps-Bridge needs exactly **7** Wet-resident names (`sizeCapAt`,
  `sizeCapAt-mono`, `INV?-widen`, `cascadeLatch-INV`, `cascadeFinish-INV`,
  `chainsOf-B`, `cascadeGo-walk`); everything else its header credits to `.Wet`
  actually originates in `.Measures` and already arrives independently via
  `Subscribe-Face → Caps-Face → Delivery-Walk → Caps → Keeps-Ring → Measures`.
- None of the 7 sit inside Wet's mutual blocks (3920/3977), so extraction is
  *possible* — but their natural home is `.Caps`, and editing `.Caps` dirties
  Delivery-Walk → Caps-Face → **Subscribe-Face (~44 min)** → Wet → everything.
  Rejected on cost.
- So instead **`cascade-dry`/`drain-dry`/`budget-sufficient` MOVE from `.Wet` to
  `.Caps-Bridge`**, caps-threaded, where `cascade-wet-via-caps`, `sub-charge`,
  `slots-tick`, `chainStep-slots`, `cascadeGo-slots`, `fn-tick`, B1/B2 are all
  already proven and local. MOVE, not copy — a second fuel-loop induction beside
  the first is the same duplication in a new place.
- `Verify-Well-Formed.agda:43` imports `budget-sufficient` from `.Wet` **by
  name**, so the tower's top is pinned by one import line. That line changes;
  the theorem's face does not. Verify-Well-Formed gets rechecked either way (it
  imports Wet), so this costs nothing extra.

**THE PRIZE, and it is bigger than the tidiness.** `cascade-wet-via-caps` is
proven modulo `dry-tick`. Routing `budget-sufficient` through it **retires P2
(`cascadeGo-wet`)** — trading a postulate for one already on the ledger — and
makes P2 an orphan, i.e. retired *by deletion* rather than by proof. Phase 1's
`burst-caps` postulate should likewise be re-examined against `sub-charge`
(GAP 4(a), proven), which may discharge it outright rather than assume it.

**EXECUTED 2026-08-05 (phase 2).** The move landed: `cascade-dry`/`drain-dry`/
`budget-sufficient` are OUT of `.Wet` and IN `.Caps-Bridge`, caps-threaded,
consuming `cascade-wet-via-caps` (not a `cascade-dry` restatement — that name
is retired, its job absorbed directly into `drain-dry`'s loop body).
`Verify-Well-Formed.agda:47` now imports `budget-sufficient` from
`.Caps-Bridge`; its TYPE did not change so nothing else in that 5348-line
module needed editing (recheck cost, measured for the first time: ~21s
total via `make agda`'s first dirty pass, once `.Wet`/`.Caps-Bridge`
themselves were already fresh — trivial next to Subscribe-Face's ~44 min).

- **`burst-caps` was checked against `sub-charge` and NOT discharged** — see
  `burst-caps`'s own header comment in `Caps-Bridge.agda` for the two
  independent reasons (the base case `capsOK?` at the initial state is a
  `sub-charge` HYPOTHESIS, not something it supplies — no `capsOK?` analogue
  of `init-INV` exists yet; and `sub-charge`'s witness bound is `opIterD`,
  the subscribe clique's own measure, not the `sizeCount`/`capsH` recurrence
  `capsAt` is actually defined by — unlike `caps-tick` on the cascade side,
  nothing ties the two together for subscribe). Landed as a postulate with
  that reason recorded; **`sub-charge` itself is consequently still an
  orphan** (zero consumers) — pre-existing, not new.
- **`cascadeGo-wet` [P2] IS NOW ORPHANED** — confirmed by `make wiring`
  (zero consumers) — retired by deletion exactly as predicted. Left in place
  per standing instruction (deleting a postulate is Anthony's call).
- **Nine of the ten previously-unreachable V-B-S modules are now reachable**
  from `Main` via `Caps-Bridge → {Wet, Subscribe-Face → Caps-Face →
  {Delivery-Walk → Deliveries, Caps-Nest}, Subscribe-Face → Caps-Chain →
  Caps-Sadd}, Caps-Bridge → Caps-Depth` (verified by reading the import
  graph, not by assuming it): Subscribe-Face, Caps-Face, Caps-Chain,
  Caps-Sadd, Caps-Depth, Delivery-Walk, Caps-Nest, Deliveries, and
  Caps-Bridge itself. **`Depth-Bound.agda` is the one still unreached** —
  nothing anywhere in `agda/src` imports it; `depth-compositional`'s only
  "consumer" is inside its own module.
- **Wiring ledger, before → after this move:** total postulates 54→55 (+1,
  `burst-caps`), orphaned postulates 4→5 (+1, `cascadeGo-wet`), orphaned
  proven definitions 87→86 (−1). All four gates green: `make agda` (22s),
  `make agda-all` (2:48, all 39 modules), `make bug-cache` (3.9s),
  `make wiring` (report, not a gate).

**Generalised lesson for every future wiring pass: check the import graph BEFORE
designing the edge.** Two of this campaign's wiring errors are now the same
error — a header asserting a consumer relationship that the module's own imports
make impossible. A one-line `grep '^open import' <module>` would have caught
both. Do it first, every time.

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
