# Formal Verification Campaign — Worker Handoff (2026-08-04)

**Current session:** Fable 5 design-authority running on main account. **Next worker:** Opus 5 or Haiku on secondary account.

**Status:** Tier 1 item 4 (Step C) — Units 0 and 1 done and green; the level conjunct's SHAPES
are landed on ten heads with twelve clauses proven, and the rest of its clauses are the current
work. Postulate ledger: **5 real postulates** (Caps-Face 2, Measures 1, Wet 2).

## ⚠ RESUME HERE — the conjunct SHAPES are landed; 20 clause sites remain

**`origin/main` = `aded321`, verified green** (`MAKE_AGDA_EXIT=0`, `BUG_CACHE_EXIT=0`). The
level conjunct is IN the Σ on nine heads, and the composition gate in `Caps-Chain` is built.
What remains of Step C is discharging **20 `level-TEMP` clause sites** — and they have been
surveyed, so this is a worklist, not an exploration. Take the buckets in the order given.

**`grep -c "level-TEMP" agda/src/Verify-Budget-Sufficient/Subscribe-Face.agda` = 23**: 20 real
proof sites, the postulate declaration, and two prose mentions. `grep -rn "TEMP" agda/src` must
return zero before Step C is done — the BARE word, not `"TEMP-"`, which misses `level-TEMP`
and reported a false all-clear once.

**Where this document errs, the tree wins** — it has been wrong about repo state twice. One
correction already: an earlier revision claimed "the `input` clause is now closed by
`op-step-share`". It is NOT (bucket E below); the comment in the clause itself says so.

---

## THE STEP C SITE CENSUS (2026-08-04) — all 20 sites, classified

Read off the head signatures and the clause witnesses; no build needed, because each head's
Σ *declares* its conjunct's transformer and index, so the goal is the witness substituted in.
Five transformer families are in play, one per head group:

| head group | conjunct it reports |
|---|---|
| `subscribeE` / `subscribeAll` | `j + j′ ≤ opIterD S W dep bud ops j` |
| `subscribeInner` / `thruConsume` | `suc (j + j′) ≤ sLvlD S W dep bud (suc j)` |
| `thruWalk` / `concatDrain` | `j + j′ ≤ sIterD S W dep bud (length …) j` |
| `innerFinish` / `innerReact` / `stepFrame` | `j + j′ ≤ fLvlD S W dep j` |
| `pushBurst` | `j + j′ ≤ fIterD S W dep bud (length str) j` |

**Bucket A — ONE new trivial lemma closes SIX sites.** Lines 1718, 1841, 1862, 2087, 2095,
2171 (innerFinish merge/switch/exhaust, both innerReact clauses, stepFrame take-f). Every
witness is `0`, so every goal is `j + 0 ≤ fLvlD S W dep j`. Add to `Caps-Chain`:
`frame-nil S W d j = ≤-trans (≤-reflexive (+-identityʳ j)) (fLvlD-infl S W d j)`.
Start here: it is a third of the remaining sites for one line.

**Bucket B — an EXISTING `Caps-Chain` lemma applies, FIVE sites.** No new math.
- 1607 concatDrain (inner stays open, witness `j₁`) — `walk-step` at `j₂ := 0`; the head
  premise is `subscribeInner`'s report weakened by `n≤1+n`, the tail is `sIterD-infl`.
  Wants a one-line `walk-last` wrapper to absorb `j₁ + 0 ≡ j₁`.
- 1639 concatDrain (inner completed, recurses, witness `j₁ + j₂`) — `walk-step` verbatim.
- 2503 subscribeAll `suc ops′` (witness `suc (j₁ + j₂)`) — `op-step` verbatim; its
  conclusion is this goal on the nose.
- 2749 subscribeE `takeᵉ`/`suc ops′` (witness `suc (j₁ + j₂)`) — `op-step`.
- 2819 subscribeE `scanᵉ` (witness `j₀ + suc (j₁ + j₂)`) — `op-step-eval`.

**Bucket C — split `ops` using the `hidx` the head ALREADY carries, TWO sites.** Both
conjuncts are FALSE at `ops = 0` (the transformer does not move and the witness is positive),
so both clauses must case on `ops`; `hidx : suc (sizeᵉ b) ≤ ops` supplies `1 ≤ ops` outright.
This is the `queue-push` pattern, already proven once.
- 2602 subscribeE `ofᵉ` (witness `j₀ + 3`, `j₀` from `evalTms-caps`) — `op-step-eval`.
- 2992 subscribeE `*All`/`mergeᵒ` (witness `1`) — `op-step-share` at `j₁ := 0`.

**Bucket D — one new EASY lemma plus a receipt conjunct on three non-clique helpers, THREE
sites.** These report a positive witness into `fLvlD S W dep j` at a GENERIC `dep`, and
`frame-step` only concludes at `suc d`. But `fLvlD` at zero is NOT the identity — it is
`fLvl S W J + suc (widAt S W J)` with `fLvl S W J = J + fCharge S W J` — so a dep-generic
receipt lemma goes through by inflation in both branches:
`frame-recv : ∀ S W d j j₀ → j₀ ≤ fCharge S W j → j + j₀ ≤ fLvlD S W d j`
(at `0`, monotonicity into `j + fCharge + suc widAt`; at `suc d`, `sIterD-infl` off `fLvl`).
Then each site needs its helper to report `j′ ≤ fCharge S W j` — a signature addition on three
helpers OUTSIDE the SCC, so each is a cheap solo check:
- 1674 `innerFinish-zero′` ← `innerFinish-zero`
- 2136 stepFrame `map-f` ← `mapFrame-caps`
- 2153 stepFrame `scan-f` ← `stepFrame-scan-caps`

**Bucket E — DESIGN, FOUR sites. These are the schedule; do them FIRST if you have design
authority, because each can change a signature the other buckets rest on.**
- **979 `subscribeInner-caps` — the keystone, and the math is DONE.** `inner-step` is proven
  and landed in `Caps-Chain` § 5. Two supplies remain, both signature-level: the IH must be
  called at index `sizeAt S (suc j)` (NOT its successor — at the successor the IH lands flush
  with nothing over, which is why this site resisted), and it needs `bud ≡ suc bud′` (a
  payload subscribe is a nesting level and spends one, as the μ edge does). Gap is THREE
  rungs, not two, and needs `2 ≤ S` via `2≤sizeAt`.
- **1778 `innerFinish-caps` concat — a wrong call-site argument.** It hands `concatDrain-caps`
  its own `dep` and `bud`. A drain is a WALK: the depth must descend as it does in
  `stepFrame-caps`'s thru-outer clause, and the budget must be the REFRESHED `frameBud c j`.
- **2203 `stepFrame-caps` thru-outer at `dep = zero` — MACHINE-REFUTED. Do not grind it.**
  `agda/probe/Dep0-Walk-Probe.agda` proves
  `suc (fLvlD S W 0 j) ≤ sIterD S W 0 (suc k) (suc m) j` for every cap with `2 ≤ S` — the walk
  at exhausted depth STRICTLY OVERSHOOTS the exhausted frame. Since `thruWalk-caps`'s report is
  the only bound the clause holds on its witness, the transitivity it would use runs the wrong
  way and no rearrangement recovers it. The cause is structural: `fLvlD S W zero` is a closed
  formula (it makes no recursive call — that is what carries the family's termination), while a
  depth-zero walk still re-enters the family through `sLvlD`/`opIterD`. **The fix is a
  signature — depth sufficiency has to reach this head — and it is scoped as Unit 3 below.**
- **2574 `subscribeE-caps (input i)` — THE LANDMINE, and it is a MEASURE question.** The slot
  edge runs through `subscribeE-input` / `sharedSlot` / `sharedConnect`, none of which carry
  the conjunct or even an `ops` parameter. The clause's own comment records why this is not a
  grind: a fresh entry's index is the level's WHOLE size cap, and **`ops` does not dominate
  it**. So either those three heads gain a conjunct in a different currency, or the entry gets
  re-measured. **Consult the design session before spending here** — this is the one Step C
  site that can force a re-measure, and it is the analogue of the Wet item's gate.

**Order:** E (get the signatures right) → A (six sites, one line) → B → C → D. Green
`make agda && make bug-cache` per batch, push per batch, then delete `level-TEMP`.

### UNIT 3 — DEPTH SUFFICIENCY (discovered 2026-08-04; ASK BEFORE GRINDING)

Step C was scoped as two units. The refutation at site 2203 says there is a third, and it is
the mirror of Unit 1: the clique carries a sufficiency hypothesis for the budget
(`nest o sl cs ≤ bud`) and for the operator count (`suc (sizeᵉ b) ≤ ops`), but **nothing bounds
`dep` from below**, and one arc of the cycle spends it.

What the tree says, verified:
- `stepFrame-caps`'s own conjunct comment already names the intent — a frame "is the ONE arc
  that spends a unit of depth fuel — its payload walk runs at `dep` minus one, on the REFRESHED
  budget". The `suc dep′` clause does exactly that (`thruWalk-caps c dep′ (frameBud c j) …`).
  The `zero` clause has nothing to descend into.
- Both callers (`Subscribe-Face:2351`, `:3150`) pass `dep` straight through unchanged, so `dep`
  is inherited from the top and never re-established anywhere in the clique.
- **No depth measure exists yet** — `grep depthᵉ/allDepth/nestDepth` in `Rx/` is empty. So Unit 3
  needs a currency invented, not just threaded.

Why this needs a ruling rather than a grind: the natural currency is not syntactic. `sizeᵉ`
would descend at the thru-outer edge (the inner is a strict subterm), but `stepFrame-caps` does
not hold the inner expression — a `thru-outer` frame carries a `NodeId`, and the inner lives in
the state/registry. So the bound has to come from a **state**-level invariant, which is the same
shape of object as the **registry-cardinality invariant that Tier 1 item 1 (Wet) is already
gated on**. These may be one design problem serving two items, and choosing the currency once
for both is worth more than closing 2203 quickly. CLAUDE.md's rule for the Wet invariant applies
here verbatim: consult before grinding.

---

## The Goal & Structure

**Ultimate goal:** Fully machine-checked proof, `Formal-Verification` discharged, **no postulates, everything typechecks**. The work is decomposed into three tiers:

### Tier 1: Postulate Ledger Discharge (5 remaining, originally ~50)
**Done:** cascadeGo-charge framework, full receipt/queue-length quantification apparatus, supply proofs, Unit 2 (all TEMP scaffolding deleted).

**Current (item 4):** Step C — add level conjuncts to the nesting receipt across the 13-member mutual clique in `Subscribe-Face.agda`.

**Remaining after Step C:**
- **Item 3** — discharge the two Caps-Face faces (`innerFinish-concat-face`, `thruOuter-face`; the single `postulate` block is at ~line 6119), taking the ledger from 5 to 3.
- **Item 2** — discharge subscribeE-walk postulate.
- **Item 1** — discharge subscribeE-wet + cascadeGo-wet + Wet.agda's remaining postulates.

**Tier 1 is the authorization boundary:** once ledger reaches 0, the design session (~Fable) has standing permission to delegate Tier 2 work to another agent pool with full autonomy (no more ruling/stop conditions, purely mechanical grinding).

### Tier 2: Verify-Well-Formed (8 postulates)
The second main module holding 8 postulates that depend on Tier 1 being complete. Batch-online also sits here. Lower priority; begins after Tier 1 closes.

### Tier 3: Theorem Ring (30 postulates spread across 4 modules)
Readme, Time, Evaluator, Provenance. All depend on both Tier 1 and Tier 2. Lowest priority.

---

## The Current Leg: Step C — Units 0 and 1 DONE, the CONJUNCT remains

**Unit 0 — DONE.** The composition gate now lives in
`agda/src/Verify-Budget-Sufficient/Caps-Chain.agda` (a new non-SCC module, ~6 s solo): the five
clause-shape steps `walk-step`/`frame-step`/`op-step`/`op-step-eval`/`op-step-mu`, the quadratic
`quad-arith`, the index conversions `index-mono`/`entry-is-sweep`/`entry-to-index`/`walk-index`,
and `chain-desc` (§ 3, added by Unit 1). `Subscribe-Face` imports it directly — note the
top-level `Verify-Budget-Sufficient.agda` also opens it, which is downstream and does NOT put it
in scope for the clique.

**Unit 1 — DONE, and it needed no scaffolding.** Both operator-shaped heads
(`subscribeE-caps`, `subscribeAll-caps`) now carry an `ops` parameter and the hypothesis
`suc (sizeᵉ b) ≤ ops`, every call site supplies it outright, and **no TEMP postulate was left
behind** (`grep -rn "TEMP-" agda/src` is empty). `make agda && make bug-cache` green.

**THE DESCENT FINDING — read this before touching the conjunct.** Unit 1 was scoped as
"thread the parameter, park the hypothesis behind a weak hole, discharge in Unit 2." That plan
is WRONG, and the hole is what hides the error:

- `op-step` concludes at `suc ops`, so a clause can only report if its own index is a
  SUCCESSOR. Every recursing clause must therefore **split** its index and hand the source the
  predecessor. A clause that does not split has no predecessor to hand over — and a weak
  `∀ {x y : ℕ} → x ≤ y` hole accepts the mismatch silently, so the module goes green with a
  descent that cannot ever close. **The split belongs in the same pass that threads the
  parameter.**
- The supply is then free, and one lemma covers the family. `chain-desc hd src m′` turns
  `suc (suc (hd + src)) ≤ suc m′` into `suc src ≤ m′`; every chain constructor's size is
  `suc (head + source)` (`Rx.Exp:463-475`), so `hd := sizeᵗ f` for map/take, `hd := sizeᵗ f +
  sizeᵗ z` for scan (`+` associates left, so its head being a sum costs no rewrite), and
  `hd := 0` for the headless ones, where it degenerates to `≤-pred`. The zero half of each
  split is absurd **by constructor** (`suc x ≤ zero` is uninhabited whatever `x` is, stuck or
  not), so it costs one line, not a proof.

**WHICH CLAUSES SPLIT — count off the clause BODIES, not the constructor list.** The two
disagree, and reading the constructor list is how the first probe got this wrong (it claimed
nine). **Four** split:
- `mapᵉ`, `takeᵉ`, `scanᵉ` — chain edges, `chain-desc` as above.
- `subscribeAll-caps` — the four `*All` clauses delegate their WHOLE body to it, so they share
  its conclusion and therefore its index; the `op-step` that consumes the source and the pushed
  frames sits inside IT, and so does the split. Its hypothesis is stated about the `*All` TERM
  (`suc (suc (sizeᵉ b)) ≤ ops`) and is inherited from its callers verbatim.

The rest owe nothing: the four `*All` clauses pass index and hypothesis straight through;
`μᵉ`-with-gas is a **FRESH ENTRY, not a chain edge** — it subscribes `unfoldμ body`, which is
LARGER than `body`, so no descent exists, which is exactly why `op-step-mu` consumes it at
`sLvlD` and charges it as one nesting level (it mints the index at the level's size cap and pays
one `s≤s`); and `μᵉ`-out-of-gas, `deferᵉ` (it PARKS its body as a pending live source), `input`,
`ofᵉ`, `emptyᵉ`, `varᵉ` never recurse, so `ops` stays abstract and unused.

**Design facts (probed and settled):**
1. The level conjunct **cannot be reported in entry shape** (`sLvlD S W d bud J`). A recursive call inside an operator clause is not a fresh subscribe — it's the same sweep, one shorter. The entry-sweep-in-operator-remaining absurdity is machine-refuted at zero-operators-left (`agda/probe/Chain-Index-Probe.agda`).
2. **The index meets the conjunct via `opIterD-mono`**, consuming exactly one step. At the entry site, `index-mono` and `entry-to-index` discharge the conversion.
3. **The descent split belongs only at the reporting clause.** `sIterD`, `opIterD`, `fIterD` all pass the budget `k` through untouched — that's a family-level property, not clause-specific.
4. **Which transformer each head reports in is FORCED, not chosen** — the family's clause
   equations close into a cycle and each head sits at exactly one arc
   (`agda/probe/Chain-Supply-Probe.agda` § 4). Only the two `opIterD` heads need an index
   PARAMETER; every other index is already a function of what the head holds (a payload list's
   length, a queue's length, an emit count).

**What remains of Step C:** the shapes are landed on nine heads; the 20 open clause sites are
enumerated and classified in the census at the top of this document. Green commit per batch. If
a site resists two distinct attempts → STOP with the goal type verbatim.

**After the conjunct lands green (ledger still 5):**
- Proceed to item 3 (the two Caps-Face faces, 5 → 3)

---

## Container Resilience: Rollbacks & Usage Limits

**Observed failures (2026-08-04):**

1. **Container snapshot rollback (twice):** The execution environment rolled back to an August 1 snapshot mid-work, wiping the local repo and running processes. Recovery: immediate re-sync from GitHub (`git fetch origin; git checkout -B branch origin/branch`). **All work was safe on origin** — nothing was lost that had been pushed.

2. **Usage limits (twice):**
   - Weekly limit hit mid-work at ~02:05 UTC (resets Aug 7, 1pm UTC)
   - Session limit hit earlier (resets 3:20am UTC, quoted in API error)
   - Worker died with in-flight edits lost (never pushed)

**Standing practice for the next worker:**
- **Push per green batch, not per commit.** Bundling 2-3 commits into a green batch and pushing the batch as a unit is correct. Pushing every commit is fine too. **Leaving multiple green commits unpushed is the risk:** if the container rolls back or kills, only pushed work survives.
- **Detect rollback via commit dates:** Before any edit, run `git log -1 --format=%ci`. If it's days old but the transcript claims recently-pushed commits, re-sync immediately.
- **Handle usage limits gracefully:** The error message quotes a reset time (e.g., "resets Aug 7, 1pm UTC"). On that error, **note the reset time and schedule a self-check-in 5 minutes after the reset** rather than reviving immediately. Usage limits are hard walls; reviving before the reset fires only burns tokens.

---

## The Probe-Before-Grind Law

Proven three times now (2026-08-04):

1. **`with … in` syntax (Subscribe-Face):** The unifier was not binding the equation as expected. A 10-line probe in `agda/probe/` settled it in seconds instead of two 14-minute Subscribe-Face rechecks.

2. **Unifier-shaped holes (Unit 2):** Precise hole shapes like `nest e sl cs ≤ bud` fail to unify if the term unfolds to a sum. Weak holes (`∀ {x y} → x ≤ y`) unify against any goal. Probe: `agda/probe/Hole-Shape-Probe.agda` (fictional name for the pattern).

3. **Chain index (Chain-Index-Probe):** Reporting in entry shape was the natural guess; the probe refuted it at the zero-operators-left instance and identified the operator count as the real currency.

**Standing rule for all future work:**
- Any syntax/elaboration question you haven't used in THIS file → write a ≤10-line probe in `agda/probe/` BEFORE incorporating it into the big module. Probes are ephemeral (deleted after proof, not shipped in the final artifact), but they save hours of big-module rechecks.

---

## Standing Rules (Carry These Forward)

### Design & Proof Structure
- **Spec is gospel.** Impl ≠ spec → impl is wrong. Only touch spec after asking (Fable authority).
- **Outside-in assembly:** State full signatures and end goals first with postulate bodies, then prove leaves-first. Never prove pieces before their assembly exists.
- **Σ-witness law:** Before adding a conjunct, check if it's upward-closed in the witness. If yes, it's vacuous — state why it's needed before grinding. (`agda/probe/Level-Shape-Probe.agda` discharged this for Step C.)

### Editing Discipline
- **Hand-edit, no scripts.** Agda clause-LHS syntax cannot be parsed line-by-line (with-continuations, absurd clauses don't fit the `=`-terminated pattern). Per-head count check before invoking Agda.
- **Weak TEMP holes:** Not precise shapes. Shape `∀ {x y} → x ≤ y` works; `sizeAt S j + k ≤ n` does not.
- **Walk-index/index-mono/entry-to-index spent as-is.** If a call site needs more arithmetic, that's a smell — probe before grinding.
- **Descent split only at the reporting clause.** Carrying edges forward untouched (`sIterD`/`opIterD`/`fIterD` pass `k` through — family property).

### Commit & Push Protocol
- **Green `make agda && make bug-cache` before each commit.** No exceptions; type-level unit tests (`Implementation/Unit-Test.agda`, run via `make bug-cache`) must pass.
- **Push per green batch.** Batches are 2-3 related commits grouped by "green" builds. Unpushed work is at risk (rollback, usage limits).
- **Commit messages in repo voice.** No "Worker 44", no model IDs, no meta-commentary. Focus on the theorem state and what changed.

### Stop Conditions
- **Two failed distinct attempts on one site → STOP with goal type verbatim.** Report the goal to Fable before proceeding.
- **Spec ambiguity → surface with a TypeScript rxjs example, defer to naive plain rxjs semantics.**
- **Impossibility pair discovered → STOP, report immediately to Fable. Do not act on it.**

### Container & Fallback Management
- **On the persistent laptop (current setup), keep-alives are RETIRED** (CLAUDE.md, 2026-08-03): detached builds advance on their own; poll their `EXIT=` log with short foreground calls for pacing/verification only. Keep only a sparse (~60 min) fallback check-in for wedged workers.
- **The container-era rules below apply ONLY if running in a suspendable cloud container** (the environment this document was written in): foreground wait-loops (`for i in $(seq 1 55); do grep -q 'EXIT=' log && break; sleep 10; done`) to hold the container awake, 30-min fallback cadence, delete-and-re-arm trigger discipline.
- Long Agda checks (>600s) must outlive the Bash tool's ~600 s per-call ceiling. **On the laptop `setsid` DOES NOT EXIST** (verified 2026-08-04: `nohup setsid …` dies silently writing no log, and the sandbox additionally denies detached writes under `/private/tmp`). Use the Bash tool's own **`run_in_background: true`** instead — it survives across turns, writes to a task output file you can `Read`, and re-invokes the session when it exits, which is strictly better than polling for an `EXIT=` line. The `nohup setsid` recipe in older memos is container-era; do not copy it.
- **Interfaces are cached per module**, so a green tree plus one new leaf module is a ~1 min `make agda`, not 35–40 min. The full 35–40 min figure applies when Subscribe-Face (~7 min) or Wet (~14–18 min) is dirty.
- **NEVER trust a reported exit code that came through a pipe or a trailing command — write agda's own `$?` into the log and read THAT.** This bit twice for real on 2026-08-04. (a) `agda … 2>&1 | tail -25` was notified as "exit code 0" while the output held a `Not in scope` error — the shell reports the PIPE's code. (b) A wrapper of the form `agda … ; echo "EXIT=$?"; tail -20 log` was notified as "exit code 0" for a run that had been SIGTERMed — the harness summarises the wrapper's last command (`tail`), not agda's. The log itself said `AGDA_EXIT=143`. Correct form, and the only one to use:
  `agda … > /tmp/x.log 2>&1; echo "AGDA_EXIT=$?" >> /tmp/x.log` — then `grep AGDA_EXIT` the file. Piping also hides OOM kills, the original reason for the rule.

---

## Files of Interest

### Core Working Files (Tier 1, Item 4)
- **`agda/src/Verify-Budget-Sufficient/Subscribe-Face.agda`** (18 `-caps` heads; the big mutual clique; this is the ~7 min SCC — iterate in probes, land in batches, detach rechecks)
  - Current state: the two operator-shaped heads carry `(c : Caps) (dep bud ops j : ℕ)` + the
    `nest … ≤ bud` and `suc (sizeᵉ b) ≤ ops` hypotheses, and four clauses split `ops`. **The
    level conjunct IS in the Σ** on nine heads (the five families tabulated in the census);
    what remains is its 20 open clause sites.
  - The clique's signature block starts at `subscribeE-caps` (~line 890); the `level-TEMP`
    postulate and its pass memo sit just above at ~855-888 — that memo is where a known-wrong
    call-site argument gets recorded the moment it is noticed.

- **`agda/src/Verify-Budget-Sufficient/Caps-Chain.agda`** (the composition gate, landed by Unit 0)
  - § 1 the five clause shapes + `quad-arith`; § 2 the index conversions
    (`index-mono`, `entry-is-sweep`, `entry-to-index`, `walk-index`); § 3 `chain-desc`, the
    descent supply. Non-SCC, ~6 s solo — put new non-mutual arithmetic here.

- **`agda/src/Verify-Budget-Sufficient/Caps-Nest.agda`**
  - Nesting measure `nest e sl cs = syncSizeᵉ e + resid sl cs`, per-constructor steps (`share-step`, `mu-step`, `chain-step`, `map/take/scan/all/merge/concat/switch/exhaust-step`), `refresh-supplies-nest`, `k-raise`.

- **`agda/src/Verify-Budget-Sufficient/Caps-Sadd.agda`** (superadditivity family `fLvl/sIterD/opIterD/fIterD-sadd`, `walk-step-lift`, `walk-step-suc`)

- **`agda/src/Verify-Budget-Sufficient/Caps-Face.agda`**
  - Two ledger postulates `innerFinish-concat-face` + `thruOuter-face` in the single `postulate` block at ~line 6119 (item 3, after Step C); the pass memo (why (b) precedes (a), what the faces wait on) sits directly above it.

- **`agda/probe/Chain-Index-Probe.agda`** (settled the conjunct shape; refuted entry-shape reporting)
- **`agda/probe/Level-Shape-Probe.agda`** (discharged Σ-vacuity; § 3 the descent-point fact)
- **`agda/probe/Sub-Charge-Probe.agda`** (§ 5: the five clause-shape arithmetic steps, proven)
- **`agda/probe/Chain-Supply-Probe.agda`** (§ 1-2 the index hypothesis and that it is free at
  every supplier; § 4 the per-head transformer map, and why it is forced)
- **`agda/probe/Chain-Descent-Probe.agda`** (the split: why it cannot be deferred, the one
  descent lemma for the whole family, and § 3 the corrected count of which clauses split)

### Build & Test
- **`Makefile`:** `make agda` (full Agda check), `make bug-cache` (type-level unit tests), `make test` (other suites)
- **`agda/src/Implementation/Unit-Test.agda`:** Type-level unit test cache, run via `make bug-cache`
- **`scripts/gen-unit-tests.sh`:** Append new counterexamples to the cache

---

## Next Handoff Checklist

Before pausing for the design session to transfer authority to another account:

- [ ] All work is pushed (green legs go to `main` — merging verified-green work to main is
      standing authorization from Anthony, 2026-07-31)
- [ ] Last commit is green (`make agda && make bug-cache` both exit 0)
- [ ] `grep -rn "TEMP" agda/src/` returns zero — note the bare word, NOT `"TEMP-"`: the
      hyphenated pattern misses suffix names like `level-TEMP` and reported a false all-clear once.
- [ ] No uncommitted changes (`git status --short` is empty)
- [ ] Fallback triggers are deleted (check `mcp__claude_code_remote__list_triggers` or let design session clean up)
- [ ] New worker receives: this document, current git branch tip SHA, postulate ledger summary

---

## Contact & Authority

**Design session (Fable 5):** Reviews worker reports, merges green work to main, makes spec rulings, launches next worker. Anthony supervises the entire campaign.

**Worker (Opus 5 / Haiku):** Executes the assigned leg (e.g., "Step C Unit 1, then Unit 2"), commits+pushes per green batch, reports completion or stops on a caution condition.

**Tier 1 completion** is the threshold for **full worker autonomy on Tier 2:** Once the ledger reaches zero, Tier 2's 8 postulates are fully available and can be discharged by any competent worker without design-session rulings (all shape decisions are settled, all stop conditions are specification-hard).
