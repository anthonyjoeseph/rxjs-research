# Formal Verification Campaign — Worker Handoff (2026-08-04)

**Current session:** Fable 5 design-authority running on main account. **Next worker:** Opus 5 or Haiku on secondary account.

**Status:** Tier 1 item 4 (Step C) — probes landed, **Unit 1 not yet started** (see The Current Leg below). `main` and `claude/agda-install-build-g6t144` are in sync at `7c56612` (all pushed). Postulate ledger: **5 real postulates** (Caps-Face 2, Measures 1, Wet 2), zero TEMP scaffolding. No uncommitted changes.

**Where this document errs, the tree wins.** It was written under duress; its repo-state claims have been corrected once already (2026-08-04, design session) after verification against `7c56612`. Re-verify anything load-bearing with grep before spending on it.

---

## The Goal & Structure

**Ultimate goal:** Fully machine-checked proof, `Formal-Verification` discharged, **no postulates, everything typechecks**. The work is decomposed into three tiers:

### Tier 1: Postulate Ledger Discharge (5 remaining, originally ~50)
**Done:** cascadeGo-charge framework, full receipt/queue-length quantification apparatus, supply proofs, Unit 2 (all TEMP scaffolding deleted).

**Current (item 4):** Step C — add level conjuncts to the nesting receipt across the 13-member mutual clique in `Subscribe-Face.agda`.

**Remaining after Step C:**
- **Item 3** — discharge the two Caps-Face faces (`innerFinish-concat-face` at line 5902, `thruOuter-face` at 5932), taking the ledger from 5 to 3.
- **Item 2** — discharge subscribeE-walk postulate.
- **Item 1** — discharge subscribeE-wet + cascadeGo-wet + Wet.agda's remaining postulates.

**Tier 1 is the authorization boundary:** once ledger reaches 0, the design session (~Fable) has standing permission to delegate Tier 2 work to another agent pool with full autonomy (no more ruling/stop conditions, purely mechanical grinding).

### Tier 2: Verify-Well-Formed (8 postulates)
The second main module holding 8 postulates that depend on Tier 1 being complete. Batch-online also sits here. Lower priority; begins after Tier 1 closes.

### Tier 3: Theorem Ring (30 postulates spread across 4 modules)
Readme, Time, Evaluator, Provenance. All depend on both Tier 1 and Tier 2. Lowest priority.

---

## The Current Leg: Step C Unit 1 (NOT STARTED — verified against the tree 2026-08-04)

**Tree state at `7c56612` (main == working branch, both pushed, clean):** the clique in
`Subscribe-Face.agda` still reads `(c : Caps) (dep bud j : ℕ)` — **no `m` parameter, no level
conjunct, zero TEMP postulates anywhere in `agda/src`** (`grep -rn "TEMP-" agda/src` is empty).
An earlier draft of this document claimed the 42 LHSs already carry `m` with ~29 TEMP holes;
that state was in-flight edits that died UNPUSHED with the old worker (see the usage-limits
note below). The last pushed Step C work is the probe alone (`cafdaaf`). Start Unit 1 from
scratch; trust the tree, not this document's history.

**What it is:** Threading the operator count (`m`) through the mutual chain members alongside existing `dep`/`bud` parameters, then adding the indexed level conjunct `… ≤ opIterD S W dep k m j` per the Chain-Index-Probe findings.

**Unit 0 (prerequisite, small):** the arithmetic the conjuncts spend currently lives in
PROBES, which `agda/src` modules cannot import. Land in a small non-SCC src module (≤20 s solo
recheck, e.g. extend `Caps-Sadd` or a new `Caps-Chain.agda`):
- `index-mono`, `entry-is-sweep`, `entry-to-index` (from `agda/probe/Chain-Index-Probe.agda` § 2)
- `walk-step`, `frame-step`, `op-step`, `op-step-eval`, `op-step-mu` (from `agda/probe/Sub-Charge-Probe.agda` § 5)
- `walk-index` (from `agda/probe/Level-Shape-Probe.agda` § 2)
These are already proven in the probes — this is a copy + import-fix pass, one green commit.

**Design facts (probed and settled):**
1. The level conjunct **cannot be reported in entry shape** (`sLvlD S W d bud J`). A recursive call inside an operator clause is not a fresh subscribe — it's the same sweep, one shorter. The entry-sweep-in-operator-remaining absurdity is machine-refuted at zero-operators-left (see `agda/probe/Chain-Index-Probe.agda`).
2. **The index meets the conjunct via `opIterD-mono`**, consuming exactly one step. At the entry site, `index-mono` and `entry-to-index` discharge the conversion.
3. **The descent split belongs only at the reporting clause.** `sIterD`, `opIterD`, `fIterD` all pass the budget `k` through untouched — that's a family-level property, not clause-specific.

**Unit 1 scope (BEFORE any edit):**
- Per-head count check of the 42 clause LHSs to ensure every one receives the new `m` parameter
- Hand-edit pass (no scripts; scripts failed twice on clause-LHS scanning in Unit 2)
- Weak TEMP postulate holes at call sites (shape `∀ {x y : ℕ} → x ≤ y`, not precise sums — unifier lessons learned)
- One green commit with TEMPs and conjuncts in place

**Unit 2 scope (after Unit 1 commits green):**
- Discharge conjuncts leaves-first in batches against the §5 gate (composition gate — proven in `agda/probe/Sub-Charge-Probe.agda` § 5, landed in src by Unit 0; `Caps-Sadd` holds the superadditivity family + `walk-step-lift`/`walk-step-suc`)
- Green commit per batch
- Delete TEMP postulates with the last replacement
- If a site resists two distinct attempts → STOP with the goal type verbatim (caution rule, now standing since Unit 2)

**After Step C Unit 2 completes green (ledger back to 5):**
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
- **Interfaces are cached per module**, so a green tree plus one new leaf module is a ~1 min `make agda`, not 35–40 min. The full 35–40 min figure applies when Subscribe-Face (~7 min) or Wet (~14–18 min) is dirty. Never pipe agda through `head` (it hides OOM kills); read the exit code.

---

## Files of Interest

### Core Working Files (Tier 1, Item 4)
- **`agda/src/Verify-Budget-Sufficient/Subscribe-Face.agda`** (18 `-caps` heads; the big mutual clique; this is the ~7 min SCC — iterate in probes, land in batches, detach rechecks)
  - Current state: heads carry `(c : Caps) (dep bud j : ℕ)` + the `nest … ≤ bud` hypothesis; Σ reports `capsOK?` × `burstCaps?`/`valsCaps?` × `burstCount?`. **No `m`, no level conjunct yet** — that is Unit 1.
  - The clique's signature block starts at `subscribeE-caps` (~line 838); the pass memo sits above it.

- **`agda/src/Verify-Budget-Sufficient/Caps-Nest.agda`**
  - Nesting measure `nest e sl cs = syncSizeᵉ e + resid sl cs`, per-constructor steps (`share-step`, `mu-step`, `chain-step`, `map/take/scan/all/merge/concat/switch/exhaust-step`), `refresh-supplies-nest`, `k-raise`.
  - NOTE: `walk-index`, `index-mono`, `entry-to-index` are **NOT here** — they live in probes and must be landed in src by Unit 0.

- **`agda/src/Verify-Budget-Sufficient/Caps-Sadd.agda`** (superadditivity family `fLvl/sIterD/opIterD/fIterD-sadd`, `walk-step-lift`, `walk-step-suc`)

- **`agda/src/Verify-Budget-Sufficient/Caps-Face.agda`**
  - Two ledger postulates `innerFinish-concat-face` + `thruOuter-face` in the single `postulate` block at ~line 6119 (item 3, after Step C); the pass memo (why (b) precedes (a), what the faces wait on) sits directly above it.

- **`agda/probe/Chain-Index-Probe.agda`** (settled the conjunct shape; § 2 has `index-mono`/`entry-is-sweep`/`entry-to-index`)
- **`agda/probe/Level-Shape-Probe.agda`** (discharged Σ-vacuity; § 2 has `walk-index`; § 3 the descent-point fact)
- **`agda/probe/Sub-Charge-Probe.agda`** (§ 5: `walk-step`, `frame-step`, `op-step`, `op-step-eval`, `op-step-mu` — the five clause-shape arithmetic steps, proven)

### Build & Test
- **`Makefile`:** `make agda` (full Agda check), `make bug-cache` (type-level unit tests), `make test` (other suites)
- **`agda/src/Implementation/Unit-Test.agda`:** Type-level unit test cache, run via `make bug-cache`
- **`scripts/gen-unit-tests.sh`:** Append new counterexamples to the cache

---

## Next Handoff Checklist

Before pausing for the design session to transfer authority to another account:

- [ ] All work is pushed to `claude/agda-install-build-g6t144` (not main)
- [ ] Last commit is green (`make agda && make bug-cache` both exit 0)
- [ ] `grep -r "TEMP-" agda/src/` returns zero
- [ ] No uncommitted changes (`git status --short` is empty)
- [ ] Fallback triggers are deleted (check `mcp__claude_code_remote__list_triggers` or let design session clean up)
- [ ] New worker receives: this document, current git branch tip SHA, postulate ledger summary

---

## Contact & Authority

**Design session (Fable 5):** Reviews worker reports, merges green work to main, makes spec rulings, launches next worker. Anthony supervises the entire campaign.

**Worker (Opus 5 / Haiku):** Executes the assigned leg (e.g., "Step C Unit 1, then Unit 2"), commits+pushes per green batch, reports completion or stops on a caution condition.

**Tier 1 completion** is the threshold for **full worker autonomy on Tier 2:** Once the ledger reaches zero, Tier 2's 8 postulates are fully available and can be discharged by any competent worker without design-session rulings (all shape decisions are settled, all stop conditions are specification-hard).
