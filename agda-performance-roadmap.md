# Agda typecheck performance: roadmap

Written 2026-08-11. Every number below is **measured on this machine** (24 GB, 14 cores,
Agda 2.7.0.1, agda-stdlib at `~/Developer/agda-libs/agda-stdlib`), with `--profile=internal`
on a genuinely dirty solo check. Raw logs were kept in the session scratchpad only; the
numbers are transcribed here because **this file is the archive** for them.

---

## 1. WHERE THE TIME ACTUALLY GOES

`agda src/Verify-Budget-Sufficient/Subscribe-Face.agda`, dirty, solo: **927 s (15.5 min)**.

| Phase | Time | Share |
|---|---|---|
| **Positivity** | **779 s** | **86 %** |
| Termination.Graph | 92 s | 10 % |
| Typing (all of it: CheckRHS, OccursCheck, With, TypeSig …) | ~18 s | 2 % |
| Parsing / Deserialization / Serialization / DeadCode / Highlighting | ~7 s | <1 % |

`Wet` measures the same way: 908 s total, **828 s (91 %) positivity**. Together these two
modules are ~31 minutes of the ~40-minute build.

**The proofs are not the cost.** `--profile=definitions` attributes only ~18 s to *all*
definitions combined — the largest single one is `subscribeE-caps` at 2.9 s, then `_.IH`
2.4 s, `innerFinish-caps` 1.8 s, and everything else under 700 ms. 98 % of the check is
whole-mutual-block analysis that `--profile=definitions` reports as `Miscellaneous`.

### The partition experiment (the load-bearing measurement)

I cut the file at line 904 — everything before `subscribeE-caps`, i.e. the imports plus the
~45 standalone prelude lemmas — into its own module and profiled it:

| Slice | Definitions | Time | Positivity |
|---|---|---|---|
| Prelude only (lines 1–904) | ~45, each its own block | **7.8 s** | **~0 (absent from profile)** |
| Whole module | prelude + 17-member mutual clique | 927 s | 779 s |

So **the mutual clique alone costs ~919 s**, and 45 definitions in *separate* blocks cost
8 s. Positivity is superlinear in **mutual-block membership**, and nothing else matters.

### Two corrections to received wisdom in CLAUDE.md

- **Subscribe-Face's solo dirty check is 15.5 min, not 44 min.** The 44-minute figure
  presumably included its downstream cone. The cone is real and is why `make agda` is
  ~40 min: `Subscribe-Face` is imported by `Caps-Face`, `Caps-Bridge`, `Caps-Depth`,
  `Level-Mono`, `Burst-Walk`, `Depth-Bound`, and `Main`.
- **"Cut at mutual-SCC boundaries / keep modules ≤20 s" is right but for the wrong reason.**
  Module *size* is nearly irrelevant (904 lines → 8 s). Mutual *block* size is everything.
  A 5,000-line module of independent lemmas would be fast; a 200-line module with one
  15-member mutual block would not.

---

## 2. RULED OUT, WITH RECEIPTS — do not re-attempt

The original plan for `make agda-dev` was to temporarily insert `NO_POSITIVITY_CHECK` and
run a fast check. **This cannot work.** All three routes to disabling the 779 s pass were
tested and all three fail:

1. **`{-# NO_POSITIVITY_CHECK #-}` on the block is a NO-OP.** Agda accepts it only before a
   `data`/`record` definition or a mutual block *containing* one. On a function-only block it
   emits `-W[no]InvalidNoPositivityCheckPragma` — "can only precede a data/record definition
   or a mutual block (that contains a data/record definition)" — and ignores it.
   Subscribe-Face declares **no `data` and no `record`** at all.
2. **`--no-positivity-check` on the command line is REJECTED.** agda-stdlib's modules carry
   `{-# OPTIONS --safe #-}`, and an unsafe global option is refused as soon as the build
   reaches one: `Cannot set OPTIONS pragma --no-positivity-check with safe flag`, at
   `Data/Unit/Base.agda`. Fails in **267 ms with EXIT=42** — the exact "never ran" signature
   CLAUDE.md warns about (`Total 267ms`, 4 `Checking` lines).
3. **As a per-module `{-# OPTIONS --no-positivity-check #-}` it is accepted but BUYS
   NOTHING.** Per-module is accepted (the option is neither blocked by importing `--safe`
   modules nor infective onto importers — both verified). Measured on Subscribe-Face:
   **805 s Positivity / 936 s total, versus 779 s / 927 s without it.** No saving; the delta
   is noise.

**Why:** the 779 s "Positivity" region is the **occurrence-graph / polarity computation**,
which Agda needs for every mutual block regardless of soundness settings. The option
suppresses only the strict-positivity *verdict* on datatypes. There is no flag, pragma, or
option in Agda 2.7.0.1 that skips the graph computation.

**Consequence for the `agda-dev` idea:** the *goal* survives, the *mechanism* does not.
Pragma insertion cannot make this faster. See §3 for the mechanism that can.

### Also ruled out / not worth it

- **`{-# TERMINATING #-}` in dev mode** would work mechanically (it is valid on functions and
  does skip the check), but it targets `Termination.Graph` = 92 s, i.e. **10 %** — about
  90 seconds off a 15-minute loop. Termination is where this proof's induction correctness
  actually lives, so it is the one check whose suppression could hide a genuinely wrong
  induction rather than a typo. Bad trade: real risk for a rounding error. Skip.
- **`--no-infer-absurd-clauses`** is advertised as a speedup and is accepted as a per-module
  pragma, but `Coverage.UnifyIndices` is **78 ms** here. There is nothing to win. Skip.
- **`--termination-depth`** is already at its cheapest default (N=1).
- **A synthetic scaling benchmark** (N mutually-recursive functions with N `Nat` arguments)
  **does not reproduce the cost** — it checks in ~0 ms at N=16. The cost comes from large
  *dependent* telescopes and terms, not from arity alone, so the scaling law can only be
  measured on real modules. Do not bother re-writing that generator.

---

## 3. THE REVISED `make agda-dev`: break the mutual block, not the safety check

The measurement in §1 hands us the mechanism. Separate blocks are nearly free; a big block is
ruinous. So a fast in-`src` loop means **temporarily removing mutual-block membership**, not
temporarily disabling a check:

> `make agda-dev FOCUS=<definition-name>` rewrites the target module in place so that the
> definition under edit keeps its real body while its **siblings in the same mutual block are
> replaced by `postulate`s at their exact existing signatures**. No mutual recursion remains,
> so the occurrence graph collapses and the check should drop from ~15 min to seconds.
> The rewrite is reverted unconditionally afterwards (`trap`-style, so an interrupted run
> cannot leave a mutated tree).

Why this satisfies the original brief better than the pragma version did:

- **Nothing unsafe is switched off.** Positivity and termination both still run — they simply
  have less to chew on. There is no pragma that could leak into a commit, and it opens no
  door to more dangerous relaxations, because it isn't a safety relaxation at all.
- **Work stays in `src`**, under `make wiring`'s jurisdiction. This is what lets `probe/` go.
- **`make agda` remains the merge gate**, unchanged, and stays the only thing that certifies
  the real mutual block.

### What can slip through (be honest about this)

A postulate **does not reduce**. Any clause whose proof depends on a sibling's *computational*
behaviour — pattern-matching on its result, relying on it unfolding under conversion — can
typecheck against the stub and fail against the real definition. In this codebase the clique
members are Σ-returning proofs consumed through `proj₁`/`proj₂`, which is the benign shape, so
most edits are unaffected. But the failure mode is real and it is *not* always "minor": a
witness-arithmetic mismatch (`j + j′` vs `suc (j + j′)`) surfaces only at the real check.

Verdict: this is a genuine 99 %-confidence loop with a cheap, localized failure mode
(a type error at the site you just edited), which is exactly the trade requested — provided
the P0 experiment below confirms the speedup.

### P0 — RUN, AND IT PASSED: 927 s → 17.7 s (52×)

Two generated copies of Subscribe-Face were measured (both since deleted; the generator is
described under "how to reproduce" below).

| Experiment | Contents | Total | Positivity | Termination.Graph |
|---|---|---|---|---|
| Real module | prelude + 15-member mutual block | 927 s | 779 s | 92 s |
| **A — signatures only** | prelude + all 19 clique signatures as bare `postulate`s, no bodies | **9.0 s** | **absent (~0)** | ~0 |
| **B — the dev-loop shape** | prelude + 18 siblings postulated + `subscribeE-caps`'s REAL signature and all 22 clauses | **17.7 s** | **3.0 s** | 0.9 s |

Both conclusions are now measured facts rather than hypotheses:

- **The telescopes are NOT the cost.** All 19 signatures — 16 to 50 lines each — cost 9.0 s,
  and 5.3 s of that is merely *deserializing* the imported interfaces. The real work is ~3.6 s.
  So §4b (record-bundling) is **not** the lever it looked like; see the revision there.
- **Mutual-block membership IS the cost, and it is steeply superlinear.** One real body in the
  block puts Positivity at 3.0 s; fifteen real bodies put it at 779 s. That is ~260× the cost
  for ~15× the members.
- **The stub approach works on real code, not just in principle.** Experiment B typechecked
  `subscribeE-caps`'s actual 457-line, 22-clause body against postulated siblings and exited
  0 with no errors. `subscribeE-caps` is the largest and most entangled member of the clique,
  so this is close to a worst case rather than a favourable one.

**Therefore `make agda-dev` is unblocked, with a measured target of ~18 s per iteration
against 927 s today.** Note the floor: ~6 s of any check in this position is interface
deserialization, so ~18 s is within 3× of the best any tool could do here.

**One trap, hit while running this.** The first attempt at B reported a beautiful 12.5 s — and
was invalid: it had `EXIT=42` from a truncated final clause, and **Agda aborts before the
positivity pass on a type error**, so the expensive pass never ran. A stubbing tool that emits
a subtly broken file will therefore look *faster*, not slower. `make agda-dev` must treat any
nonzero exit as "no timing information", and the fast loop must never be reported as green
without checking the exit code.

**How to reproduce.** A ~40-line Python pass over the module: locate each clique member's
signature span (from its `^name :` line to the next top-level declaration) and its clause
range (first clause line to just before the next definition's first clause); emit prelude +
`postulate` block of the sibling signatures indented two spaces + the focus definition's
signature and clause range verbatim. The 19 members and their line numbers are in §4a. No
signature text is ever re-typed, which is what keeps the stub honest.

### The generalized interface, and are the targets realistic?

The tool must be **per-file and generic**, not tailored to the subscribe clique — Wet is 91 %
positivity too (§4d), so a Subscribe-Face-specific hack would solve half the problem and rot.
Proposed targets, and my calibration of each:

| Target | Verdict | Basis |
|---|---|---|
| `make agda-dev <file>` in **≤30 s** | **Realistic — keep it, with ≤45 s as the worst-case escape** | Measured: 4 foci of the repo's worst module ran **in parallel in 14 s wall clock at ~120 MB each**. Subscribe-Face needs 15 foci; on 14 cores that is ~20–35 s. |
| `make agda-dev` (whole project) in **≤3 min** | **Plausible but not yet demonstrated — I would set 5 min initially and tighten it** | The two profiled modules are ~31 min of the ~40 min build and should each collapse to ~30 s. The unmeasured residual is the other ~10 min spread across every remaining module; if that does not decompose the same way, 3 min is out of reach and ~5 min is honest. |
| **99 % accuracy** | **Right in spirit; see the exact residual below** | The bulk of grind errors are type errors, and those are caught in full. |

**Why a whole *file* needs more than one run.** A name cannot be both a `postulate` and a
definition in the same module, so one generated file checks exactly **one** focus body. Checking
a whole file therefore means one generated file per mutual-block member, run concurrently.
This is the single most important design consequence, and it is also good news: the runs are
**~120 MB each**, so the constraint is *cores*, not RAM — the standing "at most TWO heavyweight
Agda checks" rule does **not** apply to dev-mode runs, and a dozen can run at once.

Definitions outside any mutual block need no stubbing at all; they are already fast (the
904-line prelude checks in 7.8 s). The tool's work is confined to blocks with ≥2 members.

### What the missing 1 % actually is — read this before trusting a green dev check

Precisely three things are given up, and they are not equally harmless:

1. **Termination of the real recursion is NOT CHECKED — this is the big one.** With siblings
   postulated, no recursive call graph exists, so `Termination.Graph` has nothing to look at.
   In this proof the mutual recursion *is* the induction, so a body that recurses on a
   non-decreasing measure will pass dev-mode and fail `make agda`. That failure is **not**
   "minor and easily fixable" — it can mean the proof shape is wrong.
2. **Postulates do not reduce.** A clause that needs a sibling to unfold under conversion
   (pattern-matching on its result, or relying on definitional behaviour) can pass dev and fail
   real. In this codebase clique members are Σ-returning proofs consumed via `proj₁`/`proj₂`,
   which is the benign shape — but witness arithmetic (`j + j′` versus `suc (j + j′)`) is
   exactly where this bites.
3. Positivity is skipped in effect — **irrelevant here**, since these blocks declare no
   `data`/`record` (§2.1).

Everything else is checked in full: types, implicit resolution, metas, **and coverage /
exhaustiveness per definition**. So the honest slogan is *"dev-green means the types line up,
not that the proof is valid"* — which is the right trade for clause grinding, and the wrong
one for believing a proof is finished.

**Verified non-vacuous.** Corrupting a focus body (one `proj₁` → `proj₂` inside
`thruConsume-caps`) made the stubbed check fail with `EXIT=42` and a precise type error
(`Σ (Sched Γ) (λ x → EvalSt e) !=< Bool`). The fast check is load-bearing, not green-by-
construction. **Re-run this falsification test whenever the stubbing logic changes** — a
generator bug that silently drops the focus body would otherwise read as a very fast pass.

### Implementation notes for when P0 passes

- Interface-cache thrash is the one real hazard: the dev rewrite dirties the module, so the
  next `make agda` rechecks it (and its 7-module cone) regardless. Two mitigations —
  Agda keeps interfaces in `agda/_build/2.7.0.1/agda/`, and `--local-interfaces` puts them
  next to the source instead, so **dev mode can use `--local-interfaces` to keep its own
  cache** and leave the strict `_build` tree untouched. Verify this actually isolates the two
  caches before relying on it; gitignore `src/**/*.agdai` if so.
- Rewrite mechanically from the *existing* signature text — never re-type a signature by
  hand, or the stub drifts from the real one and the loop starts lying.
- `make agda-dev` must refuse to run on a dirty git tree it did not create, and must verify
  `git diff --quiet` on exit. A leftover mutation in `src` is the one outcome that would make
  this worse than `probe/`.

---

## 4. THE PERMANENT FIXES (independent of `agda-dev`, and worth doing anyway)

Ranked by measured leverage.

### 4a. Shrink the mutual block — AUDITED, and it is nearly a dead end

The audit is done (call graph traced from clause bodies only, `where` blocks and `with`
continuations included, comment mentions stripped). **The recursion is real: 13 of the 15
members form ONE genuine SCC.**

Four independent confirming cycles:

- `subscribeE-caps → subscribeE-input-caps → sharedSlot-caps → sharedConnect-caps → subscribeE-caps`
- `subscribeE-caps → subscribeAll-caps → subscribeE-caps`
- `subscribeE-caps → pushBurst-caps → stepFrame-caps → thruWalk-caps → thruConsume-caps → subscribeInner-caps → subscribeE-caps`
- `subscribeE-caps → pushBurst-caps → stepFrame-caps → innerReact-caps → innerFinish-caps → concatDrain-caps → subscribeInner-caps → subscribeE-caps`

Only **two** members are pure callees that participate in no cycle and could be hoisted to
before the block:

| Candidate | Called by | Why it is safe to hoist |
|---|---|---|
| `innerFinish-zero′` (sig 1755) | `innerFinish-caps`, ~20 sites in the mergeᵒ/concatᵒ/switchᵒ/exhaustᵒ branches | calls nothing in the block; its signature mentions no block member |
| `retagEvents-caps` (sig 2406) | `pushBurst-caps` (line 2522, inside a `where`) | self-recursive on a list only; signature mentions no block member |

That is **15 → 13 members, ~87 %**, against a cost curve where 1 member costs 3 s and 15 cost
779 s. Two nodes off a 15-node graph will not deliver a meaningful fraction of that. Do it if
it is free (it is a reordering, no statement changes), but **do not expect a speedup, and do
not schedule it as a performance fix.**

**This is why `agda-dev` is not merely convenient but necessary:** the mutual recursion is
genuine mathematics, the block cannot be decomposed, and therefore the full check cannot be
made cheap. The only way to iterate quickly is to check members *against postulated siblings*,
which is exactly §3.

Caveat recorded from the audit: this is a *call* graph, while Agda's positivity pass walks an
*occurrence* graph, which can also pick up polarity through type arguments. The two hoisting
candidates are safe either way (no sibling appears in their signatures), but do not assume the
two graphs are identical in general.

### 4b. Record-bundle the hypothesis telescopes — DEMOTED by experiment A

This was the second-ranked candidate on the theory that telescope width drives the occurrence
graph. **Experiment A refutes that:** all 19 signatures, 16–50 lines each, cost 9.0 s total
with Positivity absent. There is no measurable signature-side cost to recover, so bundling
cannot pay for itself as a *performance* change, and it would touch every clause and call site
in the clique.

Keep it on the table only as a **readability/ergonomics** change, judged on its own merits.
Do not sell it as a speedup. (If it is done for other reasons, re-measure afterwards — a
smaller telescope will not hurt, it simply is not where the 779 s lives.)

### 4c. GHC RTS flags — MEASURED, and the lever is CLOSED

`agda` here accepts `+RTS` (built with `rtsopts`), and RTS flags are not Agda options so they do
not invalidate interfaces — the trial was genuinely free.

| Run | Total | Positivity |
|---|---|---|
| baseline (no RTS flags) | 927 s | 779 s |
| `+RTS -A128m`, **run concurrently with the Wet profile** | 1,039 s | 912 s |
| `+RTS -A128m`, **solo** | **944 s** | 817 s |

The solo number is **1.8 % slower than baseline, i.e. no measurable effect** (run-to-run noise
on this machine is a couple of percent). So the pass is **not GC-bound in any way a bigger
allocation area helps**, and there is no reason to expect `-A256m` or other RTS knobs to
behave differently. Do not spend more time here.

The middle row is kept as a **methodology warning**: it read as "12 % slower" purely because it
shared the machine with another heavyweight check. *A performance comparison run concurrently
with another heavy job measures contention, not the flag.* Two measurements, one confounded,
one clean, disagreeing by 10 % — that is the size of the error this mistake introduces.

### 4d. Profile Wet — DONE, and the pattern generalizes

`Wet` (4,708 lines), dirty solo: **908 s total, Positivity 828 s (91 %)**, Termination.Graph
48 s, everything else under 5 s. Same shape as Subscribe-Face, slightly more extreme.

So the two modules together are ~31 minutes of the ~40-minute build, and **both are ~90 %
positivity over their mutual blocks.** Whatever `agda-dev` does for Subscribe-Face it should do
for Wet, and the design must therefore be per-file and generic rather than tailored to one
clique. `Caps-Face` has not been profiled; on this evidence it is expected to look the same,
and it is not worth 17 minutes to confirm a third instance of the same finding before the tool
exists. (Measure it *after* `agda-dev` works, as a validation of the tool.)

### 4e. Agda 2.8 — SCHEDULED FIRST by Anthony's ruling; see §8

My initial recommendation was to defer this (a source build plus a matching stdlib plus a cold
recheck is a lot of machine time for an unknown return). **Anthony's call, 2026-08-11: upgrade
first.** §8 is the live plan and status; this subsection exists only so the ranking here is not
read as still current.

One thing that does survive the upgrade unchanged: the `--safe` stdlib interaction in §2.2 is a
property of *stdlib*, not of Agda's version, so `--no-positivity-check` on the command line will
still be rejected on 2.8.

### 4f. Two OPT-IN flags for `agda-dev` (Anthony, 2026-08-11)

Neither speeds up `make agda`. Both are exposed as **opt-in flags on `make agda-dev`, off by
default** — that is the ruling, and the defaults matter for a reason given below.

- **`SCOPE=1` → `--only-scope-checking`.** Resolves names and syntax without typechecking.
  Seconds, and it catches the most common grind mistakes (typo, wrong name, bad fixity). Note
  it is a *stage*, not a modifier: it skips typechecking entirely, so it can never be the real
  check — its job is to fail fast before a dozen stub runs are spawned.
- **`HOLES=1` → `--allow-unsolved-metas` (+ `--allow-incomplete-matches`).** Lets a file with
  `?` holes or missing clauses still produce an interface, so hole-driven iteration can happen
  in `src` instead of in a probe file. **Must stay off by default:** if it were always on, a
  `?` would pass silently and "dev-green means the types line up" would stop being true.

---

## 5. RETIRING `probe/`

The point of `agda-dev` is that `probe/` loses its reason to exist. `probe/` was created
because the only fast loop available was "import the heavy module and don't touch it"; a fast
in-`src` loop replaces that. The standing complaint is that code enters `probe/` and never
leaves, diluting context and causing the repo's number-one failure mode — **redundant work,
re-deriving what was already written.**

Plan, once `agda-dev` is real and measured:

1. **Assemble or delete every remaining probe file**, per the existing rule ("a probe is
   temporary, and its end state is assembly + deletion"). No third state.
2. **What survives is not a scratchpad but a cache of negative results**: refutations,
   measurements, reached-state receipts — the things whose value is *stopping* a route from
   being retried. That is a genuinely different artifact from a work-in-progress directory.
3. **Rename it `dead-ends/`.** Of the candidates, this one states the contents rather than
   the ambition: a file lands there only if it records something that does *not* work.
   `intelligence-cache` invites anything "useful"; `refuted-statements` excludes
   measurements, which belong. `dead-ends/` earns the same standing as `bug-cache`: a small,
   append-mostly, load-bearing record with a stated admission test.
4. **Admission test, enforced by `make wiring-gate`:** a file in `dead-ends/` must name, in
   its header, the specific route it forecloses, and must typecheck (the 2026-08-09 finding
   that ten of thirty-three probes did not compile is what makes this non-negotiable — a
   refutation nobody can re-run is an anecdote). Anything with provable content that the main
   proof could consume is not admissible; it gets assembled into `src` instead.
5. The `PROBES.txt` ratchet mostly dissolves with the directory: its job was to catch proven
   work parked outside the claim graph, which is precisely what working in `src` prevents.

---

## 6. MEASUREMENT DISCIPLINE (traps hit while producing this document)

- **`--profile=definitions` cannot see this cost** — it lands in `Miscellaneous`. Use
  `--profile=internal` for phase attribution. `--profile` takes exactly one type.
- **Read the phase table, not the wall clock.** A run that fails instantly still prints a
  `Total`; §2.2's rejection printed `Total 267ms` with `EXIT=42`. `Total` under a second, or
  a missing/short list of `Checking` lines, means Agda never really ran.
- **`touch` does not dirty a module** (content-addressed), so a re-measurement needs a real
  edit. Comment edits count and are the cheapest honest way to dirty a module.
- **Never run two checks of the same module concurrently** — they contend for one `.agdai`.
  Two *different* heavyweight modules at once is fine (the standing 2-at-a-time ceiling).
- **The `--safe` finish line is unaffected by everything here.** No pragma or flag in this
  roadmap lands in the tree, so `agda --safe src/Main.agda` remains the acceptance test.
- **Never edit a source file while a gate is reading the tree.** Done accidentally here: a
  comment fix landed while `make agda` was mid-run. It happened to be harmless (the build had
  not yet reached that module, so it read the new content), but the general case makes a gate
  result describe a tree that no longer exists.
- **`make unsafe-check` does not strip comments, so do not quote a pragma verbatim in prose.**
  Writing the delimited form of a pragma name inside a `--` comment **fails the gate**
  (`UNSAFE_EXIT=2`, hit 2026-08-11 by this very roadmap's documentation). The guard greps for
  `{-#` followed by the pragma name; write the bare name instead. This is arguably the guard
  working as intended — it stays maximally paranoid — so the fix is to reword, **not** to teach
  the checker about comments.

---

## 7. ORDER OF WORK

Everything that was a *question* on this list has been answered by measurement. What remains is
almost entirely construction.

Note what is *not* on this list: every flag-, pragma-, and RTS-level shortcut has now been
measured and closed. There is no configuration change left that makes `make agda` faster. The
remaining work is all structural.

0. **Toolchain upgrade — DONE and validated, except for the last switch** (§8). Stage 1 (stdlib
   v2.3) is adopted; Stage 2 (Agda 2.8.0) is installed, measured at 2.6× on the dominant pass,
   and green over the whole repo. **The one remaining step needs Anthony's call: making 2.8 the
   default `agda`** so `make agda` uses it. That means repointing the
   `~/.cabal/bin/agda` symlink (currently 2.7.0.1) — a change to the machine's environment
   rather than to the repo, and the reason it is being asked rather than done.
   Two consequences to accept with it: `_build/2.8.0` becomes the live cache (the 2.7 one can
   then be deleted, reclaiming space), and `agda-mode`/editor integration should be repointed
   to `agda-mode-2.8` to match.
1. **Build `make agda-dev <file>`** (§3). P0 has passed; this is the whole ballgame.
   Stage it: `SCOPE`-style scope-check first for a seconds-level fail-fast, then one stubbed run
   per mutual-block member, in parallel, with a hard non-zero-exit check.
2. **Re-run the falsification test** (§3) against the finished tool, not just the prototype.
3. **Measure `make agda-dev` on the whole project**, and set the published target from what it
   actually does rather than from the ambition.
4. **Retire `probe/`** (§5) once the loop is real.
5. **Hoist `innerFinish-zero′` and `retagEvents-caps`** out of the block (§4a) — free, but
   expect no measurable win; do not bill it as performance work.
6. **Profile Caps-Face** (§4d) as a validation of the tool rather than as research.
7. **Migrate off the stdlib names deprecated in v2.3** (§8) — mechanical, and required before
   any later move to v2.4.

Dropped from the list: telescope bundling as a speedup (§4b, refuted by experiment A), and any
further attempt to disable positivity (§2, three routes tested and closed).

## 8. THE TOOLCHAIN UPGRADE (in progress, 2026-08-11)

Anthony's call: upgrade Agda before building `agda-dev`. Inventory at the start:

| | Version | Location |
|---|---|---|
| Agda | **2.7.0.1** | `~/.cabal/bin/agda` → cabal store (GHC 9.4.8) |
| agda-stdlib | **v2.2** | `~/Developer/agda-libs/agda-stdlib`, pinned by `agda/rxjs-research.agda-lib` as `depend: standard-library-2.2` |
| available GHCs | 8.10.7, 9.2.8, 9.4.8, 9.6.6, 9.8.4 | ghcup |
| Agda on Hackage | up to **2.8.0** | source build, tens of minutes |
| Agda in Homebrew | **2.8.0-r3, bottled** | prebuilt; needs `ghc@9.12` + `icu4c@78` |

### Stage the upgrade on ONE axis at a time — stdlib v2.3 is the bridge

The key discovery that makes this safe: **agda-stdlib v2.3 is tested against BOTH Agda 2.7.0
and 2.8.0** (its CHANGELOG says so; v2.4 is 2.8.0-only). So the upgrade splits into two steps
that can each be validated independently, instead of one step where a failure is ambiguous
between "library drift" and "compiler change":

- **Stage 1 — stdlib v2.2 → v2.3, still on Agda 2.7.0.1.** Any breakage here is library API
  drift, diagnosed against a known-good compiler.
- **Stage 2 — Agda 2.7.0.1 → 2.8.0, on stdlib v2.3.** Now only the compiler moves.

### Stage 1 — PASSED (2026-08-11)

**`src/Main.agda` typechecks end to end against stdlib v2.3 under Agda 2.7.0.1: `EXIT=0`,
35 modules, zero hard errors.** All 1,248 diagnostics are `UserWarning` deprecations and
nothing else (verified by grepping for type mismatches, unsolved metas, and `!=<`: none).

**ADOPTED, and the invalidated cache was recovered rather than wasted.** Since v2.3 works on
both 2.7.0.1 and 2.8.0, adopting it is not a bet on the Stage 2 outcome. Two changes:

- `agda/rxjs-research.agda-lib`: `depend: standard-library-2.2` → `standard-library-2.3`.
- `~/.agda/libraries`: the v2.3 worktree registered **in addition to** v2.2 (the v2.2 line is
  untouched, so any other project on this machine is unaffected). Note this is a *user-level*
  file outside the repo; reverting is deleting one line.

Verified afterwards: a plain `agda src/Rx/Slots.agda` — the same invocation shape `make agda`
uses — completed in **6 s with `EXIT=0`**, reusing the interfaces the Stage 1 run had written.
So the `_build` overwrite described below cost nothing in the end: the cache is now *valid* for
the configuration the repo actually declares.

**The one migration v2.3 requires** — mechanical, and it is the whole of it:

| Deprecated | Replacement |
|---|---|
| `Data.List.all` | `Data.Nat.ListAction.all` |
| `Data.List.any` | `Data.Bool.ListAction.any` |
| `Data.List.sum` | `Data.Nat.ListAction.sum` |

**17 import sites across 17 files** (both `Rx/` and most of `Verify-Budget-Sufficient/`,
including Subscribe-Face and Wet). Deprecated names still work, so this is not urgent — but it
is required before any later move to v2.4, and it should be folded into the upgrade's single
full rebuild rather than paid as a separate recheck of the two expensive modules.

### Supporting evidence gathered before the gate

- **Union-of-imports probe: GREEN.** A generated module importing *every stdlib name the repo
  uses* — **28 modules, 160 names**, extracted mechanically from all of `src/` — typechecks
  against v2.3 under 2.7.0.1. Zero API drift on the repo's entire stdlib surface.
  - The v2.2 **baseline was run first and it caught a bug in the probe generator** (a bare
    `module` token scraped out of `using (module +-*-Solver)`). Worth restating as method: an
    experiment whose control was not run is not an experiment. Had only the v2.3 arm been run,
    a generator bug would have read as library breakage.
  - Limits of this probe: it proves every name still **resolves**. It does not prove types are
    unchanged, and v2.3's changelog explicitly mentions some definitions becoming *more level
    polymorphic*, which can break inference at use sites without breaking resolution.
- **Real repo code: GREEN.** `Rx/Evaluator.agda` (1,684 lines) plus its Rx dependencies
  typecheck against v2.3 with zero errors.
These two probes were what justified spending an hour on the real gate above.

### Stage 2 — Agda 2.8.0 is INSTALLED, side by side

`cabal install Agda-2.8.0 --program-suffix=-2.8` (Homebrew's bottle was unreachable: `curl (56)
No route to host` fetching the `ghc@9.12` blob from ghcr.io — a network failure, not a local
one; Hackage was reachable throughout). Result:

- `~/.cabal/bin/agda-2.8` → **Agda 2.8.0**, built with the existing GHC 9.4.8.
- **bare `agda` is still 2.7.0.1**, so `make agda` is unchanged and nothing switched underfoot.
- **Smoke test green:** the 160-name union probe typechecks under 2.8 + v2.3.
- The `--program-suffix` route is what makes this safe. A `brew install agda` would have put
  2.8 at `/opt/homebrew/bin/agda`, which **precedes `~/.cabal/bin` on PATH** — silently
  redefining bare `agda` and running `make agda` on 2.8 against stdlib v2.2.

**RESULT: Agda 2.8.0 is a 2.6× cut to the dominant pass, and the whole repo is green under it.**

The like-for-like measurement — **1 module checked, solo, warm dependencies: exactly the
baseline's conditions**, with Subscribe-Face dirtied by a comment edit:

| | 2.7.0.1 + v2.2 | **2.8.0 + v2.3** | Speedup |
|---|---|---|---|
| Total | 927 s | **384 s** | **2.42×** |
| **Positivity** | 779 s | **300 s** | **2.60×** |
| Termination.Graph | 92 s | 52 s | 1.78× |

Subscribe-Face's solo dirty check: **15.5 min → 6.4 min.**

**Full-repo gate under 2.8: `agda-2.8 src/Main.agda` → `EXIT=0`, 40 modules, zero hard errors**
(741 s / 12.4 min for that run, though it was partially warm, so do not read it as a cold-build
figure). Extrapolating the 2.6× across a pass that is 86–91 % of the build puts a cold
`make agda` near ~17 min against today's ~40 — an estimate, not a measurement.

**This is the only lever in this entire document that reduced the 86 %.** Every flag, pragma,
and RTS knob failed; the mutual block cannot be decomposed (§4a); the telescopes are not the
cost (§4b). A newer compiler was the one thing that moved it.

**It does not replace `agda-dev`.** 2.42× off 927 s is still 6.4 minutes, which is not a dev
loop. The two multiply: the stub loop's 17.7 s was only ~3 s positivity to begin with, so under
2.8 a focus check should land nearer ~12–15 s, and the §3 targets get easier rather than harder.

An earlier, **confounded** version of this measurement is worth keeping as method: the first 2.8
run cold-built Subscribe-Face's whole 17-module tower alongside it (428 s total / 290 s
positivity) and so was not comparable to the solo baseline — it just happened to be biased
*conservatively*, since 2.8 did strictly more work in less than half the wall clock. The clean
run above confirms it rather than correcting it, but the lesson from §4c stands: compare only
runs whose conditions match.

### Isolation mechanics (so nothing here can damage the working setup)

Every step is reversible, and none of it disturbs the 2.7.0.1 + v2.2 configuration:

- stdlib v2.3 is a **git worktree** (`agda-stdlib-2.3`), sharing the object store; the v2.2
  checkout is untouched and still reports `v2.2`.
- Trials run with **`--no-libraries` plus explicit `-i` paths**, so `rxjs-research.agda-lib`'s
  `depend: standard-library-2.2` line is not edited until the upgrade is actually adopted.
- ~~Trials use `--local-interfaces` to keep `_build/2.7.0.1/`'s v2.2 interfaces intact.~~
  **THIS DID NOT WORK — measured, and it is the one part of the isolation plan that failed.**
  The Stage 1 run passed `--local-interfaces`, yet zero `.agdai` appeared next to sources and
  `_build/2.7.0.1/agda/src/…` interfaces have mtimes from the middle of that run. For a project
  with an `.agda-lib` root, Agda still routes interfaces to the project `_build`, and interface
  directories are keyed by **Agda version only, not by stdlib version**. So the v2.2 cache
  **has been overwritten with v2.3-built interfaces.**
  - **Cost: one full ~40-minute rebuild** the next time the tree is built against v2.2. Nothing
    worse — this is *not* a correctness risk: Agda validates interfaces against dependency
    source hashes, so v2.2 sources will not match v2.3-built interfaces and it will recheck
    rather than trust them.
  - **What actually isolates:** the *Agda version* key. `agda-2.8` writes `_build/2.8.0/` and
    cannot disturb `_build/2.7.0.1/` at all. The stdlib worktree likewise got its own
    `agda-stdlib-2.3/_build` (490 interfaces) without touching v2.2's.
  - **Consequence for `agda-dev`:** its planned interface isolation must NOT be built on
    `--local-interfaces`. Either accept sharing `_build` with the strict build (dev runs
    generate differently-named modules, so they do not collide on interface paths anyway), or
    isolate by pointing dev runs at a copied source tree. Verify by mtime, not by the flag's
    documentation.
- `**/*.agdai` was added to `.gitignore` — interfaces are build artifacts wherever they land,
  and `--local-interfaces` scatters them next to sources where they were previously committable.
- **Homebrew's Agda is `brew unlink`ed immediately after install.** This matters: `/opt/homebrew/bin`
  precedes `~/.cabal/bin` on PATH, so a plain `brew install agda` would silently redefine bare
  `agda` as 2.8 — and `make agda` would start running 2.8 against stdlib v2.2 with confusing
  results. Unlinked, 2.8 is reachable only at `/opt/homebrew/opt/agda/bin/agda`.
- Rollback for the whole experiment: `brew uninstall agda ghc@9.12`, `git worktree remove
  agda-stdlib-2.3`, delete stray `*.agdai`.

### Making 2.8 the default, and the remnants that had to be swept

Anthony's call: move everything over, leave nothing of 2.7. The two symlinks are his to run
(they touch the machine's environment, not the repo):

```
ln -sfn ../store/ghc-9.4.8/Agd-2.8.0-800245bd/bin/agda      ~/.cabal/bin/agda
ln -sfn ../store/ghc-9.4.8/Agd-2.8.0-f8c0a710/bin/agda-mode ~/.cabal/bin/agda-mode
rm ~/.cabal/bin/agda-2.8 ~/.cabal/bin/agda-mode-2.8
rm -rf ~/.cabal/store/ghc-9.4.8/Agd-2.7.0.1-ec1766ec        # 225 MB
```

Swept on the repo side (done):

- **`scripts/install-agda.sh` pinned `AGDA_VERSION=2.7.0.1` and `STDLIB_VERSION=2.2`.** This was
  the most important remnant by far: it is the fresh-box bootstrap and the file a new agent is
  told to run first, so leaving it would have quietly reinstalled the old toolchain on every new
  machine while this document claimed the upgrade was done. Now 2.8.0 / 2.3, with the reason
  recorded in its header.
- **`scripts/joint-probe.sh` and `scripts/burst-probe.sh`** each *generate* a throwaway
  `.agda-lib` containing `depend: standard-library-2.2`. Those still resolve on this machine
  only because v2.2 remains registered; on a fresh box built by the updated bootstrap they would
  have failed. Both now say `2.3`.
- `agda/_build/2.7.0.1` (56 MB of dead interfaces) deleted. `_build/2.8.0` is the live cache.
- Nothing else in the tree pins a version: `make agda` invokes bare `agda`, and
  `rxjs-research.agda-lib` names only the stdlib.

**stdlib CONSOLIDATED too** (Anthony's call, after checking for other consumers — the only hit
was the stdlib's own `.agda-lib` declaring `name: standard-library-2.2`, which is a
self-declaration, not a dependant). End state:

- one stdlib directory, `~/Developer/agda-libs/agda-stdlib`, checked out at **v2.3**;
- the `agda-stdlib-2.3` worktree removed (it was only ever scaffolding for the staged upgrade);
- `~/.agda/libraries` reduced to a **single** canonical line.

**I predicted this would invalidate the repo's cache. It did not — measured, and the prediction
was wrong.** The reasoning was that interfaces record dependency *paths*, so moving stdlib from
the worktree to the canonical directory would force a full cold rebuild. What actually happened
on the post-consolidation `make agda`: **`EXIT=0` in 66 s**, of which the work was rebuilding the
**227 stdlib** interfaces (its `_build` had been deleted as stale); **every repo interface was
reused** — `Subscribe-Face.agdai` still carries its pre-consolidation timestamp.

The real rule: **Agda validates an interface against its dependencies' source *hashes*, not their
paths.** The v2.3 sources are byte-identical in the worktree and the canonical clone, so nothing
downstream was invalidated. Relocating a library is therefore cheap; *changing its content* is
what costs a rebuild.

Two things follow. First, `agda-dev`'s isolation can rely on this: moving or copying a source
tree does not by itself invalidate anything. Second — **that 66 s is not a cold-build figure for
this repo and must not be quoted as one.** A genuine cold full-build number under 2.8 would mean
deleting a valid, green `_build/2.8.0` and spending ~15–20 min to regain it, which is not worth a
vanity metric when the per-module like-for-like comparison above is already authoritative. The
~17 min whole-build figure in this document remains an **extrapolation**, explicitly not measured.

### What Stage 2 had to answer

The upgrade has independent value (staying current), but its *performance* rationale rests on
one number: **does Agda 2.8.0 reduce the Positivity pass?** That is measurable without a full
repo build — typecheck Subscribe-Face under 2.8 + v2.3 and compare Positivity against the
779 s baseline. If it does not improve, the upgrade is hygiene rather than performance, and
`agda-dev` remains the only real speedup.

## 9. OPEN QUESTIONS

- **Does the whole-project dev check fit in 3 minutes?** The two heavy modules should collapse
  to ~30 s each, but the remaining ~10 minutes of the build has never been profiled and may not
  decompose the same way.
- **Does `--local-interfaces` truly isolate a dev cache from `_build`?** Assumed, not verified,
  and the answer decides whether dev mode thrashes the strict interface cache.
- **Does Agda's occurrence graph differ from the call graph** in a way that changes §4a's
  hoisting analysis? The two candidates are safe either way, but the general question is open.
