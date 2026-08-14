# Typecheck performance numbers

**Every measured timing that is tied to specific code lives here, and nowhere else.**
CLAUDE.md, the Makefile and PROOF-STATE.md carry the *rules*; this file carries the
*numbers*. They were split because numbers age much faster than rules — a module gets
split, a version bumps, and a figure quoted in three places becomes wrong in three
places.

**How to use it.** These are receipts, not specifications. Nothing here is a budget or a
target; the only enforced number is the Makefile's `AGDA_DEV_BUDGET`. Before acting on
any figure, re-measure — and read *Two ways these numbers lie* at the bottom first,
because most of the wrong numbers this project has recorded came from those two mistakes
rather than from drift.

Machine: 24 GB RAM, 14 cores, ~12 GB free at rest. Agda 2.8.0 unless stated.
Last full re-measure: 2026-08-12.

## Recorded by the build

`make agda` and `make agda-dev` write their own timings here on every green run, so
this section stays current without anyone maintaining it. **Read `best`, not `last`:**
every way a timing can be distorted — a rebuilding dependency, a concurrent
heavyweight check, a cold cache — makes a run *slower*, never faster, so the minimum
over many runs converges on the real cost while `last` reflects whatever the previous
run's cache state happened to be. A `last` far above `best` is a statement about the
cache, not about the code. Only green runs are recorded; the file is left byte-identical
when nothing moved, so a build does not dirty the tree.

<!-- AUTO:BEGIN -- maintained by scripts/perf_record.py, do not hand-edit -->

*Recorded automatically by the build. `best` is the number to trust — see `scripts/perf_record.py` for why.*

| Target | Best | Last | Runs |
|---|---|---|---|
| `make agda (full gate, 58 modules)` | **2095.0 s** | 2095.0 s | 1 |
| `make agda (full gate, 25 modules)` | **1405.0 s** | 1405.0 s | 1 |
| `make agda (full gate, 174 modules)` | **802.0 s** | 802.0 s | 1 |
| `make agda (full gate, 49 modules)` | **743.0 s** | 743.0 s | 1 |
| `make agda (full gate, 59 modules)` | **704.0 s** | 704.0 s | 1 |
| `make agda (full gate, 34 modules)` | **669.0 s** | 669.0 s | 1 |
| `make agda (full gate, 45 modules)` | **662.0 s** | 662.0 s | 1 |
| `make agda (full gate, 50 modules)` | **660.0 s** | 660.0 s | 1 |
| `make agda (full gate, 23 modules)` | **399.0 s** | 399.0 s | 1 |
| `make agda (full gate, 22 modules)` | **352.0 s** | 352.0 s | 1 |
| `make agda (full gate, 85 modules)` | **114.0 s** | 114.0 s | 1 |
| `make agda (full gate, 17 modules)` | **76.0 s** | 76.0 s | 1 |
| `make agda (full gate, 19 modules)` | **43.0 s** | 1368.0 s | 5 |
| `make agda (full gate, 18 modules)` | **40.0 s** | 69.0 s | 4 |
| `make agda (full gate, 21 modules)` | **35.0 s** | 59.0 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Init-Caps.agda` | **33.7 s** | 33.7 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda` | **21.8 s** | 21.8 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Measures.agda` | **15.9 s** | 15.9 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Caps-Depth.agda` | **13.1 s** | 13.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda` | **12.9 s** | 12.9 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda` | **11.0 s** | 11.0 s | 1 |
| `agda-dev Rx/Evaluator.agda` | **10.9 s** | 10.9 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda` | **9.4 s** | 9.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Burst-Walk.agda` | **9.2 s** | 12.0 s | 8 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7.agda` | **8.2 s** | 8.2 s | 2 |
| `agda-dev QuickCheck.agda` | **6.3 s** | 6.3 s | 1 |
| `agda-dev Rx/Frame-Width.agda` | **6.2 s** | 6.2 s | 1 |
| `agda-dev Rx/Evaluator-Theorems.agda` | **5.5 s** | 5.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Demand-Probe.agda` | **5.5 s** | 26.6 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level.agda` | **5.5 s** | 47.8 s | 11 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part6.agda` | **5.2 s** | 5.2 s | 3 |
| `agda-dev CLI/Decode.agda` | **5.1 s** | 5.1 s | 1 |
| `agda-dev Rx/Exp.agda` | **5.1 s** | 5.1 s | 1 |
| `agda-dev Rx/Slots.agda` | **5.0 s** | 5.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Chain.agda` | **4.7 s** | 4.7 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Nest.agda` | **4.6 s** | 4.6 s | 1 |
| `agda-dev Harness/Main.agda` | **4.3 s** | 7.0 s | 4 |
| `agda-dev Readme-Theorems.agda` | **4.1 s** | 4.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Demand-Probe-TEMP.agda` | **3.7 s** | 5.4 s | 2 |

<!-- AUTO:DATA {"agda-dev CLI/Decode.agda": {"best": 5.1, "last": 5.1, "runs": 1}, "agda-dev Harness/Main.agda": {"best": 4.3, "last": 7.0, "runs": 4}, "agda-dev QuickCheck.agda": {"best": 6.3, "last": 6.3, "runs": 1}, "agda-dev Readme-Theorems.agda": {"best": 4.1, "last": 4.1, "runs": 1}, "agda-dev Rx/Evaluator-Theorems.agda": {"best": 5.5, "last": 5.5, "runs": 1}, "agda-dev Rx/Evaluator.agda": {"best": 10.9, "last": 10.9, "runs": 1}, "agda-dev Rx/Exp.agda": {"best": 5.1, "last": 5.1, "runs": 1}, "agda-dev Rx/Frame-Width.agda": {"best": 6.2, "last": 6.2, "runs": 1}, "agda-dev Rx/Slots.agda": {"best": 5.0, "last": 5.0, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Burst-Walk.agda": {"best": 9.2, "last": 12.0, "runs": 8}, "agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda": {"best": 12.9, "last": 12.9, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Caps-Chain.agda": {"best": 4.7, "last": 4.7, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Caps-Depth.agda": {"best": 13.1, "last": 13.1, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Caps-Face/Part7.agda": {"best": 8.2, "last": 8.2, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Caps-Nest.agda": {"best": 4.6, "last": 4.6, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda": {"best": 9.4, "last": 9.4, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Demand-Probe-TEMP.agda": {"best": 3.7, "last": 5.4, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Demand-Probe.agda": {"best": 5.5, "last": 26.6, "runs": 3}, "agda-dev Verify-Budget-Sufficient/Init-Caps.agda": {"best": 33.7, "last": 33.7, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda": {"best": 11.0, "last": 11.0, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Measures.agda": {"best": 15.9, "last": 15.9, "runs": 4}, "agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda": {"best": 21.8, "last": 21.8, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Walk-Level.agda": {"best": 5.5, "last": 47.8, "runs": 11}, "agda-dev Verify-Budget-Sufficient/Wet/Part6.agda": {"best": 5.2, "last": 5.2, "runs": 3}, "make agda (full gate, 17 modules)": {"best": 76.0, "last": 76.0, "runs": 1}, "make agda (full gate, 174 modules)": {"best": 802.0, "last": 802.0, "runs": 1}, "make agda (full gate, 18 modules)": {"best": 40.0, "last": 69.0, "runs": 4}, "make agda (full gate, 19 modules)": {"best": 43.0, "last": 1368.0, "runs": 5}, "make agda (full gate, 21 modules)": {"best": 35.0, "last": 59.0, "runs": 3}, "make agda (full gate, 22 modules)": {"best": 352.0, "last": 352.0, "runs": 1}, "make agda (full gate, 23 modules)": {"best": 399.0, "last": 399.0, "runs": 1}, "make agda (full gate, 25 modules)": {"best": 1405.0, "last": 1405.0, "runs": 1}, "make agda (full gate, 34 modules)": {"best": 669.0, "last": 669.0, "runs": 1}, "make agda (full gate, 45 modules)": {"best": 662.0, "last": 662.0, "runs": 1}, "make agda (full gate, 49 modules)": {"best": 743.0, "last": 743.0, "runs": 1}, "make agda (full gate, 50 modules)": {"best": 660.0, "last": 660.0, "runs": 1}, "make agda (full gate, 58 modules)": {"best": 2095.0, "last": 2095.0, "runs": 1}, "make agda (full gate, 59 modules)": {"best": 704.0, "last": 704.0, "runs": 1}, "make agda (full gate, 85 modules)": {"best": 114.0, "last": 114.0, "runs": 1}} -->

<!-- AUTO:END -->

## The gate

| | |
|---|---|
| `make agda` full gate, cold | **802 s** (13 m 22 s), 41 modules |
| `make gate` on a warm-ish cache | ~350 s, 27 modules rechecked |
| `make wiring-gate`, `make unsafe-check` | seconds (textual) |

Agda 2.7.0.1 → 2.8.0 was the one lever that ever moved the gate: **927 s → 384 s** total
on Subscribe-Face, **779 s → 300 s** of that being Positivity (2.6×).

## Per-module dev-loop cost

`make agda-dev ARGS='<file>'`, cold, on a coherent cache — i.e. the real edit-one-file
case: the file is dirtied, every dependency already built.

| Module | Cold |
|---|---|
| Wet/Part2 | **35.0 s** (33.8 / 34.9 / 35.2 / 35.6 over four runs) |
| Subscribe-Face | 22.3 s |
| Caps | 21.5 s |
| Caps-Face/Part4 | 19.4 s |
| Caps-Depth | 16.7 s |
| Keeps-Ring | 16.1 s |
| Wet/Part4 | 12.0 s |
| Wet/Part5 | 10.7 s |
| Evaluator | 9.4 s |
| Caps-Sadd | 9.4 s |
| Wet/Part1, Part3, Part6 | 6.4-6.5 s |
| Verify-Well-Formed/Part1 | 6.7 s |
| Main | 6.7 s |
| Rx/Exp, Frame-Width, Provenance-Theorems | 3.6-4.7 s |

**One member: ~6 s.** That is the only number that matters for iteration speed.

Full cold scan of all 66 claim-graph modules: **512.9 s serial, max 35.0 s, median
6.6 s**, nothing over 45 s, none RED. Modules with no multi-member block cost 1.8-7.3 s.

## Where the time goes

`--profile=internal` on a genuinely dirty Wet/Part2 (254.7 s solo under real Agda):

| Pass | Time | Share |
|---|---|---|
| **Positivity** | 244,314 ms | **87.8%** |
| Termination.Graph | 20,754 ms | 7.5% |
| Typing (all) | 5,702 ms | 2.0% |
| everything else | <5,000 ms | ~2% |

`--profile=definitions` cannot answer this — it files the whole 256 s under
"Miscellaneous", because the cost belongs to no single definition.

**TERM SIZE drives Positivity, not member count.** Caps-Face's 83-member block cost
15.2 s; Subscribe-Face's 15-member block cost 300 s. In Subscribe-Face one real body is
63 ms of Positivity and fifteen are 300 s — steeply superlinear in block membership. Its
904-line prelude of 45 independent blocks is 7.8 s, so module *size* is nearly irrelevant.

A single focus run is 5.6 s total, of which **4.9 s is deserialization** and 63 ms is
Positivity (Typing 370 ms). Once the block is broken, the cost is loading imported
interfaces — a per-*process* toll.

## Splits: before and after

| | Before | After |
|---|---|---|
| Caps-Face (→ Part1..Part7) | 72.6 s whole file | **8.3 s** worst part |
| Wet (→ Part1..Part6) | 55.1 s whole file | **35.0 s** Part2; 6-12 s each for the rest |

Wet/Part2's **gate** cost is unchanged at 254.7 s — a split does not make the split-out
block cheaper, it stops every *other* edit from paying for it.

## Closed experiments — do not re-attempt

Each was measured and lost. The rules they justify are in CLAUDE.md.

| Attempt | Result |
|---|---|
| `NO_POSITIVITY_CHECK` on the block | **No-op** — accepted only before a `data`/`record` or a mutual block containing one; these declare neither (`InvalidNoPositivityCheckPragma`) |
| `--no-positivity-check` on the CLI | **Rejected** — agda-stdlib is `--safe` (exit 42 in 267 ms) |
| Per-module `OPTIONS` pragma | **Accepted, buys nothing: 805 s vs 779 s.** The pass computes the occurrence graph regardless; the flag only suppresses the strict-positivity *verdict* on datatypes, and there are no datatypes in these blocks |
| Hoisting Wet's 22 non-SCC members out of its 36 | 255 s → 220 s of Positivity: **~35 s of a ~17-minute build**, for a large refactor with real meta-coupling risk. 61% of the members for 14% of the time — which is itself the proof that the 14-member cycle carries the term size |
| Whole-project `agda-dev` sweep | **521.3 s warm / 512.9 s cold** over 66 modules against ~350 s for `make gate` at full fidelity. Strictly dominated. Warm ≈ cold because the cost is the per-process toll paid 66 times, not rechecking — so it could not be a cache-warming play either |
| `+RTS -A128m` | Noise: 944 s vs 927 s. Not GC-bound |
| Telescope width as the cost | Not it: all 19 clique signatures as bare postulates cost 9.0 s with Positivity absent |
| `--only-scope-checking` (`SCOPE=1`) as a speedup | **Buys nothing: 11.1 s vs 11.3 s.** The run is 4.9 s of deserialization; skipping ~0.5 s of typing is noise. Keep it as a fail-fast for typos, not for time |
| Dissolving Caps-Face's spurious block, judged on gate cost | "Saves nothing" — **true of the gate and the wrong number to judge a split by.** Judged on dev cost it was 72.6 s → 8.3 s |

## Parallelism and memory

- **Subscribe-Face peaks ~5.2 GB** as a single check — and a dev run was observed at
  **6.3 GB**, so 5.2 is not the true ceiling. Re-measure with `ps -eo rss` rather than
  assuming.
- **At most TWO heavyweight checks at once.** Two fit ~12 GB free; three do not, and an
  OOM costs more than the wait.
- **Maximum parallelism is wrong for the dev loop.** One process per member, 12-way: runs
  costing 5.6 s solo took 13-24 s each, 2.5 min wall. Deserialization is
  memory-bandwidth bound and does not scale with cores.
- **Batching is the lever.** Whole-file wall by `--batch`: 1→42.3 s, 2→18.5 s, 3→18.6 s,
  **4→17.2 s**, 5→23.6 s, 8→45.7 s. The U is the two costs crossing. Default 4.
- **Unsealed proof bodies on the `budget-sufficient` spine OOM Verify-Well-Formed**: three
  times, >15 GB and 30-50 min before `Killed: 9`. Sealed with `abstract`, VWF checks in
  ~1 min under 2 GB.

## Two ways these numbers lie

**1. An incoherent cache inflates a module by up to 50×.** If a dependency is rebuilding,
you are measuring the dependency. This has produced **four** phantom "slow module"
diagnoses:

| Recorded | Actual | Cause |
|---|---|---|
| Verify-Well-Formed/Part1 357 s | **6.3 s** | seven new Caps-Face interfaces building underneath |
| Main.agda 904.6 s | **6.7 s** | Main's dependencies rebuilding |
| a `Part1.agda` at ~400 s | **7.13 s** | the `-W` flag cache thrash |
| Wet 22.2 s (recorded too *low*) | **55.1 s** | measured warm and quoted as cold |

The `-W` one is worth understanding: Agda records warning mode in an interface's validity
key, so when `agda-dev` passed `-W noUserWarning` and `make agda` did not, each run
invalidated the other's entire cone — measured ping-pong on a two-line module: 120 / 0 /
120 / 120 / 120 s. **Every number recorded before 2026-08-12 is suspect, and suspect in
the slow direction.**

**2. `touch` does not dirty an Agda module — invalidation is by CONTENT.** A file whose
content is unchanged reuses its interface, so the "recheck" measures only deserialization
(6.4 s for Subscribe-Face, of which 5.1 s *is* deserialization) and reports zero
`Checking` lines. Re-appending an *identical* marker line therefore measures nothing: one
profiling run came back 4,891 ms with everything under "Miscellaneous" for exactly this
reason. Vary the marker.
