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

**Three environments, three sets of numbers.** This campaign runs in exactly three
places (`scripts/detect_env.py`): a contributor's own laptop, a Claude Code Remote
cloud container, and a GitHub Actions runner. They are not the same machine wearing a
different hostname — the cloud container measured for this file is 4 cores / 15 GB,
against the laptop's 24 GB / 14 cores below, and the ratio between them on the same
module has run 1.2x-2.9x, not a single clean multiplier. A number from one is not noise
around the other's truth; it is a measurement of a different machine. So every row below
is tagged by the environment it was measured on and rendered in its own section, and
`AGDA_DEV_BUDGET`/`CONE_BUDGET` (`scripts/detect_env.py`) are looked up per-environment
rather than set once for all three — the laptop's own 45s budget below is what it always
was, tuned to the laptop, and does not apply to the other two.

Laptop: 24 GB RAM, 14 cores, ~12 GB free at rest. Agda 2.8.0 unless stated.
Last full re-measure: 2026-08-12.

Cloud container: 4 cores, 15 GB RAM, non-macOS (Linux). No single from-nothing 66-module
cold scan has been run here yet — a `gate-heavy` run on a partially-warm cache still
recorded real, checked-for-real numbers for whichever modules its cache had not already
seen (13 of them, at the last run). The AUTO block below is that real, growing sample
rather than the laptop's one exhaustive sweep. Treat its rows as real but partial.

GitHub Actions: not yet measured at all. `AGDA_DEV_BUDGET`/`CONE_BUDGET` currently borrow
the cloud container's figures as an honest placeholder (same non-macOS shape, comparable
core count) rather than the laptop's; the first PR whose `make gate` takes the light path
in CI will start accumulating real `ci`-tagged rows the same way the cloud section grew.

## Recorded by the build

`make gate-heavy` and `make agda-dev` write their own timings here on every green run, so
this section stays current without anyone maintaining it. **Read `best`, not `last`:**
every way a timing can be distorted — a rebuilding dependency, a concurrent
heavyweight check, a cold cache — makes a run *slower*, never faster, so the minimum
over many runs converges on the real cost while `last` reflects whatever the previous
run's cache state happened to be. A `last` far above `best` is a statement about the
cache, not about the code. Only green runs are recorded; the file is left byte-identical
when nothing moved, so a build does not dirty the tree.

<!-- AUTO:BEGIN -- maintained by scripts/perf_record.py, do not hand-edit -->

*Recorded automatically by the build, one section per environment (`scripts/detect_env.py`). `best` is the number to trust — see `scripts/perf_record.py` for why.*

### local machine

| Target | Best | Last | Runs |
|---|---|---|---|
| `make gate-heavy (full gate, 55 modules)` | **3004.0 s** | 3004.0 s | 1 |
| `make gate-heavy (full gate, 58 modules)` | **2095.0 s** | 2095.0 s | 1 |
| `make gate-heavy (full gate, 51 modules)` | **1980.0 s** | 1980.0 s | 1 |
| `make gate-heavy (full gate, 52 modules)` | **1893.0 s** | 1893.0 s | 1 |
| `make gate-heavy (full gate, 37 modules)` | **1831.0 s** | 1831.0 s | 1 |
| `make gate-heavy (full gate, 43 modules)` | **1791.0 s** | 1791.0 s | 1 |
| `make gate-heavy (full gate, 54 modules)` | **1788.0 s** | 1788.0 s | 1 |
| `make gate-heavy (full gate, 306 modules)` | **1709.0 s** | 1709.0 s | 2 |
| `make gate-heavy (full gate, 77 modules)` | **1658.0 s** | 1658.0 s | 1 |
| `make gate-heavy (full gate, 32 modules)` | **1642.0 s** | 1642.0 s | 1 |
| `make gate-heavy (full gate, 35 modules)` | **1633.0 s** | 1633.0 s | 1 |
| `make gate-heavy (full gate, 61 modules)` | **1592.0 s** | 1592.0 s | 1 |
| `make gate-heavy (full gate, 70 modules)` | **1583.0 s** | 1583.0 s | 1 |
| `make gate-heavy (full gate, 69 modules)` | **1578.0 s** | 1578.0 s | 1 |
| `make gate-heavy (full gate, 38 modules)` | **1477.0 s** | 1477.0 s | 1 |
| `make gate-heavy (full gate, 28 modules)` | **1448.0 s** | 1448.0 s | 1 |
| `make gate-heavy (full gate, 46 modules)` | **1407.0 s** | 1407.0 s | 1 |
| `make gate-heavy (full gate, 24 modules)` | **1368.0 s** | 1368.0 s | 2 |
| `make gate-heavy (full gate, 30 modules)` | **1342.0 s** | 1342.0 s | 2 |
| `make gate-heavy (full gate, 36 modules)` | **1338.0 s** | 1338.0 s | 1 |
| `make gate-heavy (full gate, 29 modules)` | **1298.0 s** | 1298.0 s | 1 |
| `make gate-heavy (full gate, 26 modules)` | **1297.0 s** | 1297.0 s | 1 |
| `make gate-heavy (full gate, 25 modules)` | **1211.0 s** | 1486.0 s | 3 |
| `make gate-heavy (full gate, 174 modules)` | **802.0 s** | 802.0 s | 1 |
| `make gate-heavy (full gate, 49 modules)` | **743.0 s** | 743.0 s | 1 |
| `make gate-heavy (full gate, 59 modules)` | **704.0 s** | 704.0 s | 1 |
| `make gate-heavy (full gate, 34 modules)` | **669.0 s** | 669.0 s | 1 |
| `make gate-heavy (full gate, 45 modules)` | **662.0 s** | 662.0 s | 1 |
| `make gate-heavy (full gate, 50 modules)` | **660.0 s** | 1760.0 s | 4 |
| `make gate-heavy (full gate, 23 modules)` | **399.0 s** | 399.0 s | 1 |
| `make gate-heavy (full gate, 12 modules)` | **375.0 s** | 1107.0 s | 5 |
| `make gate-heavy (full gate, 22 modules)` | **352.0 s** | 1312.0 s | 2 |
| `make gate-heavy (full gate, 85 modules)` | **114.0 s** | 114.0 s | 1 |
| `make gate-heavy (full gate, 13 modules)` | **88.0 s** | 1106.0 s | 5 |
| `make gate-heavy (full gate, 10 modules)` | **65.0 s** | 65.0 s | 5 |
| `agda-dev ../evidence/probed/Probed/Depth-Sighted.agda` | **57.5 s** | 57.5 s | 1 |
| `agda-dev Main.agda` | **45.0 s** | >45 s | 1 |
| `make gate-heavy (full gate, 8 modules)` | **38.0 s** | 38.0 s | 6 |
| `make gate-heavy (full gate, 21 modules)` | **35.0 s** | 1697.0 s | 5 |
| `make gate-heavy (full gate, 20 modules)` | **32.0 s** | 32.0 s | 1 |
| `make gate-heavy (full gate, 19 modules)` | **31.0 s** | 1203.0 s | 11 |
| `make gate-heavy (full gate, 18 modules)` | **28.0 s** | 278.0 s | 8 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Connect.agda` | **25.9 s** | >45 s | 31 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part2.agda` | **22.6 s** | 22.6 s | 3 |
| `make gate-heavy (full gate, 14 modules)` | **19.0 s** | 1889.0 s | 2 |
| `make gate-heavy (full gate, 15 modules)` | **19.0 s** | 80.0 s | 5 |
| `make gate-heavy (full gate, 11 modules)` | **18.0 s** | 1052.0 s | 9 |
| `make gate-heavy (full gate, 16 modules)` | **15.0 s** | 1101.0 s | 6 |
| `agda-dev ../evidence/probed/Probed/Scan-Burst-Nest.agda` | **14.5 s** | >45 s | 3 |
| `agda-dev ../evidence/probed/Probed/Sight-Fit-Width.agda` | **14.4 s** | 20.9 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps.agda` | **14.1 s** | 24.4 s | 9 |
| `make gate-heavy (full gate, 9 modules)` | **14.0 s** | 38.0 s | 7 |
| `agda-dev ../evidence/refuted/Refuted/Sight-All-Fit-Slot.agda` | **13.8 s** | 13.8 s | 2 |
| `make gate-heavy (full gate, 7 modules)` | **13.0 s** | 37.0 s | 11 |
| `agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda` | **12.2 s** | 16.5 s | 11 |
| `make gate-heavy (full gate, 17 modules)` | **12.0 s** | 1495.0 s | 7 |
| `agda-dev ../evidence/probed/Probed/Thru-Step-Indexed.agda` | **10.4 s** | 10.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Measures.agda` | **10.0 s** | 12.0 s | 10 |
| `make gate-heavy (full gate, 6 modules)` | **10.0 s** | 34.0 s | 8 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part2.agda` | **9.5 s** | 11.1 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Burst-Walk.agda` | **9.2 s** | >520 s | 18 |
| `agda-dev ../evidence/refuted/Refuted/Thru-Scan-Burst-Nest.agda` | **9.0 s** | 9.0 s | 1 |
| `make gate-heavy (full gate, 3 modules)` | **9.0 s** | 9.0 s | 1 |
| `make gate-heavy (full gate, 4 modules)` | **9.0 s** | 11.0 s | 4 |
| `make gate-heavy (full gate, 5 modules)` | **9.0 s** | 13.0 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Parts.agda` | **8.7 s** | >45 s | 37 |
| `agda-dev Verify-Well-Formed/Part9.agda` | **8.7 s** | 8.7 s | 2 |
| `agda-dev Verify-Well-Formed/Part12.agda` | **8.5 s** | 8.5 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda` | **8.1 s** | 8.1 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda` | **8.1 s** | 8.1 s | 2 |
| `agda-dev Verify-Well-Formed/Part6.agda` | **7.9 s** | 7.9 s | 1 |
| `agda-dev Rx/Evaluator.agda` | **7.7 s** | 7.7 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part4.agda` | **7.7 s** | 9.5 s | 8 |
| `agda-dev Verify-Well-Formed/Part10.agda` | **7.7 s** | 9.0 s | 3 |
| `agda-dev Verify-Well-Formed/Part7.agda` | **7.5 s** | 7.5 s | 2 |
| `agda-dev Verify-Well-Formed/Part11.agda` | **7.4 s** | 7.4 s | 4 |
| `agda-dev Verify-Well-Formed/Part4.agda` | **7.3 s** | 8.5 s | 4 |
| `agda-dev Verify-Well-Formed/Part5.agda` | **7.3 s** | 7.3 s | 2 |
| `agda-dev Verify-Batch-Simultaneous/The-Proof.agda` | **7.0 s** | >2 s | 1023 |
| `make gate-heavy (full gate, 2 modules)` | **7.0 s** | 7.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Depth.agda` | **6.5 s** | 6.5 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda` | **6.4 s** | >2 s | 292 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part6.agda` | **6.4 s** | 36.0 s | 7 |
| `agda-dev Verify-Budget-Sufficient/Desc-Ceil.agda` | **5.9 s** | 5.9 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Nest-Clos-Cap-Free.agda` | **5.8 s** | 5.8 s | 2 |
| `agda-dev ../evidence/probed/Probed/Scan-Arr-Clos-Key.agda` | **5.6 s** | 5.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Arms.agda` | **5.6 s** | >45 s | 35 |
| `agda-dev ../evidence/probed/Probed/Sight-All-Stream.agda` | **5.5 s** | 5.5 s | 1 |
| `agda-dev Rx/Evaluator-Theorems.agda` | **5.5 s** | 5.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level.agda` | **5.5 s** | >46 s | 29 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part3.agda` | **5.4 s** | 6.3 s | 5 |
| `agda-dev ../evidence/refuted/Refuted/Chain-Level-Unbounded.agda` | **5.3 s** | 5.3 s | 1 |
| `agda-dev QuickCheck.agda` | **5.3 s** | 5.3 s | 2 |
| `agda-dev Verify-Well-Formed/Part13.agda` | **5.3 s** | >1 s | 164 |
| `agda-dev CLI/Decode.agda` | **5.1 s** | 5.1 s | 1 |
| `make gate-heavy (full gate, 1 modules)` | **5.0 s** | 7.0 s | 3 |
| `agda-dev ../evidence/probed/Probed/Sight-Thru-Val.agda` | **4.8 s** | 4.8 s | 1 |
| `agda-dev Rx/Frame-Width.agda` | **4.7 s** | 4.7 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part3.agda` | **4.7 s** | 4.7 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Nest-Clos-Flat.agda` | **4.6 s** | 4.6 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Step-Frame-Clos.agda` | **4.6 s** | 4.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nodes-Nest-Walk.agda` | **4.6 s** | 4.6 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Live-Nest-Walk.agda` | **4.4 s** | 5.1 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Chain-Step-Store.agda` | **4.3 s** | 4.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part1.agda` | **4.3 s** | 4.3 s | 5 |
| `agda-dev Rx/Hop-Depth.agda` | **4.2 s** | 4.2 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Nest-Arith.agda` | **4.2 s** | 4.2 s | 5 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Step.agda` | **4.2 s** | 4.2 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Sub.agda` | **4.2 s** | 4.9 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Walk-Factor.agda` | **4.2 s** | 4.2 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Nest-Depth-Live-Reg.agda` | **4.1 s** | 4.1 s | 1 |
| `agda-dev Readme-Theorems.agda` | **4.1 s** | 4.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Psi-Split.agda` | **4.1 s** | 4.1 s | 9 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Statement.agda` | **4.1 s** | 4.1 s | 8 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part5.agda` | **4.0 s** | 4.9 s | 10 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Push.agda` | **4.0 s** | 4.0 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Init-Nest.agda` | **4.0 s** | 4.6 s | 5 |
| `agda-dev ../evidence/probed/Probed/Chain-Step-Live-Deferred.agda` | **3.9 s** | 3.9 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Nest-Size-Currency.agda` | **3.9 s** | 3.9 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Burst-Walk/Predicates.agda` | **3.9 s** | 3.9 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part1.agda` | **3.9 s** | 5.5 s | 12 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part6.agda` | **3.9 s** | 3.9 s | 6 |
| `agda-dev ../evidence/probed/Probed/Chain-Step-Abs-Charge.agda` | **3.8 s** | 9.7 s | 3 |
| `agda-dev ../evidence/probed/Probed/PushVals-Caps.agda` | **3.8 s** | >45 s | 5 |
| `agda-dev ../evidence/refuted/Refuted/Chain-Step-Live-Additive.agda` | **3.8 s** | 3.8 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Drain-Reach-Gas.agda` | **3.8 s** | 3.8 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Subscribe-Burst-Width.agda` | **3.8 s** | >45 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Regs-Nest-Walk.agda` | **3.8 s** | 4.9 s | 10 |
| `agda-dev ../evidence/refuted/Refuted/Nest-Clos-Stratified.agda` | **3.7 s** | 3.7 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Chain.agda` | **3.7 s** | 3.7 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Deliver-Measure.agda` | **3.7 s** | 4.6 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Deliveries.agda` | **3.7 s** | 3.7 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Depth-Sighted.agda` | **3.7 s** | >200 s | 12 |
| `agda-dev Verify-Budget-Sufficient/Node-Fresh.agda` | **3.7 s** | 6.6 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Op-Budget.agda` | **3.7 s** | 3.7 s | 3 |
| `agda-dev ../evidence/probed/Probed/Scan-Arr-Margin.agda` | **3.6 s** | 8.6 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Clos-Wrap-Sum.agda` | **3.6 s** | 3.6 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Share-Go-Path.agda` | **3.6 s** | 3.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Face.agda` | **3.6 s** | 3.6 s | 4 |
| `agda-dev Rx/Hop-Spine.agda` | **3.5 s** | 3.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Init-Caps.agda` | **3.5 s** | 20.3 s | 9 |
| `agda-dev Verify-Budget-Sufficient/Level-Mono.agda` | **3.5 s** | 3.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nest-Subst.agda` | **3.5 s** | 3.9 s | 8 |
| `agda-dev Verify-Budget-Sufficient/Sighted-Fit.agda` | **3.5 s** | 3.5 s | 3 |
| `agda-dev Verify-Well-Formed/Part8.agda` | **3.5 s** | 3.5 s | 5 |
| `agda-dev ../evidence/refuted/Refuted/Subscribe-Caps-Nest.agda` | **3.4 s** | 3.4 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Thru-Subscribe-Nest.agda` | **3.4 s** | 5.4 s | 2 |
| `agda-dev Harness/Main.agda` | **3.4 s** | 3.7 s | 18 |
| `agda-dev Rx/Hop-Eta-Cong.agda` | **3.4 s** | 3.4 s | 1 |
| `agda-dev Rx/Inputs-Below.agda` | **3.4 s** | 3.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Term.agda` | **3.4 s** | 3.4 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Nest-Ceiling.agda` | **3.4 s** | 3.7 s | 3 |
| `agda-dev Verify-Well-Formed/Part1.agda` | **3.4 s** | 3.4 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Inner-Drain-Nest.agda` | **3.3 s** | 3.3 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Op-Dominance.agda` | **3.3 s** | 3.3 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Inner-Drain-Share-Nest.agda` | **3.2 s** | 3.2 s | 1 |
| `agda-dev Rx/Exp.agda` | **3.2 s** | 3.2 s | 3 |
| `agda-dev Rx/Width-Subst.agda` | **3.2 s** | 3.2 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Nest.agda` | **3.2 s** | 3.9 s | 4 |
| `agda-dev ../evidence/refuted/Refuted/Scan-Seed-Caps.agda` | **3.1 s** | 3.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nest-Store.agda` | **3.1 s** | 4.0 s | 14 |
| `agda-dev Verify-Budget-Sufficient/Nest-Walk.agda` | **3.1 s** | >45 s | 78 |
| `agda-dev Verify-Budget-Sufficient/Node-Table.agda` | **3.1 s** | 3.1 s | 2 |
| `agda-dev Verify-Well-Formed/Part2.agda` | **3.1 s** | 3.1 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Fan-Caps.agda` | **3.0 s** | 3.5 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Nest-Cap.agda` | **3.0 s** | 3.8 s | 4 |
| `agda-dev Verify-Well-Formed/Part3.agda` | **3.0 s** | 3.1 s | 7 |
| `agda-dev Rx/Burst-Ceil.agda` | **2.8 s** | 2.8 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Queue-Dead.agda` | **2.8 s** | 6.7 s | 2 |
| `agda-dev Rx/Clos-Eta-Cong.agda` | **2.7 s** | 2.7 s | 1 |
| `agda-dev ../evidence/probed/Probed/Sync-Factor.agda` | **2.6 s** | 2.6 s | 1 |
| `agda-dev Rx/MergeAll-Laws.agda` | **2.6 s** | 2.6 s | 4 |
| `agda-dev Rx/Nest-Depth.agda` | **2.6 s** | 2.7 s | 3 |
| `agda-dev Rx/Slot-Hop.agda` | **2.6 s** | 3.0 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Nest-Burst.agda` | **2.6 s** | 3.4 s | 4 |
| `agda-dev Rx/Clos-Size.agda` | **2.5 s** | 3.2 s | 3 |
| `agda-dev Rx/Slot-Clos.agda` | **2.5 s** | 3.5 s | 3 |
| `agda-dev Rx/Slots.agda` | **2.5 s** | 2.5 s | 3 |
| `agda-dev Decide.agda` | **1.6 s** | 1.6 s | 1 |

### cloud container

| Target | Best | Last | Runs |
|---|---|---|---|
| `make gate-heavy (full gate, 51 modules)` | **3917.0 s** | 3917.0 s | 1 |
| `make gate-heavy (full gate, 24 modules)` | **2643.0 s** | 2643.0 s | 1 |
| `make gate-heavy (full gate, 37 modules)` | **2476.0 s** | 2476.0 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Chains-Burst-Flat.agda` | **160.2 s** | >160 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Main.agda` | **160.1 s** | >160 s | 1 |
| `agda-dev ../evidence/probed/Probed/Cascade-Chain-Count.agda` | **139.0 s** | 139.0 s | 1 |
| `agda-dev ../evidence/probed/Probed/Depth-Sighted.agda` | **107.3 s** | 107.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nest-Walk.agda` | **106.8 s** | >160 s | 5 |
| `agda-dev Implementation/Unit-Test/Case-378.agda` | **97.0 s** | 97.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Connect.agda` | **82.4 s** | 82.4 s | 1 |
| `agda-dev Implementation/Unit-Test/Case-315.agda` | **73.4 s** | 73.4 s | 1 |
| `make gate-heavy (full gate, 13 modules)` | **64.0 s** | 64.0 s | 1 |
| `agda-dev ../evidence/probed/Probed/Chain-Step-Abs-Charge.agda` | **59.1 s** | 59.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Parts.agda` | **47.4 s** | 47.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level.agda` | **47.3 s** | 47.3 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps.agda` | **46.5 s** | 68.9 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Nest-Walk/Share-Fold.agda` | **40.0 s** | >160 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda` | **36.5 s** | 47.2 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Walk-Sink.agda` | **34.3 s** | 41.7 s | 4 |
| `agda-dev ../evidence/probed/Probed/Cascade-Store-Components.agda` | **33.9 s** | 33.9 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Measures.agda` | **32.3 s** | 45.4 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part2.agda` | **29.6 s** | 29.6 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Burst-Walk.agda` | **29.3 s** | 29.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part2.agda` | **26.7 s** | 31.5 s | 2 |
| `agda-dev Rx/Evaluator.agda` | **23.2 s** | 23.2 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Depth-Sighted.agda` | **22.6 s** | 22.6 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part4.agda` | **22.1 s** | 27.0 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part6.agda` | **21.3 s** | 30.3 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Depth.agda` | **20.4 s** | 27.6 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Nodes.agda` | **19.8 s** | >160 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda` | **19.5 s** | 23.6 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Arms.agda` | **19.2 s** | 19.2 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Sadd.agda` | **17.9 s** | 17.9 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda` | **17.8 s** | 23.5 s | 3 |
| `agda-dev Main.agda` | **16.0 s** | 67.2 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Desc-Ceil.agda` | **15.3 s** | 15.3 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Node-Fresh.agda` | **14.9 s** | 23.0 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Frame-Face.agda` | **14.5 s** | 32.5 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part3.agda` | **14.4 s** | 16.5 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Arrival-Caps.agda` | **14.4 s** | 33.7 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Queue-Dead.agda` | **14.3 s** | 14.3 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Sub.agda` | **13.8 s** | 13.8 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Depth-Fit.agda` | **13.6 s** | >160 s | 18 |
| `agda-dev ../evidence/probed/Probed/Thru-Step-Indexed.agda` | **13.3 s** | 13.3 s | 1 |
| `agda-dev CLI/Decode.agda` | **13.3 s** | 13.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Nest.agda` | **12.9 s** | >160 s | 3 |
| `agda-dev ../evidence/refuted/Refuted/Fold-Path-Regs-Len.agda` | **12.7 s** | 12.7 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nest-Subst.agda` | **12.6 s** | 12.6 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Frame-Step-Size-Level.agda` | **12.1 s** | 12.1 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Nest-Arith.agda` | **11.9 s** | 14.6 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Live-Nest-Walk.agda` | **11.9 s** | 14.8 s | 8 |
| `agda-dev Verify-Budget-Sufficient/Nest-Ceiling.agda` | **11.8 s** | 11.8 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Caps.agda` | **11.7 s** | 20.9 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Ring-Vocabulary.agda` | **11.7 s** | >160 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part5.agda` | **11.6 s** | 15.3 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Step.agda` | **11.6 s** | 11.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Init-Caps.agda` | **11.6 s** | 13.9 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Arrival-Ledger.agda` | **11.3 s** | 13.2 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Nodes-Nest-Walk.agda` | **11.3 s** | 13.8 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Chain-Caps-OK.agda` | **11.2 s** | 13.7 s | 6 |
| `agda-dev Verify-Budget-Sufficient/Nest-Store.agda` | **11.2 s** | 11.2 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part1.agda` | **11.1 s** | 11.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part1.agda` | **11.0 s** | 13.0 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Live.agda` | **10.8 s** | 15.3 s | 2 |
| `agda-dev ../evidence/refuted/Refuted/Frame-Step-Size-Store.agda` | **10.6 s** | 10.6 s | 1 |
| `agda-dev QuickCheck.agda` | **10.6 s** | 10.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Deliver-Measure.agda` | **10.6 s** | 10.6 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Push.agda` | **10.5 s** | 10.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Regs-Nest-Walk.agda` | **10.4 s** | 12.3 s | 12 |
| `agda-dev Verify-Budget-Sufficient/Caps-Term.agda` | **10.3 s** | 10.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Init-Nest.agda` | **10.3 s** | 10.3 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level/Statement.agda` | **10.3 s** | 10.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Deliveries.agda` | **10.2 s** | 10.2 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Hop-Spine-Face.agda` | **10.2 s** | 10.2 s | 1 |
| `agda-dev ../evidence/probed/Probed/Chain-Step-Live-Deferred.agda` | **9.9 s** | 9.9 s | 2 |
| `agda-dev ../evidence/probed/Probed/Thru-Arr-Slot.agda` | **9.8 s** | 14.7 s | 5 |
| `agda-dev Verify-Budget-Sufficient/Nest-Cap.agda` | **9.8 s** | 9.8 s | 2 |
| `agda-dev ../evidence/probed/Probed/Burst-Nest-Ladder.agda` | **9.7 s** | 9.7 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Nest.agda` | **9.6 s** | 9.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Walk-Factor.agda` | **9.6 s** | 9.6 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Burst-Walk/Predicates.agda` | **9.5 s** | 9.5 s | 1 |
| `agda-dev Rx/Frame-Width.agda` | **9.4 s** | 9.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Level-Mono.agda` | **9.4 s** | 9.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part6.agda` | **9.4 s** | 9.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Fan-Caps.agda` | **9.3 s** | 9.3 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Psi-Split.agda` | **9.3 s** | 9.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Chain.agda` | **9.2 s** | 9.2 s | 1 |
| `agda-dev Verify-Well-Formed/Part7.agda` | **8.9 s** | 8.9 s | 1 |
| `agda-dev Verify-Well-Formed/Part12.agda` | **8.8 s** | 8.8 s | 1 |
| `agda-dev Verify-Well-Formed/Part8.agda` | **8.8 s** | 8.8 s | 1 |
| `agda-dev Verify-Well-Formed/Part9.agda` | **8.8 s** | 8.8 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Drain-Root-Ceil.agda` | **8.8 s** | 8.8 s | 1 |
| `agda-dev Rx/Exp.agda` | **8.6 s** | 8.6 s | 1 |
| `agda-dev Rx/Width-Subst.agda` | **8.5 s** | 8.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Op-Budget.agda` | **8.5 s** | 8.5 s | 1 |
| `agda-dev Verify-Well-Formed/Part11.agda` | **8.5 s** | 8.5 s | 1 |
| `agda-dev ../evidence/probed/Probed/Chain-Step-Live-Nest.agda` | **8.4 s** | 8.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part3.agda` | **8.4 s** | 8.4 s | 1 |
| `agda-dev Verify-Well-Formed/Part5.agda` | **8.4 s** | 8.4 s | 1 |
| `agda-dev CLI/Main.agda` | **8.3 s** | 8.3 s | 1 |
| `agda-dev Verify-Well-Formed/Part1.agda` | **8.2 s** | 8.2 s | 1 |
| `agda-dev Verify-Well-Formed/Part6.agda` | **8.1 s** | 8.1 s | 1 |
| `agda-dev Rx/Inputs-Below.agda` | **8.0 s** | 8.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Sighted-Fit.agda` | **8.0 s** | 8.0 s | 1 |
| `agda-dev Verify-Well-Formed/Part10.agda` | **7.9 s** | 7.9 s | 1 |
| `agda-dev ../evidence/refuted/Refuted/Chain-Step-Regs-Cap.agda` | **7.8 s** | 7.8 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Op-Dominance.agda` | **7.8 s** | 7.8 s | 1 |
| `agda-dev Verify-Well-Formed/Part2.agda` | **7.8 s** | 7.8 s | 1 |
| `agda-dev Verify-Well-Formed/Part4.agda` | **7.8 s** | 7.8 s | 1 |
| `agda-dev Rx/Clos-Size.agda` | **7.6 s** | 7.6 s | 1 |
| `agda-dev Rx/Hop-Depth.agda` | **7.5 s** | 7.5 s | 1 |
| `agda-dev ../evidence/probed/Probed/Sync-Factor.agda` | **7.4 s** | 7.4 s | 1 |
| `agda-dev CLI/Encode.agda` | **7.3 s** | 7.3 s | 1 |
| `agda-dev Rx/MergeAll-Laws.agda` | **7.3 s** | 7.3 s | 1 |
| `agda-dev Verify-Well-Formed/Part3.agda` | **7.3 s** | 7.3 s | 1 |
| `agda-dev Harness/Main.agda` | **7.2 s** | 10.6 s | 2 |
| `agda-dev Rx/Hop-Eta-Cong.agda` | **7.2 s** | 7.2 s | 1 |
| `agda-dev Rx/Time-Theorems.agda` | **7.2 s** | 7.2 s | 1 |
| `agda-dev Readme-Theorems.agda` | **7.1 s** | 7.1 s | 1 |
| `agda-dev Rx/Clos-Eta-Cong.agda` | **7.1 s** | 7.1 s | 1 |
| `agda-dev Rx/Hop-Spine.agda` | **7.1 s** | 7.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nest-Depth-Size.agda` | **7.1 s** | 7.1 s | 1 |
| `agda-dev Rx/Evaluator-Theorems.agda` | **7.0 s** | 7.0 s | 1 |
| `agda-dev Rx/Slot-Clos.agda` | **7.0 s** | 7.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Depth/Take-Zero.agda` | **7.0 s** | 7.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Nest-Burst.agda` | **7.0 s** | 7.0 s | 2 |
| `agda-dev ../evidence/probed/Probed/Burst-OutW.agda` | **6.9 s** | 6.9 s | 1 |
| `agda-dev Implementation/Unit-Test/Prelude.agda` | **6.9 s** | 6.9 s | 1 |
| `agda-dev Rx/Burst-Ceil.agda` | **6.9 s** | 6.9 s | 1 |
| `agda-dev Rx/Provenance-Theorems.agda` | **6.9 s** | 6.9 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Node-Table.agda` | **6.9 s** | 6.9 s | 1 |
| `agda-dev Rx/Slot-Hop.agda` | **6.8 s** | 6.8 s | 1 |
| `agda-dev Rx/Nest-Depth.agda` | **6.7 s** | 6.7 s | 1 |
| `agda-dev Rx/Slots.agda` | **6.7 s** | 6.7 s | 1 |
| `agda-dev Implementation/Unit-Test.agda` | **6.6 s** | 6.6 s | 2 |
| `agda-dev ../evidence/probed/Probed/Root.agda` | **6.5 s** | 6.5 s | 1 |
| `agda-dev CLI/IO.agda` | **6.4 s** | 6.4 s | 1 |
| `agda-dev Verify-Batch-Simultaneous/Batch-Theorems.agda` | **5.0 s** | 5.0 s | 1 |
| `agda-dev Rx/Protocol.agda` | **3.8 s** | 3.8 s | 1 |
| `agda-dev Rx/Prim.agda` | **3.6 s** | 3.6 s | 1 |
| `agda-dev CLI/JSON.agda` | **3.5 s** | 3.5 s | 1 |
| `agda-dev Implementation.agda` | **3.5 s** | 3.5 s | 1 |
| `agda-dev Spec.agda` | **3.5 s** | 3.5 s | 1 |
| `agda-dev Decide.agda` | **3.4 s** | 3.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda` | **2.0 s** | 43.7 s | 14 |
| `agda-dev Verify-Batch-Simultaneous/The-Proof.agda` | **1.0 s** | >2 s | 81 |
| `agda-dev Verify-Well-Formed/Part13.agda` | **1.0 s** | >1 s | 3 |

<!-- AUTO:DATA {"cloud|agda-dev ../evidence/probed/Probed/Burst-Nest-Ladder.agda": {"best": 9.7, "last": 9.7, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Burst-OutW.agda": {"best": 6.9, "last": 6.9, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Cascade-Chain-Count.agda": {"best": 139.0, "last": 139.0, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Cascade-Store-Components.agda": {"best": 33.9, "last": 33.9, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Chain-Step-Abs-Charge.agda": {"best": 59.1, "last": 59.1, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Chain-Step-Live-Deferred.agda": {"best": 9.9, "last": 9.9, "runs": 2}, "cloud|agda-dev ../evidence/probed/Probed/Chain-Step-Live-Nest.agda": {"best": 8.4, "last": 8.4, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Depth-Sighted.agda": {"best": 107.3, "last": 107.3, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Root.agda": {"best": 6.5, "last": 6.5, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Sync-Factor.agda": {"best": 7.4, "last": 7.4, "runs": 1}, "cloud|agda-dev ../evidence/probed/Probed/Thru-Arr-Slot.agda": {"best": 9.8, "last": 14.7, "runs": 5}, "cloud|agda-dev ../evidence/probed/Probed/Thru-Step-Indexed.agda": {"best": 13.3, "last": 13.3, "runs": 1}, "cloud|agda-dev ../evidence/refuted/Refuted/Chain-Step-Regs-Cap.agda": {"best": 7.8, "last": 7.8, "runs": 1}, "cloud|agda-dev ../evidence/refuted/Refuted/Chains-Burst-Flat.agda": {"best": 160.2, "floor": true, "last": 160.2, "runs": 1}, "cloud|agda-dev ../evidence/refuted/Refuted/Drain-Root-Ceil.agda": {"best": 8.8, "last": 8.8, "runs": 1}, "cloud|agda-dev ../evidence/refuted/Refuted/Fold-Path-Regs-Len.agda": {"best": 12.7, "last": 12.7, "runs": 1}, "cloud|agda-dev ../evidence/refuted/Refuted/Frame-Step-Size-Level.agda": {"best": 12.1, "last": 12.1, "runs": 2}, "cloud|agda-dev ../evidence/refuted/Refuted/Frame-Step-Size-Store.agda": {"best": 10.6, "last": 10.6, "runs": 1}, "cloud|agda-dev ../evidence/refuted/Refuted/Main.agda": {"best": 160.1, "floor": true, "last": 160.1, "runs": 1}, "cloud|agda-dev CLI/Decode.agda": {"best": 13.3, "last": 13.3, "runs": 1}, "cloud|agda-dev CLI/Encode.agda": {"best": 7.3, "last": 7.3, "runs": 1}, "cloud|agda-dev CLI/IO.agda": {"best": 6.4, "last": 6.4, "runs": 1}, "cloud|agda-dev CLI/JSON.agda": {"best": 3.5, "last": 3.5, "runs": 1}, "cloud|agda-dev CLI/Main.agda": {"best": 8.3, "last": 8.3, "runs": 1}, "cloud|agda-dev Decide.agda": {"best": 3.4, "last": 3.4, "runs": 1}, "cloud|agda-dev Harness/Main.agda": {"best": 7.2, "last": 10.6, "runs": 2}, "cloud|agda-dev Implementation.agda": {"best": 3.5, "last": 3.5, "runs": 1}, "cloud|agda-dev Implementation/Unit-Test.agda": {"best": 6.6, "last": 6.6, "runs": 2}, "cloud|agda-dev Implementation/Unit-Test/Case-315.agda": {"best": 73.4, "last": 73.4, "runs": 1}, "cloud|agda-dev Implementation/Unit-Test/Case-378.agda": {"best": 97.0, "last": 97.0, "runs": 1}, "cloud|agda-dev Implementation/Unit-Test/Prelude.agda": {"best": 6.9, "last": 6.9, "runs": 1}, "cloud|agda-dev Main.agda": {"best": 16.0, "last": 67.2, "runs": 4}, "cloud|agda-dev QuickCheck.agda": {"best": 10.6, "last": 10.6, "runs": 1}, "cloud|agda-dev Readme-Theorems.agda": {"best": 7.1, "last": 7.1, "runs": 1}, "cloud|agda-dev Rx/Burst-Ceil.agda": {"best": 6.9, "last": 6.9, "runs": 1}, "cloud|agda-dev Rx/Clos-Eta-Cong.agda": {"best": 7.1, "last": 7.1, "runs": 1}, "cloud|agda-dev Rx/Clos-Size.agda": {"best": 7.6, "last": 7.6, "runs": 1}, "cloud|agda-dev Rx/Evaluator-Theorems.agda": {"best": 7.0, "last": 7.0, "runs": 1}, "cloud|agda-dev Rx/Evaluator.agda": {"best": 23.2, "last": 23.2, "runs": 1}, "cloud|agda-dev Rx/Exp.agda": {"best": 8.6, "last": 8.6, "runs": 1}, "cloud|agda-dev Rx/Frame-Width.agda": {"best": 9.4, "last": 9.4, "runs": 1}, "cloud|agda-dev Rx/Hop-Depth.agda": {"best": 7.5, "last": 7.5, "runs": 1}, "cloud|agda-dev Rx/Hop-Eta-Cong.agda": {"best": 7.2, "last": 7.2, "runs": 1}, "cloud|agda-dev Rx/Hop-Spine.agda": {"best": 7.1, "last": 7.1, "runs": 1}, "cloud|agda-dev Rx/Inputs-Below.agda": {"best": 8.0, "last": 8.0, "runs": 1}, "cloud|agda-dev Rx/MergeAll-Laws.agda": {"best": 7.3, "last": 7.3, "runs": 1}, "cloud|agda-dev Rx/Nest-Depth.agda": {"best": 6.7, "last": 6.7, "runs": 1}, "cloud|agda-dev Rx/Prim.agda": {"best": 3.6, "last": 3.6, "runs": 1}, "cloud|agda-dev Rx/Protocol.agda": {"best": 3.8, "last": 3.8, "runs": 1}, "cloud|agda-dev Rx/Provenance-Theorems.agda": {"best": 6.9, "last": 6.9, "runs": 1}, "cloud|agda-dev Rx/Slot-Clos.agda": {"best": 7.0, "last": 7.0, "runs": 1}, "cloud|agda-dev Rx/Slot-Hop.agda": {"best": 6.8, "last": 6.8, "runs": 1}, "cloud|agda-dev Rx/Slots.agda": {"best": 6.7, "last": 6.7, "runs": 1}, "cloud|agda-dev Rx/Time-Theorems.agda": {"best": 7.2, "last": 7.2, "runs": 1}, "cloud|agda-dev Rx/Width-Subst.agda": {"best": 8.5, "last": 8.5, "runs": 1}, "cloud|agda-dev Spec.agda": {"best": 3.5, "last": 3.5, "runs": 1}, "cloud|agda-dev Verify-Batch-Simultaneous/Batch-Theorems.agda": {"best": 5.0, "last": 5.0, "runs": 1}, "cloud|agda-dev Verify-Batch-Simultaneous/The-Proof.agda": {"best": 1.0, "floor": true, "last": 2.0, "runs": 81}, "cloud|agda-dev Verify-Budget-Sufficient/Burst-Walk.agda": {"best": 29.3, "last": 29.3, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Burst-Walk/Predicates.agda": {"best": 9.5, "last": 9.5, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda": {"best": 2.0, "last": 43.7, "runs": 14}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Chain.agda": {"best": 9.2, "last": 9.2, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Depth.agda": {"best": 20.4, "last": 27.6, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Depth/Take-Zero.agda": {"best": 7.0, "last": 7.0, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Nest-Arith.agda": {"best": 11.9, "last": 14.6, "runs": 6}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part1.agda": {"best": 11.0, "last": 13.0, "runs": 4}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part2.agda": {"best": 26.7, "last": 31.5, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part3.agda": {"best": 14.4, "last": 16.5, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part4.agda": {"best": 22.1, "last": 27.0, "runs": 6}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part5.agda": {"best": 11.6, "last": 15.3, "runs": 4}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part6.agda": {"best": 21.3, "last": 30.3, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Arrival-Caps.agda": {"best": 14.4, "last": 33.7, "runs": 6}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Arrival-Ledger.agda": {"best": 11.3, "last": 13.2, "runs": 4}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Caps.agda": {"best": 11.7, "last": 20.9, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Live.agda": {"best": 10.8, "last": 15.3, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Nest.agda": {"best": 12.9, "floor": true, "last": 160.3, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Cascade-Nodes.agda": {"best": 19.8, "floor": true, "last": 160.2, "runs": 4}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Chain-Caps-OK.agda": {"best": 11.2, "last": 13.7, "runs": 6}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Depth-Fit.agda": {"best": 13.6, "floor": true, "last": 160.2, "runs": 18}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Frame-Face.agda": {"best": 14.5, "last": 32.5, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Ring-Vocabulary.agda": {"best": 11.7, "floor": true, "last": 160.2, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Face/Part7/Walk-Sink.agda": {"best": 34.3, "last": 41.7, "runs": 4}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Nest.agda": {"best": 9.6, "last": 9.6, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Sadd.agda": {"best": 17.9, "last": 17.9, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Caps-Term.agda": {"best": 10.3, "last": 10.3, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Caps.agda": {"best": 46.5, "last": 68.9, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Deliver-Measure.agda": {"best": 10.6, "last": 10.6, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Deliveries.agda": {"best": 10.2, "last": 10.2, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda": {"best": 19.5, "last": 23.6, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Depth-Sighted.agda": {"best": 22.6, "last": 22.6, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Desc-Ceil.agda": {"best": 15.3, "last": 15.3, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Fan-Caps.agda": {"best": 9.3, "last": 9.3, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Hop-Spine-Face.agda": {"best": 10.2, "last": 10.2, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Hop-Spine-Push.agda": {"best": 10.5, "last": 10.5, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Hop-Spine-Step.agda": {"best": 11.6, "last": 11.6, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Hop-Spine-Sub.agda": {"best": 13.8, "last": 13.8, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Init-Caps.agda": {"best": 11.6, "last": 13.9, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Init-Nest.agda": {"best": 10.3, "last": 10.3, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda": {"best": 17.8, "last": 23.5, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Level-Mono.agda": {"best": 9.4, "last": 9.4, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Live-Nest-Walk.agda": {"best": 11.9, "last": 14.8, "runs": 8}, "cloud|agda-dev Verify-Budget-Sufficient/Measures.agda": {"best": 32.3, "last": 45.4, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Burst.agda": {"best": 7.0, "last": 7.0, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Cap.agda": {"best": 9.8, "last": 9.8, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Ceiling.agda": {"best": 11.8, "last": 11.8, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Depth-Size.agda": {"best": 7.1, "last": 7.1, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Store.agda": {"best": 11.2, "last": 11.2, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Subst.agda": {"best": 12.6, "last": 12.6, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Walk.agda": {"best": 106.8, "floor": true, "last": 160.3, "runs": 5}, "cloud|agda-dev Verify-Budget-Sufficient/Nest-Walk/Share-Fold.agda": {"best": 40.0, "floor": true, "last": 160.2, "runs": 4}, "cloud|agda-dev Verify-Budget-Sufficient/Node-Fresh.agda": {"best": 14.9, "last": 23.0, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Node-Table.agda": {"best": 6.9, "last": 6.9, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Nodes-Nest-Walk.agda": {"best": 11.3, "last": 13.8, "runs": 3}, "cloud|agda-dev Verify-Budget-Sufficient/Op-Budget.agda": {"best": 8.5, "last": 8.5, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Op-Dominance.agda": {"best": 7.8, "last": 7.8, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Psi-Split.agda": {"best": 9.3, "last": 9.3, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Queue-Dead.agda": {"best": 14.3, "last": 14.3, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Regs-Nest-Walk.agda": {"best": 10.4, "last": 12.3, "runs": 12}, "cloud|agda-dev Verify-Budget-Sufficient/Sighted-Fit.agda": {"best": 8.0, "last": 8.0, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda": {"best": 36.5, "last": 47.2, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Walk-Factor.agda": {"best": 9.6, "last": 9.6, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Walk-Level.agda": {"best": 47.3, "last": 47.3, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Walk-Level/Arms.agda": {"best": 19.2, "last": 19.2, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Walk-Level/Connect.agda": {"best": 82.4, "last": 82.4, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Walk-Level/Parts.agda": {"best": 47.4, "last": 47.4, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Walk-Level/Statement.agda": {"best": 10.3, "last": 10.3, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Wet/Part1.agda": {"best": 11.1, "last": 11.1, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Wet/Part2.agda": {"best": 29.6, "last": 29.6, "runs": 2}, "cloud|agda-dev Verify-Budget-Sufficient/Wet/Part3.agda": {"best": 8.4, "last": 8.4, "runs": 1}, "cloud|agda-dev Verify-Budget-Sufficient/Wet/Part6.agda": {"best": 9.4, "last": 9.4, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part1.agda": {"best": 8.2, "last": 8.2, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part10.agda": {"best": 7.9, "last": 7.9, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part11.agda": {"best": 8.5, "last": 8.5, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part12.agda": {"best": 8.8, "last": 8.8, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part13.agda": {"best": 1.0, "floor": true, "last": 1.0, "runs": 3}, "cloud|agda-dev Verify-Well-Formed/Part2.agda": {"best": 7.8, "last": 7.8, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part3.agda": {"best": 7.3, "last": 7.3, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part4.agda": {"best": 7.8, "last": 7.8, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part5.agda": {"best": 8.4, "last": 8.4, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part6.agda": {"best": 8.1, "last": 8.1, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part7.agda": {"best": 8.9, "last": 8.9, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part8.agda": {"best": 8.8, "last": 8.8, "runs": 1}, "cloud|agda-dev Verify-Well-Formed/Part9.agda": {"best": 8.8, "last": 8.8, "runs": 1}, "cloud|make gate-heavy (full gate, 13 modules)": {"best": 64.0, "last": 64.0, "runs": 1}, "cloud|make gate-heavy (full gate, 24 modules)": {"best": 2643.0, "last": 2643.0, "runs": 1}, "cloud|make gate-heavy (full gate, 37 modules)": {"best": 2476.0, "last": 2476.0, "runs": 1}, "cloud|make gate-heavy (full gate, 51 modules)": {"best": 3917.0, "last": 3917.0, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/Chain-Step-Abs-Charge.agda": {"best": 3.8, "last": 9.7, "runs": 3}, "local|agda-dev ../evidence/probed/Probed/Chain-Step-Live-Deferred.agda": {"best": 3.9, "last": 3.9, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/Depth-Sighted.agda": {"best": 57.5, "last": 57.5, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/PushVals-Caps.agda": {"best": 3.8, "floor": true, "last": 45.0, "runs": 5}, "local|agda-dev ../evidence/probed/Probed/Scan-Arr-Clos-Key.agda": {"best": 5.6, "last": 5.6, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/Scan-Arr-Margin.agda": {"best": 3.6, "last": 8.6, "runs": 2}, "local|agda-dev ../evidence/probed/Probed/Scan-Burst-Nest.agda": {"best": 14.5, "floor": true, "last": 45.0, "runs": 3}, "local|agda-dev ../evidence/probed/Probed/Sight-All-Stream.agda": {"best": 5.5, "last": 5.5, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/Sight-Fit-Width.agda": {"best": 14.4, "last": 20.9, "runs": 2}, "local|agda-dev ../evidence/probed/Probed/Sight-Thru-Val.agda": {"best": 4.8, "last": 4.8, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/Sync-Factor.agda": {"best": 2.6, "last": 2.6, "runs": 1}, "local|agda-dev ../evidence/probed/Probed/Thru-Step-Indexed.agda": {"best": 10.4, "last": 10.4, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Chain-Level-Unbounded.agda": {"best": 5.3, "last": 5.3, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Chain-Step-Live-Additive.agda": {"best": 3.8, "last": 3.8, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Chain-Step-Store.agda": {"best": 4.3, "last": 4.3, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Clos-Wrap-Sum.agda": {"best": 3.6, "last": 3.6, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Drain-Reach-Gas.agda": {"best": 3.8, "last": 3.8, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Inner-Drain-Nest.agda": {"best": 3.3, "last": 3.3, "runs": 3}, "local|agda-dev ../evidence/refuted/Refuted/Inner-Drain-Share-Nest.agda": {"best": 3.2, "last": 3.2, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Nest-Clos-Cap-Free.agda": {"best": 5.8, "last": 5.8, "runs": 2}, "local|agda-dev ../evidence/refuted/Refuted/Nest-Clos-Flat.agda": {"best": 4.6, "last": 4.6, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Nest-Clos-Stratified.agda": {"best": 3.7, "last": 3.7, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Nest-Depth-Live-Reg.agda": {"best": 4.1, "last": 4.1, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Nest-Size-Currency.agda": {"best": 3.9, "last": 3.9, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Scan-Seed-Caps.agda": {"best": 3.1, "last": 3.1, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Share-Go-Path.agda": {"best": 3.6, "last": 3.6, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Sight-All-Fit-Slot.agda": {"best": 13.8, "last": 13.8, "runs": 2}, "local|agda-dev ../evidence/refuted/Refuted/Step-Frame-Clos.agda": {"best": 4.6, "last": 4.6, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Subscribe-Burst-Width.agda": {"best": 3.8, "floor": true, "last": 45.0, "runs": 3}, "local|agda-dev ../evidence/refuted/Refuted/Subscribe-Caps-Nest.agda": {"best": 3.4, "last": 3.4, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Thru-Scan-Burst-Nest.agda": {"best": 9.0, "last": 9.0, "runs": 1}, "local|agda-dev ../evidence/refuted/Refuted/Thru-Subscribe-Nest.agda": {"best": 3.4, "last": 5.4, "runs": 2}, "local|agda-dev CLI/Decode.agda": {"best": 5.1, "last": 5.1, "runs": 1}, "local|agda-dev Decide.agda": {"best": 1.6, "last": 1.6, "runs": 1}, "local|agda-dev Harness/Main.agda": {"best": 3.4, "last": 3.7, "runs": 18}, "local|agda-dev Main.agda": {"best": 45.0, "floor": true, "last": 45.0, "runs": 1}, "local|agda-dev QuickCheck.agda": {"best": 5.3, "last": 5.3, "runs": 2}, "local|agda-dev Readme-Theorems.agda": {"best": 4.1, "last": 4.1, "runs": 1}, "local|agda-dev Rx/Burst-Ceil.agda": {"best": 2.8, "last": 2.8, "runs": 1}, "local|agda-dev Rx/Clos-Eta-Cong.agda": {"best": 2.7, "last": 2.7, "runs": 1}, "local|agda-dev Rx/Clos-Size.agda": {"best": 2.5, "last": 3.2, "runs": 3}, "local|agda-dev Rx/Evaluator-Theorems.agda": {"best": 5.5, "last": 5.5, "runs": 1}, "local|agda-dev Rx/Evaluator.agda": {"best": 7.7, "last": 7.7, "runs": 2}, "local|agda-dev Rx/Exp.agda": {"best": 3.2, "last": 3.2, "runs": 3}, "local|agda-dev Rx/Frame-Width.agda": {"best": 4.7, "last": 4.7, "runs": 2}, "local|agda-dev Rx/Hop-Depth.agda": {"best": 4.2, "last": 4.2, "runs": 1}, "local|agda-dev Rx/Hop-Eta-Cong.agda": {"best": 3.4, "last": 3.4, "runs": 1}, "local|agda-dev Rx/Hop-Spine.agda": {"best": 3.5, "last": 3.5, "runs": 1}, "local|agda-dev Rx/Inputs-Below.agda": {"best": 3.4, "last": 3.4, "runs": 1}, "local|agda-dev Rx/MergeAll-Laws.agda": {"best": 2.6, "last": 2.6, "runs": 4}, "local|agda-dev Rx/Nest-Depth.agda": {"best": 2.6, "last": 2.7, "runs": 3}, "local|agda-dev Rx/Slot-Clos.agda": {"best": 2.5, "last": 3.5, "runs": 3}, "local|agda-dev Rx/Slot-Hop.agda": {"best": 2.6, "last": 3.0, "runs": 4}, "local|agda-dev Rx/Slots.agda": {"best": 2.5, "last": 2.5, "runs": 3}, "local|agda-dev Rx/Width-Subst.agda": {"best": 3.2, "last": 3.2, "runs": 1}, "local|agda-dev Verify-Batch-Simultaneous/The-Proof.agda": {"best": 7.0, "floor": true, "last": 2.0, "runs": 1023}, "local|agda-dev Verify-Budget-Sufficient/Burst-Walk.agda": {"best": 9.2, "floor": true, "last": 520.1, "runs": 18}, "local|agda-dev Verify-Budget-Sufficient/Burst-Walk/Predicates.agda": {"best": 3.9, "last": 3.9, "runs": 1}, "local|agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda": {"best": 6.4, "floor": true, "last": 2.0, "runs": 292}, "local|agda-dev Verify-Budget-Sufficient/Caps-Chain.agda": {"best": 3.7, "last": 3.7, "runs": 6}, "local|agda-dev Verify-Budget-Sufficient/Caps-Depth.agda": {"best": 6.5, "last": 6.5, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Nest-Arith.agda": {"best": 4.2, "last": 4.2, "runs": 5}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Part1.agda": {"best": 3.9, "last": 5.5, "runs": 12}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Part2.agda": {"best": 9.5, "last": 11.1, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Part3.agda": {"best": 5.4, "last": 6.3, "runs": 5}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Part4.agda": {"best": 7.7, "last": 9.5, "runs": 8}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Part5.agda": {"best": 4.0, "last": 4.9, "runs": 10}, "local|agda-dev Verify-Budget-Sufficient/Caps-Face/Part6.agda": {"best": 6.4, "last": 36.0, "runs": 7}, "local|agda-dev Verify-Budget-Sufficient/Caps-Nest.agda": {"best": 3.2, "last": 3.9, "runs": 4}, "local|agda-dev Verify-Budget-Sufficient/Caps-Term.agda": {"best": 3.4, "last": 3.4, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Caps.agda": {"best": 14.1, "last": 24.4, "runs": 9}, "local|agda-dev Verify-Budget-Sufficient/Deliver-Measure.agda": {"best": 3.7, "last": 4.6, "runs": 4}, "local|agda-dev Verify-Budget-Sufficient/Deliveries.agda": {"best": 3.7, "last": 3.7, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda": {"best": 8.1, "last": 8.1, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Depth-Sighted.agda": {"best": 3.7, "floor": true, "last": 200.0, "runs": 12}, "local|agda-dev Verify-Budget-Sufficient/Desc-Ceil.agda": {"best": 5.9, "last": 5.9, "runs": 1}, "local|agda-dev Verify-Budget-Sufficient/Fan-Caps.agda": {"best": 3.0, "last": 3.5, "runs": 4}, "local|agda-dev Verify-Budget-Sufficient/Hop-Spine-Face.agda": {"best": 3.6, "last": 3.6, "runs": 4}, "local|agda-dev Verify-Budget-Sufficient/Hop-Spine-Push.agda": {"best": 4.0, "last": 4.0, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Hop-Spine-Step.agda": {"best": 4.2, "last": 4.2, "runs": 6}, "local|agda-dev Verify-Budget-Sufficient/Hop-Spine-Sub.agda": {"best": 4.2, "last": 4.9, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Init-Caps.agda": {"best": 3.5, "last": 20.3, "runs": 9}, "local|agda-dev Verify-Budget-Sufficient/Init-Nest.agda": {"best": 4.0, "last": 4.6, "runs": 5}, "local|agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda": {"best": 8.1, "last": 8.1, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Level-Mono.agda": {"best": 3.5, "last": 3.5, "runs": 1}, "local|agda-dev Verify-Budget-Sufficient/Live-Nest-Walk.agda": {"best": 4.4, "last": 5.1, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Measures.agda": {"best": 10.0, "last": 12.0, "runs": 10}, "local|agda-dev Verify-Budget-Sufficient/Nest-Burst.agda": {"best": 2.6, "last": 3.4, "runs": 4}, "local|agda-dev Verify-Budget-Sufficient/Nest-Cap.agda": {"best": 3.0, "last": 3.8, "runs": 4}, "local|agda-dev Verify-Budget-Sufficient/Nest-Ceiling.agda": {"best": 3.4, "last": 3.7, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Nest-Store.agda": {"best": 3.1, "last": 4.0, "runs": 14}, "local|agda-dev Verify-Budget-Sufficient/Nest-Subst.agda": {"best": 3.5, "last": 3.9, "runs": 8}, "local|agda-dev Verify-Budget-Sufficient/Nest-Walk.agda": {"best": 3.1, "floor": true, "last": 45.3, "runs": 78}, "local|agda-dev Verify-Budget-Sufficient/Node-Fresh.agda": {"best": 3.7, "last": 6.6, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Node-Table.agda": {"best": 3.1, "last": 3.1, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Nodes-Nest-Walk.agda": {"best": 4.6, "last": 4.6, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Op-Budget.agda": {"best": 3.7, "last": 3.7, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Op-Dominance.agda": {"best": 3.3, "last": 3.3, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Psi-Split.agda": {"best": 4.1, "last": 4.1, "runs": 9}, "local|agda-dev Verify-Budget-Sufficient/Queue-Dead.agda": {"best": 2.8, "last": 6.7, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Regs-Nest-Walk.agda": {"best": 3.8, "last": 4.9, "runs": 10}, "local|agda-dev Verify-Budget-Sufficient/Sighted-Fit.agda": {"best": 3.5, "last": 3.5, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda": {"best": 12.2, "last": 16.5, "runs": 11}, "local|agda-dev Verify-Budget-Sufficient/Walk-Factor.agda": {"best": 4.2, "last": 4.2, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Walk-Level.agda": {"best": 5.5, "floor": true, "last": 46.5, "runs": 29}, "local|agda-dev Verify-Budget-Sufficient/Walk-Level/Arms.agda": {"best": 5.6, "floor": true, "last": 45.0, "runs": 35}, "local|agda-dev Verify-Budget-Sufficient/Walk-Level/Connect.agda": {"best": 25.9, "floor": true, "last": 45.0, "runs": 31}, "local|agda-dev Verify-Budget-Sufficient/Walk-Level/Parts.agda": {"best": 8.7, "floor": true, "last": 45.0, "runs": 37}, "local|agda-dev Verify-Budget-Sufficient/Walk-Level/Statement.agda": {"best": 4.1, "last": 4.1, "runs": 8}, "local|agda-dev Verify-Budget-Sufficient/Wet/Part1.agda": {"best": 4.3, "last": 4.3, "runs": 5}, "local|agda-dev Verify-Budget-Sufficient/Wet/Part2.agda": {"best": 22.6, "last": 22.6, "runs": 3}, "local|agda-dev Verify-Budget-Sufficient/Wet/Part3.agda": {"best": 4.7, "last": 4.7, "runs": 2}, "local|agda-dev Verify-Budget-Sufficient/Wet/Part6.agda": {"best": 3.9, "last": 3.9, "runs": 6}, "local|agda-dev Verify-Well-Formed/Part1.agda": {"best": 3.4, "last": 3.4, "runs": 2}, "local|agda-dev Verify-Well-Formed/Part10.agda": {"best": 7.7, "last": 9.0, "runs": 3}, "local|agda-dev Verify-Well-Formed/Part11.agda": {"best": 7.4, "last": 7.4, "runs": 4}, "local|agda-dev Verify-Well-Formed/Part12.agda": {"best": 8.5, "last": 8.5, "runs": 2}, "local|agda-dev Verify-Well-Formed/Part13.agda": {"best": 5.3, "floor": true, "last": 1.0, "runs": 164}, "local|agda-dev Verify-Well-Formed/Part2.agda": {"best": 3.1, "last": 3.1, "runs": 3}, "local|agda-dev Verify-Well-Formed/Part3.agda": {"best": 3.0, "last": 3.1, "runs": 7}, "local|agda-dev Verify-Well-Formed/Part4.agda": {"best": 7.3, "last": 8.5, "runs": 4}, "local|agda-dev Verify-Well-Formed/Part5.agda": {"best": 7.3, "last": 7.3, "runs": 2}, "local|agda-dev Verify-Well-Formed/Part6.agda": {"best": 7.9, "last": 7.9, "runs": 1}, "local|agda-dev Verify-Well-Formed/Part7.agda": {"best": 7.5, "last": 7.5, "runs": 2}, "local|agda-dev Verify-Well-Formed/Part8.agda": {"best": 3.5, "last": 3.5, "runs": 5}, "local|agda-dev Verify-Well-Formed/Part9.agda": {"best": 8.7, "last": 8.7, "runs": 2}, "local|make gate-heavy (full gate, 1 modules)": {"best": 5.0, "last": 7.0, "runs": 3}, "local|make gate-heavy (full gate, 10 modules)": {"best": 65.0, "last": 65.0, "runs": 5}, "local|make gate-heavy (full gate, 11 modules)": {"best": 18.0, "last": 1052.0, "runs": 9}, "local|make gate-heavy (full gate, 12 modules)": {"best": 375.0, "last": 1107.0, "runs": 5}, "local|make gate-heavy (full gate, 13 modules)": {"best": 88.0, "last": 1106.0, "runs": 5}, "local|make gate-heavy (full gate, 14 modules)": {"best": 19.0, "last": 1889.0, "runs": 2}, "local|make gate-heavy (full gate, 15 modules)": {"best": 19.0, "last": 80.0, "runs": 5}, "local|make gate-heavy (full gate, 16 modules)": {"best": 15.0, "last": 1101.0, "runs": 6}, "local|make gate-heavy (full gate, 17 modules)": {"best": 12.0, "last": 1495.0, "runs": 7}, "local|make gate-heavy (full gate, 174 modules)": {"best": 802.0, "last": 802.0, "runs": 1}, "local|make gate-heavy (full gate, 18 modules)": {"best": 28.0, "last": 278.0, "runs": 8}, "local|make gate-heavy (full gate, 19 modules)": {"best": 31.0, "last": 1203.0, "runs": 11}, "local|make gate-heavy (full gate, 2 modules)": {"best": 7.0, "last": 7.0, "runs": 1}, "local|make gate-heavy (full gate, 20 modules)": {"best": 32.0, "last": 32.0, "runs": 1}, "local|make gate-heavy (full gate, 21 modules)": {"best": 35.0, "last": 1697.0, "runs": 5}, "local|make gate-heavy (full gate, 22 modules)": {"best": 352.0, "last": 1312.0, "runs": 2}, "local|make gate-heavy (full gate, 23 modules)": {"best": 399.0, "last": 399.0, "runs": 1}, "local|make gate-heavy (full gate, 24 modules)": {"best": 1368.0, "last": 1368.0, "runs": 2}, "local|make gate-heavy (full gate, 25 modules)": {"best": 1211.0, "last": 1486.0, "runs": 3}, "local|make gate-heavy (full gate, 26 modules)": {"best": 1297.0, "last": 1297.0, "runs": 1}, "local|make gate-heavy (full gate, 28 modules)": {"best": 1448.0, "last": 1448.0, "runs": 1}, "local|make gate-heavy (full gate, 29 modules)": {"best": 1298.0, "last": 1298.0, "runs": 1}, "local|make gate-heavy (full gate, 3 modules)": {"best": 9.0, "last": 9.0, "runs": 1}, "local|make gate-heavy (full gate, 30 modules)": {"best": 1342.0, "last": 1342.0, "runs": 2}, "local|make gate-heavy (full gate, 306 modules)": {"best": 1709.0, "last": 1709.0, "runs": 2}, "local|make gate-heavy (full gate, 32 modules)": {"best": 1642.0, "last": 1642.0, "runs": 1}, "local|make gate-heavy (full gate, 34 modules)": {"best": 669.0, "last": 669.0, "runs": 1}, "local|make gate-heavy (full gate, 35 modules)": {"best": 1633.0, "last": 1633.0, "runs": 1}, "local|make gate-heavy (full gate, 36 modules)": {"best": 1338.0, "last": 1338.0, "runs": 1}, "local|make gate-heavy (full gate, 37 modules)": {"best": 1831.0, "last": 1831.0, "runs": 1}, "local|make gate-heavy (full gate, 38 modules)": {"best": 1477.0, "last": 1477.0, "runs": 1}, "local|make gate-heavy (full gate, 4 modules)": {"best": 9.0, "last": 11.0, "runs": 4}, "local|make gate-heavy (full gate, 43 modules)": {"best": 1791.0, "last": 1791.0, "runs": 1}, "local|make gate-heavy (full gate, 45 modules)": {"best": 662.0, "last": 662.0, "runs": 1}, "local|make gate-heavy (full gate, 46 modules)": {"best": 1407.0, "last": 1407.0, "runs": 1}, "local|make gate-heavy (full gate, 49 modules)": {"best": 743.0, "last": 743.0, "runs": 1}, "local|make gate-heavy (full gate, 5 modules)": {"best": 9.0, "last": 13.0, "runs": 6}, "local|make gate-heavy (full gate, 50 modules)": {"best": 660.0, "last": 1760.0, "runs": 4}, "local|make gate-heavy (full gate, 51 modules)": {"best": 1980.0, "last": 1980.0, "runs": 1}, "local|make gate-heavy (full gate, 52 modules)": {"best": 1893.0, "last": 1893.0, "runs": 1}, "local|make gate-heavy (full gate, 54 modules)": {"best": 1788.0, "last": 1788.0, "runs": 1}, "local|make gate-heavy (full gate, 55 modules)": {"best": 3004.0, "last": 3004.0, "runs": 1}, "local|make gate-heavy (full gate, 58 modules)": {"best": 2095.0, "last": 2095.0, "runs": 1}, "local|make gate-heavy (full gate, 59 modules)": {"best": 704.0, "last": 704.0, "runs": 1}, "local|make gate-heavy (full gate, 6 modules)": {"best": 10.0, "last": 34.0, "runs": 8}, "local|make gate-heavy (full gate, 61 modules)": {"best": 1592.0, "last": 1592.0, "runs": 1}, "local|make gate-heavy (full gate, 69 modules)": {"best": 1578.0, "last": 1578.0, "runs": 1}, "local|make gate-heavy (full gate, 7 modules)": {"best": 13.0, "last": 37.0, "runs": 11}, "local|make gate-heavy (full gate, 70 modules)": {"best": 1583.0, "last": 1583.0, "runs": 1}, "local|make gate-heavy (full gate, 77 modules)": {"best": 1658.0, "last": 1658.0, "runs": 1}, "local|make gate-heavy (full gate, 8 modules)": {"best": 38.0, "last": 38.0, "runs": 6}, "local|make gate-heavy (full gate, 85 modules)": {"best": 114.0, "last": 114.0, "runs": 1}, "local|make gate-heavy (full gate, 9 modules)": {"best": 14.0, "last": 38.0, "runs": 7}} -->

<!-- AUTO:END -->

## `Caps-Face/Part7`: the kills were the CONE, and the module is now split

An earlier revision of this section recorded that Part7's shared-context stage
was killed at 120 s twice and 300 s once "on a warm cache", and concluded that
the container, not the module, was the problem and that splitting was not the
repair. **Both halves of that were wrong, and the second cost the most.**

The cache was COLD. A cloud container clones the repo and builds no
interfaces, so the first dev check of anything pays for its whole dependency
cone — and `agda-dev` checks every dependency for real, stubbing only mutual
blocks in the TARGET. What the three kills measured was Part7's cone being
built, attributed to Part7.

The bisection that settled it: Part7 was cut at block boundaries and the
9-line piece holding only `chainBurstOK` was checked on its own. It was killed
at 120 s, ran past 163 s at 2.39 GB, and was killed again at 300 s. Nine lines
cannot cost that. Its one distinguishing import is `Nest-Walk`, which the
pieces that passed do not take — so the run was building `Nest-Walk`'s cone
from cold. This is the "rebuilding dependency masquerading as module cost"
failure the cost-model rule warns about, and it is the fifth recorded
instance.

Two things follow, and they are the reason the row above was misleading rather
than merely imprecise. **A FLOOR row from a cold container is not a
measurement of the module it names** — it is a measurement of whatever had not
been built yet, so it may not be compared against a local row, which is always
warm. And **a killed run is not wasted**: every interface that completed
before the kill is persisted, so repeated kills warm the cache monotonically
and the same check gets cheaper each time.

Splitting was worth doing on its own merits and the numbers say so: the first
three pieces came in at 25.1 s, 14.5 s and 12.4 s cold, then 10.5 s, 10.7 s
and 10.8 s once the cone under them was built — as REAL, unstubbed checks,
against a whole module that had never once completed here. What the split buys
is not a faster tower but a per-piece loop that fits the budget, and cuts that
land on the four-member SCC's boundary rather than through it.

## The gate

| | |
|---|---|
| `make gate-heavy` full gate, cold | **802 s** (13 m 22 s), 41 modules |
| `make gate` on a warm-ish cache | ~350 s, 27 modules rechecked |
| `make wiring-gate`, `make unsafe-check` | seconds (textual) |

Agda 2.7.0.1 → 2.8.0 was the one lever that ever moved the gate: **927 s → 384 s** total
on Subscribe-Face, **779 s → 300 s** of that being Positivity (2.6×).

## The comment-stripped mirror — what a comment edit costs (2026-08-18)

Agda invalidates an interface by source CONTENT, so before the mirror every
`-- PROBED` / `-- DEAD ROUTE` line this methodology *requires* cost a full cone
rebuild. `scripts/strip-comments.py` mirrors `src` + `refuted` into
`agda/_stripped-comments/` with every full-line `--` comment deleted; a
comment-only edit leaves the mirror byte-identical and nothing rebuilds.

**The control was run FIRST**, which is the only reason the second row means
anything:

| edit to `Rx/Prim.agda` | mirror files rewritten | modules rechecked |
|---|---|---|
| a real definition appended (CONTROL) | 1 | **3** |
| three comment lines inserted | 0 | **0** |

29% of this tree is comment lines. The strip itself costs ~50 ms and is a
prerequisite of every one of the six `$(AGDA)` call sites.

Two things paid for by the same move: `agda-dev` generates into
`_stripped-comments/_dev/` and runs with the mirror as its cwd, so the dev loop
and the gate share **one** `_build` instead of invalidating each other's cone on
every alternation. Removing the now-dead `agda/_build` recovered 262 MB.

## Per-module dev-loop cost

`make agda-dev ARGS='<file>'`, cold, on a coherent cache — i.e. the real edit-one-file
case: the file is dirtied, every dependency already built.

### `Typing.With` — a THIRD cost centre, and the only one a rewrite has ever removed

**`Verify-Well-Formed/Part13`: 51.5 s → 7.5 s by deleting three `with`es and one
`rewrite` from ONE definition (2026-08-17).** No split, no new module, no change to
what is proven. This is the largest single-module win the repo has recorded outside
the Agda 2.8 upgrade, and every part of the standing cost model pointed the wrong way
at it, so the attribution is worth keeping:

| | |
|---|---|
| `--list` | **6 blocks, 0 multi-member** — no mutual block to blame, and the smallest file in its directory (315 lines) |
| `--profile=definitions` | `evaluate-well-formed` **36.6 s** of 44 s; the other five members 10–58 ms *each* |
| `--profile=internal` | **`Typing.With` 42.3 s** of 49.6 s. `Positivity` **18 ms**. `Deserialization` 6.8 s |

`with` abstracts its SCRUTINEE out of the goal, whether or not the clause needs case
analysis — and all four steps here were irrefutable Σ destructurings that needed none.
The goal is `WellFormed (evaluate fuel e ins)`, which unfolds to carry the whole seeded
`subscribeE … ++ drain …` term, so each `with` (and `rewrite`, which is a fourth) paid
to re-abstract that term. Irrefutable `let` patterns plus one `subst` do the same work
with no abstraction at all.

**The generalisation, and it is cheap to check: `with`/`rewrite` in a body whose goal
is a fully-applied CLOSED term is a cost centre, and a `with` that only destructures a
record is pure loss.** The tell is a body that is short, non-recursive, and slow —
`drain-wf` sits directly above this one, uses four `with`es, and costs 54 ms, because
its goal is over variables rather than over `evaluate fuel e ins`. Term SIZE is the
common factor with the Positivity story; the pass is different.

Method note: `--profile=definitions` localised this to one member in a single run, after
`--list` had already ruled out the mutual-block explanation for free. Both were cheaper
than the split that was queued, and the split would have moved the 36 s into a new module
rather than removing it.

**THE SWEEP FOR A SECOND INSTANCE CAME BACK EMPTY — do not re-run it.** Every other
module in `src` whose recorded cost is above the deserialization floor AND which `--list`
reports as **0 multi-member** (so Positivity cannot be the cost) was profiled the same
way on 2026-08-17. `Typing.With`: Init-Caps **0 ms**, Caps-Bridge **85 ms**, Part11
**45 ms**, Measures **684 ms** of its 18.1 s. Part13 was singular, and the lever does not
generalise to a repo-wide pass.

Two things that sweep incidentally settled, both worth more than the negative result:

- **`Deserialization` IS the floor and it dominates everything left.** Init-Caps 4.1 s of
  5.6 s, Part11 5.4 s of 7.7 s, Caps-Bridge 4.9 s of 9.7 s. No restructuring removes it —
  it is the per-PROCESS import toll the dev loop's batching already exists to amortise.
  A module sitting near 6–8 s is at the floor and is not worth looking at.
- **THE SINGLE-RUN ENTRIES IN THE TABLE BELOW RUN HOT, CONFIRMED.** Init-Caps is recorded
  at 33.7 s (`runs: 1`) and profiled at **5.5 s**; Part11 is recorded at 14.9 s (`runs: 1`)
  and profiled at **7.7 s**. That is the incoherent-cache distortion this file warns about,
  caught in the act — a 6× inflation. `perf_record` takes the minimum over runs, so these
  self-correct with use, but **treat any `runs: 1` figure as an upper bound, not a
  measurement**, and re-measure before acting on one.

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

## The evidence trees after a `Nest-Walk` edit — warm, one real edit

The question this answers: what does a normal commit cost in `make probed` +
`make refuted`, given that the module almost every commit touches is low in the
tower.  Method: warm both caches, APPEND a real definition to `Nest-Walk.agda`
(`touch` does not dirty a module and a comment edit is free — the mirror is
comment-stripped), then time each target separately, one Agda at a time.

| config | `probed` | `refuted` | total |
| --- | --- | --- | --- |
| predicates still under the level face | 27.9 s | **1357.3 s** | 1385.2 s |
| predicates hoisted below it | 27.6 s | 17.5 s | 45.1 s |
| hoisted, plus a proof-stubbed `src` mirror | 26.5 s | **4.4 s** | 30.9 s |

**The hoist is 78× and the stub mirror is 4× on top of it.** Three refutations
took two predicates from a module that imports the level face, so every
evidence build built that face and its cone; nothing else in either tree goes
deeper than the nest walk.

**`probed` DOES NOT MOVE, and cannot.** A probe normalises the evaluator at
concrete inputs to land a `refl`, so its bill is definition bodies — which the
stubber never stubs, by design, and which the hoist never removed.
Proof-checking was never this target's cost, and no amount of it will be.

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
| Migrating to `Agda.Builtin.Nat` | **Nothing to migrate: already there.** `Data.Nat`'s `ℕ`, `zero`, `suc`, `_+_`, `_*_`, `_∸_`, `_≡ᵇ_`, `_<ᵇ_` are re-exports of the builtin (`Data/Nat/Base.agda`), and no `data ℕ` exists in `agda/src` or `agda/evidence`. Termination checking cannot benefit under any Nat: it is a call-graph descent analysis and evaluates no arithmetic |
| Swapping `_⊔_` for the builtin-backed `_⊔′_` (2026-08-24) | **30× compiled, ~0 in the checker, and rejected on both.** 300k maxima over values in [0,599]: compiled 0.89 s vs 0.03 s; typechecked, 1500 maxima cost 0.13 s against a 1.31 s baseline for building the list, and `⊔′` cost nothing measurable. So the absolute saving is a fraction of a second at the magnitudes these measures take, while every `⊔` lemma in the tower is stated over `_⊔_` and the `a ⊔ (b ⊔ c)` projections rest on its definitional behaviour. The harness rows that time out are the evaluator, not the maxima |
| Dissolving Caps-Face's spurious block, judged on gate cost | "Saves nothing" — **true of the gate and the wrong number to judge a split by.** Judged on dev cost it was 72.6 s → 8.3 s |

## Parallelism and memory

- **A PARALLEL `warm-cache` FOR `make gate-heavy` WAS MEASURED AND REJECTED (2026-08-18).
  THE DAG DOES NOT OFFER THE PARALLELISM.** Main's cone is 66 modules over a
  **37-level** critical path, and **levels 15–36 are WIDTH 1** — a strict chain
  holding every expensive module: Caps-Face → Subscribe-Face → Walk-Level →
  Burst-Walk → Caps-Bridge → Verify-Well-Formed Part1…Part13 → VWF → The-Proof →
  Main. Weighting each module by its recorded best:

  | | |
  |---|---|
  | serial total | 510.7 s |
  | critical path | **302.6 s** — the floor for ANY parallelism |
  | max speedup | **1.69×**, with infinite cores and zero contention |

  And 1.69× is an OVERESTIMATE, because the weights come from `agda-dev` bests,
  which stub mutual blocks — the modules that cost most under real `make gate-heavy`
  are exactly the ones ON the critical path, so true weights push the ceiling
  DOWN. Against that ceiling stand two measured facts in this same section:
  deserialization is memory-bandwidth bound and does not scale with cores
  (12-way turned 5.6 s runs into 13–24 s), and at most TWO heavyweight checks
  fit in RAM. Two-way parallelism against a <1.69× ceiling, with per-process
  contention, is net zero at best.
  There is also a CORRECTNESS hazard, not just a wasted-work one: two `agda`
  processes on overlapping cones both build the shared prefix and race on
  writing the same `.agdai` files.
  **The Verify-Well-Formed chain is genuine** — Part_n imports Part_{n-1} for
  every n in 2…13, checked, not incidental — so 13 of those serial levels
  cannot be widened without restructuring proof shape, which "cut at mutual-SCC
  boundaries" forbids doing for check time.
  **What actually governs `make gate-heavy`'s cost is which module you EDITED.** Warm
  with a shallow change it is 19–43 s (14–21 modules); editing something
  foundational (Rx/Exp, Frame-Width, Measures) invalidates the cone and costs
  the near-cold 660–2095 s. No scheduler changes that.

- **NATIVE arm64 vs x86_64-UNDER-ROSETTA, COLD, BOTH LEGS (2026-08-21).** The whole
  ghcup/cabal toolchain on this host was x86_64 — `agda`, `ghc 9.4.8`
  (`x86_64-apple-darwin`), `cabal`, `stack` — so every build until now ran under
  Rosetta 2 on an arm64 M4 Pro. Homebrew's bottled `agda 2.8.0-r3` for
  `arm64_tahoe` is native (GHC 9.12.3, `rts_thr_dyn`, `aarch64`) and carries the
  SAME `optimise-heavily` flag as the cabal build, so the A/B is clean. Both legs
  wiped `agda/_stripped-comments/_build` AND the stdlib `_build` first, same tree,
  same 306 modules, sequential (never concurrent):

  | binary | seconds | modules | exit |
  | --- | --- | --- | --- |
  | `~/.cabal/bin/agda` (x86_64, Rosetta) | 1982 | 306 | 0 |
  | `/opt/homebrew/bin/agda` (arm64, native) | 1709 | 306 | 0 |

  **1.16×, i.e. 273 s off a 33-minute build.** Real and free — `/opt/homebrew/bin`
  precedes `~/.cabal/bin` on this PATH, so a bare `agda` already resolves to the
  native one and the Makefile needed no change beyond the `AGDA_BIN` knob that
  made the A/B possible at all.

- **AND THE PROXY THAT PREDICTED IT WAS WRONG BY 2×, WHICH IS THE LESSON.** Before
  installing anything, the two universal slices of `/usr/bin/python3` were timed on
  an allocation-heavy pointer-chasing workload: arm64 0.58/0.58 s vs x86_64
  0.77/0.86 s, i.e. **1.3–1.5×**. The real build delivered 1.16×. The proxy was
  COMPUTE-bound; this build is deserialization-bound, and deserialization is
  memory-bandwidth bound (the 12-way experiment above turned 5.6 s runs into
  13–24 s), which is precisely where Rosetta costs least. Watchable live: at module
  286 of 306 the two legs were within two minutes of each other (17:18 vs ~17:20)
  having been ~3× apart at module 266. **A microbenchmark chosen for the wrong
  bottleneck does not predict this build**, and the gap was in the optimistic
  direction.

- **AMENDMENT (2026-08-21): THE CONCLUSION ABOVE STANDS, AND THE DAG IT MEASURED
  WAS WRONG.** Re-derived from scratch, the shape had gotten worse — 78 modules,
  **41** levels, **24** of them width 1, ceiling **1.47×** on the same
  `agda-dev`-best weights. But twelve of those levels were an artefact. All
  thirteen `Verify-Well-Formed/Part*` carried
  `open import Verify-Budget-Sufficient.Caps-Bridge using (budget-sufficient)`,
  and **grep for non-comment uses returns exactly one: Part13.** Twelve dead
  edges stacked the whole VWF ladder on the whole budget-sufficient tower.
  Deleting them:

  | | before | after |
  |---|---|---|
  | depth | 41 levels | **29** |
  | width-1 levels | 24 | **10** |
  | critical path | 638 s | 547 s |
  | ceiling | 1.47× | 1.72× |

  **The parallelism gain is still not worth having; the REBUILD-CONE gain is the
  point**, and it is the row above ("which module you EDITED") collecting:

  | edited | rebuilds before | after |
  |---|---|---|
  | `Walk-Level/Parts` | 22 mod / 227 s | **10 mod / 136 s** |
  | `Walk-Level` | 19 mod / 141 s | **7 mod / 49 s** |
  | `Burst-Walk` | 18 mod / 135 s | **6 mod / 44 s** |
  | `Caps-Bridge` | 17 mod / 126 s | **5 mod / 35 s** |
  | `Caps-Face/Part4` | 32 mod / 360 s | **20 mod / 269 s** |
  | `Rx/Exp` | 73 mod / 908 s | 73 mod / 908 s — it is under everything |

  The rest of the ladder is GENUINE, and it was checked at the level of NAMES and
  not of imports, which is the check the original row did not make: `Part_n` really
  does read names defined in `Part_{n-1}` for every n in 2…13 except Part3, and
  Caps-Face is the same. The only other slack found was `Wet/Part6`, which uses
  nothing from Part3/4/5; it is not on the critical path, so it buys nothing.
  `make imports-check` now holds this — the class of defect is invisible to
  `-W error`, because Agda emits no warning for an unused import.

- **THE PER-TIER REBUILD CONE — which is what "does the build get cheaper as we
  climb the tiers?" actually asks.** Mapping every PROOF-STATE row head to the
  module its postulate lives in, and taking the union of the tier's dependent
  cones:

  | tier | rebuilt by an edit anywhere in it | after the import fix |
  |---|---|---|
  | tier 1 | 30 mod / 292 s | **18 mod / 200 s** |
  | tier 2 | 14 mod / 102 s | 14 mod / 102 s |

  **It is not monotone: tier 1 is the most expensive tier, not tier 2.** (The
  anchor cone, since discharged, measured 23 mod / 234 s and 11 mod / 142 s after
  the import fix — cheaper than tier 1 while sitting below it.) Tier 1
  reaches down to `Caps-Face/Part7`, which sits under everything above it, while
  all 21 of tier 2's rows are in `Verify-Well-Formed/Part3…Part11`, near the top —
  an edit to Part11 rebuilds six modules. So the answer is not "cheap unless we
  reopen a lower tier"; it is that **tier number is not the variable.** Position in
  the DAG is, and the two agree only loosely.
  **And the cost that WILL grow is orthogonal to all of it: discharging a postulate
  makes the module it lands in more expensive.** Positivity is steeply superlinear
  in a mutual block's term size (Subscribe-Face: one real body 63 ms, fifteen
  300 s), and every postulate→definition adds term size to a block. The grind lane
  gets slower as it fills in, wherever in the DAG it sits.

- **`make refuted` warm: 5.46 s** (real, right after `make gate-heavy`). It imports
  `src` deeply, so run AFTER `agda` — which is where `make gate` puts it.


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
- **A FOURTH instance, 2026-08-15 — and it sharpens the trigger.** Discharging
  `wet-landing-lift` (Walk-Level) from postulate to definition died `Killed: 9` / exit 137
  in `Verify-Well-Formed.Part13` at 7.3 GB after ~19 min. The refinement: *unsealed* is not
  the trigger by itself. `entry-ceiling` sits ten lines above it, unsealed, calling the same
  `opIterD-dominated`, and has built green since 2026-08-13. What is fatal is a postulate
  **the spine already consumed as an axiom** becoming transparent to it. So the trigger is
  the postulate→definition TRANSITION on the spine, not body shape — seal in that same edit.
  Caveat on this figure: a second agda (3.8 GB) was running concurrently, so contention is a
  sufficient explanation on its own and the 7.3 GB is a floor, not the sealed/unsealed delta.
- **A FIFTH instance, 2026-08-20 — and it SURVIVED, unsealed, which narrows the
  trigger again.** Discharging `hopD-relᵉ` (.Measures) from postulate to
  definition is a textbook instance of the trigger above: a postulate the
  `budget-sufficient` spine consumed as an axiom (through `slotHop-cap`)
  becoming transparent to it, landed unsealed as a three-member mutual block.
  It built GREEN — peak **7.26 GB** on Walk-Level, FLAT across successive
  one-minute samples, cleared that module, then the whole tower, `Main`, the
  refuted tree and bug-cache: 59 modules, ALL GREEN. Single agda process, ~3.1
  GB reclaimable headroom at peak.
  Set beside the 2026-08-15 death (`Killed: 9` at 7.3 GB after ~19 min) this is
  the same figure with the opposite outcome — and the difference is the caveat
  already recorded on that row: a second 3.8 GB agda was running concurrently
  there, so contention was a sufficient explanation and 7.3 GB was a floor.
  **Conclusion: peak RSS near 7 GB is not itself the predictor, and CONCURRENCY
  is doing more of the work in these deaths than the seal is.** Do not read
  "spine transition ⇒ will OOM unless sealed"; read "spine transition ⇒ measure
  it, and do not run a second agda while you do."
  The corollary matters because sealing is not free: see the next bullet, where
  the idiom drove Walk-Level to 12.5 GB and died IN that module — worse than the
  unsealed build. Reflexive sealing has its own failure mode.
  **Method note, and it is the reusable part:** the run was diagnosed live by
  `ps -eo pid,rss,etime` rather than by waiting for the verdict — a runaway
  allocation CLIMBS, and a flat RSS across samples is the signal that a large
  figure is a plateau and not a blowup. That distinction is what made letting it
  finish the right call instead of killing it on the resemblance to a recorded
  death.

- **THE SEALING IDIOM ITSELF COST MORE THAN THE SEAL SAVED — duplicate the signature and you
  pay for it twice.** `abstract` cannot hold a body with an untyped `where` or a
  with-abstraction, so those use private-impl + abstract-alias, which needs the type written
  at BOTH sites. `wet-landing-lift`'s type binds a `subscribeE` run in a `let` and applies
  `INV?` at its projections; writing it twice made Agda elaborate that twice, and Walk-Level
  climbed to **12.5 GB / 0.14 GB free** and died IN THAT MODULE — strictly worse than the
  unsealed build, which at least cleared Walk-Level and only died later in VWF. **Fix: name
  the type** (`WetLandingLift : Set`, `InnerNodryFuel : Set`) and use the name at both sites,
  the idiom the files already use for `WalkLevel` / `WetOuter` / `SiNodry`.
  Two corrections this episode forced, both worth keeping:
  - **Sealing what the body CALLS does not help the producer.** `entry-ceiling-at` was sealed
    on that theory and the build still died on Walk-Level; it has since been reverted to
    unsealed, which is how `entry-ceiling` has consumed it since 2026-08-13. Sealing is a
    consumer-side fix, and the defining module is the producer.
  - **`agda-dev` DID measure it; the reader did not look.** The AUTO:DATA line in this file
    had `Walk-Level` at **best 5.5 s** and **last 38.4 s** across the episode — a ~7× blowup
    sitting in the same file being appended to all night, while each run was read as a
    standalone "GREEN in 38 s". A dev run's absolute time means nothing; **the number that
    carries information is the ratio to that module's recorded best**, which is why the best
    is kept. Check it before concluding a module is fine.

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
key, so when `agda-dev` passed `-W noUserWarning` and `make gate-heavy` did not, each run
invalidated the other's entire cone — measured ping-pong on a two-line module: 120 / 0 /
120 / 120 / 120 s. **Every number recorded before 2026-08-12 is suspect, and suspect in
the slow direction.**

**2. `touch` does not dirty an Agda module — invalidation is by CONTENT.** A file whose
content is unchanged reuses its interface, so the "recheck" measures only deserialization
(6.4 s for Subscribe-Face, of which 5.1 s *is* deserialization) and reports zero
`Checking` lines. Re-appending an *identical* marker line therefore measures nothing: one
profiling run came back 4,891 ms with everything under "Miscellaneous" for exactly this
reason. Vary the marker.

**3. A ROW FOR A MODULE THAT CAN NO LONGER FINISH IS NOT MERELY STALE, IT IS
INVERTED — and until now this file produced exactly that.** The auto-recorder took
only GREEN runs, on the sound argument that a failed check measures how long it
took to FAIL. A run the BUDGET killed is not that: nothing went wrong, the clock ran
out, and the number is a lower bound distorted in the same slow direction that makes
every other observation here safe to merge. Dropping it meant a module that used to
be fast and can no longer finish kept its old row and kept reporting the old figure.
Measured on `Caps-Bridge`, which this file recorded at **6.4 s over ten runs** while
it was in fact **not completing a dev check in 600 s** — a hundredfold error in the
reassuring direction, on the module that is the `Verify-Budget-Sufficient` tree's
only door. A timeout now records as a FLOOR, rendered `>Ns`, and never enters
`best`, which stays a real measurement of a run that really finished.

One consequence carries whatever the cause turns out to be: **the light gate cannot
clear a module in this state at all**, even for a comment-only edit, because a changed
file over budget is red by design while a cone member over budget is merely skipped —
so an edit to `Caps-Bridge` forces the heavy gate whatever it touches.

**AND THE CAUSE WAS A FIFTH INSTANCE OF LIE 1, SELF-INFLICTED.** It was first written
up as the module having outgrown the budget, with the split arithmetic attached:
`--list` reports 31 blocks and no multi-member one, so every member is in no cycle,
nothing is stubbed, and each focused check re-proves the whole file. All true, none of
it the diagnosis. Measured after a green heavy gate on a quiet machine, the same module
is **6.6 s** — its recorded best. Measured again immediately after `make harness`,
**4.8 s**, which kills the obvious suspect: compiling the tree does not poison the dev
cache, and that hypothesis is refuted rather than merely unmentioned. What the slow runs
had in common was a second Agda alive at the time, mine, racing the same interface cache
across a `make gate`, a `gate-heavy` and a `git stash` round trip — the collision the
delegation rules already forbid a worker, here committed by the session that wrote the
rule. **>900 s against 6.6 s is a 140× reading about the machine, not the module**, and
the split-candidate reading is withdrawn.

The uncomfortable corollary belongs here rather than anywhere flattering. The floor
recording directly above was added BECAUSE of this episode, and had it been working it
would have written `>900 s` into this file as a durable claim about `Caps-Bridge`. A
floor is honest as a bound and it is still worth having, since an inverted row is worse
than a pessimistic one — but a floor is exactly the kind of number lie 1 distorts
hardest, because a run slow enough to be killed is a run something else was probably
interfering with. **Read a `>Ns` as a statement about a session, and re-measure on a
quiet machine before believing it of the code.**

## Series Q crossover: exponential, not quadratic (2026-08-20, COMPILED harness)

`measured-not-rechecked` — read off `_harness/Main`, whose row 0 (`towerℕ 4 =
65536`) and rows 3-4 (`runDry 2/3 (progD 1 2)`) are `refl`-pinned in
`Harness/Main.agda`, so the backend is calibrated on BOTH arithmetic and
`subscribeE` before any row is read.

26 points over d ∈ 1..9, k ∈ 1..6, all `false` (safe). Cost is a function of the
PRODUCT d·k and is nearly shape-independent — four different shapes at d·k = 12
land within a factor of 1.7:

| d·k | 8 | 9 | 10 | 12 |
|---|---|---|---|---|
| cost | 53 ms | 80–107 ms | 235–352 ms | 2141–3659 ms |
| shapes | (4,2) (2,4) | (3,3) (9,1) | (5,2) (2,5) | (6,2) (4,3) (3,4) (2,6) |

Least squares on log(cost): **base 2.895 per unit of d·k.** Extrapolated:

| d·k | 21 | 30 | 40 | 54 (crossing) |
|---|---|---|---|---|
| cost | ~1 day | 17 yr | 7×10⁵ yr | **2×10¹² yr** |

The crossing condition `5d + k + 12 ≤ d·k` first bites at d·k ≈ 54, so the
cheapest refuting row is ~150× the age of the universe against a practical
ceiling of d·k ≈ 21 — a gap of 2.9³³ ≈ 10¹⁵.

**This supersedes the 2026-08-13 estimate**, which called the row "a multi-hour
job" on a quadratic model (d·k(k+1)/2 ≈ 250 subscription levels). The level count
was right; it just is not what costs. `scanᵉ` re-emits every intermediate
accumulator and the outer `*All` subscribes each one, so each nested level's
burst is re-pushed through every level enclosing it — a re-traversal cascade.

Same verdict as the caps-counting quarantine (harness rows 10+), reached the same
way: the blowup is COMPUTATIONAL, so compiling does not help. Consequence for the
proof: series Q cannot settle the FALSITY it was built to test, and the walk
face's chain-frame rows are classed structurally instead (they peel no gas —
Evaluator:1436-1458).
