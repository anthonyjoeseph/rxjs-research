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
| `make agda (full gate, 51 modules)` | **1980.0 s** | 1980.0 s | 1 |
| `make agda (full gate, 37 modules)` | **1831.0 s** | 1831.0 s | 1 |
| `make agda (full gate, 43 modules)` | **1791.0 s** | 1791.0 s | 1 |
| `make agda (full gate, 54 modules)` | **1788.0 s** | 1788.0 s | 1 |
| `make agda (full gate, 32 modules)` | **1642.0 s** | 1642.0 s | 1 |
| `make agda (full gate, 28 modules)` | **1448.0 s** | 1448.0 s | 1 |
| `make agda (full gate, 25 modules)` | **1405.0 s** | 1405.0 s | 1 |
| `make agda (full gate, 174 modules)` | **802.0 s** | 802.0 s | 1 |
| `make agda (full gate, 49 modules)` | **743.0 s** | 743.0 s | 1 |
| `make agda (full gate, 59 modules)` | **704.0 s** | 704.0 s | 1 |
| `make agda (full gate, 34 modules)` | **669.0 s** | 669.0 s | 1 |
| `make agda (full gate, 45 modules)` | **662.0 s** | 662.0 s | 1 |
| `make agda (full gate, 50 modules)` | **660.0 s** | 1935.0 s | 2 |
| `make agda (full gate, 23 modules)` | **399.0 s** | 399.0 s | 1 |
| `make agda (full gate, 22 modules)` | **352.0 s** | 352.0 s | 1 |
| `make agda (full gate, 85 modules)` | **114.0 s** | 114.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part2.agda` | **38.4 s** | 38.4 s | 1 |
| `make agda (full gate, 21 modules)` | **35.0 s** | 59.0 s | 3 |
| `make agda (full gate, 19 modules)` | **31.0 s** | 1370.0 s | 9 |
| `make agda (full gate, 18 modules)` | **28.0 s** | 28.0 s | 5 |
| `make agda (full gate, 17 modules)` | **22.0 s** | 22.0 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda` | **21.8 s** | 25.4 s | 2 |
| `make agda (full gate, 15 modules)` | **21.0 s** | 21.0 s | 2 |
| `make agda (full gate, 14 modules)` | **19.0 s** | 1889.0 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part6.agda` | **18.5 s** | 18.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps.agda` | **16.7 s** | 16.7 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Measures.agda` | **15.2 s** | 17.9 s | 7 |
| `make agda (full gate, 9 modules)` | **14.0 s** | 14.0 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Depth.agda` | **13.1 s** | 13.1 s | 1 |
| `make agda (full gate, 7 modules)` | **13.0 s** | 13.0 s | 1 |
| `make agda (full gate, 6 modules)` | **12.0 s** | 12.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda` | **11.0 s** | 11.0 s | 1 |
| `agda-dev Rx/Evaluator.agda` | **10.9 s** | 10.9 s | 1 |
| `make agda (full gate, 4 modules)` | **10.0 s** | 10.0 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda` | **9.4 s** | 9.4 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Burst-Walk.agda` | **9.2 s** | 14.6 s | 9 |
| `agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda` | **9.1 s** | 9.1 s | 5 |
| `agda-dev Verify-Well-Formed/Part9.agda` | **8.7 s** | 8.7 s | 2 |
| `agda-dev Verify-Well-Formed/Part12.agda` | **8.5 s** | 8.5 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part7.agda` | **8.1 s** | 9.6 s | 4 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part1.agda` | **8.0 s** | 8.0 s | 1 |
| `agda-dev Verify-Well-Formed/Part2.agda` | **7.9 s** | 9.3 s | 2 |
| `agda-dev Verify-Well-Formed/Part6.agda` | **7.9 s** | 7.9 s | 1 |
| `agda-dev Verify-Well-Formed/Part10.agda` | **7.7 s** | 9.0 s | 3 |
| `agda-dev Verify-Well-Formed/Part13.agda` | **7.5 s** | 8.7 s | 3 |
| `agda-dev Verify-Well-Formed/Part7.agda` | **7.5 s** | 7.5 s | 2 |
| `agda-dev Verify-Well-Formed/Part8.agda` | **7.5 s** | 11.9 s | 4 |
| `agda-dev Verify-Well-Formed/Part11.agda` | **7.4 s** | 7.4 s | 4 |
| `agda-dev Verify-Well-Formed/Part1.agda` | **7.3 s** | 7.3 s | 1 |
| `agda-dev Verify-Well-Formed/Part4.agda` | **7.3 s** | 8.5 s | 4 |
| `agda-dev Verify-Well-Formed/Part5.agda` | **7.3 s** | 7.3 s | 2 |
| `make agda (full gate, 2 modules)` | **7.0 s** | 7.0 s | 1 |
| `agda-dev Verify-Well-Formed/Root-Probe.agda` | **6.5 s** | 7.7 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part1.agda` | **6.4 s** | 6.4 s | 2 |
| `agda-dev Verify-Well-Formed/Part3.agda` | **6.4 s** | 7.2 s | 4 |
| `agda-dev QuickCheck.agda` | **6.3 s** | 6.3 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Caps-Face/Part5.agda` | **6.2 s** | 6.2 s | 1 |
| `agda-dev Rx/Evaluator-Theorems.agda` | **5.5 s** | 5.5 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Demand-Probe.agda` | **5.5 s** | 26.6 s | 3 |
| `agda-dev Verify-Budget-Sufficient/Walk-Level.agda` | **5.5 s** | 33.6 s | 17 |
| `agda-dev Verify-Budget-Sufficient/Init-Caps.agda` | **5.2 s** | 5.2 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Wet/Part6.agda` | **5.2 s** | 6.6 s | 4 |
| `agda-dev CLI/Decode.agda` | **5.1 s** | 5.1 s | 1 |
| `agda-dev Rx/Slots.agda` | **5.0 s** | 5.0 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Deliveries.agda` | **4.9 s** | 4.9 s | 1 |
| `agda-dev Rx/Frame-Width.agda` | **4.7 s** | 4.7 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Chain.agda` | **4.7 s** | 4.7 s | 2 |
| `agda-dev Verify-Budget-Sufficient/Caps-Nest.agda` | **4.6 s** | 4.6 s | 1 |
| `agda-dev Rx/Exp.agda` | **4.5 s** | 4.5 s | 2 |
| `agda-dev Harness/Main.agda` | **4.3 s** | 7.0 s | 4 |
| `agda-dev Rx/Hop-Depth.agda` | **4.2 s** | 4.2 s | 1 |
| `agda-dev Readme-Theorems.agda` | **4.1 s** | 4.1 s | 1 |
| `agda-dev Verify-Budget-Sufficient/Demand-Probe-TEMP.agda` | **3.7 s** | 5.4 s | 2 |
| `agda-dev Rx/Hop-Eta-Cong.agda` | **3.4 s** | 3.4 s | 1 |
| `agda-dev Rx/Slot-Hop.agda` | **3.3 s** | 3.3 s | 2 |

<!-- AUTO:DATA {"agda-dev CLI/Decode.agda": {"best": 5.1, "last": 5.1, "runs": 1}, "agda-dev Harness/Main.agda": {"best": 4.3, "last": 7.0, "runs": 4}, "agda-dev QuickCheck.agda": {"best": 6.3, "last": 6.3, "runs": 1}, "agda-dev Readme-Theorems.agda": {"best": 4.1, "last": 4.1, "runs": 1}, "agda-dev Rx/Evaluator-Theorems.agda": {"best": 5.5, "last": 5.5, "runs": 1}, "agda-dev Rx/Evaluator.agda": {"best": 10.9, "last": 10.9, "runs": 1}, "agda-dev Rx/Exp.agda": {"best": 4.5, "last": 4.5, "runs": 2}, "agda-dev Rx/Frame-Width.agda": {"best": 4.7, "last": 4.7, "runs": 2}, "agda-dev Rx/Hop-Depth.agda": {"best": 4.2, "last": 4.2, "runs": 1}, "agda-dev Rx/Hop-Eta-Cong.agda": {"best": 3.4, "last": 3.4, "runs": 1}, "agda-dev Rx/Slot-Hop.agda": {"best": 3.3, "last": 3.3, "runs": 2}, "agda-dev Rx/Slots.agda": {"best": 5.0, "last": 5.0, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Burst-Walk.agda": {"best": 9.2, "last": 14.6, "runs": 9}, "agda-dev Verify-Budget-Sufficient/Caps-Bridge.agda": {"best": 9.1, "last": 9.1, "runs": 5}, "agda-dev Verify-Budget-Sufficient/Caps-Chain.agda": {"best": 4.7, "last": 4.7, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Caps-Depth.agda": {"best": 13.1, "last": 13.1, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Caps-Face/Part1.agda": {"best": 6.4, "last": 6.4, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Caps-Face/Part5.agda": {"best": 6.2, "last": 6.2, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Caps-Face/Part6.agda": {"best": 18.5, "last": 18.5, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Caps-Face/Part7.agda": {"best": 8.1, "last": 9.6, "runs": 4}, "agda-dev Verify-Budget-Sufficient/Caps-Nest.agda": {"best": 4.6, "last": 4.6, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Caps.agda": {"best": 16.7, "last": 16.7, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Deliveries.agda": {"best": 4.9, "last": 4.9, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Delivery-Walk.agda": {"best": 9.4, "last": 9.4, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Demand-Probe-TEMP.agda": {"best": 3.7, "last": 5.4, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Demand-Probe.agda": {"best": 5.5, "last": 26.6, "runs": 3}, "agda-dev Verify-Budget-Sufficient/Init-Caps.agda": {"best": 5.2, "last": 5.2, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Keeps-Ring.agda": {"best": 11.0, "last": 11.0, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Measures.agda": {"best": 15.2, "last": 17.9, "runs": 7}, "agda-dev Verify-Budget-Sufficient/Subscribe-Face.agda": {"best": 21.8, "last": 25.4, "runs": 2}, "agda-dev Verify-Budget-Sufficient/Walk-Level.agda": {"best": 5.5, "last": 33.6, "runs": 17}, "agda-dev Verify-Budget-Sufficient/Wet/Part1.agda": {"best": 8.0, "last": 8.0, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Wet/Part2.agda": {"best": 38.4, "last": 38.4, "runs": 1}, "agda-dev Verify-Budget-Sufficient/Wet/Part6.agda": {"best": 5.2, "last": 6.6, "runs": 4}, "agda-dev Verify-Well-Formed/Part1.agda": {"best": 7.3, "last": 7.3, "runs": 1}, "agda-dev Verify-Well-Formed/Part10.agda": {"best": 7.7, "last": 9.0, "runs": 3}, "agda-dev Verify-Well-Formed/Part11.agda": {"best": 7.4, "last": 7.4, "runs": 4}, "agda-dev Verify-Well-Formed/Part12.agda": {"best": 8.5, "last": 8.5, "runs": 2}, "agda-dev Verify-Well-Formed/Part13.agda": {"best": 7.5, "last": 8.7, "runs": 3}, "agda-dev Verify-Well-Formed/Part2.agda": {"best": 7.9, "last": 9.3, "runs": 2}, "agda-dev Verify-Well-Formed/Part3.agda": {"best": 6.4, "last": 7.2, "runs": 4}, "agda-dev Verify-Well-Formed/Part4.agda": {"best": 7.3, "last": 8.5, "runs": 4}, "agda-dev Verify-Well-Formed/Part5.agda": {"best": 7.3, "last": 7.3, "runs": 2}, "agda-dev Verify-Well-Formed/Part6.agda": {"best": 7.9, "last": 7.9, "runs": 1}, "agda-dev Verify-Well-Formed/Part7.agda": {"best": 7.5, "last": 7.5, "runs": 2}, "agda-dev Verify-Well-Formed/Part8.agda": {"best": 7.5, "last": 11.9, "runs": 4}, "agda-dev Verify-Well-Formed/Part9.agda": {"best": 8.7, "last": 8.7, "runs": 2}, "agda-dev Verify-Well-Formed/Root-Probe.agda": {"best": 6.5, "last": 7.7, "runs": 3}, "make agda (full gate, 14 modules)": {"best": 19.0, "last": 1889.0, "runs": 2}, "make agda (full gate, 15 modules)": {"best": 21.0, "last": 21.0, "runs": 2}, "make agda (full gate, 17 modules)": {"best": 22.0, "last": 22.0, "runs": 3}, "make agda (full gate, 174 modules)": {"best": 802.0, "last": 802.0, "runs": 1}, "make agda (full gate, 18 modules)": {"best": 28.0, "last": 28.0, "runs": 5}, "make agda (full gate, 19 modules)": {"best": 31.0, "last": 1370.0, "runs": 9}, "make agda (full gate, 2 modules)": {"best": 7.0, "last": 7.0, "runs": 1}, "make agda (full gate, 21 modules)": {"best": 35.0, "last": 59.0, "runs": 3}, "make agda (full gate, 22 modules)": {"best": 352.0, "last": 352.0, "runs": 1}, "make agda (full gate, 23 modules)": {"best": 399.0, "last": 399.0, "runs": 1}, "make agda (full gate, 25 modules)": {"best": 1405.0, "last": 1405.0, "runs": 1}, "make agda (full gate, 28 modules)": {"best": 1448.0, "last": 1448.0, "runs": 1}, "make agda (full gate, 32 modules)": {"best": 1642.0, "last": 1642.0, "runs": 1}, "make agda (full gate, 34 modules)": {"best": 669.0, "last": 669.0, "runs": 1}, "make agda (full gate, 37 modules)": {"best": 1831.0, "last": 1831.0, "runs": 1}, "make agda (full gate, 4 modules)": {"best": 10.0, "last": 10.0, "runs": 2}, "make agda (full gate, 43 modules)": {"best": 1791.0, "last": 1791.0, "runs": 1}, "make agda (full gate, 45 modules)": {"best": 662.0, "last": 662.0, "runs": 1}, "make agda (full gate, 49 modules)": {"best": 743.0, "last": 743.0, "runs": 1}, "make agda (full gate, 50 modules)": {"best": 660.0, "last": 1935.0, "runs": 2}, "make agda (full gate, 51 modules)": {"best": 1980.0, "last": 1980.0, "runs": 1}, "make agda (full gate, 54 modules)": {"best": 1788.0, "last": 1788.0, "runs": 1}, "make agda (full gate, 58 modules)": {"best": 2095.0, "last": 2095.0, "runs": 1}, "make agda (full gate, 59 modules)": {"best": 704.0, "last": 704.0, "runs": 1}, "make agda (full gate, 6 modules)": {"best": 12.0, "last": 12.0, "runs": 1}, "make agda (full gate, 7 modules)": {"best": 13.0, "last": 13.0, "runs": 1}, "make agda (full gate, 85 modules)": {"best": 114.0, "last": 114.0, "runs": 1}, "make agda (full gate, 9 modules)": {"best": 14.0, "last": 14.0, "runs": 2}} -->

<!-- AUTO:END -->

## The gate

| | |
|---|---|
| `make agda` full gate, cold | **802 s** (13 m 22 s), 41 modules |
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

- **A PARALLEL `warm-cache` FOR `make agda` WAS MEASURED AND REJECTED (2026-08-18).
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
  which stub mutual blocks — the modules that cost most under real `make agda`
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
  **What actually governs `make agda`'s cost is which module you EDITED.** Warm
  with a shallow change it is 19–43 s (14–21 modules); editing something
  foundational (Rx/Exp, Frame-Width, Measures) invalidates the cone and costs
  the near-cold 660–2095 s. No scheduler changes that.

- **`make refuted` warm: 5.46 s** (real, right after `make agda`). It imports
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
