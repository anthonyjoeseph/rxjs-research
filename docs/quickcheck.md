# `make quickcheck` — the compiled sweep

`agda/src/CLI/QuickCheck.agda`, compiled by GHC: draws random programs, runs the
real evaluator, decides `Main`'s statements, the simulation and its leaf on each
run. Feeds the bug cache. Never a proof's dependency.

```
make quickcheck                       CI's sweep: seeds 1..300, 200 runs each
make quickcheck ARGS='42 42'          one seed
make qc-fast QC='SEED RUNS DEPTH'     one sweep under a hard budget (QC_BUDGET=secs)
make qc-shrink QC=... QC_AT=<case>    shrink one red case
```

All are ordinary builds: one at a time, through `make bg`.

## Knobs

- `QC_STMT` — one statement, in `Main`'s order (simulation fifth, its leaf sixth); `0` for all.
- `QC_DRAW` — one JSON object weighting the generator's arms; unset for the uniform draw.
- `QC_FUEL`, `QC_CASE` (secs per case), `QC_BEAR`.

## A red

1. `make qc-shrink` with the sweep's `QC`, `QC_STMT`, `QC_DRAW` and `QC_AT=<case>`. It shrinks the DRAWS, so the program it prints is one the generator could draw.
2. Paste it as a row of `agda/src/CLI/Unit-Test.agda` → [bug-cache.md](bug-cache.md).
3. Evaluator bug → fix the evaluator. Statement false → restate it.

`make bug-cache` green ⟺ no known counterexample remains.
