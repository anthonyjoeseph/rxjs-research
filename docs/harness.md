# `make harness` — the compiled calculator

Numbers the typechecker cannot reach.

```
make harness-build        compile it (agda --compile → agda/_harness/Main)
make harness              the terminating rows, one process each, calibrated first
make harness ARGS='10'    ONE row by index (the only way to run a quarantined row)
```

`agda/src/Harness/Main.agda` is a **MODULE_ROOT** — in `src` under the wiring law,
but not reached by `src/Main.agda`, so `make agda` never pays for it.

**It exists because the GHC backend ignores `abstract`**: opacity is a *typechecking*
contract, not a runtime one, so the compiled binary runs the real bodies of families
the checker refuses to unfold — the ones the evaluator's `abstract` block seals — and
it laughs at rungs that OOM the checker.

## ⚠ Every number it prints is `measured-not-rechecked`, and saying so is mandatory

A harness row is **not** a `refl` pin: it cannot discharge a postulate, no proof may
depend on it, and reporting one as "verified" or "typechecks" is the same false-green
failure as calling a dev run a gate.

Its two legitimate uses are to **AIM the grind** and to **REFUTE** — and a row that
contradicts a postulate is a lead to chase back to a type-level witness, not itself
the finding.

## Row 0 is a calibration and it is load-bearing

It prints a value the module also pins by `refl` (`towerℕ 4 ≡ 65536`), so the
typechecker fixes the expected number and the binary prints the computed one.
`make harness` runs it FIRST and **stops on mismatch**, because a backend that has
quietly diverged makes every other row a confident lie. Never bypass it by calling
`./_harness/Main` directly.

## Adding a row

Extend `rowAt`, keep row 0 where it is, and say what would make the row INTERESTING —
the "a row that could not have failed is not a row" rule applies here exactly as it
does to probes.

**Pins are ANONYMOUS (`_ : lhs ≡ rhs`), by the bug-cache idiom.** A *named* pin is a
proven definition nothing reaches, and `make wiring-gate` correctly fails it; an
anonymous one is a reachability seed and is never reported.

## What it cannot do

**Compiling a family does not make it measurable.** Unsealing buys opacity, not
speed: a family whose blowup is COMPUTATIONAL runs just as long in the binary as it
sticks in the checker, and rows against one are quarantined at 10+ and excluded from
the default sweep. The measured instance and its consequences live at the `abstract`
block in `Rx/Evaluator.agda` — read that header before proposing a harness row
against anything it seals.
