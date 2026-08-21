-- THE MEASUREMENT HARNESS — a COMPILED calculator for the machine's own
-- arithmetic.  A MODULE_ROOT (`make harness-build` / `make harness`), so it
-- lives in `src` under the wiring law rather than in a staging directory
-- outside the claim graph.  `src/Main.agda` never reaches it, so `make agda`
-- does not pay for it.
--
-- WHY IT EXISTS.  Two of this machine's number families do not normalise in
-- the TYPECHECKER at all:
--
--   * the `fLvlD`/`sizeAt`/`widAt`/`regAt` family is `abstract`
--     (Evaluator:729) and `blowH` is `abstract` (Evaluator:899), both for a
--     measured performance reason — with the bodies visible, one whnf
--     unfolds the whole loop and the consuming module runs past an hour.
--     `poolCount` is NOT itself abstract, but it calls `fLvlD`, so
--     `poolCount 1 0` is STUCK at the smallest possible arguments;
--   * the deep rungs simply exceed the typechecker (one was killed at
--     12.6 GB after 20 minutes).
--
-- THE GHC BACKEND RUNS THE SAME DEFINITIONS AND IGNORES `abstract`, because
-- opacity is a TYPECHECKING contract and not a runtime one.  So a number
-- unreachable by `refl` is reachable here.
--
-- ⚠ ANYTHING READ OFF THIS BINARY IS `measured-not-rechecked` BY
-- CONSTRUCTION, and must be flagged as such wherever it is recorded.  A
-- compiled number is NOT a `refl` pin and must never be reported as one: no
-- proof may depend on it, and it cannot discharge a postulate.  Its use is
-- to AIM the grind and to REFUTE — a single compiled row that contradicts a
-- postulate is a finding worth chasing back to a type-level witness.
--
-- THE GUARD against a backend that has quietly diverged from the
-- typechecker is CALIBRATION.  Row 0 is a value this very module also pins
-- by `refl` (`calibration-pin` below), so the typechecker fixes the
-- expected number at compile time and the binary prints the computed one.
-- IF ROW 0 DOES NOT PRINT 65536, EVERY OTHER ROW IS VOID — stop and
-- diagnose the backend, do not read on.
--
-- ONE ROW PER PROCESS, deliberately: a single process that computes several
-- deep rungs retains all of them and dies of memory; a fresh process per row
-- does not.
--
--     make harness-build          compile it
--     make harness                every row, one process each
--     make harness ARGS='1'       just row 1
module Harness.Main where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; Unit)
open import Rx.Prim using (towerℕ)
open import Rx.Evaluator using (poolCount; blowH; capsHgo; lvls; iterL)
open import Verify-Budget-Sufficient.Demand-Programs
  using (runDry; progD; sucG)

------------------------------------------------------------------
-- THE CALIBRATION PIN.  `towerℕ` is the one member of this
-- neighbourhood that DOES normalise in the typechecker, which is what
-- makes it usable as a cross-check: the same expression is fixed here by
-- `refl` (so `make agda-dev` checks it) and printed by the compiled
-- binary as row 0.  Agreement is the evidence that the backend computes
-- what the typechecker computes; divergence voids every other row.
--
-- NB `towerℕ` is NOT the thing the harness exists to reach — it was
-- tested and found NOT to be the blocker for the anchor.  It is here
-- precisely BECAUSE it is computable on both sides.
------------------------------------------------------------------

calibration : ℕ
calibration = towerℕ 4

-- ANONYMOUS by the bug-cache idiom (`_ : lhs ≡ rhs`), not by accident: a
-- NAMED pin is a proven definition with no consumer, i.e. an orphan, and
-- `make wiring-gate` rightly fails it (observed while landing this file).
-- Anonymous, the typechecker still fixes the number at compile time and
-- there is no name to orphan.
_ : calibration ≡ 65536
_ = refl

-- THE FAMILY CALIBRATION, pinned.  `towerℕ` agreement says the backend
-- does arithmetic; it says nothing about whether it runs `subscribeE`.
-- These two pin the dry threshold of `progD 1 2` exactly, and rows 3-4
-- print the same two expressions from the compiled binary.  Cheap
-- because the PROGRAM is small (d·k(k+1)/2 = 3 subscription levels), not
-- because drying exits early — it does not.
_ : runDry 2 (progD 1 2) ≡ true
_ = refl
_ : runDry 3 (progD 1 2) ≡ false
_ = refl

------------------------------------------------------------------
-- THE ROWS.  Add rows freely; keep row 0 where it is.  State for each
-- what it would take to make the row INTERESTING — a row that could not
-- have surprised anyone is not a row (CLAUDE.md, de-risk mode).
------------------------------------------------------------------

-- ROWS 0–2 TERMINATE and are what `make harness` sweeps.
-- ROWS 10+ ARE THE QUARANTINE: measured non-terminating, kept because
-- they are the exact expressions someone will want to retry.  They are
-- NOT in the default sweep — running them is an explicit `ARGS=10`.

showB : Bool → String
showB true  = "true"
showB false = "false"

rowAt : ℕ → String
rowAt 0 = "CALIBRATION towerℕ 4 (refl-pinned 65536 in this module) = "
            ++ show calibration
-- towerℕ is the SCALE REFERENCE, not a target: it is the one member of
-- this neighbourhood the typechecker also evaluates, and it shows how
-- fast the caps arithmetic's inputs climb.  towerℕ 5 = 2^65536 is a
-- ~19730-digit number, hence printed as its digit count rather than in
-- full.
rowAt 1 = "towerℕ 3 = " ++ show (towerℕ 3)
rowAt 2 = "towerℕ 4 = " ++ show (towerℕ 4)

------------------------------------------------------------------
-- SERIES Q, THE CROSSOVER — rows 3-8.  The one region this campaign
-- has named FALSITY and left unmeasured, and the reason it was left is
-- exactly the reason this harness exists: `runDry` short-circuits in
-- NEITHER direction (`hasDry` reads the stream `subscribeE` returns, so
-- the whole run normalises before the first dry event is visible), the
-- cost is d·k(k+1)/2 subscription levels, and at the cheapest crossing
-- point that is ~250 — where the typechecker burned 56 min CPU at (8,8)
-- without finishing.  The blowup here is NORMALISER OVERHEAD, not the
-- computational blowup that quarantined rows 10+: ~250 subscription
-- levels is nothing for native code.
--
-- WHAT A ROW MEANS.  `sucG p` is the gas the walk face's demand
-- hypothesis supplies at the adversarial instantiation (Ŝ = R̂ = F = 0,
-- no shares), where `hasAtLeast-pad` makes the gas hypothesis hold
-- EXACTLY.  Every other hypothesis of the face is satisfiable there.
-- So the face asserts `runDry (sucG p) p ≡ false`, and a TRUE row
-- REFUTES WalkStmt itself — not merely a leaf.
--
-- ROWS 3-4 ARE THE FAMILY CALIBRATION and they are load-bearing in both
-- directions: they pin the dry threshold of `progD 1 2` EXACTLY (true at
-- 2, false at 3), and both are ALSO `refl`-pinned in this module below.
-- Row 0 calibrates `towerℕ`, which says nothing about whether the
-- backend runs `subscribeE` the way the typechecker does; these do.
------------------------------------------------------------------

-- the sum side, so a crossover row is self-documenting
rowAt 3 = "CALIBRATION runDry 2 (progD 1 2) [refl-pinned true here] = "
            ++ showB (runDry 2 (progD 1 2))
rowAt 4 = "CALIBRATION runDry 3 (progD 1 2) [refl-pinned false here] = "
            ++ showB (runDry 3 (progD 1 2))
rowAt 5 = "sucG (progD 6 8) = " ++ show (sucG (progD 6 8))
            ++ "   sucG (progD 6 9) = " ++ show (sucG (progD 6 9))
            ++ "   sucG (progD 7 8) = " ++ show (sucG (progD 7 8))
-- (6,8): model says the LAST SAFE point — sucG 50 against demand 49.
-- INTERESTING either way: `true` refutes, `false` is the tight safe row.
rowAt 6 = "runDry (sucG (progD 6 8)) (progD 6 8)  [false = safe] = "
            ++ showB (runDry (sucG (progD 6 8)) (progD 6 8))
-- (6,9): model says the FIRST REFUTING point — sucG 51 against demand 55.
rowAt 7 = "runDry (sucG (progD 6 9)) (progD 6 9)  [TRUE = REFUTES] = "
            ++ showB (runDry (sucG (progD 6 9)) (progD 6 9))
-- (7,8): the second crossing, independent of (6,9) in both d and k.
rowAt 8 = "runDry (sucG (progD 7 8)) (progD 7 8)  [TRUE = REFUTES] = "
            ++ showB (runDry (sucG (progD 7 8)) (progD 7 8))

------------------------------------------------------------------
-- QUARANTINE — DEAD ROUTE 2026-08-12: the caps counting family is
-- UNREACHABLE BY MEASUREMENT, and compiling it does not change that.
--
-- WHAT WAS TRIED.  This harness was built partly on the hypothesis that
-- `poolCount`'s silence in the typechecker was OPACITY (`fLvlD` is
-- `abstract` at Evaluator:729, `blowH` at :899) and that the GHC backend,
-- which ignores `abstract`, would therefore compute it.
--
-- WHAT HAPPENED.  Native, -O, at the SMALLEST POSSIBLE ARGUMENTS:
-- `poolCount 1 0` and `blowH 0` each still running at 45 s, killed with
-- no value.  Row 0 calibrated at 65536 in the same binary, so this is
-- not a broken build — it is the arithmetic.
--
-- WHY IT IS STRUCTURAL, not a matter of waiting longer or of hardware:
-- `blowH m = 6 + m + 2 * poolCount (towerℕ m) m` feeds `poolCount` a
-- TOWER as its first argument, and `poolCount` pools that through
-- `lvls`/`dLvl`/`iterL`, where `dLvl S W d J = iterL S W d (suc (sizeAt S J)) J`
-- iterates a number that itself grows with the level.  The value is
-- astronomically large by construction; no backend prints it.
--
-- CONSEQUENCE — this CONFIRMS the 2026-08-11 ruling "THE ANCHOR CANNOT
-- BE PROBED" by an INDEPENDENT route (native code, no typechecker in the
-- loop), and confirms its stated reason: the blowup is COMPUTATIONAL,
-- not definitional.  Un-sealing the `abstract` blocks would not help,
-- and neither would a faster machine.  **Do not build a probe, a
-- harness row, or a `refl` pin against this family.  The anchor is
-- symbolic-or-nothing.**
------------------------------------------------------------------

rowAt 10 = "poolCount 1 0 = " ++ show (poolCount 1 0)   -- DIVERGENT (45s+, killed)
rowAt 11 = "poolCount 1 1 = " ++ show (poolCount 1 1)   -- DIVERGENT
rowAt 12 = "poolCount 2 0 = " ++ show (poolCount 2 0)   -- DIVERGENT
rowAt 13 = "blowH 0 = "       ++ show (blowH 0)         -- DIVERGENT (45s+, killed)
rowAt 14 = "blowH 1 = "       ++ show (blowH 1)         -- DIVERGENT
rowAt 15 = "capsHgo 0 0 = "   ++ show (capsHgo 0 0)     -- DIVERGENT
rowAt 16 = "lvls 1 1 0 0 1 = "  ++ show (lvls 1 1 0 0 1)
rowAt 17 = "iterL 1 1 0 1 0 = " ++ show (iterL 1 1 0 1 0)
-- THE SWEEPABLE ROW — `d*100 + k + 1000`, so 1608 is (6,8).  Rows 6-8
-- above are the three points the model singles out; this one exists
-- because the COST CURVE of the family had to be measured before any of
-- them could be trusted to terminate, and a rebuild per point is not a
-- measurement loop.  Prints the sum side and the verdict together, so a
-- row is readable without cross-referencing row 5.
rowAt n with 1000 ≤ᵇ n
... | false = "(no such row)"
... | true  =
  let dk = n ∸ 1000
      d  = dk / 100
      k  = dk % 100
      p  = progD d k
      G  = sucG p
  in "d=" ++ show d ++ " k=" ++ show k
     ++ "  sucG=" ++ show G
     ++ "  runDry G p = " ++ showB (runDry G p)
     ++ "   [true = REFUTES WalkStmt]"

------------------------------------------------------------------
-- stdin: a single row index.  Anything unparseable reads as 0, which is
-- the calibration row — the safe default, since a mis-typed index then
-- reports the one number whose expected value is written down.
------------------------------------------------------------------

private
  isDigit : ℕ → Bool
  isDigit c = if 48 ≤ᵇ c then c ≤ᵇ 57 else false

  digits : List ℕ → ℕ → ℕ
  digits []       acc = acc
  digits (c ∷ cs) acc =
    if isDigit c then digits cs (acc * 10 + (c ∸ 48)) else acc

  skipToDigit : List ℕ → List ℕ
  skipToDigit []       = []
  skipToDigit (c ∷ cs) = if isDigit c then (c ∷ cs) else skipToDigit cs

main : IO Unit
main = getContents >>= λ s →
  putStr (rowAt (digits (skipToDigit (map toℕ (toList s))) 0) ++ "\n")
