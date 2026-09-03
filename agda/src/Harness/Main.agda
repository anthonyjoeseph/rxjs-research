-- THE MEASUREMENT HARNESS — a COMPILED calculator for the machine's own
-- arithmetic.  A MODULE_ROOT (`make harness-build` / `make harness`), so it
-- lives in `src` under the wiring law rather than in a staging directory
-- outside the claim graph.  `src/Main.agda` never reaches it, so `make gate-heavy`
-- does not pay for it.
--
-- WHY IT EXISTS.  Two of this machine's number families do not normalise in
-- the TYPECHECKER at all:
--
--   * `fLvlD` and `blowH` are `abstract` in `Rx.Evaluator`, and
--     `cDel`/`sizeCount` in `Verify-Budget-Sufficient.Caps`, all for a
--     measured performance reason — with the bodies visible, one whnf
--     unfolds the whole loop and the consuming module runs past an hour.
--     `sizeAt`/`widAt`/`regAt` and `poolCount` are NOT themselves
--     abstract, but they call the sealed ones, so `poolCount 1 0` is
--     STUCK at the smallest possible arguments — and so is the CAPS
--     RECURRENCE at its own entry, since `capsAt e sl 0` is
--     `frameBlowup` of `sizeCount`;
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

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_; toList)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; Unit)
open import Rx.Prim using (towerℕ; cold; after_,_; gasPad; g0)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; scanᵉ; mergeAllᵉ;
  emptyᵉ; varᵗ; fstᵗ; strmᵗ; input; syncSizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (poolCount; blowH; capsHgo; lvls; iterL;
  capsBase; subscribeE; sched-next; cascade; Sched; EvalSt; root; sched-init;
  st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit; slotWrapSum;
  nestCapAt)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestWalkAt;
  capΦAt; nestΦAt)

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

------------------------------------------------------------------
-- THE ROWS.  Add rows freely; keep row 0 where it is.  State for each
-- what it would take to make the row INTERESTING — a row that could not
-- have surprised anyone is not a row (CLAUDE.md, de-risk mode).
------------------------------------------------------------------

-- ROWS 0–2 TERMINATE and are what `make harness` sweeps.
-- ROWS 10+ ARE THE QUARANTINE: measured non-terminating, kept because
-- they are the exact expressions someone will want to retry.  They are
-- NOT in the default sweep — running them is an explicit `ARGS=10`.
-- Indices 20+ cannot be literal PATTERNS (Agda expands a numeric
-- literal pattern to that many constructors), so a series wanting them
-- dispatches on an offset from the catch-all clause instead.

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

------------------------------------------------------------------
-- SERIES — THE DEPTH CHARGE AT THE ENTRY INSTANT, PRICED.
--
-- TARGET: scanΦ-fit @ce80e6
--
-- WHY THIS CANNOT BE A PROBE.  The arm's residue is that no premise
-- names the node table, and the fact that would is ambient — so the
-- question is what the two sides actually MEASURE at a state a run
-- reached.  The store side computes in the typechecker; the charge
-- side does not, at any instant.  `nestΦAt` and its two summands are
-- sealed in `Caps-Face.Nest-Arith`, and the `-def` equations only hand
-- the body back in terms of `capsAt`, which is itself stuck at its own
-- ENTRY: `capsAt e sl 0` is `frameBlowup` of the sealed `sizeCount`,
-- so there is no instant at which a `refl` reaches these numbers.
--
-- AND THE CHARGE IS UNREACHABLE HERE TOO, WHICH IS WHAT THESE ROWS
-- REPORT.  Rows 3, 5, 6 and 18 terminate at once; rows 4, 7, 8 and 9
-- were each killed at 180 s with no value, native, at the smallest
-- program that reaches this arm.  They are kept for the reason the
-- quarantine's rows are kept — they are the expressions someone will
-- want to retry — and the cause is the same one, reached by a
-- different route: every one of them reads `Caps.cSize (capsAt e sl
-- 0)`, and the entry caps are `frameBlowup` of `sizeCount`, which
-- pools `cDel` through `lvls`.  `nestCapAt` is the one summand that
-- escapes, and only at the entry, where it IS `nestUnit`.
--
-- SO THE TWO SIDES CANNOT BE COMPARED BY INSTANTIATION AT ALL, and
-- that is a fact about the obligation rather than about this harness:
-- the store side computes in the typechecker and the charge side
-- computes nowhere.  A row above the walk would have been a FALSITY on
-- the charge, and no row can be taken.
--
-- WHAT THE STORE SIDE DOES SAY, and row 18 is where it says it.  The
-- table is read at the subscribe frame and after each arrival, and it
-- reads one less than two to the burst length, then DOUBLES on the
-- first later value and stands still after -- which is the doubling
-- step under the burst, in the table, at the arm's own shape.  The
-- side that can be measured therefore grows exponentially in a count
-- the arm's premises never bound, which is the same defect its header
-- records about `valsΦ?` arriving from the store rather than from the
-- charge.

Γᴴ : Ctx 2
Γᴴ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- THE ARM'S OWN SHAPE.  `scanΦ-fit` is the SCAN arm, and the step here
-- names its accumulator twice -- in the inner scan's seed and in its
-- step -- so one application doubles the stored nesting.  That is what
-- puts a positive `nodeNest` in the table at all; a `mapᵉ` program
-- leaves it flat at zero and its store row could not have failed.
deepenᴴ : Fn Γᴴ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepenᴴ = strmᵗ (mergeAllᵉ nothing
            (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                   (fstᵗ (varᵗ (here refl)))
                   (input (fsuc fzero))))

eᴴ : Closed Γᴴ (obs natᵗ)
eᴴ = scanᵉ deepenᴴ (strmᵗ emptyᵉ) (input (fsuc fzero))

slᴴ : Slots Γᴴ
slᴴ fzero        = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ []))
slᴴ (fsuc fzero) = scripted (cold (4 ∷ 3 ∷ 2 ∷ 1 ∷ []) ((after 9 , 0) ∷ []))

-- one arrival, state threaded; `drain` returns the stream alone, and
-- what this series needs is the store the run LEFT
stepH : Sched Γᴴ × EvalSt eᴴ → Sched Γᴴ × EvalSt eᴴ
stepH (sd , st) with sched-next sd
... | inj₁ _       = sd , st
... | inj₂ (a , s) = let r = cascade a 1 s st in proj₁ (proj₂ r) , proj₂ (proj₂ r)

driveH : ℕ → Sched Γᴴ × EvalSt eᴴ
driveH n = go n (let r = subscribeE
                           (gasPad (syncSizeᵉ eᴴ + hopDᵉ 0 (slotHop 0 slᴴ) eᴴ) g0)
                           eᴴ root 0 0 (sched-init eᴴ slᴴ) (st-init eᴴ)
                 in proj₁ (proj₂ r) , proj₂ (proj₂ r))
  where
  go : ℕ → Sched Γᴴ × EvalSt eᴴ → Sched Γᴴ × EvalSt eᴴ
  go 0       x = x
  go (suc k) x = go k (stepH x)


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

rowAt 3 = "capsBase = "   ++ show (capsBase eᴴ slᴴ)
rowAt 4 = "cSize@0 = "    ++ show (Caps.cSize (capsAt eᴴ slᴴ 0))   -- NO VALUE (180s)
rowAt 5 = "nestUnit = "   ++ show (nestUnit eᴴ slᴴ)
            ++ "  slotWrapSum = " ++ show (slotWrapSum slᴴ)
rowAt 6 = "nestCapAt@0 = " ++ show (nestCapAt eᴴ slᴴ 0)
rowAt 7 = "nestWalkAt@0 = " ++ show (nestWalkAt eᴴ slᴴ 0)  -- NO VALUE (180s)
rowAt 8 = "capΦAt@0 = "   ++ show (capΦAt eᴴ slᴴ 0)        -- NO VALUE (180s)
rowAt 9 = "nestΦAt@0 = "  ++ show (nestΦAt eᴴ slᴴ 0)       -- NO VALUE (180s)


------------------------------------------------------------------
-- QUARANTINE.  The caps counting family is UNREACHABLE BY MEASUREMENT,
-- and compiling it does not change that.
--
-- WHAT WAS TRIED.  This harness was built partly on the hypothesis that
-- `poolCount`'s silence in the typechecker was OPACITY (`fLvlD` is
-- `abstract` at Rx.Evaluator, `blowH` at :899) and that the GHC backend,
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
-- CONSEQUENCE — this CONFIRMS the ruling "THE ANCHOR CANNOT
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

-- the STORE side of the series above, kept out of the quarantine's
-- range: the node table a RUN reaches, driven past the subscribe frame
-- rather than read at `st-init`, whose `nodesMax` is zero by
-- construction and would make the row degenerate
rowAt 18 = "nodesMax@0..4 = " ++ show (nodesMax (proj₂ (driveH 0)))
             ++ " " ++ show (nodesMax (proj₂ (driveH 1)))
             ++ " " ++ show (nodesMax (proj₂ (driveH 2)))
             ++ " " ++ show (nodesMax (proj₂ (driveH 4)))
rowAt n = "(no such row)"

main : IO Unit
main = getContents >>= λ s →
  putStr (rowAt (digits (skipToDigit (map toℕ (toList s))) 0) ++ "\n")

