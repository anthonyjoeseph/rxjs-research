-- A COMPILED MEASUREMENT HARNESS.  `scripts/measure.sh` reads a number off
-- an Agda NORMAL FORM, which is the honest thing to do for a number a
-- `refl` pin will later have to reproduce.  But the deep rungs of the
-- mint-loop ladders do not normalise in the typechecker at all — L = 4,
-- k = 3 was killed at 12.6 GB after 20 minutes — and the GHC backend runs
-- the SAME definitions in seconds.  So the two harnesses divide the work:
-- measure.sh for anything that will be pinned, this for anything that
-- cannot be.
--
-- ANYTHING READ OFF HERE IS `measured-not-rechecked` BY CONSTRUCTION and
-- must be flagged as such wherever it is recorded.  The guard against a
-- backend that has quietly diverged from the typechecker is CALIBRATION:
-- index 0 is a row the `refl` wall already pins, and no compiled number is
-- believed until the compiled harness has reproduced it.
--
-- Usage: `echo N | ./_measure/Measure-Main` prints row N.  One row per
-- process, because a single process that computes several deep rungs
-- retains all of them and dies at ~12 GB; a fresh process per row does not.
--
--     agda -i src -i probe --compile --compile-dir=_measure probe/Measure-Main.agda
--     for n in $(seq 0 20); do echo $n | ./_measure/Measure-Main; done
module Measure-Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.String using (String; _++_; lines)
open import Data.List using (List; []; _∷_)

open import CLI.IO
open import Mint-Loop-Shapes

row : String → ℕ → String
row nm v = nm ++ " = " ++ show v ++ "\n"

rows : List String
rows =
  -- 0: CALIBRATION — pinned by `refl` in Mint-Loop-Probe at 2546
    row "CAL mFolds 0 (pL4 2) insG4 [2546]" (mFolds 0 (pL⁴ 2) insG⁴)
  -- 1: CALIBRATION — pinned at 576
  ∷ row "CAL mFib   0 (pL4 2) insG4 [576]" (mFib 0 (pL⁴ 2) insG⁴)
  -- 2 …: the L = 4 k-sweep proper
  ∷ row "mFolds 0 (pL4 6) insG4" (mFolds 0 (pL⁴ 6) insG⁴)
  ∷ row "mMints 0 (pL4 6) insG4" (mMints 0 (pL⁴ 6) insG⁴)
  ∷ row "mFolds 0 (pL4 7) insG4" (mFolds 0 (pL⁴ 7) insG⁴)
  ∷ row "mMints 0 (pL4 7) insG4" (mMints 0 (pL⁴ 7) insG⁴)
  ∷ row "mFolds 0 (pL4 8) insG4" (mFolds 0 (pL⁴ 8) insG⁴)
  ∷ row "mMints 0 (pL4 8) insG4" (mMints 0 (pL⁴ 8) insG⁴)
  ∷ row "mFolds 0 (pL4 9) insG4" (mFolds 0 (pL⁴ 9) insG⁴)
  ∷ row "mFolds 0 (pL4 10) insG4" (mFolds 0 (pL⁴ 10) insG⁴)
  ∷ row "mFolds 0 (pL4 11) insG4" (mFolds 0 (pL⁴ 11) insG⁴)
  ∷ row "mFolds 0 (pL4 12) insG4" (mFolds 0 (pL⁴ 12) insG⁴)
  ∷ row "mS     0 (pL4 5) insG4" (mS 0 (pL⁴ 5) insG⁴)
  ∷ row "mS     0 (pL4 6) insG4" (mS 0 (pL⁴ 6) insG⁴)
  ∷ row "mReg   0 (pL4 6) insG4" (mReg 0 (pL⁴ 6) insG⁴)
  ∷ row "mReg   0 (pL4 10) insG4" (mReg 0 (pL⁴ 10) insG⁴)
  ∷ row "mJ     0 (pL4 4) insG4" (mJ 0 (pL⁴ 4) insG⁴)
  ∷ row "mJ     0 (pL4 5) insG4" (mJ 0 (pL⁴ 5) insG⁴)
  ∷ row "mFib   0 (pL4 4) insG4" (mFib 0 (pL⁴ 4) insG⁴)
  ∷ row "mPre   0 (pL4 4) insG4" (mPre 0 (pL⁴ 4) insG⁴)
  ∷ row "mS     0 (pL4 12) insG4" (mS 0 (pL⁴ 12) insG⁴)
  ∷ []

idx : ℕ → List String → String
idx _       []       = "OUT-OF-RANGE\n"
idx zero    (x ∷ _)  = x
idx (suc n) (_ ∷ xs) = idx n xs

firstLine : String → String
firstLine s with lines s
... | []      = ""
... | (l ∷ _) = l

main : IO Unit
main =
  getContents >>= λ inp →
  putStr (maybe′ (λ n → idx n rows) "BAD-INDEX\n" (readMaybe 10 (firstLine inp)))
