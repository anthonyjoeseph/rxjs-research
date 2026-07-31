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
open import Data.List using (List; []; _∷_; map; foldr)

open import CLI.IO
open import Mint-Loop-Shapes

row : String → ℕ → String
row nm v = nm ++ " = " ++ show v ++ "\n"

showL : List ℕ → String
showL []       = ""
showL (x ∷ []) = show x
showL (x ∷ xs) = show x ++ " " ++ showL xs

rowL : String → List ℕ → String
rowL nm vs = nm ++ " = " ++ showL vs ++ "\n"

-- the slot vectors: slot L is the scripted input and never fans out
s1 s2 s3 s4 : List ℕ
s1 = 0 ∷ []
s2 = 0 ∷ 1 ∷ []
s3 = 0 ∷ 1 ∷ 2 ∷ []
s4 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

-- the same, plus the scripted input, which dispatches the root chains
d1 d2 d3 d4 : List ℕ
d1 = 0 ∷ 1 ∷ []
d2 = 0 ∷ 1 ∷ 2 ∷ []
d3 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
d4 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

gens : List ℕ
gens = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []

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
  -- 21 …: THE BRANCHING PROFILES.  fires first (off the evaluator's own
  -- handoffs, one cascade per row), then the mirror's cross-check, then
  -- the generation histogram (the mirror walk, so far dearer)
  ∷ rowL "FIRE pS1" (mFires 0 pS¹ insG s1)
  ∷ rowL "FIRE pS2" (mFires 0 pS² insG² s2)
  ∷ rowL "FIRE pS3" (mFires 0 pS³ insG³ s3)
  ∷ rowL "FIRE pS4" (mFires 0 pS⁴ insG⁴ s4)
  ∷ rowL "FIRE pL1 0" (mFires 0 (pL¹ 0) insG s1)
  ∷ rowL "FIRE pL1 1" (mFires 0 (pL¹ 1) insG s1)
  ∷ rowL "FIRE pL1 2" (mFires 0 (pL¹ 2) insG s1)
  ∷ rowL "FIRE pL1 3" (mFires 0 (pL¹ 3) insG s1)
  ∷ rowL "FIRE pL1 4" (mFires 0 (pL¹ 4) insG s1)
  ∷ rowL "FIRE pL1 5" (mFires 0 (pL¹ 5) insG s1)
  ∷ rowL "FIRE pL2 0" (mFires 0 (pL² 0) insG² s2)
  ∷ rowL "FIRE pL2 1" (mFires 0 (pL² 1) insG² s2)
  ∷ rowL "FIRE pL2 2" (mFires 0 (pL² 2) insG² s2)
  ∷ rowL "FIRE pL2 3" (mFires 0 (pL² 3) insG² s2)
  ∷ rowL "FIRE pL2 4" (mFires 0 (pL² 4) insG² s2)
  ∷ rowL "FIRE pL2 5" (mFires 0 (pL² 5) insG² s2)
  ∷ rowL "FIRE pL3 0" (mFires 0 (pL³ 0) insG³ s3)
  ∷ rowL "FIRE pL3 1" (mFires 0 (pL³ 1) insG³ s3)
  ∷ rowL "FIRE pL3 2" (mFires 0 (pL³ 2) insG³ s3)
  ∷ rowL "FIRE pL3 3" (mFires 0 (pL³ 3) insG³ s3)
  ∷ rowL "FIRE pL3 4" (mFires 0 (pL³ 4) insG³ s3)
  ∷ rowL "FIRE pL3 5" (mFires 0 (pL³ 5) insG³ s3)
  ∷ rowL "FIRE pL4 0" (mFires 0 (pL⁴ 0) insG⁴ s4)
  ∷ rowL "FIRE pL4 1" (mFires 0 (pL⁴ 1) insG⁴ s4)
  ∷ rowL "FIRE pL4 2" (mFires 0 (pL⁴ 2) insG⁴ s4)
  ∷ rowL "FIRE pL4 3" (mFires 0 (pL⁴ 3) insG⁴ s4)
  ∷ rowL "FIRE pL4 4" (mFires 0 (pL⁴ 4) insG⁴ s4)
  ∷ rowL "FIRE pL4 5" (mFires 0 (pL⁴ 5) insG⁴ s4)
  -- 49 …: the accumulating ladders, for the lean/accumulating contrast
  ∷ rowL "FIRE pG1 0" (mFires 0 (pG′ 0) insG s1)
  ∷ rowL "FIRE pG1 2" (mFires 0 (pG′ 2) insG s1)
  ∷ rowL "FIRE pG2 0" (mFires 0 (pG′² 0) insG² s2)
  ∷ rowL "FIRE pG2 3" (mFires 0 (pG′² 3) insG² s2)
  ∷ rowL "FIRE pG3 0" (mFires 0 (pG′³ 0) insG³ s3)
  -- 54 …: the mirror's cross-check of the fire vectors
  ∷ rowL "FIREM pL2 2" (mFiresM 0 (pL² 2) insG² s2)
  ∷ rowL "FIREM pL3 2" (mFiresM 0 (pL³ 2) insG³ s3)
  ∷ rowL "FIREM pL4 2" (mFiresM 0 (pL⁴ 2) insG⁴ s4)
  -- 57 …: the generation histograms, with the ledger total as its own
  -- calibration (it must equal mMints)
  ∷ rowL "GEN pL1 0" (mGens 0 (pL¹ 0) insG gens)
  ∷ rowL "GEN pL1 1" (mGens 0 (pL¹ 1) insG gens)
  ∷ rowL "GEN pL1 2" (mGens 0 (pL¹ 2) insG gens)
  ∷ rowL "GEN pL1 3" (mGens 0 (pL¹ 3) insG gens)
  ∷ rowL "GEN pL1 4" (mGens 0 (pL¹ 4) insG gens)
  ∷ rowL "GEN pL1 5" (mGens 0 (pL¹ 5) insG gens)
  ∷ rowL "GEN pL2 0" (mGens 0 (pL² 0) insG² gens)
  ∷ rowL "GEN pL2 1" (mGens 0 (pL² 1) insG² gens)
  ∷ rowL "GEN pL2 2" (mGens 0 (pL² 2) insG² gens)
  ∷ rowL "GEN pL2 3" (mGens 0 (pL² 3) insG² gens)
  ∷ rowL "GEN pL2 4" (mGens 0 (pL² 4) insG² gens)
  ∷ rowL "GEN pL2 5" (mGens 0 (pL² 5) insG² gens)
  ∷ rowL "GEN pL3 0" (mGens 0 (pL³ 0) insG³ gens)
  ∷ rowL "GEN pL3 1" (mGens 0 (pL³ 1) insG³ gens)
  ∷ rowL "GEN pL3 2" (mGens 0 (pL³ 2) insG³ gens)
  ∷ rowL "GEN pL3 3" (mGens 0 (pL³ 3) insG³ gens)
  ∷ rowL "GEN pL3 4" (mGens 0 (pL³ 4) insG³ gens)
  ∷ rowL "GEN pL3 5" (mGens 0 (pL³ 5) insG³ gens)
  ∷ rowL "GEN pL4 0" (mGens 0 (pL⁴ 0) insG⁴ gens)
  ∷ rowL "GEN pL4 1" (mGens 0 (pL⁴ 1) insG⁴ gens)
  ∷ rowL "GEN pL4 2" (mGens 0 (pL⁴ 2) insG⁴ gens)
  ∷ rowL "GEN pL4 3" (mGens 0 (pL⁴ 3) insG⁴ gens)
  ∷ rowL "GEN pL4 4" (mGens 0 (pL⁴ 4) insG⁴ gens)
  ∷ rowL "GEN pL4 5" (mGens 0 (pL⁴ 5) insG⁴ gens)
  ∷ rowL "GEN pS3"   (mGens 0 pS³ insG³ gens)
  ∷ rowL "GEN pS4"   (mGens 0 pS⁴ insG⁴ gens)
  -- 83 …: the ledger totals, which must reproduce mMints exactly
  ∷ row "GENTOT pL3 2" (mGenTot 0 (pL³ 2) insG³)
  ∷ row "GENTOT pL4 2" (mGenTot 0 (pL⁴ 2) insG⁴)
  ∷ row "GENMAX pL3 5" (mGenMax 0 (pL³ 5) insG³)
  ∷ row "GENMAX pL4 4" (mGenMax 0 (pL⁴ 4) insG⁴)
  -- 87 …: THE FAN-OUT WIDTHS.  D split by dispatching source; the row
  -- sums to mFolds, which is its calibration
  ∷ rowL "DELIV pS1" (mDelivs 0 pS¹ insG d1)
  ∷ rowL "DELIV pS2" (mDelivs 0 pS² insG² d2)
  ∷ rowL "DELIV pS3" (mDelivs 0 pS³ insG³ d3)
  ∷ rowL "DELIV pS4" (mDelivs 0 pS⁴ insG⁴ d4)
  ∷ rowL "DELIV pL1 0" (mDelivs 0 (pL¹ 0) insG d1)
  ∷ rowL "DELIV pL1 1" (mDelivs 0 (pL¹ 1) insG d1)
  ∷ rowL "DELIV pL1 2" (mDelivs 0 (pL¹ 2) insG d1)
  ∷ rowL "DELIV pL1 3" (mDelivs 0 (pL¹ 3) insG d1)
  ∷ rowL "DELIV pL1 4" (mDelivs 0 (pL¹ 4) insG d1)
  ∷ rowL "DELIV pL1 5" (mDelivs 0 (pL¹ 5) insG d1)
  ∷ rowL "DELIV pL2 0" (mDelivs 0 (pL² 0) insG² d2)
  ∷ rowL "DELIV pL2 1" (mDelivs 0 (pL² 1) insG² d2)
  ∷ rowL "DELIV pL2 2" (mDelivs 0 (pL² 2) insG² d2)
  ∷ rowL "DELIV pL2 3" (mDelivs 0 (pL² 3) insG² d2)
  ∷ rowL "DELIV pL2 4" (mDelivs 0 (pL² 4) insG² d2)
  ∷ rowL "DELIV pL2 5" (mDelivs 0 (pL² 5) insG² d2)
  ∷ rowL "DELIV pL3 0" (mDelivs 0 (pL³ 0) insG³ d3)
  ∷ rowL "DELIV pL3 1" (mDelivs 0 (pL³ 1) insG³ d3)
  ∷ rowL "DELIV pL3 2" (mDelivs 0 (pL³ 2) insG³ d3)
  ∷ rowL "DELIV pL3 3" (mDelivs 0 (pL³ 3) insG³ d3)
  ∷ rowL "DELIV pL3 4" (mDelivs 0 (pL³ 4) insG³ d3)
  ∷ rowL "DELIV pL3 5" (mDelivs 0 (pL³ 5) insG³ d3)
  ∷ rowL "DELIV pL3 6" (mDelivs 0 (pL³ 6) insG³ d3)
  ∷ rowL "DELIV pL4 0" (mDelivs 0 (pL⁴ 0) insG⁴ d4)
  ∷ rowL "DELIV pL4 1" (mDelivs 0 (pL⁴ 1) insG⁴ d4)
  ∷ rowL "DELIV pL4 2" (mDelivs 0 (pL⁴ 2) insG⁴ d4)
  ∷ rowL "DELIV pL4 3" (mDelivs 0 (pL⁴ 3) insG⁴ d4)
  ∷ rowL "DELIV pL4 4" (mDelivs 0 (pL⁴ 4) insG⁴ d4)
  ∷ rowL "DELIV pL4 5" (mDelivs 0 (pL⁴ 5) insG⁴ d4)
  ∷ rowL "DELIV pG1 0" (mDelivs 0 (pG′ 0) insG d1)
  ∷ rowL "DELIV pG1 2" (mDelivs 0 (pG′ 2) insG d1)
  ∷ rowL "DELIV pG2 0" (mDelivs 0 (pG′² 0) insG² d2)
  ∷ rowL "DELIV pG2 3" (mDelivs 0 (pG′² 3) insG² d2)
  ∷ rowL "DELIV pG3 0" (mDelivs 0 (pG′³ 0) insG³ d3)
  ∷ rowL "FIRE pL3 6" (mFires 0 (pL³ 6) insG³ s3)
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
