-- THE COMPILED HARNESS FOR THE INSTANT SWEEP, Measure-Main's twin.
--
-- Every quantity Instant-Height-Probe measures at instant id re-runs the
-- evaluator through id + 1 cascades, and the tower families are exactly
-- the ones whose SECOND cascade Charge-Probe could not normalise in the
-- typechecker (progW cascade 1 ran past five minutes).  The GHC backend
-- runs the same definitions in seconds, so the two harnesses divide the
-- work the same way they do next door: the typechecker for anything that
-- will be pinned, this for anything that cannot be.
--
-- ANYTHING READ OFF HERE IS `compiled` — measured-not-rechecked — and is
-- marked as such in the probe's tables.  The guard is CALIBRATION: rows
-- 0 and 1 are Charge-Probe's own pinned receipt-weighted j, recomputed
-- by this probe's pair-carrying walk, and no compiled number is believed
-- until they reproduce 23 and 47.
--
-- Usage: `echo N | ./_ih/Instant-Height-Main` prints row N.  One row per
-- process — a single process that computes several deep rungs retains
-- all of them and dies.
--
--     agda -i src -i probe --compile --compile-dir=_ih probe/Instant-Height-Main.agda
--     for n in $(seq 0 40); do echo $n | ./_ih/Instant-Height-Main; done
module Instant-Height-Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.String using (String; _++_; lines)
open import Data.List using (List; []; _∷_)

open import CLI.IO
open import Mint-Loop-Shapes using (pL²; pL³; insG; insG²; insG³;
                                   mS; mJ; mFolds)
open import Charge-Probe using (progD; progDT; progW; pF1; pF2;
                                mW; ins₀; insD₁; insD₂)
open import Instant-Height-Probe

row : String → ℕ → String
row nm v = nm ++ " = " ++ show v ++ "\n"

showL : List ℕ → String
showL []       = ""
showL (x ∷ []) = show x
showL (x ∷ xs) = show x ++ " " ++ showL xs

-- V J F D S W S+   (W+ is its own row: on the deepening families it
-- outgrows the numeral)
rowT : String → List ℕ → String
rowT nm vs = nm ++ " = " ++ showL vs ++ "\n"

rows : List String
rows =
  -- 0, 1: CALIBRATION against Charge-Probe's pinned receipt-weighted j
    row "CAL iJ 0 progDT insD1 [23]" (iJ 0 progDT insD₁)
  ∷ row "CAL iJ 0 progW  insD2 [47]" (iJ 0 progW  insD₂)
  ∷ rowT "TUP progDT insD2 id0" (tup 0 progDT insD₂)
  ∷ row  "WPL progDT insD2 id0" (wStore 0 progDT insD₂)
  ∷ row  "WDG progDT insD2 id0" (wDig 0 progDT insD₂)
  ∷ rowT "TUP progDT insD2 id1" (tup 1 progDT insD₂)
  ∷ row  "WPL progDT insD2 id1" (wStore 1 progDT insD₂)
  ∷ row  "WDG progDT insD2 id1" (wDig 1 progDT insD₂)
  ∷ rowT "TUP progDT insD4 id0" (tup 0 progDT insD⁴)
  ∷ row  "WPL progDT insD4 id0" (wStore 0 progDT insD⁴)
  ∷ row  "WDG progDT insD4 id0" (wDig 0 progDT insD⁴)
  ∷ rowT "TUP progDT insD4 id1" (tup 1 progDT insD⁴)
  ∷ row  "WPL progDT insD4 id1" (wStore 1 progDT insD⁴)
  ∷ row  "WDG progDT insD4 id1" (wDig 1 progDT insD⁴)
  ∷ rowT "TUP progDT insD4 id2" (tup 2 progDT insD⁴)
  ∷ row  "WPL progDT insD4 id2" (wStore 2 progDT insD⁴)
  ∷ row  "WDG progDT insD4 id2" (wDig 2 progDT insD⁴)
  ∷ rowT "TUP progDT insD4 id3" (tup 3 progDT insD⁴)
  ∷ row  "WPL progDT insD4 id3" (wStore 3 progDT insD⁴)
  ∷ row  "WDG progDT insD4 id3" (wDig 3 progDT insD⁴)
  ∷ rowT "TUP progW insD2 id0" (tup 0 progW insD₂)
  ∷ row  "WPL progW insD2 id0" (wStore 0 progW insD₂)
  ∷ row  "WDG progW insD2 id0" (wDig 0 progW insD₂)
  ∷ rowT "TUP progW insD2 id1" (tup 1 progW insD₂)
  ∷ row  "WPL progW insD2 id1" (wStore 1 progW insD₂)
  ∷ row  "WDG progW insD2 id1" (wDig 1 progW insD₂)
  ∷ rowT "TUP progW insD4 id0" (tup 0 progW insD⁴)
  ∷ row  "WPL progW insD4 id0" (wStore 0 progW insD⁴)
  ∷ row  "WDG progW insD4 id0" (wDig 0 progW insD⁴)
  ∷ rowT "TUP progW insD4 id1" (tup 1 progW insD⁴)
  ∷ row  "WPL progW insD4 id1" (wStore 1 progW insD⁴)
  ∷ row  "WDG progW insD4 id1" (wDig 1 progW insD⁴)
  ∷ rowT "TUP progW insD4 id2" (tup 2 progW insD⁴)
  ∷ row  "WPL progW insD4 id2" (wStore 2 progW insD⁴)
  ∷ row  "WDG progW insD4 id2" (wDig 2 progW insD⁴)
  ∷ rowT "TUP progW insD4 id3" (tup 3 progW insD⁴)
  ∷ row  "WPL progW insD4 id3" (wStore 3 progW insD⁴)
  ∷ row  "WDG progW insD4 id3" (wDig 3 progW insD⁴)
  ∷ rowT "TUP pF1 insG id0" (tup 0 pF1 insG)
  ∷ row  "WPL pF1 insG id0" (wStore 0 pF1 insG)
  ∷ row  "WDG pF1 insG id0" (wDig 0 pF1 insG)
  ∷ rowT "TUP pF1 insG id1" (tup 1 pF1 insG)
  ∷ row  "WPL pF1 insG id1" (wStore 1 pF1 insG)
  ∷ row  "WDG pF1 insG id1" (wDig 1 pF1 insG)
  ∷ rowT "TUP pF1 insG id2" (tup 2 pF1 insG)
  ∷ row  "WPL pF1 insG id2" (wStore 2 pF1 insG)
  ∷ row  "WDG pF1 insG id2" (wDig 2 pF1 insG)
  ∷ rowT "TUP pF1 insG id3" (tup 3 pF1 insG)
  ∷ row  "WPL pF1 insG id3" (wStore 3 pF1 insG)
  ∷ row  "WDG pF1 insG id3" (wDig 3 pF1 insG)
  ∷ rowT "TUP pF2 insG2 id0" (tup 0 pF2 insG²)
  ∷ row  "WPL pF2 insG2 id0" (wStore 0 pF2 insG²)
  ∷ row  "WDG pF2 insG2 id0" (wDig 0 pF2 insG²)
  ∷ rowT "TUP pF2 insG2 id1" (tup 1 pF2 insG²)
  ∷ row  "WPL pF2 insG2 id1" (wStore 1 pF2 insG²)
  ∷ row  "WDG pF2 insG2 id1" (wDig 1 pF2 insG²)
  ∷ rowT "TUP pF2 insG2 id2" (tup 2 pF2 insG²)
  ∷ row  "WPL pF2 insG2 id2" (wStore 2 pF2 insG²)
  ∷ row  "WDG pF2 insG2 id2" (wDig 2 pF2 insG²)
  ∷ rowT "TUP pF2 insG2 id3" (tup 3 pF2 insG²)
  ∷ row  "WPL pF2 insG2 id3" (wStore 3 pF2 insG²)
  ∷ row  "WDG pF2 insG2 id3" (wDig 3 pF2 insG²)
  ∷ rowT "TUP pmu2 id0" (tup 0 pμ2 ins₀)
  ∷ row  "WPL pmu2 id0" (wStore 0 pμ2 ins₀)
  ∷ row  "WDG pmu2 id0" (wDig 0 pμ2 ins₀)
  ∷ rowT "TUP pmu2 id1" (tup 1 pμ2 ins₀)
  ∷ row  "WPL pmu2 id1" (wStore 1 pμ2 ins₀)
  ∷ row  "WDG pmu2 id1" (wDig 1 pμ2 ins₀)
  ∷ rowT "TUP pmu2 id2" (tup 2 pμ2 ins₀)
  ∷ row  "WPL pmu2 id2" (wStore 2 pμ2 ins₀)
  ∷ row  "WDG pmu2 id2" (wDig 2 pμ2 ins₀)
  ∷ rowT "TUP pmu2 id3" (tup 3 pμ2 ins₀)
  ∷ row  "WPL pmu2 id3" (wStore 3 pμ2 ins₀)
  ∷ row  "WDG pmu2 id3" (wDig 3 pμ2 ins₀)
  ∷ rowT "TUP pmuD id0" (tup 0 pμD ins₀)
  ∷ row  "WPL pmuD id0" (wStore 0 pμD ins₀)
  ∷ row  "WDG pmuD id0" (wDig 0 pμD ins₀)
  ∷ rowT "TUP pmuD id1" (tup 1 pμD ins₀)
  ∷ row  "WPL pmuD id1" (wStore 1 pμD ins₀)
  ∷ row  "WDG pmuD id1" (wDig 1 pμD ins₀)
  ∷ rowT "TUP pmuD id2" (tup 2 pμD ins₀)
  ∷ row  "WPL pmuD id2" (wStore 2 pμD ins₀)
  ∷ row  "WDG pmuD id2" (wDig 2 pμD ins₀)
  ∷ rowT "TUP pmuD id3" (tup 3 pμD ins₀)
  ∷ row  "WPL pmuD id3" (wStore 3 pμD ins₀)
  ∷ row  "WDG pmuD id3" (wDig 3 pμD ins₀)
  ∷ rowT "TUP pL2 2 insG2 id0" (tup 0 (pL² 2) insG²)
  ∷ row  "WPL pL2 2 insG2 id0" (wStore 0 (pL² 2) insG²)
  ∷ row  "WDG pL2 2 insG2 id0" (wDig 0 (pL² 2) insG²)
  ∷ rowT "TUP pL2 2 insG2 id1" (tup 1 (pL² 2) insG²)
  ∷ row  "WPL pL2 2 insG2 id1" (wStore 1 (pL² 2) insG²)
  ∷ row  "WDG pL2 2 insG2 id1" (wDig 1 (pL² 2) insG²)
  ∷ rowT "TUP pL2 2 insG2 id2" (tup 2 (pL² 2) insG²)
  ∷ row  "WPL pL2 2 insG2 id2" (wStore 2 (pL² 2) insG²)
  ∷ row  "WDG pL2 2 insG2 id2" (wDig 2 (pL² 2) insG²)
  ∷ rowT "TUP pL2 2 insG2 id3" (tup 3 (pL² 2) insG²)
  ∷ row  "WPL pL2 2 insG2 id3" (wStore 3 (pL² 2) insG²)
  ∷ row  "WDG pL2 2 insG2 id3" (wDig 3 (pL² 2) insG²)
  ∷ rowT "TUP pL3 0 insG3 id0" (tup 0 (pL³ 0) insG³)
  ∷ row  "WPL pL3 0 insG3 id0" (wStore 0 (pL³ 0) insG³)
  ∷ row  "WDG pL3 0 insG3 id0" (wDig 0 (pL³ 0) insG³)
  ∷ rowT "TUP pL3 0 insG3 id1" (tup 1 (pL³ 0) insG³)
  ∷ row  "WPL pL3 0 insG3 id1" (wStore 1 (pL³ 0) insG³)
  ∷ row  "WDG pL3 0 insG3 id1" (wDig 1 (pL³ 0) insG³)
  ∷ rowT "TUP progD id0" (tup 0 progD ins₀)
  ∷ row  "WPL progD id0" (wStore 0 progD ins₀)
  ∷ row  "WDG progD id0" (wDig 0 progD ins₀)
  ∷ rowT "CAS progDT insD4 id3" (cas 3 progDT insD⁴)
  ∷ row  "SPL progDT insD4 id3" (sStore 3 progDT insD⁴)
  ∷ row  "VON progDT insD4 id3" (iV 3 progDT insD⁴)
  ∷ rowT "CAS progW insD2 id1" (cas 1 progW insD₂)
  ∷ row  "SPL progW insD2 id1" (sStore 1 progW insD₂)
  ∷ row  "VON progW insD2 id1" (iV 1 progW insD₂)
  ∷ rowT "CAS progW insD4 id1" (cas 1 progW insD⁴)
  ∷ row  "SPL progW insD4 id1" (sStore 1 progW insD⁴)
  ∷ row  "VON progW insD4 id1" (iV 1 progW insD⁴)
  ∷ rowT "CAS progW insD4 id2" (cas 2 progW insD⁴)
  ∷ row  "SPL progW insD4 id2" (sStore 2 progW insD⁴)
  ∷ row  "VON progW insD4 id2" (iV 2 progW insD⁴)
  ∷ rowT "CAS progW insD4 id3" (cas 3 progW insD⁴)
  ∷ row  "SPL progW insD4 id3" (sStore 3 progW insD⁴)
  ∷ row  "VON progW insD4 id3" (iV 3 progW insD⁴)
  ∷ rowT "CAS pF1 insG id3" (cas 3 pF1 insG)
  ∷ row  "SPL pF1 insG id3" (sStore 3 pF1 insG)
  ∷ row  "VON pF1 insG id3" (iV 3 pF1 insG)
  ∷ rowT "CAS pF2 insG2 id1" (cas 1 pF2 insG²)
  ∷ row  "SPL pF2 insG2 id1" (sStore 1 pF2 insG²)
  ∷ row  "VON pF2 insG2 id1" (iV 1 pF2 insG²)
  ∷ rowT "CAS pF2 insG2 id2" (cas 2 pF2 insG²)
  ∷ row  "SPL pF2 insG2 id2" (sStore 2 pF2 insG²)
  ∷ row  "VON pF2 insG2 id2" (iV 2 pF2 insG²)
  ∷ rowT "CAS pF2 insG2 id3" (cas 3 pF2 insG²)
  ∷ row  "SPL pF2 insG2 id3" (sStore 3 pF2 insG²)
  ∷ row  "VON pF2 insG2 id3" (iV 3 pF2 insG²)
  ∷ rowT "CAS pmuD id2" (cas 2 pμD ins₀)
  ∷ row  "SPL pmuD id2" (sStore 2 pμD ins₀)
  ∷ row  "VON pmuD id2" (iV 2 pμD ins₀)
  ∷ rowT "CAS pmuD id3" (cas 3 pμD ins₀)
  ∷ row  "SPL pmuD id3" (sStore 3 pμD ins₀)
  ∷ row  "VON pmuD id3" (iV 3 pμD ins₀)
  ∷ row  "JON progDT insD4 id3" (iJ 3 progDT insD⁴)
  ∷ row  "SON progDT insD4 id3" (mS 3 progDT insD⁴)
  ∷ row  "DON progDT insD4 id3" (mFolds 3 progDT insD⁴)
  ∷ row  "WON progDT insD4 id3" (mW 3 progDT insD⁴)
  ∷ row  "JON progW insD2 id1" (iJ 1 progW insD₂)
  ∷ row  "SON progW insD2 id1" (mS 1 progW insD₂)
  ∷ row  "DON progW insD2 id1" (mFolds 1 progW insD₂)
  ∷ row  "WON progW insD2 id1" (mW 1 progW insD₂)
  ∷ row  "JON progW insD4 id1" (iJ 1 progW insD⁴)
  ∷ row  "SON progW insD4 id1" (mS 1 progW insD⁴)
  ∷ row  "DON progW insD4 id1" (mFolds 1 progW insD⁴)
  ∷ row  "WON progW insD4 id1" (mW 1 progW insD⁴)
  ∷ row  "JON pF1 insG id3" (iJ 3 pF1 insG)
  ∷ row  "SON pF1 insG id3" (mS 3 pF1 insG)
  ∷ row  "DON pF1 insG id3" (mFolds 3 pF1 insG)
  ∷ row  "WON pF1 insG id3" (mW 3 pF1 insG)
  ∷ row  "JON pF2 insG2 id1" (iJ 1 pF2 insG²)
  ∷ row  "SON pF2 insG2 id1" (mS 1 pF2 insG²)
  ∷ row  "DON pF2 insG2 id1" (mFolds 1 pF2 insG²)
  ∷ row  "WON pF2 insG2 id1" (mW 1 pF2 insG²)
  ∷ row  "JON pmuD id2" (iJ 2 pμD ins₀)
  ∷ row  "SON pmuD id2" (mS 2 pμD ins₀)
  ∷ row  "DON pmuD id2" (mFolds 2 pμD ins₀)
  ∷ row  "WON pmuD id2" (mW 2 pμD ins₀)
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
