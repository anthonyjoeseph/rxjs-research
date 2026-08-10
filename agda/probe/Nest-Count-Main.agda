-- ROADMAP: INFRASTRUCTURE — GHC driver for Nest-Count-Probe's rows.
-- DELETE WHEN: its last dependent probe is deleted  [T8]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- THE COMPILED HARNESS FOR THE NEST-COUNT PROBE, Instant-Height-Main's
-- twin and for the same reason: every row re-runs the evaluator through
-- id + 1 cascades, and the fan-out families do it once per delivery.
-- The typechecker reaches the syntax rows (which is where the `refl`
-- pins are); this reaches the RUNS.
--
-- ANYTHING READ OFF HERE IS `compiled` — measured-not-rechecked — and is
-- marked so in the probe's tables.  The guard is CALIBRATION: rows 0
-- and 1 reproduce Instant-Height's own progDT heights, and the `pFan`
-- rungs whose W⁺ is a numeral reproduce that probe's 6 and 3072.
--
--     agda -i src -i probe --compile --compile-dir=_nc probe/Nest-Count-Main.agda
--     for n in $(seq 0 30); do echo $n | ./_nc/Nest-Count-Main; done
module Nest-Count-Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.String using (String; _++_; lines)
open import Data.List using (List; []; _∷_)

open import CLI.IO
open import Rx.Exp using (Ctx; Closed)
open import Rx.Prim using (Fuel)
open import Rx.Evaluator using (Slots)
open import Charge-Probe using (ins₀; insD₂; progD; progDT; progW; pF1; pF2)
open import Instant-Height-Probe using (pμ2; pμD; wStore; wNeed)
open import Mint-Loop-Shapes using (mS; mReg; mFolds; insG; insG²; insG³;
                                    pL²; pL³)
-- moved to Rx.Evaluator when the Verify-Budget-Sufficient umbrella was
-- split (a8508d6)
open import Rx.Evaluator using (iterFold)
open import Nest-Count-Probe

showL : List ℕ → String
showL []       = ""
showL (x ∷ []) = show x
showL (x ∷ xs) = show x ++ " " ++ showL xs

rowS : String → List ℕ → String
rowS nm vs = nm ++ " = " ++ showL vs ++ "\n"

-- §9's gate row: R (the registrations the pre-cascade state holds) ;
-- D (the cascade's real deliveries) ; S (the tightest admissible cSize)
grow : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → List ℕ
grow id e ins = mReg id e ins ∷ mFolds id e ins ∷ mS id e ins ∷ []

-- every row is S ; N(id) ; N(id+1) ; acc(id) ; acc(id+1)
rows : List String
rows =
  -- 0, 1: CALIBRATION against Instant-Height's deepening rows
    rowS "CAL progDT id0" (nrow 0 progDT insD₂)
  ∷ rowS "CAL progDT id1" (nrow 1 progDT insD₂)
  ∷ rowS "CAL pmuD id0"   (nrow 0 pμD ins₀)
  ∷ rowS "CAL pmuD id1"   (nrow 1 pμD ins₀)
  ∷ rowS "CAL progW id0"  (nrow 0 progW insD₂)
  ∷ rowS "CAL pF1 id0"    (nrow 0 pF1 insG)
  ∷ rowS "CAL pF2 id0"    (nrow 0 pF2 insG²)
  -- the per-application half: one fn2 fold per instant, four instants
  ∷ rowS "APP pmuD2M id0" (nrow 0 pμD2M ins₀)
  ∷ rowS "APP pmuD2M id1" (nrow 1 pμD2M ins₀)
  ∷ rowS "APP pmuD2M id2" (nrow 2 pμD2M ins₀)
  ∷ rowS "APP pmuD2M id3" (nrow 3 pμD2M ins₀)
  -- the per-instant half: n deliveries, one nesting
  ∷ rowS "FAN pFan1 id0" (nrow 0 (pFan 1) insD₂)
  ∷ rowS "FAN pFan2 id0" (nrow 0 (pFan 2) insD₂)
  ∷ rowS "FAN pFan3 id0" (nrow 0 (pFan 3) insD₂)
  ∷ rowS "FAN pFan4 id0" (nrow 0 (pFan 4) insD₂)
  ∷ rowS "FAN pFan5 id0" (nrow 0 (pFan 5) insD₂)
  ∷ rowS "FAN pFan3 id1" (nrow 1 (pFan 3) insD₂)
  -- and the numerals where the numerals exist
  ∷ rowS "NUM pFan1 W+"  (wStore 0 (pFan 1) insD₂ ∷ [])
  ∷ rowS "NUM pFan2 W+"  (wStore 0 (pFan 2) insD₂ ∷ [])
  ∷ rowS "NUM pFan1 wNeed" (wNeed 20 (wStore 0 (pFan 1) insD₂) 1 ∷ [])
  ∷ rowS "NUM pFan2 wNeed" (wNeed 20 (wStore 0 (pFan 2) insD₂) 1 ∷ [])
  ∷ rowS "NUM pFan3 S"     (mS 0 (pFan 3) insD₂ ∷ [])
  ∷ rowS "DIG pFan3 W+"    (dig (wStore 0 (pFan 3) insD₂) ∷ [])
  ∷ rowS "DIG iterFold 20 2 1" (dig (iterFold 20 2 1) ∷ [])
  -- deliveries × nesting
  ∷ rowS "MUL pFan2 1 id0" (nrow 0 (pFan2 1) insD₂)
  ∷ rowS "MUL pFan2 2 id0" (nrow 0 (pFan2 2) insD₂)
  ∷ rowS "MUL pFan2 3 id0" (nrow 0 (pFan2 3) insD₂)
  -- the contrast: a multiplicative step climbs no stories at all
  ∷ rowS "TUP pTupM8 id0" (nrow 0 (pTupM 8) insD₂)
  ∷ rowS "TUP pTupM8 W+"  (wStore 0 (pTupM 8) insD₂ ∷ [])
  -- §9's GATE ROWS: R ; D ; S, on the 19 Instant-Height rows and on
  -- every family above, so the ruled count can be checked at the
  -- MEASURED registry rather than at capsAt's
  ∷ rowS "G progDT 0" (grow 0 progDT insD₂)
  ∷ rowS "G progDT 1" (grow 1 progDT insD₂)
  ∷ rowS "G progDT 2" (grow 2 progDT insD₂)
  ∷ rowS "G progW 0"  (grow 0 progW  insD₂)
  ∷ rowS "G pF1 0"    (grow 0 pF1    insG)
  ∷ rowS "G pF1 1"    (grow 1 pF1    insG)
  ∷ rowS "G pF1 2"    (grow 2 pF1    insG)
  ∷ rowS "G pF2 0"    (grow 0 pF2    insG²)
  ∷ rowS "G pmu2 0"   (grow 0 pμ2    ins₀)
  ∷ rowS "G pmu2 1"   (grow 1 pμ2    ins₀)
  ∷ rowS "G pmu2 2"   (grow 2 pμ2    ins₀)
  ∷ rowS "G pmu2 3"   (grow 3 pμ2    ins₀)
  ∷ rowS "G pmuD 0"   (grow 0 pμD    ins₀)
  ∷ rowS "G pmuD 1"   (grow 1 pμD    ins₀)
  ∷ rowS "G pL2 0"    (grow 0 (pL² 2) insG²)
  ∷ rowS "G pL2 1"    (grow 1 (pL² 2) insG²)
  ∷ rowS "G pL3 0"    (grow 0 (pL³ 0) insG³)
  ∷ rowS "G pL3 1"    (grow 1 (pL³ 0) insG³)
  ∷ rowS "G progD 0"  (grow 0 progD  ins₀)
  ∷ rowS "G pFan1 0"  (grow 0 (pFan 1) insD₂)
  ∷ rowS "G pFan2 0"  (grow 0 (pFan 2) insD₂)
  ∷ rowS "G pFan3 0"  (grow 0 (pFan 3) insD₂)
  ∷ rowS "G pFan4 0"  (grow 0 (pFan 4) insD₂)
  ∷ rowS "G pFan5 0"  (grow 0 (pFan 5) insD₂)
  ∷ rowS "G pFan3 1"  (grow 1 (pFan 3) insD₂)
  ∷ rowS "G pFan2-1 0" (grow 0 (pFan2 1) insD₂)
  ∷ rowS "G pFan2-2 0" (grow 0 (pFan2 2) insD₂)
  ∷ rowS "G pFan2-3 0" (grow 0 (pFan2 3) insD₂)
  ∷ rowS "G pmuD2M 0" (grow 0 pμD2M ins₀)
  ∷ rowS "G pmuD2M 1" (grow 1 pμD2M ins₀)
  ∷ rowS "G pmuD2M 2" (grow 2 pμD2M ins₀)
  ∷ rowS "G pmuD2M 3" (grow 3 pμD2M ins₀)
  ∷ rowS "G pTupM8 0" (grow 0 (pTupM 8) insD₂)
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
