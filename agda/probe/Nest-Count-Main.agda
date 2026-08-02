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
open import Charge-Probe using (ins₀; insD₂; progDT; progW; pF1; pF2)
open import Instant-Height-Probe using (pμD; wStore; wNeed)
open import Mint-Loop-Shapes using (mS; insG; insG²)
open import Verify-Budget-Sufficient.Caps using (iterFold)
open import Nest-Count-Probe

showL : List ℕ → String
showL []       = ""
showL (x ∷ []) = show x
showL (x ∷ xs) = show x ++ " " ++ showL xs

rowS : String → List ℕ → String
rowS nm vs = nm ++ " = " ++ showL vs ++ "\n"

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
