-- The batch CLI: read NDJSON from stdin (one { slots, exp, driver } case
-- per line), run impl-batchSimultaneous on each, print one JSON result line.
module CLI.Main where

open import Prelude
open import CLI.IO
open import CLI.Serialize

splitLines : List ℕ → List (List ℕ)
splitLines []       = [] ∷ []
splitLines (c ∷ cs) =
  if eqℕ c 10 then [] ∷ splitLines cs else consHead c (splitLines cs)
  where
    consHead : ℕ → List (List ℕ) → List (List ℕ)
    consHead x []        = (x ∷ []) ∷ []
    consHead x (l ∷ ls)  = (x ∷ l) ∷ ls

dropEmpty : List (List ℕ) → List (List ℕ)
dropEmpty []              = []
dropEmpty ([]      ∷ ls)  = dropEmpty ls
dropEmpty ((c ∷ l) ∷ ls)  = (c ∷ l) ∷ dropEmpty ls

main : IO Unit
main = getContents >>= λ s →
       putStr (concatStr
         (map (λ l → appendStr (processLine l) "\n")
              (dropEmpty (splitLines (toCodes s)))))
