-- The batch CLI: read NDJSON from stdin (one serialized TestCase per
-- line, in order), process each, print one JSON result line in the same
-- order. (Decode/evaluate/encode land incrementally; this stage
-- validates the pipe by echoing `null` per case.)
module CLI.Main where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.String using (String; toList; fromList; fromChar)
open import Data.Bool using (if_then_else_)

open import CLI.IO

-- one input line → one output line
process : List Char → String
process _ = "null"

private
  nl : Char
  nl = '\n'

  -- split on '\n' into lines (as Char lists)
  splitLines : List Char → List (List Char)
  splitLines []       = [] ∷ []
  splitLines (c ∷ cs) =
    if toℕ c ≡ᵇ toℕ nl
    then [] ∷ splitLines cs
    else consHead c (splitLines cs)
    where
      consHead : Char → List (List Char) → List (List Char)
      consHead x []       = (x ∷ []) ∷ []
      consHead x (l ∷ ls) = (x ∷ l) ∷ ls

  nonEmpty : List (List Char) → List (List Char)
  nonEmpty []              = []
  nonEmpty ([]      ∷ ls)  = nonEmpty ls
  nonEmpty ((c ∷ l) ∷ ls)  = (c ∷ l) ∷ nonEmpty ls

  concatStr : List String → String
  concatStr []       = ""
  concatStr (s ∷ ss) = Data.String._++_ s (concatStr ss)

main : IO Unit
main =
  getContents >>= λ input →
  putStr
    (concatStr
      (map (λ line → Data.String._++_ (process line) (fromChar nl))
           (nonEmpty (splitLines (toList input)))))
