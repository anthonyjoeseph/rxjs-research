-- The batch CLI: read NDJSON from stdin (one serialized TestCase per
-- line, in order), and for each: parse (CLI.JSON) → decode to an
-- intrinsically-typed program (CLI.Decode) → evaluate → encode the stream
-- (CLI.Encode) → stdout, one JSON line per case in the same order. A parse
-- or decode failure prints `null`.
module CLI.Main where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.String using (String; toList; fromChar; _++_)
open import Data.Bool using (if_then_else_)

open import CLI.IO
open import CLI.JSON using (parseJSON)
open import CLI.Decode using (decodeCase)

toCodes : List Char → List ℕ
toCodes = map toℕ

-- one input line → one output line: parse, decode, evaluate, encode; a
-- parse or decode failure prints `null` (kept positional by execAgda).
-- NB: maybe′ (the NON-dependent eliminator), not maybe — the dependent
-- `maybe` makes Agda infer a motive over `decodeCase j`, which forces it
-- to normalize that call symbolically and unfold the whole elaborator
-- (minutes of typechecking). maybe′'s constant result type sidesteps it.
process : List Char → String
process line =
  maybe′ (λ j → maybe′ (λ s → s) "null" (decodeCase j)) "null"
         (parseJSON (toCodes line))

private
  nl : Char
  nl = '\n'

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
  concatStr (s ∷ ss) = s ++ concatStr ss

main : IO Unit
main =
  getContents >>= λ input →
  putStr
    (concatStr
      (map (λ line → process line ++ fromChar nl)
           (nonEmpty (splitLines (toList input)))))
