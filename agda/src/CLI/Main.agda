-- The batch CLI: read NDJSON from stdin (one serialized TestCase per
-- line, in order), process each, print one JSON result line in the same
-- order.
--
-- Pipeline status: stdin → JSON parse (CLI.JSON) → [decode → evaluate] →
-- encode (CLI.Encode) → stdout. The parse and encode halves are wired
-- and exercised here. The middle — decode (JSON → intrinsically-typed
-- Closed) and evaluate — is gated on discharging the Agda evaluator's
-- runtime postulates (freshId, evalTm, applyFn, unfoldμ, _≟ᵗ_, and a
-- concrete PrimOp); MAlonzo compiles a postulate to a runtime error, so
-- `evaluate` cannot run until they are defined. Until then a parseable
-- case emits an empty stream `[]`, an unparseable one `null`.
module CLI.Main where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.String using (String; toList; fromChar; _++_)
open import Data.Bool using (if_then_else_)
open import Data.Vec using ([])

open import Rx.Exp using (natᵗ)
open import CLI.IO
open import CLI.JSON using (parseJSON)
open import CLI.Encode using (encodeStream)

toCodes : List Char → List ℕ
toCodes = map toℕ

-- one input line → one output line
process : List Char → String
process line =
  maybe (λ _ → encodeStream {Γ = []} natᵗ []) "null" (parseJSON (toCodes line))

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
