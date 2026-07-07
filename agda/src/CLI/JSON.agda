-- A JSON-subset parser over ℕ codepoints (all our compact JSON.stringify
-- output needs): objects, arrays, unescaped ASCII strings, non-negative
-- integers, true/false. Fuel-threaded for termination.
module CLI.JSON where

open import Prelude

data JSON : Set where
  jnum  : ℕ → JSON
  jstr  : List ℕ → JSON              -- string content, as codepoints
  jbool : Bool → JSON
  jarr  : List JSON → JSON
  jobj  : List (List ℕ × JSON) → JSON

------------------------------------------------------------------------
-- character codes and classifiers

private
  cQuote cLBrace cRBrace cLBrack cRBrack cColon cComma : ℕ
  cQuote  = 34   -- "
  cLBrace = 123  -- {
  cRBrace = 125  -- }
  cLBrack = 91   -- [
  cRBrack = 93   -- ]
  cColon  = 58   -- :
  cComma  = 44   -- ,

  isWs : ℕ → Bool
  isWs c = eqℕ c 32 ∨ eqℕ c 9 ∨ eqℕ c 10 ∨ eqℕ c 13

  isDigit : ℕ → Bool
  isDigit c = leqℕ 48 c ∧ leqℕ c 57

  skipWs : List ℕ → List ℕ
  skipWs []       = []
  skipWs (c ∷ cs) = if isWs c then skipWs cs else (c ∷ cs)

  _>>=?_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>=? _ = nothing
  just x  >>=? f = f x

  -- consume an exact codepoint prefix
  expect : List ℕ → List ℕ → Maybe (List ℕ)
  expect []       cs       = just cs
  expect (_ ∷ _)  []       = nothing
  expect (e ∷ es) (c ∷ cs) = if eqℕ e c then expect es cs else nothing

  -- string body up to the closing quote (no escapes)
  strBody : List ℕ → Maybe (List ℕ × List ℕ)
  strBody []       = nothing
  strBody (c ∷ cs) =
    if eqℕ c cQuote
    then just ([] , cs)
    else (strBody cs >>=? λ p → just (c ∷ fst p , snd p))

  -- digits into a ℕ
  digits : ℕ → List ℕ → ℕ × List ℕ
  digits acc []       = acc , []
  digits acc (c ∷ cs) =
    if isDigit c then digits ((acc * 10) + (c ∸ 48)) cs else (acc , c ∷ cs)

------------------------------------------------------------------------
-- the recursive-descent core, structural on `fuel`

parseValue : ℕ → List ℕ → Maybe (JSON × List ℕ)
parseArrElems : ℕ → List ℕ → Maybe (List JSON × List ℕ)
parseObjMembers : ℕ → List ℕ → Maybe (List (List ℕ × JSON) × List ℕ)

parseValue zero      _   = nothing
parseValue (suc fuel) cs0 with skipWs cs0
... | []       = nothing
... | (c ∷ cs) =
  if eqℕ c cLBrace then
    (parseObjMembers fuel cs >>=? λ p → just (jobj (fst p) , snd p))
  else if eqℕ c cLBrack then
    (parseArrElems fuel cs >>=? λ p → just (jarr (fst p) , snd p))
  else if eqℕ c cQuote then
    (strBody cs >>=? λ p → just (jstr (fst p) , snd p))
  else if eqℕ c 116 then     -- 't' rue
    (expect (114 ∷ 117 ∷ 101 ∷ []) cs >>=? λ r → just (jbool true , r))
  else if eqℕ c 102 then     -- 'f' alse
    (expect (97 ∷ 108 ∷ 115 ∷ 101 ∷ []) cs >>=? λ r → just (jbool false , r))
  else if isDigit c then
    (let p = digits 0 (c ∷ cs) in just (jnum (fst p) , snd p))
  else nothing

parseArrElems zero      _  = nothing
parseArrElems (suc fuel) cs with skipWs cs
... | []          = nothing
... | (c ∷ cs′) =
  if eqℕ c cRBrack then just ([] , cs′)            -- empty array
  else parseValue fuel (c ∷ cs′) >>=? λ p →
       (λ rest → if eqℕ (headOr 0 rest) cComma
                 then (parseArrElems fuel (tailOf rest) >>=? λ q →
                       just (fst p ∷ fst q , snd q))
                 else if eqℕ (headOr 0 rest) cRBrack
                 then just (fst p ∷ [] , tailOf rest)
                 else nothing) (skipWs (snd p))
  where
    headOr : ℕ → List ℕ → ℕ
    headOr d []      = d
    headOr d (x ∷ _) = x
    tailOf : List ℕ → List ℕ
    tailOf []       = []
    tailOf (_ ∷ xs) = xs

parseObjMembers zero      _  = nothing
parseObjMembers (suc fuel) cs with skipWs cs
... | []          = nothing
... | (c ∷ cs′) =
  if eqℕ c cRBrace then just ([] , cs′)            -- empty object
  else if eqℕ c cQuote then
    (strBody cs′ >>=? λ key →                       -- "key"
     (λ afterKey → if eqℕ (headOr 0 afterKey) cColon
       then (parseValue fuel (tailOf afterKey) >>=? λ v →
             (λ rest → if eqℕ (headOr 0 rest) cComma
                       then (parseObjMembers fuel (tailOf rest) >>=? λ q →
                             just ((fst key , fst v) ∷ fst q , snd q))
                       else if eqℕ (headOr 0 rest) cRBrace
                       then just ((fst key , fst v) ∷ [] , tailOf rest)
                       else nothing) (skipWs (snd v)))
       else nothing) (skipWs (snd key)))
  else nothing
  where
    headOr : ℕ → List ℕ → ℕ
    headOr d []      = d
    headOr d (x ∷ _) = x
    tailOf : List ℕ → List ℕ
    tailOf []       = []
    tailOf (_ ∷ xs) = xs

-- parse a whole value from codepoints (fuel = length is a safe upper bound
-- on the number of descents)
parseJSON : List ℕ → Maybe JSON
parseJSON cs = parseValue (suc (length cs)) cs >>=? λ p → just (fst p)
