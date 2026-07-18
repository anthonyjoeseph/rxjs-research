-- A JSON-subset parser over ℕ codepoints — everything our compact
-- JSON.stringify output needs: objects, arrays, unescaped ASCII strings,
-- non-negative integers, true/false, null. Fuel-threaded for termination.
module CLI.JSON where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

data JSON : Set where
  jnum  : ℕ → JSON
  jstr  : List ℕ → JSON              -- string content, as codepoints
  jbool : Bool → JSON
  jnull : JSON
  jarr  : List JSON → JSON
  jobj  : List (List ℕ × JSON) → JSON

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
  isWs c = (c ≡ᵇ 32) ∨ (c ≡ᵇ 9) ∨ (c ≡ᵇ 10) ∨ (c ≡ᵇ 13)

  isDigit : ℕ → Bool
  isDigit c = (48 ≤ᵇ c) ∧ (c ≤ᵇ 57)

  skipWs : List ℕ → List ℕ
  skipWs []       = []
  skipWs (c ∷ cs) = if isWs c then skipWs cs else (c ∷ cs)

  infixl 1 _>>=?_
  _>>=?_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>=? _ = nothing
  just x  >>=? f = f x

  expect : List ℕ → List ℕ → Maybe (List ℕ)
  expect []       cs       = just cs
  expect (_ ∷ _)  []       = nothing
  expect (e ∷ es) (c ∷ cs) = if e ≡ᵇ c then expect es cs else nothing

  strBody : List ℕ → Maybe (List ℕ × List ℕ)
  strBody []       = nothing
  strBody (c ∷ cs) =
    if c ≡ᵇ cQuote
    then just ([] , cs)
    else (strBody cs >>=? λ p → just (c ∷ proj₁ p , proj₂ p))

  digits : ℕ → List ℕ → ℕ × List ℕ
  digits acc []       = acc , []
  digits acc (c ∷ cs) =
    if isDigit c then digits ((acc * 10) + (c ∸ 48)) cs else (acc , c ∷ cs)

  headOr : ℕ → List ℕ → ℕ
  headOr d []      = d
  headOr d (x ∷ _) = x

  tailOf : List ℕ → List ℕ
  tailOf []       = []
  tailOf (_ ∷ xs) = xs

parseValue : ℕ → List ℕ → Maybe (JSON × List ℕ)
parseArrElems : ℕ → List ℕ → Maybe (List JSON × List ℕ)
parseObjMembers : ℕ → List ℕ → Maybe (List (List ℕ × JSON) × List ℕ)

parseValue zero      _   = nothing
parseValue (suc fuel) cs0 with skipWs cs0
... | []       = nothing
... | (c ∷ cs) =
  if c ≡ᵇ cLBrace then
    (parseObjMembers fuel cs >>=? λ p → just (jobj (proj₁ p) , proj₂ p))
  else if c ≡ᵇ cLBrack then
    (parseArrElems fuel cs >>=? λ p → just (jarr (proj₁ p) , proj₂ p))
  else if c ≡ᵇ cQuote then
    (strBody cs >>=? λ p → just (jstr (proj₁ p) , proj₂ p))
  else if c ≡ᵇ 116 then     -- 't'rue
    (expect (114 ∷ 117 ∷ 101 ∷ []) cs >>=? λ r → just (jbool true , r))
  else if c ≡ᵇ 102 then     -- 'f'alse
    (expect (97 ∷ 108 ∷ 115 ∷ 101 ∷ []) cs >>=? λ r → just (jbool false , r))
  else if c ≡ᵇ 110 then     -- 'n'ull
    (expect (117 ∷ 108 ∷ 108 ∷ []) cs >>=? λ r → just (jnull , r))
  else if isDigit c then
    (let p = digits 0 (c ∷ cs) in just (jnum (proj₁ p) , proj₂ p))
  else nothing

parseArrElems zero      _  = nothing
parseArrElems (suc fuel) cs with skipWs cs
... | []          = nothing
... | (c ∷ cs′) =
  if c ≡ᵇ cRBrack then just ([] , cs′)
  else parseValue fuel (c ∷ cs′) >>=? λ p →
       (λ rest → if headOr 0 rest ≡ᵇ cComma
                 then (parseArrElems fuel (tailOf rest) >>=? λ q →
                       just (proj₁ p ∷ proj₁ q , proj₂ q))
                 else if headOr 0 rest ≡ᵇ cRBrack
                 then just (proj₁ p ∷ [] , tailOf rest)
                 else nothing) (skipWs (proj₂ p))

parseObjMembers zero      _  = nothing
parseObjMembers (suc fuel) cs with skipWs cs
... | []          = nothing
... | (c ∷ cs′) =
  if c ≡ᵇ cRBrace then just ([] , cs′)
  else if c ≡ᵇ cQuote then
    (strBody cs′ >>=? λ key →
     (λ afterKey → if headOr 0 afterKey ≡ᵇ cColon
       then (parseValue fuel (tailOf afterKey) >>=? λ v →
             (λ rest → if headOr 0 rest ≡ᵇ cComma
                       then (parseObjMembers fuel (tailOf rest) >>=? λ q →
                             just ((proj₁ key , proj₁ v) ∷ proj₁ q , proj₂ q))
                       else if headOr 0 rest ≡ᵇ cRBrace
                       then just ((proj₁ key , proj₁ v) ∷ [] , tailOf rest)
                       else nothing) (skipWs (proj₂ v)))
       else nothing) (skipWs (proj₂ key)))
  else nothing

parseJSON : List ℕ → Maybe JSON
parseJSON cs = parseValue (suc (length cs)) cs >>=? λ p → just (proj₁ p)
