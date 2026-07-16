-- Decode a JSON case { slots, exp, driver } into an Agda Emissions × Exp,
-- run impl-batchSimultaneous, and encode the resulting batches back to JSON.
-- The JSON Exp mirrors the Agda grammar one-for-one (src/share split); the
-- only rebuilding is applyFn / applyTemplate (the defunctionalized functions).
module CLI.Serialize where

open import Prelude
open import Shared-Types
open import Implementation.Batch-Simultaneous
open import CLI.IO
open import CLI.JSON

------------------------------------------------------------------------
-- Maybe plumbing + JSON accessors

infixl 1 _>>=?_
_>>=?_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>=? _ = nothing
just x  >>=? f = f x

mapMaybe : {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
mapMaybe f []       = just []
mapMaybe f (x ∷ xs) = f x >>=? λ y → mapMaybe f xs >>=? λ ys → just (y ∷ ys)

listEqℕ : List ℕ → List ℕ → Bool
listEqℕ []       []       = true
listEqℕ (x ∷ xs) (y ∷ ys) = eqℕ x y ∧ listEqℕ xs ys
listEqℕ _        _        = false

-- compare a parsed key/tag (codepoints) to a string literal
_is_ : List ℕ → String → Bool
cs is s = listEqℕ cs (toCodes s)

getField : String → JSON → Maybe JSON
getField name (jobj ms) = find ms
  where find : List (List ℕ × JSON) → Maybe JSON
        find []             = nothing
        find ((k , v) ∷ rest) = if k is name then just v else find rest
getField _ _ = nothing

asNum : JSON → Maybe ℕ
asNum (jnum n) = just n
asNum _        = nothing

asStr : JSON → Maybe (List ℕ)
asStr (jstr s) = just s
asStr _        = nothing

asArr : JSON → Maybe (List JSON)
asArr (jarr xs) = just xs
asArr _         = nothing

asBool : JSON → Maybe Bool
asBool (jbool b) = just b
asBool _         = nothing

natToFin : (n : ℕ) → ℕ → Maybe (Fin n)
natToFin zero    _       = nothing
natToFin (suc n) zero    = just fzero
natToFin (suc n) (suc s) = natToFin n s >>=? λ i → just (fsuc i)

------------------------------------------------------------------------
-- decoders (mirroring the TS applyFn / applyTemplate)

decodeFn : JSON → Maybe (Val → Val)
decodeFn j =
  getField "op" j >>=? asStr >>=? λ op →
  getField "k"  j >>=? asNum >>=? λ k →
  if op is "add" then just (λ v → v + k)
  else if op is "mul" then just (λ v → v * k)
  else nothing

decodeExp : (n : ℕ) → ℕ → JSON → Maybe (Exp n)
decodeExpS : (n : ℕ) → ℕ → JSON → Maybe (ExpS n)
decodeTmpl : (n : ℕ) → ℕ → JSON → Maybe (Val → Exp n)

decodeExp n zero      _ = nothing
decodeExp n (suc fuel) j =
  getField "k" j >>=? asStr >>=? λ tag →
  if tag is "src" then
    (getField "slot" j >>=? asNum >>=? λ s → natToFin n s >>=? λ i → just (srcE i))
  else if tag is "empty" then just emptyE
  else if tag is "of" then
    (getField "vs" j >>=? asArr >>=? λ xs → mapMaybe asNum xs >>=? λ vs → just (ofE vs))
  else if tag is "share" then
    (getField "first" j >>=? asBool >>=? λ f →
     getField "slot" j >>=? asNum >>=? λ s → just (shareE f s))
  else if tag is "letShare" then
    (getField "src" j >>=? decodeExp n fuel >>=? λ s →
     getField "body" j >>=? decodeExp n fuel >>=? λ b → just (letShareE s b))
  else if tag is "map" then
    (getField "f" j >>=? decodeFn >>=? λ f →
     getField "e" j >>=? decodeExp n fuel >>=? λ e → just (mapE f e))
  else if tag is "take" then
    (getField "n" j >>=? asNum >>=? λ k →
     getField "e" j >>=? decodeExp n fuel >>=? λ e → just (takeE k e))
  else if tag is "scan" then
    (getField "f" j >>=? decodeFn >>=? λ f →
     getField "e" j >>=? decodeExp n fuel >>=? λ e →
     just (scanE (λ acc v → f acc + v) 0 e))
  else if tag is "mergeAll" then
    (getField "s" j >>=? decodeExpS n fuel >>=? λ s → just (mergeAllE s))
  else if tag is "concatAll" then
    (getField "s" j >>=? decodeExpS n fuel >>=? λ s → just (concatAllE s))
  else if tag is "switchAll" then
    (getField "s" j >>=? decodeExpS n fuel >>=? λ s → just (switchAllE s))
  else if tag is "exhaustAll" then
    (getField "s" j >>=? decodeExpS n fuel >>=? λ s → just (exhaustAllE s))
  else nothing

decodeExpS n zero      _ = nothing
decodeExpS n (suc fuel) j =
  getField "k" j >>=? asStr >>=? λ tag →
  if tag is "ofS" then
    (getField "es" j >>=? asArr >>=? λ xs →
     mapMaybe (decodeExp n fuel) xs >>=? λ es → just (ofS es))
  else if tag is "mapS" then
    (getField "e" j >>=? decodeExp n fuel >>=? λ e →
     getField "tmpl" j >>=? decodeTmpl n fuel >>=? λ t → just (mapS t e))
  else nothing

decodeTmpl n zero      _ = nothing
decodeTmpl n (suc fuel) j =
  getField "k" j >>=? asStr >>=? λ tag →
  if tag is "ofv" then
    (getField "extra" j >>=? asArr >>=? λ xs → mapMaybe asNum xs >>=? λ extra →
     just (λ v → ofE (v ∷ extra)))
  else if tag is "constOf" then
    (getField "vs" j >>=? asArr >>=? λ xs → mapMaybe asNum xs >>=? λ vs →
     just (λ _ → ofE vs))
  else if tag is "refI" then
    (getField "slot" j >>=? asNum >>=? λ s → natToFin n s >>=? λ i →
     just (λ _ → srcE i))
  else if tag is "mapOfv" then
    (getField "f" j >>=? decodeFn >>=? λ f →
     just (λ v → mapE f (ofE (v ∷ []))))
  else nothing

------------------------------------------------------------------------
-- driver → asyncs; run; encode

decodeDriver : (n : ℕ) → List JSON → Maybe (List (Fin n × Val))
decodeDriver n []       = just []
decodeDriver n (j ∷ js) =
  getField "slot"  j >>=? asNum >>=? λ s → natToFin n s >>=? λ i →
  getField "value" j >>=? asNum >>=? λ v →
  decodeDriver n js >>=? λ rest → just ((i , v) ∷ rest)

-- Emissions with no subscribe-time flush (subjects only fire via .next),
-- so syncs are all-empty and asyncs are the driver.
runCase : JSON → Maybe (List (List Val))
runCase j =
  getField "slots" j >>=? asNum >>=? λ n →
  getField "exp" j >>=? decodeExp n 1000 >>=? λ e →
  getField "driver" j >>=? asArr >>=? λ ds → decodeDriver n ds >>=? λ asy →
  just (impl-batchSimultaneous (emissions (pureV []) asy) e)

------------------------------------------------------------------------
-- encode List (List ℕ) as a compact JSON array of arrays

private
  commaJoin : List String → String
  commaJoin []           = ""
  commaJoin (s ∷ [])     = s
  commaJoin (s ∷ s′ ∷ ss) = appendStr s (appendStr "," (commaJoin (s′ ∷ ss)))

  encArr : List String → String
  encArr ss = appendStr "[" (appendStr (commaJoin ss) "]")

encodeBatches : List (List ℕ) → String
encodeBatches bs = encArr (map (λ b → encArr (map natToStr b)) bs)

-- one input line → one output line
processLine : List ℕ → String
processLine cs =
  maybe′ "\"PARSE-ERROR\""
         (λ j → maybe′ "\"RUN-ERROR\"" encodeBatches (runCase j))
         (parseJSON cs)
