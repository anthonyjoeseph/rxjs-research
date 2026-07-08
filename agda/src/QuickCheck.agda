-- An all-Agda QuickCheck: generate random SHARE-FREE programs (which are
-- automatically Canonical) over 3 subjects with a random driver, and check
-- impl-batchSimultaneous ≡ spec-batchSimultaneous. A fast in-Agda dev loop
-- for sorting out the implementation — no TypeScript round-trip.
--
--   agda --compile src/QuickCheck.agda   (then: echo <seed> | ./QuickCheck)
module QuickCheck where

open import Prelude
open import Shared-Types
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous
open import Spec.Batch-Simultaneous
open import CLI.IO
open import CLI.Serialize using (encodeBatches ; listEqℕ)

-- raw protocol emits of the compiled program (for diagnosing weights)
private
  shEv : Ev Val → String
  shEv (init p)  = appendStr "i" (natToStr p)
  shEv (value v) = appendStr "v" (natToStr v)
  shEv (close p) = appendStr "c" (natToStr p)
  shEv fin       = "F"
  shEv (wt k)    = appendStr "w" (natToStr k)
  shEvs : List (Ev Val) → String
  shEvs []       = ""
  shEvs (e ∷ es) = appendStr (shEv e) (appendStr " " (shEvs es))
  shEmit : Emit Val → String
  shEmit e = concatStr ("(p" ∷ natToStr (fst e) ∷ ": " ∷ shEvs (snd e) ∷ ")" ∷ [])
  shEmits : List (Emit Val) → String
  shEmits []       = ""
  shEmits (e ∷ es) = appendStr (shEmit e) (appendStr "\n      " (shEmits es))

rawEmits : {n : ℕ} → Emissions n → Exp n → String
rawEmits em e = shEmits (subscribeRx (compile e) em)

------------------------------------------------------------------------
-- randomness (FFI: a pure LCG over Integer, so no unary-ℕ blowup)

{-# FOREIGN GHC
randFoldH :: Integer -> Integer -> (Integer -> a -> a) -> a -> a
randFoldH seed count f z = go seed count where
  go _ 0 = z
  go s n = let s' = (s * 6364136223846793005 + 1442695040888963407)
                      `mod` 18446744073709551616
           in f (s' `mod` 100003) (go s' (n - 1))
#-}
postulate randFold : {A : Set} → ℕ → ℕ → (ℕ → A → A) → A → A
{-# COMPILE GHC randFold = \_ -> randFoldH #-}

postulate natMod : ℕ → ℕ → ℕ
{-# COMPILE GHC natMod = \a b -> if b == 0 then 0 else a `mod` b #-}

randList : ℕ → ℕ → List ℕ
randList seed count = randFold seed count _∷_ []

------------------------------------------------------------------------
-- a tiny generator monad: consume randoms from a List ℕ

Gen : Set → Set
Gen A = List ℕ → A × List ℕ

pureG : {A : Set} → A → Gen A
pureG x rs = x , rs

_>>=G_ : {A B : Set} → Gen A → (A → Gen B) → Gen B
(g >>=G f) rs with g rs
... | (a , rs′) = f a rs′
infixl 1 _>>=G_

-- one random in [0,bound)
genB : ℕ → Gen ℕ
genB bound []       = 0 , []
genB bound (r ∷ rs) = natMod r bound , rs

genFin3 : Gen (Fin 3)
genFin3 = genB 3 >>=G λ c →
  pureG (if eqℕ c 0 then fzero else if eqℕ c 1 then fsuc fzero else fsuc (fsuc fzero))

genVals : Gen (List Val)
genVals = genB 4 >>=G λ len → go len
  where
    go : ℕ → Gen (List Val)
    go zero    = pureG []
    go (suc n) = genB 10 >>=G λ v → go n >>=G λ vs → pureG (v ∷ vs)

genFn : Gen (Val → Val)
genFn = genB 2 >>=G λ op → genB 4 >>=G λ k →
  pureG (if eqℕ op 0 then (λ v → v + k) else (λ v → v * k))

------------------------------------------------------------------------
-- the program generator (share-free ⇒ Canonical), structural on fuel

genExp  : ℕ → Gen (Exp 3)
genExpS : ℕ → Gen (ExpS 3)
genExpN : ℕ → ℕ → Gen (List (Exp 3))
genTmpl : ℕ → Gen (Val → Exp 3)

genLeaf : Gen (Exp 3)
genLeaf = genB 3 >>=G λ c →
  if eqℕ c 0 then (genFin3 >>=G λ i → pureG (srcE i))
  else if eqℕ c 1 then pureG emptyE
  else (genVals >>=G λ vs → pureG (ofE vs))

genExp zero      = genLeaf
genExp (suc d) = genB 12 >>=G λ c →
  if leqℕ c 2 then genLeaf
  else if eqℕ c 3 then (genFn >>=G λ f → genExp d >>=G λ e → pureG (mapE f e))
  else if eqℕ c 4 then (genB 4 >>=G λ k → genExp d >>=G λ e → pureG (takeE k e))
  else if eqℕ c 5 then
    (genFn >>=G λ f → genExp d >>=G λ e → pureG (scanE (λ acc v → f acc + v) 0 e))
  else if eqℕ c 6 then (genExpS d >>=G λ s → pureG (mergeAllE s))
  else if eqℕ c 7 then (genExpS d >>=G λ s → pureG (concatAllE s))
  else if eqℕ c 8 then (genExpS d >>=G λ s → pureG (switchAllE s))
  else if eqℕ c 9 then (genExpS d >>=G λ s → pureG (exhaustAllE s))
  else genLeaf

genExpN zero    d = pureG []
genExpN (suc n) d = genExp d >>=G λ e → genExpN n d >>=G λ es → pureG (e ∷ es)

genExpS d = genB 2 >>=G λ c →
  if eqℕ c 0 then (genB 2 >>=G λ extra → genExpN (suc (suc extra)) d >>=G λ es → pureG (ofS es))
  else (genTmpl d >>=G λ t → genExp d >>=G λ e → pureG (mapS t e))

genTmpl d = genB 4 >>=G λ c →
  if eqℕ c 0 then (genVals >>=G λ extra → pureG (λ v → ofE (v ∷ extra)))
  else if eqℕ c 1 then (genVals >>=G λ vs → pureG (λ _ → ofE vs))
  else if eqℕ c 2 then (genFin3 >>=G λ i → pureG (λ _ → srcE i))
  else (genFn >>=G λ f → pureG (λ v → mapE f (ofE (v ∷ []))))

genAsyncs : Gen (List (Fin 3 × Val))
genAsyncs = genB 6 >>=G λ len → go len
  where
    go : ℕ → Gen (List (Fin 3 × Val))
    go zero    = pureG []
    go (suc n) = genFin3 >>=G λ i → genB 10 >>=G λ v → go n >>=G λ rest → pureG ((i , v) ∷ rest)

genEm : Gen (Emissions 3)
genEm = genAsyncs >>=G λ a → pureG (emissions (pureV []) a)

------------------------------------------------------------------------
-- showing a failing case (functions shown as placeholders; the shape +
-- driver + both outputs are enough to localize, then reproduce)

showExp  : Exp 3 → String
showExpL : List (Exp 3) → String
showExpS : ExpS 3 → String

showExp (srcE i)       = appendStr "src" (natToStr (toℕ i))
showExp emptyE         = "empty"
showExp (ofE vs)       = appendStr "of" (encodeBatches (vs ∷ []))
showExp (shareE _ i)   = appendStr "share" (natToStr i)
showExp (letShareE s b) = appendStr "letShare(" (appendStr (showExp s) (appendStr "," (appendStr (showExp b) ")")))
showExp (mapE _ e)     = appendStr "map(" (appendStr (showExp e) ")")
showExp (takeE k e)    = appendStr "take" (appendStr (natToStr k) (appendStr "(" (appendStr (showExp e) ")")))
showExp (scanE _ _ e)  = appendStr "scan(" (appendStr (showExp e) ")")
showExp (mergeAllE s)  = appendStr "mergeAll(" (appendStr (showExpS s) ")")
showExp (concatAllE s) = appendStr "concatAll(" (appendStr (showExpS s) ")")
showExp (switchAllE s) = appendStr "switchAll(" (appendStr (showExpS s) ")")
showExp (exhaustAllE s) = appendStr "exhaustAll(" (appendStr (showExpS s) ")")

showExpL []       = ""
showExpL (e ∷ []) = showExp e
showExpL (e ∷ es) = appendStr (showExp e) (appendStr "," (showExpL es))

showExpS (ofS es)  = appendStr "ofS[" (appendStr (showExpL es) "]")
showExpS (mapS t e) = concatStr ("mapS(λv→{0↦" ∷ showExp (t 0) ∷ "|1↦" ∷ showExp (t 1) ∷ "|7↦" ∷ showExp (t 7) ∷ "}," ∷ showExp e ∷ ")" ∷ [])

showAsync : Fin 3 × Val → String
showAsync (i , v) = appendStr (natToStr (toℕ i)) (appendStr ":" (natToStr v))

showAsyncs : List (Fin 3 × Val) → String
showAsyncs []       = ""
showAsyncs (a ∷ []) = showAsync a
showAsyncs (a ∷ as) = appendStr (showAsync a) (appendStr "," (showAsyncs as))

------------------------------------------------------------------------
-- compare + report

eqBatches : List (List Val) → List (List Val) → Bool
eqBatches []       []       = true
eqBatches (x ∷ xs) (y ∷ ys) = listEqℕ x y ∧ eqBatches xs ys
eqBatches _        _        = false

report : Emissions 3 → Exp 3 → List (List Val) → List (List Val) → String
report em e impl spec = concatStr
  ( "  FAIL " ∷ showExp e
  ∷ "\n    driver = " ∷ showAsyncs (asyncs em)
  ∷ "\n    impl   = " ∷ encodeBatches impl
  ∷ "\n    spec   = " ∷ encodeBatches spec
  ∷ "\n    raw    = " ∷ rawEmits em e ∷ "\n" ∷ [])

-- one case: nothing if impl ≡ spec, else the report
oneCase : Gen (Maybe String)
oneCase = genEm >>=G λ em → genExp 4 >>=G λ e →
  let impl = impl-batchSimultaneous em e
      spec = spec-batchSimultaneous em e
  in pureG (if eqBatches impl spec then nothing else just (report em e impl spec))

-- run k cases; accumulate (#failures , first failure report)
runN : ℕ → Gen (ℕ × Maybe String)
runN zero    = pureG (0 , nothing)
runN (suc k) = oneCase >>=G λ r → runN k >>=G λ acc →
  pureG ( maybe′ (fst acc) (λ _ → suc (fst acc)) r
        , maybe′ (snd acc) just r )

------------------------------------------------------------------------

parseNat : List ℕ → ℕ
parseNat = go 0
  where
    go : ℕ → List ℕ → ℕ
    go acc []       = acc
    go acc (c ∷ cs) =
      if leqℕ 48 c ∧ leqℕ c 57 then go ((acc * 10) + (c ∸ 48)) cs else acc

numRuns : ℕ
numRuns = 500

main : IO Unit
main = getContents >>= λ s →
  let seed = parseNat (toCodes s)
      res  = fst (runN numRuns (randList seed 2000000))
  in putStr (concatStr
       ( "seed " ∷ natToStr seed ∷ " — ran " ∷ natToStr numRuns
       ∷ " cases, " ∷ natToStr (fst res) ∷ " failures\n"
       ∷ maybe′ "  (all agree)\n" (λ r → r) (snd res) ∷ [])) >>= λ _ → returnIO unit
