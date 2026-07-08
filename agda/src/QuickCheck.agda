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

-- map/scan value functions. Output is capped mod 100: these functions only
-- RELABEL values (impl and spec apply the SAME f), so the batch-structure
-- property under test is unaffected — but the cap keeps `scan (λ acc v → f acc
-- + v)` from compounding `v * k` GEOMETRICALLY into astronomically large unary
-- ℕ, whose natToStr/comparison would take ~value operations (the sole cause of
-- the depth-4 eval "blowups"; the algorithm itself is not slow).
genFn : Gen (Val → Val)
genFn = genB 2 >>=G λ op → genB 4 >>=G λ k →
  pureG (if eqℕ op 0 then (λ v → natMod (v + k) 100) else (λ v → natMod (v * k) 100))

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

-- Agda-source emitter: prints a paste-ready Unit-Test block for a failing
-- program. Hidden value-functions become idv / scz (structure-preserving);
-- mapS templates become a constant lambda `λ _ → t 0` (templates embed the
-- outer value only as leaf values, never in structure, so this is faithful to
-- the batch-boundary discrepancy — see CLAUDE.md "Bug cache").
aVals : List Val → String
aVals []       = "[]"
aVals (v ∷ vs) = concatStr (natToStr v ∷ " ∷ " ∷ aVals vs ∷ [])

aExp  : Exp 3 → String
aExpL : List (Exp 3) → String
aExpS : ExpS 3 → String

aExp (srcE i)        = appendStr "srcE s" (natToStr (toℕ i))
aExp emptyE          = "emptyE"
aExp (ofE vs)        = concatStr ("ofE (" ∷ aVals vs ∷ ")" ∷ [])
aExp (shareE _ _)    = "emptyE"      -- QC is share-free; placeholder
aExp (letShareE _ b) = aExp b
aExp (mapE _ e)      = concatStr ("mapE idv (" ∷ aExp e ∷ ")" ∷ [])
aExp (takeE k e)     = concatStr ("takeE " ∷ natToStr k ∷ " (" ∷ aExp e ∷ ")" ∷ [])
aExp (scanE _ _ e)   = concatStr ("scanE scz 0 (" ∷ aExp e ∷ ")" ∷ [])
aExp (mergeAllE s)   = concatStr ("mergeAllE (" ∷ aExpS s ∷ ")" ∷ [])
aExp (concatAllE s)  = concatStr ("concatAllE (" ∷ aExpS s ∷ ")" ∷ [])
aExp (switchAllE s)  = concatStr ("switchAllE (" ∷ aExpS s ∷ ")" ∷ [])
aExp (exhaustAllE s) = concatStr ("exhaustAllE (" ∷ aExpS s ∷ ")" ∷ [])

aExpL []       = "[]"
aExpL (e ∷ es) = concatStr (aExp e ∷ " ∷ " ∷ aExpL es ∷ [])

aExpS (ofS es)  = concatStr ("ofS (" ∷ aExpL es ∷ ")" ∷ [])
aExpS (mapS t e) = concatStr ("mapS (λ _ → " ∷ aExp (t 0) ∷ ") (" ∷ aExp e ∷ ")" ∷ [])

aAsyncs : List (Fin 3 × Val) → String
aAsyncs []            = "[]"
aAsyncs ((i , v) ∷ r) = concatStr ("(s" ∷ natToStr (toℕ i) ∷ " , " ∷ natToStr v ∷ ") ∷ " ∷ aAsyncs r ∷ [])

aBlock : Emissions 3 → Exp 3 → String
aBlock em e = concatStr
  ( "_ : Agree (drv {3} (" ∷ aAsyncs (asyncs em) ∷ "))\n          ("
  ∷ aExp e ∷ ")\n_ = refl\n" ∷ [])

report : Emissions 3 → Exp 3 → List (List Val) → List (List Val) → String
report em e impl spec = concatStr
  ( "  FAIL " ∷ showExp e
  ∷ "\n    driver = " ∷ showAsyncs (asyncs em)
  ∷ "\n    impl   = " ∷ encodeBatches impl
  ∷ "\n    spec   = " ∷ encodeBatches spec
  ∷ "\n    raw    = " ∷ rawEmits em e
  ∷ "\n-- <<<PASTE\n" ∷ aBlock em e ∷ "-- PASTE>>>\n" ∷ [])

-- one case at generator depth d: nothing if impl ≡ spec, else the report.
-- d bounds program NESTING — the only unbounded-in-practice size axis
-- (values/driver are already tightly capped). Lower d ⇒ strictly smaller
-- programs, so a depth-capped sweep is a hard SIZE cap, not a timeout.
oneCase : ℕ → Gen (Maybe String)
oneCase d = genEm >>=G λ em → genExp d >>=G λ e →
  let impl = impl-batchSimultaneous em e
      spec = spec-batchSimultaneous em e
  in pureG (if eqBatches impl spec then nothing else just (report em e impl spec))

-- run k cases; accumulate (#failures , first failure report)
runN : ℕ → ℕ → Gen (ℕ × Maybe String)
runN zero    d = pureG (0 , nothing)
runN (suc k) d = oneCase d >>=G λ r → runN k d >>=G λ acc →
  pureG ( maybe′ (fst acc) (λ _ → suc (fst acc)) r
        , maybe′ (snd acc) just r )

------------------------------------------------------------------------

isDigit : ℕ → Bool
isDigit c = leqℕ 48 c ∧ leqℕ c 57

parseNat : List ℕ → ℕ
parseNat = go 0
  where
    go : ℕ → List ℕ → ℕ
    go acc []       = acc
    go acc (c ∷ cs) = if isDigit c then go ((acc * 10) + (c ∸ 48)) cs else acc

-- stdin is "SEED" or "SEED DEPTH"; depth defaults to 4 when absent
dropNum dropSep : List ℕ → List ℕ
dropNum []       = []
dropNum (c ∷ cs) = if isDigit c then dropNum cs else (c ∷ cs)
dropSep []       = []
dropSep (c ∷ cs) = if isDigit c then (c ∷ cs) else dropSep cs

-- the tail after the first n numbers (each a digit-run + separators)
tailAfter : ℕ → List ℕ → List ℕ
tailAfter zero    cs = cs
tailAfter (suc n) cs = tailAfter n (dropSep (dropNum cs))

-- nth leading number, or the default when stdin has fewer
numAt : ℕ → ℕ → List ℕ → ℕ
numAt n def cs with dropSep (tailAfter n cs)
... | []         = def
... | ds@(_ ∷ _) = parseNat ds

-- AST node count (a cheap size metric that does NOT evaluate the program)
sizeE  : Exp 3 → ℕ
sizeEL : List (Exp 3) → ℕ
sizeES : ExpS 3 → ℕ
sizeE (srcE _)       = 1
sizeE emptyE         = 1
sizeE (ofE vs)       = 1 + length vs
sizeE (shareE _ _)   = 1
sizeE (letShareE a b) = (1 + sizeE a) + sizeE b
sizeE (mapE _ e)     = 1 + sizeE e
sizeE (takeE _ e)    = 1 + sizeE e
sizeE (scanE _ _ e)  = 1 + sizeE e
sizeE (mergeAllE s)  = 1 + sizeES s
sizeE (concatAllE s) = 1 + sizeES s
sizeE (switchAllE s) = 1 + sizeES s
sizeE (exhaustAllE s) = 1 + sizeES s
sizeEL []       = 0
sizeEL (e ∷ es) = sizeE e + sizeEL es
sizeES (ofS es)  = 1 + sizeEL es
sizeES (mapS t e) = (1 + sizeE (t 0)) + sizeE e

-- the nth generated (em, e), WITHOUT evaluating impl/spec (consumes the RNG
-- for the first n cases, returns the (n+1)-th's program)
nthCase : ℕ → ℕ → Gen (Emissions 3 × Exp 3)
nthCase zero    d = genEm >>=G λ em → genExp d >>=G λ e → pureG (em , e)
nthCase (suc n) d = genEm >>=G λ _ → genExp d >>=G λ _ → nthCase n d

main : IO Unit
main = getContents >>= λ s →
  let cs   = toCodes s
      seed = parseNat cs
      d    = numAt 1 4 cs          -- 2nd number: generator depth (default 4)
      runs = numAt 2 500 cs        -- 3rd number: #cases (default 500)
      dry  = numAt 3 0 cs          -- 4th number >0: DRY mode, print case `runs` w/o eval
  in if ltℕ 0 dry
     then (let ce   = fst (nthCase runs d (randList seed 2000000))
               em   = fst ce
               e    = snd ce
               -- dry=2: force BOTH; dry=3: force IMPL only; dry=4: force SPEC only
               evald = if eqℕ dry 3
                       then appendStr " IMPL=" (encodeBatches (impl-batchSimultaneous em e))
                       else if eqℕ dry 4
                       then appendStr " SPEC=" (encodeBatches (spec-batchSimultaneous em e))
                       else if leqℕ 2 dry
                       then (if eqBatches (impl-batchSimultaneous em e)
                                          (spec-batchSimultaneous em e)
                             then " EVAL:agree" else " EVAL:DIFFER")
                       else ""
           in putStr (concatStr
                ( "case " ∷ natToStr runs ∷ " (seed " ∷ natToStr seed ∷ " depth " ∷ natToStr d
                ∷ ") size=" ∷ natToStr (sizeE e) ∷ evald
                ∷ "\n  prog = " ∷ showExp e
                ∷ "\n  driver = " ∷ showAsyncs (asyncs em) ∷ "\n" ∷ []))
              >>= λ _ → returnIO unit)
     else (let res = fst (runN runs d (randList seed 2000000))
           in putStr (concatStr
                ( "seed " ∷ natToStr seed ∷ " depth " ∷ natToStr d ∷ " — ran " ∷ natToStr runs
                ∷ " cases, " ∷ natToStr (fst res) ∷ " failures\n"
                ∷ maybe′ "  (all agree)\n" (λ r → r) (snd res) ∷ [])) >>= λ _ → returnIO unit)
