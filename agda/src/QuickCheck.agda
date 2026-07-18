-- An all-Agda QuickCheck: generate random well-typed programs (exp tree +
-- scripted inputs) over a fixed 2-slot nat context, run them through the
-- evaluator, and check impl-batchSimultaneous ≡ spec-batchSimultaneous on
-- the resulting stream. A fast in-Agda dev loop for the implementation.
--
--   agda --compile --compile-dir=_cli src/QuickCheck.agda
--   echo "<seed> [runs] [depth]" | ./_cli/QuickCheck
--
-- The fragment is monomorphic (all values ℕ — batching is value-agnostic),
-- μ-free (unfoldμ never forced), and its map/scan fns never return
-- observables (closeUnderFn never forced): exactly the part of evaluate
-- that reduces today. Repeated inner refs to a source inside an *All make
-- diamonds — multiple emits in one instant, the batcher's interesting case.
module QuickCheck where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Char using (Char; toℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_; toList)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Timed; after_,_; ObservableInput; hot; cold;
                           InstEvent; init; value; close; handoff; complete;
                           CloseReason; cut; exhausted; EmitKind;
                           subscribe; delivery; plumbing; InstEmit; _at_from_as_)
open import Rx.Exp using (Ty; natᵗ; obs; _×ᵗ_; Ctx; Exp; Tm; Fn; PrimOp;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ;
                          add; sub; mul; eqᵖ; ltᵖ; notᵖ)
open import Rx.Evaluator using (evaluate; Slot; scripted; shared; Slots)
open import Implementation using (impl-batchSimultaneous)
open import Spec using (spec-batchSimultaneous)
open import CLI.IO

------------------------------------------------------------------------
-- randomness (FFI: a pure LCG over Integer, no unary-ℕ blowup)

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
-- generator monad: consume randoms from a List ℕ

Gen : Set → Set
Gen A = List ℕ → A × List ℕ

pureG : {A : Set} → A → Gen A
pureG x rs = x , rs

_>>=G_ : {A B : Set} → Gen A → (A → Gen B) → Gen B
(g >>=G f) rs with g rs
... | (a , rs′) = f a rs′
infixl 1 _>>=G_

genB : ℕ → Gen ℕ
genB bound []       = 0 , []
genB bound (r ∷ rs) = natMod r bound , rs

------------------------------------------------------------------------
-- the fixed context: two nat-typed slots

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

genFin2 : Gen (Fin 2)
genFin2 = genB 2 >>=G λ c → pureG (if c ≡ᵇ 0 then zero else suc zero)

-- input i : Exp … (lookup Γ₂ i); matching i lets lookup reduce to natᵗ
inputNat : Fin 2 → Exp Γ₂ [] [] [] natᵗ
inputNat zero          = input zero
inputNat (suc zero)    = input (suc zero)
inputNat (suc (suc ()))

genNat : Gen ℕ
genNat = genB 10

-- value functions (natᵗ → natᵗ): identity, +k, *k
genFn : Gen (Fn Γ₂ [] [] [] natᵗ natᵗ)
genFn = genB 3 >>=G λ c → genNat >>=G λ k →
  pureG (if c ≡ᵇ 0 then varᵗ (here refl)
    else if c ≡ᵇ 1 then primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ k))
    else primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ k)))

-- scan step (acc, cur) → acc + cur
genScanFn : Gen (Fn Γ₂ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ)
genScanFn = pureG (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl)))
                                    (sndᵗ (varᵗ (here refl)))))

------------------------------------------------------------------------
-- scripted inputs

genTimed : ℕ → Gen (List (Timed ℕ))
genTimed zero    = pureG []
genTimed (suc n) = genB 3 >>=G λ w → genNat >>=G λ v → genTimed n >>=G λ rest →
  pureG ((after w , v) ∷ rest)

genSyncVals : ℕ → Gen (List ℕ)
genSyncVals zero    = pureG []
genSyncVals (suc n) = genNat >>=G λ v → genSyncVals n >>=G λ vs → pureG (v ∷ vs)

genInput : Gen (ObservableInput ℕ)
genInput = genB 2 >>=G λ c → genB 4 >>=G λ len →
  if c ≡ᵇ 0
  then (genTimed len >>=G λ a → pureG (hot a))
  else (genSyncVals len >>=G λ s → genTimed len >>=G λ a → pureG (cold s a))

genSlots : Gen (Slots Γ₂)
genSlots = genInput >>=G λ i0 → genInput >>=G λ i1 →
  pureG λ where
    zero          → scripted i0
    (suc zero)    → scripted i1
    (suc (suc ()))

------------------------------------------------------------------------
-- the program generator, structural on depth

{-# TERMINATING #-}
genExp : ℕ → Gen (Exp Γ₂ [] [] [] natᵗ)
genObs : ℕ → Gen (Exp Γ₂ [] [] [] (obs natᵗ))

genLeaf : Gen (Exp Γ₂ [] [] [] natᵗ)
genLeaf = genB 3 >>=G λ c →
  if c ≡ᵇ 0 then (genFin2 >>=G λ i → pureG (inputNat i))
  else if c ≡ᵇ 1 then pureG emptyᵉ
  else (genNat >>=G λ a → genNat >>=G λ b → pureG (ofᵉ (nat̂ a ∷ nat̂ b ∷ [])))

genExp zero    = genLeaf
genExp (suc d) = genB 10 >>=G λ c →
  if c ≡ᵇ 0 then genLeaf
  else if c ≡ᵇ 1 then genLeaf
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genExp d >>=G λ e → pureG (mapᵉ f e))
  else if c ≡ᵇ 3 then (genB 4 >>=G λ k → genExp d >>=G λ e → pureG (takeᵉ (nat̂ k) e))
  else if c ≡ᵇ 4 then
    (genScanFn >>=G λ f → genNat >>=G λ s → genExp d >>=G λ e → pureG (scanᵉ f (nat̂ s) e))
  else if c ≡ᵇ 5 then (genObs d >>=G λ s → pureG (mergeAllᵉ s))
  else if c ≡ᵇ 6 then (genObs d >>=G λ s → pureG (concatAllᵉ s))
  else if c ≡ᵇ 7 then (genObs d >>=G λ s → pureG (switchAllᵉ s))
  else if c ≡ᵇ 8 then (genObs d >>=G λ s → pureG (exhaustAllᵉ s))
  else genLeaf

genInners : ℕ → ℕ → Gen (List (Tm Γ₂ [] [] [] (obs natᵗ)))
genInners d zero    = pureG []
genInners d (suc n) = genExp d >>=G λ e → genInners d n >>=G λ rest → pureG (strmᵗ e ∷ rest)

genObs d = genB 2 >>=G λ extra → genInners d (suc (suc extra)) >>=G λ items → pureG (ofᵉ items)

------------------------------------------------------------------------
-- comparison of two batched streams (impl vs spec fed the SAME evaluate
-- output, so ids match exactly — no renaming needed)

eqKind : EmitKind → EmitKind → Bool
eqKind subscribe subscribe = true
eqKind delivery  delivery  = true
eqKind plumbing  plumbing  = true
eqKind _         _         = false

eqReason : CloseReason → CloseReason → Bool
eqReason cut       cut       = true
eqReason exhausted exhausted = true
eqReason _         _         = false

eqListℕ : List ℕ → List ℕ → Bool
eqListℕ []       []       = true
eqListℕ (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqListℕ xs ys
eqListℕ _        _        = false

eqEvent : InstEvent (List ℕ) → InstEvent (List ℕ) → Bool
eqEvent (init a)    (init b)    = a ≡ᵇ b
eqEvent (value a)   (value b)   = eqListℕ a b
eqEvent (close a p) (close b q) = (a ≡ᵇ b) ∧ eqReason p q
eqEvent (handoff a) (handoff b) = a ≡ᵇ b
eqEvent complete    complete    = true
eqEvent _           _           = false

eqEvents : List (InstEvent (List ℕ)) → List (InstEvent (List ℕ)) → Bool
eqEvents []       []       = true
eqEvents (x ∷ xs) (y ∷ ys) = eqEvent x y ∧ eqEvents xs ys
eqEvents _        _        = false

eqEmit : InstEmit (List ℕ) → InstEmit (List ℕ) → Bool
eqEmit (es at i from s as k) (es′ at i′ from s′ as k′) =
  eqEvents es es′ ∧ (i ≡ᵇ i′) ∧ (s ≡ᵇ s′) ∧ eqKind k k′

eqBatched : List (InstEmit (List ℕ)) → List (InstEmit (List ℕ)) → Bool
eqBatched []       []       = true
eqBatched (x ∷ xs) (y ∷ ys) = eqEmit x y ∧ eqBatched xs ys
eqBatched _        _        = false

------------------------------------------------------------------------
-- a compact dump of a batched stream (for failure reports)

private
  commaJoin : List String → String
  commaJoin []           = ""
  commaJoin (s ∷ [])     = s
  commaJoin (s ∷ t ∷ ss) = s ++ "," ++ commaJoin (t ∷ ss)

  showVals : List ℕ → String
  showVals vs = "[" ++ commaJoin (mapShow vs) ++ "]"
    where mapShow : List ℕ → List String
          mapShow []       = []
          mapShow (v ∷ vs) = show v ∷ mapShow vs

  showEvent : InstEvent (List ℕ) → String
  showEvent (init s)    = "i" ++ show s
  showEvent (value v)   = "v" ++ showVals v
  showEvent (close s _) = "c" ++ show s
  showEvent (handoff s) = "h" ++ show s
  showEvent complete    = "F"

  showEvents : List (InstEvent (List ℕ)) → String
  showEvents []       = ""
  showEvents (e ∷ es) = showEvent e ++ " " ++ showEvents es

  showEmit : InstEmit (List ℕ) → String
  showEmit (es at i from s as _) = "@" ++ show i ++ "{" ++ showEvents es ++ "}"

showBatched : List (InstEmit (List ℕ)) → String
showBatched []       = "·"
showBatched (e ∷ es) = showEmit e ++ " " ++ showBatched es

------------------------------------------------------------------------
-- render a generated program back to Agda source (a paste-ready block for
-- the Unit-Test cache). Faithful over the fragment the generator emits;
-- constructors it never produces get a placeholder (kept total).

showFin : ∀ {n} → Fin n → String
showFin zero    = "zero"
showFin (suc i) = "(suc " ++ showFin i ++ ")"

showNatList : List ℕ → String
showNatList []       = "[]"
showNatList (v ∷ vs) = show v ++ " ∷ " ++ showNatList vs

showTimedList : List (Timed ℕ) → String
showTimedList []                = "[]"
showTimedList ((after w , v) ∷ ts) =
  "(after " ++ show w ++ " , " ++ show v ++ ") ∷ " ++ showTimedList ts

showInput : ObservableInput ℕ → String
showInput (hot a)    = "hot (" ++ showTimedList a ++ ")"
showInput (cold s a) = "cold (" ++ showNatList s ++ ") (" ++ showTimedList a ++ ")"

showSlot : Slot Γ₂ natᵗ → String
showSlot (scripted i) = "scripted (" ++ showInput i ++ ")"
showSlot (shared _)   = "PLACEHOLDER-shared"

showSlots : Slots Γ₂ → String
showSlots ins =
  "(λ { zero → " ++ showSlot (ins zero)
    ++ " ; (suc zero) → " ++ showSlot (ins (suc zero))
    ++ " ; (suc (suc ())) })"

showPrim : ∀ {s t} → PrimOp s t → String
showPrim add  = "add"
showPrim sub  = "sub"
showPrim mul  = "mul"
showPrim eqᵖ  = "eqᵖ"
showPrim ltᵖ  = "ltᵖ"
showPrim notᵖ = "notᵖ"

showExp : ∀ {Θ t} → Exp Γ₂ [] [] Θ t → String
showTm  : ∀ {Θ t} → Tm Γ₂ [] [] Θ t → String

showTmList : ∀ {Θ t} → List (Tm Γ₂ [] [] Θ t) → String
showTmList []       = "[]"
showTmList (x ∷ xs) = showTm x ++ " ∷ " ++ showTmList xs

showTm (varᵗ (here refl)) = "(varᵗ (here refl))"
showTm (varᵗ (there _))   = "PLACEHOLDER-var"
showTm (nat̂ n)            = "(nat̂ " ++ show n ++ ")"
showTm (pairᵗ a b)        = "(pairᵗ " ++ showTm a ++ " " ++ showTm b ++ ")"
showTm (fstᵗ p)           = "(fstᵗ " ++ showTm p ++ ")"
showTm (sndᵗ p)           = "(sndᵗ " ++ showTm p ++ ")"
showTm (primᵗ op a)       = "(primᵗ " ++ showPrim op ++ " " ++ showTm a ++ ")"
showTm (strmᵗ e)          = "(strmᵗ " ++ showExp e ++ ")"
showTm _                  = "PLACEHOLDER-tm"

showExp (input i)       = "(input " ++ showFin i ++ ")"
showExp (ofᵉ items)     = "(ofᵉ (" ++ showTmList items ++ "))"
showExp emptyᵉ          = "emptyᵉ"
showExp (mapᵉ f e)      = "(mapᵉ " ++ showTm f ++ " " ++ showExp e ++ ")"
showExp (takeᵉ n e)     = "(takeᵉ " ++ showTm n ++ " " ++ showExp e ++ ")"
showExp (scanᵉ f s e)   = "(scanᵉ " ++ showTm f ++ " " ++ showTm s ++ " " ++ showExp e ++ ")"
showExp (mergeAllᵉ s)   = "(mergeAllᵉ " ++ showExp s ++ ")"
showExp (concatAllᵉ s)  = "(concatAllᵉ " ++ showExp s ++ ")"
showExp (switchAllᵉ s)  = "(switchAllᵉ " ++ showExp s ++ ")"
showExp (exhaustAllᵉ s) = "(exhaustAllᵉ " ++ showExp s ++ ")"
showExp _               = "PLACEHOLDER-exp"

------------------------------------------------------------------------
-- one case, a run, and reporting

FUEL : ℕ
FUEL = 30

-- a paste-ready Unit-Test block for a failing program (Agree is defined in
-- the Unit-Test module). The program line is the dedup key for the script.
report : Exp Γ₂ [] [] [] natᵗ → Slots Γ₂
       → List (InstEmit (List ℕ)) → List (InstEmit (List ℕ)) → String
report e ins impl spec =
  "  FAIL\n    impl = " ++ showBatched impl
       ++ "\n    spec = " ++ showBatched spec
       ++ "\n-- <<<PASTE\n_ : Agree " ++ show FUEL ++ "\n          "
       ++ showExp e ++ "\n          " ++ showSlots ins
       ++ "\n_ = refl\n-- PASTE>>>\n"

oneCase : ℕ → Gen (Maybe String)
oneCase d = genSlots >>=G λ ins → genExp d >>=G λ e →
  let s    = evaluate FUEL e ins
      impl = impl-batchSimultaneous s
      spec = spec-batchSimultaneous s
  in pureG (if eqBatched impl spec then nothing else just (report e ins impl spec))

runN : ℕ → ℕ → Gen (ℕ × Maybe String)
runN zero    d = pureG (0 , nothing)
runN (suc k) d = oneCase d >>=G λ r → runN k d >>=G λ acc →
  pureG (maybe′ (λ _ → suc (proj₁ acc)) (proj₁ acc) r
        , maybe′ just (proj₂ acc) r)

------------------------------------------------------------------------
-- stdin parsing: "SEED [RUNS] [DEPTH]"

toCodes : String → List ℕ
toCodes s = map toℕ (toList s)

concatStr : List String → String
concatStr []       = ""
concatStr (s ∷ ss) = s ++ concatStr ss

isDigit : ℕ → Bool
isDigit c = (48 ≤ᵇ c) ∧ (c ≤ᵇ 57)

parseNat : List ℕ → ℕ
parseNat = go 0
  where
    go : ℕ → List ℕ → ℕ
    go acc []       = acc
    go acc (c ∷ cs) = if isDigit c then go ((acc * 10) + (c ∸ 48)) cs else acc

dropNum dropSep : List ℕ → List ℕ
dropNum []       = []
dropNum (c ∷ cs) = if isDigit c then dropNum cs else (c ∷ cs)
dropSep []       = []
dropSep (c ∷ cs) = if isDigit c then (c ∷ cs) else dropSep cs

tailAfter : ℕ → List ℕ → List ℕ
tailAfter zero    cs = cs
tailAfter (suc n) cs = tailAfter n (dropSep (dropNum cs))

numAt : ℕ → ℕ → List ℕ → ℕ
numAt n def cs with dropSep (tailAfter n cs)
... | []         = def
... | ds@(_ ∷ _) = parseNat ds

main : IO Unit
main = getContents >>= λ s →
  let cs   = toCodes s
      seed = parseNat cs
      runs = numAt 1 200 cs
      d    = numAt 2 4 cs
      res  = proj₁ (runN runs d (randList seed 2000000))
  in putStr (concatStr
       ( "seed " ∷ show seed ∷ " depth " ∷ show d ∷ " — ran " ∷ show runs
       ∷ " cases, " ∷ show (proj₁ res) ∷ " failures\n"
       ∷ maybe′ (λ r → r) "  (all agree)\n" (proj₂ res) ∷ []))
