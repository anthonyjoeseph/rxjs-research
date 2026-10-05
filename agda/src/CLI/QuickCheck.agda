-- An all-Agda QuickCheck: generate random well-typed programs (exp tree +
-- scripted inputs) over a fixed 2-slot nat context, run them through the
-- real evaluator, and decide the four statements `Main` imports and the
-- simulation two of them stand on, each at its own sides
-- (`CLI.Unit-Test.Prelude`): one quickcheck per statement, selectable
-- one at a time.  A fast in-Agda dev loop for the
-- implementation.
--
--   agda --compile --compile-dir=_cli src/CLI/QuickCheck.agda
--   echo "<seed> [runs] [depth] [at]" | ./_cli/QuickCheck
--
-- A nonzero `at` prints the paste row of that one case (1-based) and runs
-- nothing, which is the only way to read a program whose evaluation costs
-- more than the sweep it sits in.
--
-- The fragment's payloads are ℕ, because batching is value-agnostic.
-- Repeated inner refs to a source inside an *All make diamonds —
-- multiple emits in one instant, the batcher's interesting case.
--
-- AND IT REACHES A FOLD AT OBSERVABLE TYPE, WHICH IS THE ONE BINDER THAT
-- LEAVES THE STATIC READING.  Substituting a value of observable type
-- reifies it under `strmᵗ`, so a template naming its own accumulator
-- hands back one a wrap deeper: the environment stops being data, and
-- the inners an *All hops onto stop being subterms of the program.  A
-- generator that folds only at ℕ cannot write that shape down at all —
-- not under-sample it, but fail to TYPE it — so its greens were silent
-- about the one region where the substitution shelf has no statement.
-- The summary line carries how many programs reached it, because that
-- is the claim and it is a number.
--
-- WHAT IS STILL OUT OF REACH, and it is the SECOND binder of the same
-- kind: a `caseᵗ` scrutinising a sum that contains an observable rebinds
-- one exactly as the fold does.  The fragment has no sums at all, so
-- that arm is unsampled and no seed changes it.
--
-- IT REACHES `μᵉ`, AND THAT IS WHAT PUTS THE SWEEP ON THE DESCENT. The
-- rank guard lives under recursion, so a μ-free generator could never
-- produce the shape the descent's one open reading is about, however
-- many seeds it ran. Recursion is generated with its binder
-- scopes carried as indices rather than checked afterwards — the
-- generator's type is `Exp` at the two μ contexts, so a synchronous
-- self-reference is not a program it can emit and be rejected for; it is
-- one it cannot write down.
--
-- AND EVERY RUN CARRIES A CENSUS LINE, ONE COUNT PER FORMER.  What a
-- green claims is that the shapes were REACHED, and that is a number
-- rather than a claim; counting per former rather than per interesting
-- region is what stops the regions from being whichever ones somebody
-- last thought about.  The per-run line is raw material: a sweep sums
-- it across seeds, and a former totalling zero is a hole in what the
-- sweep covered rather than a fact about any one seed.
module CLI.QuickCheck where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Bool.ListAction using (any; all)
open import Data.Char using (toℕ; fromℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map; length; concat; concatMap; take; drop; zipWith; upTo)
                      renaming (_++_ to _++ᴸ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_; ⌊_/2⌋)
open import Data.Nat.Show using (show)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _++_; toList; fromList) renaming (length to lengthˢ)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Rx.Prim using (after_,_; Timed; ObservableInput; hot; cold; InstEvent; init; value; close; handoff; complete; InstEmit; _at_from_as_)
open import Rx.Exp using (Ty; Ctx; boolᵗ; natᵗ; unitᵗ; obs; _×ᵗ_; _+ᵗ_; isData; PrimOp; input; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ;
  FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; Exp; Tm; ofᵉ; emptyᵉ; takeᵉ; takeWhileᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
  flattenᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; varᵗ; unit̂; bool̂; nat̂; foldᵗ; nilᵗ; consᵗ; pairᵗ; fstᵗ;
  sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import SExp.Syntax using (SExp; STm; SFn; inputˢ; ofˢ; emptyˢ; takeˢ; takeWhileˢ; mapˢ; scanˢ; flattenˢ;
  μˢ; varˢ; deferˢ; varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ;
  caseˢ; foldˢ; primˢ; ifˢ; strmˢ)
open import Data.List.Membership.Propositional using (_∈_)
open import CLI.Emit-Eq using (eqListℕ; prefixListℕ; eqBatches)
open import CLI.JSON using (JSON; jnum; jstr; jarr; jobj; parseJSON)
open import SExp.Pipeline using (runᴵ; elaborateImpl)
open import CLI.Store-Check using (storeSides)
open import CLI.Unit-Test.Prelude using (Γ₂; Case; mkSlots; cached; Statement; flatAllˢ;
  left-to-rightˢ; timing-correctˢ; batchableˢ; timed-faithfulˢ; simulationˢ; arrival-runsˢ; statements; statementName;
  batched-sandwichˢ; packets-name-arrivalsˢ; bsSides; namingSides; namesᵇ;
  same-clockˢ; sameClockᵇ; Key; storeˢ;
  ltrSides; stampsOf; batchableSides; faithfulSides; allPairsᵇ; κOf;
  Item; Arr; arrPlain; arrTimed; eqItem; simᵇ; lockstepᵇ)
open import CLI.Unit-Test using (cases)
open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; putErr; Unit)

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

-- A WALL CLOCK AROUND ONE PURE VALUE: `within s n x d` is `x` when `n`,
-- a number whose evaluation forces `x`, finishes within `s` seconds, and
-- `d` otherwise.  It is the
-- harness's one cap, because it is the one that does not change what is
-- run; zero seconds is no bound at all.
{-# FOREIGN GHC import qualified System.Timeout #-}
{-# FOREIGN GHC import qualified Control.Exception #-}
{-# FOREIGN GHC import qualified System.IO.Unsafe #-}
{-# FOREIGN GHC
withinH :: Integer -> Integer -> a -> a -> a
withinH s n x d
  | s == 0    = x
  | otherwise = System.IO.Unsafe.unsafePerformIO
      (maybe d id <$> System.Timeout.timeout (fromInteger (s * 1000000))
                        (Control.Exception.evaluate n >> return x))
#-}
postulate within : {A : Set} → ℕ → ℕ → A → A → A
{-# COMPILE GHC within = \_ -> withinH #-}

randList : ℕ → ℕ → List ℕ
randList seed count = randFold seed count _∷_ []

------------------------------------------------------------------------
-- generator monad: consume randoms from a List ℕ

-- A DRAW IS AIMED BY WEIGHTING THE ARMS IT PICKS BETWEEN, NEVER BY
-- FILTERING WHAT IT DREW.  Each `Knob` is one arm choice of the generator
-- below, named by the key a restriction spells it with; a weight list
-- replaces that choice's uniform pick, so a zero weight is an arm the
-- sweep never takes and the draw stays a draw.  An absent knob is the
-- uniform pick and consumes exactly what it always did, which is what
-- keeps every unrestricted seed the program it was.
data Knob : Set where
  kExp kSpineD kSpineG kOp kFan kScript kSlot kLeaf kObs : Knob

arity : Knob → ℕ
arity kExp    = 13
arity kSpineD = 10
arity kSpineG = 10
arity kOp     = 5
arity kFan    = 9
arity kScript = 4
arity kSlot   = 4
arity kLeaf   = 3
arity kObs    = 4

knobName : Knob → String
knobName kExp    = "exp"
knobName kSpineD = "spineD"
knobName kSpineG = "spineG"
knobName kOp     = "op"
knobName kFan    = "fan"
knobName kScript = "script"
knobName kSlot   = "slot"
knobName kLeaf   = "leaf"
knobName kObs    = "obs"

allKnobs : List Knob
allKnobs = kExp ∷ kSpineD ∷ kSpineG ∷ kOp ∷ kFan ∷ kScript ∷ kSlot ∷ kLeaf ∷ kObs ∷ []

-- the weights, the former tags every accepted case must carry, and how
-- many draws a case may spend finding one that does
record Draw : Set where
  field
    weights : Knob → List ℕ
    reach   : List (List ℕ)
    tries   : ℕ

anyDraw : Draw
anyDraw = record { weights = λ _ → [] ; reach = [] ; tries = 1 }

Gen : Set → Set
Gen A = Draw → List ℕ → A × List ℕ

pureG : {A : Set} → A → Gen A
pureG x W rs = x , rs

_>>=G_ : {A B : Set} → Gen A → (A → Gen B) → Gen B
(g >>=G f) W rs with g W rs
... | (a , rs′) = f a W rs′
infixl 1 _>>=G_

askG : Gen Draw
askG W rs = W , rs

genB : ℕ → Gen ℕ
genB bound W []       = 0 , []
genB bound W (r ∷ rs) = natMod r bound , rs

sumℕ : List ℕ → ℕ
sumℕ []       = 0
sumℕ (x ∷ xs) = x + sumℕ xs

-- the arm a point of the weights' total lands in
pick : List ℕ → ℕ → ℕ
pick []       r = 0
pick (w ∷ ws) r = if suc r ≤ᵇ w then 0 else suc (pick ws (r ∸ w))

genW : Knob → Gen ℕ
genW k W rs with Draw.weights W k
... | []       = genB (arity k) W rs
... | ws@(_ ∷ _) = (genB (sumℕ ws) >>=G λ r → pureG (pick ws r)) W rs

------------------------------------------------------------------------
-- THE TREE THE SWEEP DRAWS IS THE AUTHOR'S, WHICH IS WHAT PUTS THE
-- BATCHING QUESTION IN RANGE AT ALL.  Both batchings read the protocol
-- off an INSTEMIT, and only an elaborated program carries one, so a
-- drawn `Exp` could be run and could not be ASKED.  The generator is
-- therefore indexed by `SExp`, and `SExp.Elaborate` is what stands
-- between it and the evaluator; the two formers the plain tree has and
-- the author's does not -- mint and batchSync -- leave with it, and
-- what reaches them now is the elaboration rather than a seed.
--
-- THE CONTEXT COMES FROM THE PRELUDE BECAUSE A CACHED ROW AND THE SEED
-- THAT FOUND IT HAVE TO BE ONE RUN.  `Γ₂` is what the author sees and
-- `Γ₂ᵉ` is where an elaborated program stands, each slot holding the
-- InstEmit over the author's type.

genFin2 : Gen (Fin 2)
genFin2 = genB 2 >>=G λ c → pureG (if c ≡ᵇ 0 then zero else suc zero)

-- inputˢ i : SExp … (lookup Γ₂ i); matching i lets lookup reduce to natᵗ.
-- Polymorphic in the μ-var contexts: a slot reference is legal wherever the
-- generator stands, binders open or not.
inputNat : ∀ {Δᵍ Δ Θ} → Fin 2 → SExp Γ₂ Δᵍ Δ Θ natᵗ
inputNat zero          = inputˢ zero
inputNat (suc zero)    = inputˢ (suc zero)
inputNat (suc (suc ()))

-- WHICH SLOTS A SUBTREE MAY READ, AND IT IS A NUMBER BECAUSE THE
-- TELESCOPE IS STRATIFIED.  Slot k's def may name only slots below k,
-- so the same generator draws the program (both slots readable), slot
-- one's def (slot zero readable) and slot zero's (none) -- and the
-- side condition on `shared` is then discharged by computation rather
-- than by a proof threaded through the generator.
genSlotRef : ∀ {Δᵍ Δ Θ} → ℕ → Gen (SExp Γ₂ Δᵍ Δ Θ natᵗ)
genSlotRef zero          = pureG emptyˢ
genSlotRef (suc zero)    = pureG (inputNat zero)
genSlotRef (suc (suc _)) = genFin2 >>=G λ i → pureG (inputNat i)

genNat : Gen ℕ
genNat = genB 10

-- ONE SLOT'S DEFINITION.  `genSlotRef` is the FORWARDING arm -- slot
-- one reading slot zero -- and it is what makes the table a telescope
-- rather than two independent sources.  On its own it is not enough:
-- `genSlotRef 0` is `emptyˢ`, so a table drawn from it alone is silent
-- and the sweep would run every program against nothing, which is what
-- it already did with the constant table.  The other arms give slot
-- zero something to say, so the forwarding has traffic to forward.
genSlotDef : ℕ → Gen (SExp Γ₂ [] [] [] natᵗ)
genSlotDef k = genW kSlot >>=G λ c → genNat >>=G λ x → genNat >>=G λ y →
       if c ≡ᵇ 0 then genSlotRef k
  else if c ≡ᵇ 1 then pureG emptyˢ
  else if c ≡ᵇ 2 then pureG (ofˢ (natˢ x ∷ []))
  else                pureG (ofˢ (natˢ x ∷ natˢ y ∷ []))

-- SLOT ZERO IS A SCRIPT, AND IT IS THE ONLY THING THAT SCHEDULES.  A
-- share runs its definition inside whatever subscribed it, so a table of
-- shares alone is a run that is its subscribe burst and nothing after;
-- a scripted source is what puts ARRIVALS in a run.  Hot and cold, with
-- and without synchronous values, one or two arrivals.
Script : Set
Script = ObservableInput ℕ

-- printed as Agda, so a pasted row typechecks where the corpus lives
showNats : List ℕ → String
showNats []       = "[]"
showNats (x ∷ xs) = "(" ++ show x ++ " ∷ " ++ showNats xs ++ ")"

showTimed : List (Timed ℕ) → String
showTimed []                  = "[]"
showTimed ((after w , v) ∷ r) =
  "((after " ++ show w ++ " , " ++ show v ++ ") ∷ " ++ showTimed r ++ ")"

showScript : Script → String
showScript (hot ts)     = "hot " ++ showTimed ts
showScript (cold ss ts) = "cold " ++ showNats ss ++ " " ++ showTimed ts

genScript : Gen Script
genScript = genW kScript >>=G λ c → genNat >>=G λ x → genNat >>=G λ y →
  genB 2 >>=G λ w →
       if c ≡ᵇ 0 then pureG (hot ((after w , x) ∷ []))
  else if c ≡ᵇ 1 then pureG (hot ((after 0 , x) ∷ (after w , y) ∷ []))
  else if c ≡ᵇ 2 then pureG (cold (x ∷ []) ((after w , y) ∷ []))
  else                pureG (cold [] ((after w , x) ∷ (after 0 , y) ∷ []))

-- THE TELESCOPE IS DRAWN IN ORDER, each slot seeing only the ones
-- below it, which is exactly the argument `genSlotRef` takes.
genSlots : Gen (Script × SExp Γ₂ [] [] [] natᵗ)
genSlots = genScript >>=G λ d₀ → genSlotDef 1 >>=G λ d₁ →
  pureG (d₀ , d₁)

-- value functions (natᵗ → natᵗ): identity, +k, *k, and a CONSTANT.
--
-- THE FOURTH ARM DROPS ITS ARGUMENT, AND ITS ABSENCE WAS A COVERAGE
-- HOLE RATHER THAN A CHOICE.  `Fn` is a term with the argument pushed
-- onto the scope, so a template is free to ignore it — and an
-- argument-dropping template is what breaks a frame bound denominated
-- in what the frame was HANDED, since the input's reading cannot bound
-- an output the input never contributed to.  The three arms above all
-- USE the argument, so no seed could reach the shape however many
-- programs it drew.  That is the general trap and not a local one: a
-- generator built to produce interesting terms systematically
-- under-samples degenerate ones, and the degenerate ones are where this
-- campaign's counterexamples have been.
genFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ natᵗ natᵗ)
genFn = genB 4 >>=G λ c → genNat >>=G λ k →
  pureG (if c ≡ᵇ 0 then varˢᵗ (here refl)
    else if c ≡ᵇ 1 then primˢ add (pairˢ (varˢᵗ (here refl)) (natˢ k))
    else if c ≡ᵇ 2 then primˢ mul (pairˢ (varˢᵗ (here refl)) (natˢ k))
    else natˢ k)

-- a `takeWhile` predicate: below a bound, or anything but one value
genPredFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ natᵗ boolᵗ)
genPredFn = genB 2 >>=G λ c → genNat >>=G λ k →
  pureG (if c ≡ᵇ 0 then primˢ ltᵖ (pairˢ (varˢᵗ (here refl)) (natˢ k))
    else primˢ notᵖ (primˢ eqᵖ (pairˢ (varˢᵗ (here refl)) (natˢ k))))

-- scan step (acc, cur) → acc + cur
genScanFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) natᵗ)
genScanFn = pureG (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl)))
                                    (sndˢ (varˢᵗ (here refl)))))

-- THE STEP THAT CHANGES AN EMIT'S VALUE COUNT, WHICH IS A FLATTEN AND
-- NOT A STEP AT ALL.  `mapᵉ` and `scanᵉ` are both per-VALUE, so the
-- list they hand back is always as long as the one they were given, and
-- a sweep built only out of them never changes a count.  Zero-or-more
-- out is `flattenˢ` over a step returning an ELEMENT — an optional echo
-- beside an optional lane of LITERAL SYNTAX, rxjs's own
-- `mergeMap(x => …)` when the echo is absent — so this generates the
-- step and the fan arm spends it under a drawn policy.  The lane arms
-- are a lattice over what happens to the count: emptied, doubled, one
-- longer, filtered, and unchanged; the echo arms are the same lattice
-- spent WITHOUT a lane, which no policy sees, and one arm carrying both.
--
-- THE IDENTITY ARMS ARE DELIBERATE, on the reasoning `genFn` records: a
-- generator whose every arm exercises the interesting shape cannot
-- produce the program that distinguishes a step which ignores its input
-- from one that does not.
genFanFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ natᵗ ((unitᵗ +ᵗ natᵗ) ×ᵗ (unitᵗ +ᵗ obs natᵗ)))
genFanFn = genW kFan >>=G λ c → genNat >>=G λ k →
  let x = varˢᵗ (here refl)
      lane : ∀ {Δᵍ Δ Θ} → STm Γ₂ Δᵍ Δ Θ (obs natᵗ) → STm Γ₂ Δᵍ Δ Θ ((unitᵗ +ᵗ natᵗ) ×ᵗ (unitᵗ +ᵗ obs natᵗ))
      lane o = pairˢ (inlˢ unitˢ) (inrˢ o)
      none = pairˢ (inlˢ unitˢ) (inlˢ unitˢ)
      echo = pairˢ (inrˢ x) (inlˢ unitˢ)
  in pureG
    (      if c ≡ᵇ 0 then lane (strmˢ emptyˢ)
      else if c ≡ᵇ 1 then lane (strmˢ (ofˢ (x ∷ x ∷ [])))
      else if c ≡ᵇ 2 then lane (strmˢ (ofˢ (x ∷ natˢ k ∷ [])))
      else if c ≡ᵇ 3 then
        ifˢ (primˢ ltᵖ (pairˢ x (natˢ k))) (lane (strmˢ emptyˢ)) (lane (strmˢ (ofˢ (x ∷ []))))
      else if c ≡ᵇ 4 then lane (strmˢ (ofˢ (x ∷ [])))
      else if c ≡ᵇ 5 then none
      else if c ≡ᵇ 6 then ifˢ (primˢ ltᵖ (pairˢ x (natˢ k))) none echo
      else if c ≡ᵇ 7 then pairˢ (inrˢ x) (inrˢ (strmˢ (ofˢ (natˢ k ∷ []))))
      else echo)

-- A FLATTENER'S POLICY, each of rxjs's named ones and the bounded merge
-- between them
genOp : Gen FlatOp
genOp = genW kOp >>=G λ c → genB 3 >>=G λ k →
  pureG (      if c ≡ᵇ 0 then mergeᶠ nothing
          else if c ≡ᵇ 1 then mergeᶠ (just (suc k))
          else if c ≡ᵇ 2 then switchᶠ
          else if c ≡ᵇ 3 then exhaustᶠ
          else mergeᶠ nothing)

-- THE ACCUMULATOR AT OBSERVABLE TYPE, WHICH IS THE ONE BINDER THAT
-- BREAKS A DATA ENVIRONMENT.  Substituting a value of observable type
-- for a variable REIFIES it under `strmᵗ`, so a template mentioning its
-- own accumulator hands back one a wrap deeper and the fold feeds that
-- straight in — the arms below are a coverage LATTICE over whether the
-- template wraps, passes, resets or ignores, because the climb is a
-- property of WHICH of those it does and of nothing else.
--
-- THE DEGENERATE ARMS ARE DELIBERATE AND ARE THE POINT.  `dropped`
-- names neither component, so no seed reaching only the wrapping arms
-- could produce a fold whose output is independent of everything handed
-- to it — the same trap `genFn` records one declaration up, where three
-- arms all USED the argument and the shape that mattered was the fourth.
genObsScanFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ (obs natᵗ ×ᵗ natᵗ) (obs natᵗ))
genObsScanFn = genB 6 >>=G λ c → genNat >>=G λ k →
  let acc = fstˢ (varˢᵗ (here refl))
      cur = sndˢ (varˢᵗ (here refl))
  in pureG
    (      if c ≡ᵇ 0 then strmˢ (flatAllˢ (mergeᶠ nothing) (ofˢ (acc ∷ [])))
      else if c ≡ᵇ 1 then acc
      else if c ≡ᵇ 2 then strmˢ (ofˢ (cur ∷ []))
      else if c ≡ᵇ 3 then strmˢ emptyˢ
      else if c ≡ᵇ 4 then strmˢ (flatAllˢ switchᶠ (ofˢ (acc ∷ [])))
      else strmˢ (flatAllˢ (mergeᶠ nothing)
             (ofˢ (acc ∷ strmˢ (ofˢ (natˢ k ∷ [])) ∷ []))))

-- the fold's own seed, at observable type.  `emptyᵉ` is the shallowest
-- one there is, so a climb read off a run seeded with it is the fold's
-- entirely
genObsSeed : ∀ {Δᵍ Δ Θ} → ℕ → Gen (STm Γ₂ Δᵍ Δ Θ (obs natᵗ))
genObsSeed sl = genB 3 >>=G λ c → genNat >>=G λ k → genSlotRef sl >>=G λ r →
  pureG (      if c ≡ᵇ 0 then strmˢ emptyˢ
          else if c ≡ᵇ 1 then strmˢ (ofˢ (natˢ k ∷ []))
          else strmˢ r)

------------------------------------------------------------------------
-- the program generator, structural on depth

-- THE μ-VAR CONTEXTS AS LENGTHS.  `Exp` carries two — Δᵍ for a binder a
-- `μᵉ` has opened but no `deferᵉ` has yet admitted, Δ for one that is
-- readable — and every recursion this fragment builds is at `natᵗ`, so a
-- context is fixed by its LENGTH.  Indexing the generator by two ℕs is what
-- makes an ill-scoped program unwritable rather than generated-and-rejected:
-- a synchronous self-reference has no type here.
nats : ℕ → List Ty
nats zero    = []
nats (suc g) = natᵗ ∷ nats g

-- `deferᵉ` is the sole gate, and its body reads `Δᵍ ++ Δ` — the one place
-- the two contexts meet, so this is the only transport the generator needs.
-- It reduces to `refl` at every concrete pair, so a generated program
-- COMPUTES and a printed one pastes.
nats-++ : ∀ g u → nats g ++ᴸ nats u ≡ nats (g + u)
nats-++ zero    u = refl
nats-++ (suc g) u = cong (natᵗ ∷_) (nats-++ g u)

gate : ∀ g u → SExp Γ₂ [] (nats (g + u)) [] natᵗ → SExp Γ₂ (nats g) (nats u) [] natᵗ
gate g u b = deferˢ (subst (λ Δ → SExp Γ₂ [] Δ [] natᵗ) (sym (nats-++ g u)) b)

-- RECURSION IS GENERATED LINEAR — exactly one reference per binder — and that
-- is a feasibility bound rather than a taste.  A μ whose body reads its own
-- var twice respawns twice per tick, so the live subscription count is 2^fuel
-- by the time the run ends; real rxjs hangs on that program too, which makes
-- it a shape the sweep cannot afford and not one it is declining to test.  So
-- a μ body is a SPINE: operators nest freely, one chosen child carries the
-- obligation onward, and the obligation is discharged at exactly one leaf.
-- `genSpineG` still owes the `deferᵉ`; `genSpineD` is past it and plants the
-- var.  Ordinary subtrees never emit a var at all, so a μ's arity is a
-- property of the grammar rather than of the seed.
{-# TERMINATING #-}
genExpAt   : ∀ g u → ℕ → ℕ → Gen (SExp Γ₂ (nats g) (nats u) [] natᵗ)
genObsAt   : ∀ g u → ℕ → ℕ → Gen (SExp Γ₂ (nats g) (nats u) [] (obs natᵗ))
genInners  : ∀ g u → ℕ → ℕ → ℕ → Gen (List (STm Γ₂ (nats g) (nats u) [] (obs natᵗ)))
genSpineG  : ∀ g u → ℕ → ℕ → Gen (SExp Γ₂ (nats (suc g)) (nats u) [] natᵗ)
genSpineD  : ∀ w   → ℕ → ℕ → Gen (SExp Γ₂ [] (nats (suc w)) [] natᵗ)

genLeafAt : ∀ g u → ℕ → Gen (SExp Γ₂ (nats g) (nats u) [] natᵗ)
genLeafAt g u sl = genW kLeaf >>=G λ c →
  if c ≡ᵇ 0 then genSlotRef sl
  else if c ≡ᵇ 1 then pureG emptyˢ
  else (genNat >>=G λ a → genNat >>=G λ b → pureG (ofˢ (natˢ a ∷ natˢ b ∷ [])))

genExpAt g u sl zero    = genLeafAt g u sl
genExpAt g u sl (suc d) = genW kExp >>=G λ c →
  if c ≡ᵇ 0 then genLeafAt g u sl
  else if c ≡ᵇ 1 then genLeafAt g u sl
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genExpAt g u sl d >>=G λ e → pureG (mapˢ f e))
  else if c ≡ᵇ 3 then
    (genScanFn >>=G λ f → genNat >>=G λ z → genExpAt g u sl d >>=G λ e →
     pureG (scanˢ f (natˢ z) e))
  else if c ≡ᵇ 4 then (genObsAt g u sl d >>=G λ t → pureG (flatAllˢ (mergeᶠ nothing) t))
  else if c ≡ᵇ 5 then
    -- the limit axis, which is where bounded concurrency gets sampled:
    -- 1 is the old concat, 2 and 3 are the middle nothing here could
    -- previously reach.  Two lanes with three parked inners is the
    -- smallest shape whose drain refills more than one lane in a
    -- single instant, so `genB 3` is the floor and not a taste
    (genB 3 >>=G λ k → genObsAt g u sl d >>=G λ t → pureG (flatAllˢ (mergeᶠ (just (suc k))) t))
  else if c ≡ᵇ 6 then (genObsAt g u sl d >>=G λ t → pureG (flatAllˢ switchᶠ t))
  else if c ≡ᵇ 7 then (genObsAt g u sl d >>=G λ t → pureG (flatAllˢ exhaustᶠ t))
  else if c ≡ᵇ 8 then (genSpineG g u sl d >>=G λ b → pureG (μˢ b))
  else if c ≡ᵇ 9 then (genExpAt 0 (g + u) sl d >>=G λ b → pureG (gate g u b))
  else if c ≡ᵇ 10 then
    (genNat >>=G λ k → genExpAt g u sl d >>=G λ e → pureG (takeˢ (natˢ k) e))
  else if c ≡ᵇ 11 then
    (genPredFn >>=G λ f → genExpAt g u sl d >>=G λ e → pureG (takeWhileˢ f e))
  else
    (genOp >>=G λ op → genFanFn >>=G λ f → genExpAt g u sl d >>=G λ e →
     pureG (flattenˢ op (mapˢ f e)))

genInners g u sl d zero    = pureG []
genInners g u sl d (suc n) =
  genExpAt g u sl d >>=G λ e → genInners g u sl d n >>=G λ rest →
  pureG (strmˢ e ∷ rest)

-- TWO WAYS TO BE A STREAM OF STREAMS, AND ONLY ONE OF THEM IS STATIC.
-- A literal list of inners is closed syntax, so every observable an
-- *All hops onto is a subterm of the program.  A fold AT OBSERVABLE TYPE
-- is not: its emissions are built during the run out of its own previous
-- ones, so the inners an *All meets here are terms the program does not
-- contain.  The mix is weighted toward the list because repeated inner
-- refs are what make the diamonds the batcher is checked on, and a fold
-- emits one inner per delivery.
--
-- AND THE FOLD ARM IS CONFINED TO THE LEAF LEVEL, WHICH IS A COST BOUND
-- AND NOT A TASTE.  A fold at observable type whose SOURCE is another
-- such fold is a tower: the inner one hands out an accumulator that
-- deepens per delivery, and the outer one wraps each of those again, so
-- the term the evaluator walks grows as a product rather than a sum.
-- Unconfined, about one depth-4 program in thirty took longer to
-- evaluate than the whole sweep it was part of, which costs the harness
-- its default run.  Held at `d ≡ᵇ 0` the fold's source is a plain
-- burst, which is the shape the witness that made this region
-- interesting has, and no two folds can stack.  The region is still
-- reached — the summary line says how often — so what the confinement
-- drops is towers, not coverage.
genObsAt g u sl d =
  let inners = genB 2 >>=G λ extra → genInners g u sl d (suc (suc extra)) >>=G λ items →
                 pureG (ofˢ items)
  in genW kObs >>=G λ c →
     if c ≡ᵇ 0
     then (if d ≡ᵇ 0
           then (genObsScanFn >>=G λ f → genObsSeed sl >>=G λ z →
                 genExpAt g u sl d >>=G λ e → pureG (scanˢ f z e))
           else inners)
     else inners

-- past the gate: the var is in scope and this subtree plants exactly one
genSpineD w sl zero    = pureG (varˢ (here refl))
genSpineD w sl (suc d) = genW kSpineD >>=G λ c →
  if c ≡ᵇ 0 then pureG (varˢ (here refl))
  else if c ≡ᵇ 1 then (genFn >>=G λ f → genSpineD w sl d >>=G λ e → pureG (mapˢ f e))
  else if c ≡ᵇ 2 then
    (genScanFn >>=G λ f → genNat >>=G λ z → genSpineD w sl d >>=G λ e →
     pureG (scanˢ f (natˢ z) e))
  else if c ≡ᵇ 3 then
    (genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ (mergeᶠ nothing) (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 4 then
    (genB 3 >>=G λ k → genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ (mergeᶠ (just (suc k))) (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 5 then
    (genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ switchᶠ (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 6 then
    (genOp >>=G λ op → genFanFn >>=G λ f → genSpineD w sl d >>=G λ e →
     pureG (flattenˢ op (mapˢ f e)))
  else if c ≡ᵇ 7 then
    (genNat >>=G λ k → genSpineD w sl d >>=G λ e →
     pureG (takeˢ (natˢ (suc k)) e))
  else if c ≡ᵇ 8 then
    (genPredFn >>=G λ f → genSpineD w sl d >>=G λ e → pureG (takeWhileˢ f e))
  else
    (genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ exhaustᶠ (ofˢ (strmˢ e ∷ rest))))

-- before the gate: the binder is guarded, so every route ends in a `deferᵉ`
genSpineG g u sl zero    = pureG (gate (suc g) u (varˢ (here refl)))
genSpineG g u sl (suc d) = genW kSpineG >>=G λ c →
  if c ≡ᵇ 0 then (genSpineD (g + u) sl d >>=G λ b → pureG (gate (suc g) u b))
  else if c ≡ᵇ 1 then (genSpineD (g + u) sl d >>=G λ b → pureG (gate (suc g) u b))
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genSpineG g u sl d >>=G λ e → pureG (mapˢ f e))
  else if c ≡ᵇ 3 then
    (genScanFn >>=G λ f → genNat >>=G λ z → genSpineG g u sl d >>=G λ e →
     pureG (scanˢ f (natˢ z) e))
  else if c ≡ᵇ 4 then
    (genSpineG g u sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ (mergeᶠ nothing) (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 5 then
    (genSpineG g u sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ switchᶠ (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 6 then
    (genOp >>=G λ op → genFanFn >>=G λ f → genSpineG g u sl d >>=G λ e →
     pureG (flattenˢ op (mapˢ f e)))
  else if c ≡ᵇ 7 then
    (genNat >>=G λ k → genSpineG g u sl d >>=G λ e →
     pureG (takeˢ (natˢ (suc k)) e))
  else if c ≡ᵇ 8 then
    (genPredFn >>=G λ f → genSpineG g u sl d >>=G λ e → pureG (takeWhileˢ f e))
  else
    (genSpineG g u sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u sl d (suc extra) >>=G λ rest →
     pureG (flatAllˢ exhaustᶠ (ofˢ (strmˢ e ∷ rest))))

-- the PROGRAM's slot bound is the whole table: a program, unlike a def,
-- sits above every slot and may read any of them
genExp : ℕ → Gen (SExp Γ₂ [] [] [] natᵗ)
genExp d = genExpAt 0 0 2 d

------------------------------------------------------------------------
-- WHICH FORMERS A PROGRAM ACTUALLY CARRIED.  A generator that CAN emit
-- one says nothing about a sweep; each case reports its program's marks
-- and the run's line totals them, so a coverage receipt can name the
-- region it covered instead of the constructors that were added.

-- THE PALETTE, NAMED BY THE TAGS THE TWO TREES ARE PAIRED BY.  A census
-- per INTERESTING REGION is a census whose regions were chosen by whoever
-- last thought about one, which is how this generator came to have no
-- count-changing lane at all — found by reading, and by no check, after
-- sixty thousand programs had certified impl≡spec without once changing
-- an emit's value count.  A census per FORMER cannot have that hole: the
-- walk below is a total match, so a former added to `Exp` owes an arm
-- here, and `scripts/formers.tsv` holds these tags to the ones the
-- decoder and the TypeScript union spell.
data Former : Set where
  fInput fOf fEmpty fTake fMap fScan fFlatten fMu fVar fDefer fMint
    fBatchSync fTakeWhile : Former

formerTag : Former → String
formerTag fInput      = "input"
formerTag fOf         = "of"
formerTag fEmpty      = "empty"
formerTag fTake       = "take"
formerTag fMap        = "map"
formerTag fScan       = "scan"
formerTag fFlatten    = "flatten"
formerTag fMu         = "mu"
formerTag fVar        = "varE"
formerTag fDefer      = "defer"
formerTag fMint       = "mint"
formerTag fBatchSync  = "batchSync"
formerTag fTakeWhile  = "takeWhile"

allFormers : List Former
allFormers = fInput ∷ fOf ∷ fEmpty ∷ fTake ∷ fMap ∷ fScan ∷ fFlatten
           ∷ fMu ∷ fVar ∷ fDefer ∷ fMint ∷ fBatchSync ∷ fTakeWhile ∷ []

formerIx : Former → ℕ
formerIx fInput      = 0
formerIx fOf         = 1
formerIx fEmpty      = 2
formerIx fTake       = 3
formerIx fMap        = 4
formerIx fScan       = 5
formerIx fFlatten    = 6
formerIx fMu         = 7
formerIx fVar        = 8
formerIx fDefer      = 9
formerIx fMint       = 10
formerIx fBatchSync  = 11
formerIx fTakeWhile  = 12

sameFormer : Former → Former → Bool
sameFormer a b = formerIx a ≡ᵇ formerIx b

-- the formers a program carries, and whether any `scanᵉ` re-binds
-- something the run could subscribe
Marks : Set
Marks = List Former × Bool

noMarks : Marks
noMarks = [] , false

one : Former → Marks
one f = (f ∷ []) , false

infixr 5 _⊕_
_⊕_ : Marks → Marks → Marks
(fs , a) ⊕ (gs , b) = (fs ++ᴸ gs) , (a ∨ b)

marksˢ   : ∀ {Δᵍ Δ Θ t} → SExp Γ₂ Δᵍ Δ Θ t → Marks
marksˢᵗ  : ∀ {Δᵍ Δ Θ t} → STm Γ₂ Δᵍ Δ Θ t → Marks
marksˢᵗˢ : ∀ {Δᵍ Δ Θ t} → List (STm Γ₂ Δᵍ Δ Θ t) → Marks

marksˢ (inputˢ i)       = one fInput
marksˢ (ofˢ ts)         = one fOf ⊕ marksˢᵗˢ ts
marksˢ emptyˢ           = one fEmpty
marksˢ (takeˢ c e)      = one fTake ⊕ marksˢᵗ c ⊕ marksˢ e
marksˢ (takeWhileˢ f e) = one fTakeWhile ⊕ marksˢᵗ f ⊕ marksˢ e
-- the second component reads the CARRIED state's type, which is the former's
-- own accumulator: `isData (obs _)` is false, so it fires exactly when the
-- former re-binds something the run could subscribe
marksˢ (mapˢ f e)       = one fMap ⊕ marksˢᵗ f ⊕ marksˢ e
marksˢ (scanˢ {t = t} f z e) =
  one fScan ⊕ ([] , not (isData t)) ⊕ marksˢᵗ f ⊕ marksˢᵗ z ⊕ marksˢ e
-- the author's three flatteners are each one `flattenᵉ` over a `mapᵉ`
marksˢ (flattenˢ _ e)   = one fFlatten ⊕ marksˢ e
marksˢ (μˢ e)           = one fMu ⊕ marksˢ e
marksˢ (varˢ x)         = one fVar
marksˢ (deferˢ e)       = one fDefer ⊕ marksˢ e

marksˢᵗ (varˢᵗ x)     = noMarks
marksˢᵗ unitˢ         = noMarks
marksˢᵗ (boolˢ _)     = noMarks
marksˢᵗ (natˢ _)      = noMarks
marksˢᵗ (pairˢ a b)   = marksˢᵗ a ⊕ marksˢᵗ b
marksˢᵗ (fstˢ p)      = marksˢᵗ p
marksˢᵗ (sndˢ p)      = marksˢᵗ p
marksˢᵗ (inlˢ a)      = marksˢᵗ a
marksˢᵗ (inrˢ a)      = marksˢᵗ a
marksˢᵗ (caseˢ s l r) = marksˢᵗ s ⊕ marksˢᵗ l ⊕ marksˢᵗ r
marksˢᵗ (ifˢ c a b)   = marksˢᵗ c ⊕ marksˢᵗ a ⊕ marksˢᵗ b
marksˢᵗ (primˢ _ a)   = marksˢᵗ a
marksˢᵗ nilˢ          = noMarks
marksˢᵗ (consˢ a bs)  = marksˢᵗ a ⊕ marksˢᵗ bs
marksˢᵗ (foldˢ l z f) = marksˢᵗ l ⊕ marksˢᵗ z ⊕ marksˢᵗ f
marksˢᵗ (strmˢ e)     = marksˢ e

marksˢᵗˢ []       = noMarks
marksˢᵗˢ (y ∷ ys) = marksˢᵗ y ⊕ marksˢᵗˢ ys

-- THE FORMERS ONLY AN ELABORATION MAY WRITE are counted where they
-- are written: in the tree the case's program elaborates to, since no
-- author program can carry one (`SExp.Syntax`).  Only those, because
-- every other former is the author's and is counted above, where a
-- second count off the elaborated tree would double it.
elabMarksᵉ  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Marks
elabMarksᵗ  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → Marks
elabMarksᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → Marks

elabMarksᵉ (input i)      = noMarks
elabMarksᵉ (ofᵉ ts)       = elabMarksᵗˢ ts
elabMarksᵉ emptyᵉ         = noMarks
elabMarksᵉ (takeᵉ c e)    = elabMarksᵗ c ⊕ elabMarksᵉ e
elabMarksᵉ (takeWhileᵉ f e) = elabMarksᵗ f ⊕ elabMarksᵉ e
elabMarksᵉ (batchSyncᵉ e) = one fBatchSync ⊕ elabMarksᵉ e
elabMarksᵉ (mapᵉ f e)     = elabMarksᵗ f ⊕ elabMarksᵉ e
elabMarksᵉ (scanᵉ f z e)  = elabMarksᵗ f ⊕ elabMarksᵗ z ⊕ elabMarksᵉ e
elabMarksᵉ (flattenᵉ _ e) = elabMarksᵉ e
elabMarksᵉ (μᵉ e)         = elabMarksᵉ e
elabMarksᵉ (varᵉ x)       = noMarks
elabMarksᵉ (deferᵉ e)     = elabMarksᵉ e
elabMarksᵉ (mintᵉ e)      = one fMint ⊕ elabMarksᵉ e

elabMarksᵗ (varᵗ x)      = noMarks
elabMarksᵗ unit̂          = noMarks
elabMarksᵗ (bool̂ _)      = noMarks
elabMarksᵗ (nat̂ _)       = noMarks
elabMarksᵗ (foldᵗ l z f) = elabMarksᵗ l ⊕ elabMarksᵗ z ⊕ elabMarksᵗ f
elabMarksᵗ nilᵗ          = noMarks
elabMarksᵗ (consᵗ a bs)  = elabMarksᵗ a ⊕ elabMarksᵗ bs
elabMarksᵗ (pairᵗ a b)   = elabMarksᵗ a ⊕ elabMarksᵗ b
elabMarksᵗ (fstᵗ p)      = elabMarksᵗ p
elabMarksᵗ (sndᵗ p)      = elabMarksᵗ p
elabMarksᵗ (inlᵗ a)      = elabMarksᵗ a
elabMarksᵗ (inrᵗ a)      = elabMarksᵗ a
elabMarksᵗ (caseᵗ s l r) = elabMarksᵗ s ⊕ elabMarksᵗ l ⊕ elabMarksᵗ r
elabMarksᵗ (ifᵗ c a b)   = elabMarksᵗ c ⊕ elabMarksᵗ a ⊕ elabMarksᵗ b
elabMarksᵗ (primᵗ _ a)   = elabMarksᵗ a
elabMarksᵗ (strmᵗ e)     = elabMarksᵉ e

elabMarksᵗˢ []       = noMarks
elabMarksᵗˢ (y ∷ ys) = elabMarksᵗ y ⊕ elabMarksᵗˢ ys

------------------------------------------------------------------------
-- a compact dump of both sides' batches (for failure reports)

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

-- the batches, bracketed, in order
showBatches : List (List ℕ) → String
showBatches []       = ""
showBatches (b ∷ bs) = showVals b ++ " " ++ showBatches bs

-- same, for the RAW canonical stream (values are bare ℕ)
private
  showEventR : InstEvent ℕ → String
  showEventR (init s)    = "i" ++ show s
  showEventR (value v)   = "v" ++ show v
  showEventR (close s _) = "c" ++ show s
  showEventR (handoff s) = "h" ++ show s
  showEventR complete    = "F"

  showEventsR : List (InstEvent ℕ) → String
  showEventsR []       = ""
  showEventsR (e ∷ es) = showEventR e ++ " " ++ showEventsR es

  showEmitR : InstEmit ℕ → String
  showEmitR (es at i from s as _) = "@" ++ show i ++ "{" ++ showEventsR es ++ "}"

showStream : List (InstEmit ℕ) → String
showStream []       = "·"
showStream (e ∷ es) = showEmitR e ++ " " ++ showStream es

------------------------------------------------------------------------
-- render a generated program back to Agda source (a paste-ready block for
-- the Unit-Test cache). Faithful over every constructor rather than over
-- the fragment the generator happens to emit, and there is no placeholder
-- arm: a lane added to the generator would otherwise print a row nobody
-- can paste, and the only run that would reveal it is one that already
-- found a counterexample.

showFin : ∀ {n} → Fin n → String
showFin zero    = "zero"
showFin (suc i) = "(suc " ++ showFin i ++ ")"

showPrim : ∀ {s t} → PrimOp s t → String
showPrim add  = "add"
showPrim sub  = "sub"
showPrim mul  = "mul"
showPrim eqᵖ  = "eqᵖ"
showPrim ltᵖ  = "ltᵖ"
showPrim eqᵘ  = "eqᵘ"
showPrim notᵖ = "notᵖ"

-- the limit prints as the `Maybe ℕ` it IS, not as the ∞ a reader would
-- prefer: a witness is printed to be PASTED, and the corpus is Agda
showFlatOp : FlatOp → String
showFlatOp (mergeᶠ nothing)  = "(mergeᶠ nothing)"
showFlatOp (mergeᶠ (just k)) = "(mergeᶠ (just " ++ show k ++ "))"
showFlatOp switchᶠ           = "switchᶠ"
showFlatOp exhaustᶠ          = "exhaustᶠ"

showSExp : ∀ {Δᵍ Δ Θ t} → SExp Γ₂ Δᵍ Δ Θ t → String
showSTm  : ∀ {Δᵍ Δ Θ t} → STm Γ₂ Δᵍ Δ Θ t → String
showFlat : ∀ {Δᵍ Δ Θ u} → FlatOp → SExp Γ₂ Δᵍ Δ Θ u → String

showSTmList : ∀ {Δᵍ Δ Θ t} → List (STm Γ₂ Δᵍ Δ Θ t) → String
showSTmList []       = "[]"
showSTmList (x ∷ xs) = showSTm x ++ " ∷ " ++ showSTmList xs

-- a variable is rendered by its de Bruijn PATH, not just as "here": a
-- witness with nested binders that cannot say WHICH binder a variable
-- belongs to is not reproducible — which is the only reason witnesses
-- are printed at all
showIx : ∀ {t} {Θ : List Ty} → t ∈ Θ → String
showIx (here refl) = "(here refl)"
showIx (there x)   = "(there " ++ showIx x ++ ")"

showSTm (varˢᵗ x)      = "(varˢᵗ " ++ showIx x ++ ")"
showSTm unitˢ          = "unitˢ"
showSTm (boolˢ b)      = "(boolˢ " ++ (if b then "true" else "false") ++ ")"
showSTm (natˢ n)       = "(natˢ " ++ show n ++ ")"
showSTm (pairˢ a b)    = "(pairˢ " ++ showSTm a ++ " " ++ showSTm b ++ ")"
showSTm (fstˢ p)       = "(fstˢ " ++ showSTm p ++ ")"
showSTm (sndˢ p)       = "(sndˢ " ++ showSTm p ++ ")"
showSTm (inlˢ a)       = "(inlˢ " ++ showSTm a ++ ")"
showSTm (inrˢ a)       = "(inrˢ " ++ showSTm a ++ ")"
showSTm (caseˢ s l r)  =
  "(caseˢ " ++ showSTm s ++ " " ++ showSTm l ++ " " ++ showSTm r ++ ")"
showSTm (ifˢ c a b)    =
  "(ifˢ " ++ showSTm c ++ " " ++ showSTm a ++ " " ++ showSTm b ++ ")"
showSTm (primˢ op a)   = "(primˢ " ++ showPrim op ++ " " ++ showSTm a ++ ")"
showSTm nilˢ           = "nilˢ"
showSTm (consˢ a bs)   = "(consˢ " ++ showSTm a ++ " " ++ showSTm bs ++ ")"
showSTm (foldˢ l z f)  =
  "(foldˢ " ++ showSTm l ++ " " ++ showSTm z ++ " " ++ showSTm f ++ ")"
showSTm (strmˢ e)      = "(strmˢ " ++ showSExp e ++ ")"

showSExp (inputˢ i)      = "(inputˢ " ++ showFin i ++ ")"
showSExp (ofˢ items)     = "(ofˢ (" ++ showSTmList items ++ "))"
showSExp emptyˢ          = "emptyˢ"
showSExp (takeˢ n e)     = "(takeˢ " ++ showSTm n ++ " " ++ showSExp e ++ ")"
showSExp (takeWhileˢ f e) = "(takeWhileˢ " ++ showSTm f ++ " " ++ showSExp e ++ ")"
showSExp (mapˢ f e)      = "(mapˢ " ++ showSTm f ++ " " ++ showSExp e ++ ")"
showSExp (scanˢ f z e)   =
  "(scanˢ " ++ showSTm f ++ " " ++ showSTm z ++ " " ++ showSExp e ++ ")"
showSExp (flattenˢ op s) = showFlat op s
showSExp (μˢ e)          = "(μˢ " ++ showSExp e ++ ")"
showSExp (varˢ x)        = "(varˢ " ++ showIx x ++ ")"
showSExp (deferˢ e)      = "(deferˢ " ++ showSExp e ++ ")"

-- rxjs's named flatteners print as the corpus's `flatAllˢ`, which is
-- what they expand to, and every other flatten prints as itself.  It
-- takes its argument at ANY type because printing reads none: at the
-- element type an `inputˢ`'s lookup cannot be unified against a pair.
showFlat op (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (varˢᵗ (here refl)))) s) =
  "(flatAllˢ " ++ showFlatOp op ++ " " ++ showSExp s ++ ")"
showFlat op s = "(flattenˢ " ++ showFlatOp op ++ " " ++ showSExp s ++ ")"

------------------------------------------------------------------------
-- one case, a run, and reporting

-- THE FUEL IS AN EXPONENT FOR SOME PROGRAMS, WHICH IS WHY THE SWEEP HAS
-- TO BE BOUNDED FROM OUTSIDE.  A guarded fixpoint under an unbounded
-- merging flattener with no `takeᵉ` above it emits once per unit of fuel; one
-- whose step hands back MORE elements than it was given doubles instead,
-- and the corpus contains such programs because nothing in the generator
-- declines to draw one.  The cost is inside `evaluate↓` rather than in
-- the stream it returns, the drain forcing each cascade whole, so no
-- budget readable from here can decline the case after the fact — a cap
-- on the stream's length was tried and buys nothing, since the length is
-- reached only by paying for it.  `scripts/gen-unit-tests.sh` therefore
-- bounds a SEED in wall clock and reports the ones it could not run.
--
-- AND NOTHING CUTS THE RUN FROM INSIDE, because every check is a
-- statement's own sides at the drawn program, and a `takeᵉ` above it is
-- a different program.  An author's `takeˢ` above it IS an instance, and
-- was measured: it buys nothing, since the cases that outrun a sweep
-- spend it inside the subscribe frame, at fuel 1, before any value.  So
-- the cap is a WALL CLOCK PER CASE (`CASE`, stdin's ninth number): a case
-- that outruns it is reported as a `timeout`, with its paste row, and the
-- sweep goes on to the next.
FUEL : ℕ
FUEL = 30

CASE : ℕ
CASE = 10

-- A PASTE-READY BUG-CACHE ROW: the block IS a row of
-- `CLI.Unit-Test.cases`, trailing `∷` included, so the script
-- that appends it neither builds nor parses Agda.  The name is written
-- `"?"` rather than left blank, because a block pasted by hand has to
-- typecheck as it stands; the script substitutes the seed.  Line 2 --
-- the program -- is the dedup key.
--
-- ONE SHAPE FOR EVERY CHECK, and that is what makes the key work: the
-- cache holds every row to every statement, so a program that fails
-- any one wants the same row, and a program that fails several dedups
-- to it instead of being cached twice.
--
-- THE SLOT TABLE IS RENDERED RATHER THAN NAMED, because the sweep
-- DRAWS it: a row naming a constant table would be a DIFFERENT run
-- from the one that failed.  Both definitions are printed through the
-- same `showSExp` the program goes through, and `mkSlots` is in the
-- prelude so the corpus can see the name.
--
-- AN UNDECIDED CASE PRINTS THE SAME ROW UNDER ITS OWN MARKERS, because
-- the script appends every `PASTE` block to the corpus and the corpus
-- holds known counterexamples only: a case past its clock is not one
-- (Anthony), and a row of it would be red until the evaluator got
-- faster rather than until anything was fixed.
rowIn : String → ℕ → SExp Γ₂ [] [] [] natᵗ
      → Script → SExp Γ₂ [] [] [] natᵗ → String
rowIn m f e d₀ d₁ =
  "\n-- <<<" ++ m ++ "\n  cached \"?\" " ++ show f ++ "\n          "
       ++ showSExp e ++ "\n          (mkSlots (" ++ showScript d₀ ++ ")\n"
       ++ "                   (" ++ showSExp d₁ ++ ")) ∷\n-- " ++ m ++ ">>>\n"

pasteRow : ℕ → SExp Γ₂ [] [] [] natᵗ
         → Script → SExp Γ₂ [] [] [] natᵗ → String
pasteRow = rowIn "PASTE"

-- what a case was drawn from: the program and its slot table
Drawn : Set
Drawn = SExp Γ₂ [] [] [] natᵗ × Script × SExp Γ₂ [] [] [] natᵗ

showPair : {A : Set} → (A → String) → A × A → String
showPair f (l , r) = "lhs = " ++ f l ++ "\n    rhs = " ++ f r

showStamps : List (ℕ × List ℕ) → String
showStamps []            = ""
showStamps ((i , p) ∷ ps) = "@" ++ show i ++ showVals p ++ " " ++ showStamps ps

-- ONE STATEMENT ON ONE CASE: whether it holds, and its sides rendered.
-- EACH TAKES ITS SIDES AS ONE ARGUMENT.  A `let` is substituted at
-- compile time, so a name used in the verdict and again in the report
-- is two evaluations; a function argument is one shared thunk.
pairᴸ : List ℕ × List ℕ → Bool × String
pairᴸ (l , r) = eqListℕ l r , showPair showVals (l , r)

-- the plain run between the joined runs at the fuel and one past it
sandwichᴸ : List ℕ × List ℕ × List ℕ → Bool × String
sandwichᴸ (l , p , l′) =
  prefixListℕ l p ∧ prefixListℕ p l′ ,
  "joined = " ++ showVals l ++ "\n    plain = " ++ showVals p ++ "\n    joined at one more fuel = " ++ showVals l′

pairᴮ : List (List ℕ) × List (List ℕ) → Bool × String
pairᴮ (l , r) = eqBatches l r , showPair showBatches (l , r)

pairsᵀ : List (ℕ × List ℕ) → Bool × String
pairsᵀ ps = allPairsᵇ ps , "stamped = " ++ showStamps ps

namesᵀ : List ℕ × List (List ℕ) → Bool × String
namesᵀ (ar , ps) = namesᵇ (ar , ps) ,
  "@arrival packet = " ++ showStamps (zipWith (λ a q → a , q) ar ps)
  ++ "\n    " ++ show (length ar) ++ " arrivals, " ++ show (length ps) ++ " packets"

showItem : Item → String
showItem (p , inj₁ a) = showVals p ++ ":" ++ show a
showItem (p , inj₂ _) = showVals p ++ ":END"

-- a program's two runs cut at their arrivals, one slice to a bracket
showArr : {A : Set} → (A → String) → Arr A → String
showArr sh (is , dry , ps , ik , pk , cl) =
  "impl slices = " ++ commaJoin (map (λ i → "[" ++ commaJoin (map (λ p → "@" ++ show (proj₁ p) ++ " " ++ sh (proj₂ p)) i) ++ "]") is) ++
  (if dry then " (queue dry)" else " (at the fuel cap)") ++
  "\n    plain slices = " ++ commaJoin (map (λ p → "[" ++ commaJoin (map sh p) ++ "]") ps) ++
  "\n    impl keys = " ++ showKeys ik ++ "\n    plain keys = " ++ showKeys pk ++
  "\n    impl clocks = " ++ commaJoin (map show cl)
  where
    showKeys : List Key → String
    showKeys ks = commaJoin (map (λ k → show (proj₁ k) ++ "/" ++ show (proj₂ k)) ks)

-- A STATEMENT IS DECIDED IN HALVES WHERE ITS RUNS ARE INDEPENDENT: what
-- reads the program's own run, and what reads its timed translation's.
-- The timed impl run can outlast any clock where the program's own run
-- takes a tenth of a second, and under one clock a failing untimed half
-- was reported as undecided, since its report prints both runs.  So a
-- sweep decides every cheap half first and every dear one after,
-- stopping at the first past its clock: a slow case still costs one
-- clock, and only what reads the slow run goes undecided.
halves : Case → Statement → List (Bool × String) × List (Bool × String)
halves c left-to-rightˢ  = sandwichᴸ (ltrSides c) ∷ [] , []
halves c timing-correctˢ = [] , pairsᵀ (stampsOf c) ∷ []
halves c batchableˢ      = pairᴮ (batchableSides c) ∷ [] , []
halves c timed-faithfulˢ = [] , pairᴸ (faithfulSides c) ∷ []
halves c simulationˢ     =
  (simᵇ _≡ᵇ_ (arrPlain c) , showArr show (arrPlain c)) ∷ []
  , (simᵇ eqItem (arrTimed c) , "timed: " ++ showArr showItem (arrTimed c)) ∷ []
halves c arrival-runsˢ   =
  (lockstepᵇ _≡ᵇ_ (arrPlain c) , showArr show (arrPlain c)) ∷ []
  , (lockstepᵇ eqItem (arrTimed c) , "timed: " ++ showArr showItem (arrTimed c)) ∷ []
halves c batched-sandwichˢ = sandwichᴸ (bsSides c) ∷ [] , []
halves c packets-name-arrivalsˢ = [] , namesᵀ (namingSides c) ∷ []
halves c storeˢ          = storeSides (Case.fuel c) (Case.prog c) (Case.slots c) ∷ [] , []
halves c same-clockˢ     =
  (sameClockᵇ (arrPlain c) , showArr show (arrPlain c)) ∷ []
  , (sameClockᵇ (arrTimed c) , "timed: " ++ showArr showItem (arrTimed c)) ∷ []

joinᴴ : List (Bool × String) → Bool × String
joinᴴ []             = true , ""
joinᴴ (h ∷ [])       = h
joinᴴ ((b , r) ∷ hs) with joinᴴ hs
... | b′ , r′ = b ∧ b′ , r ++ "\n    " ++ r′

decide : Case → Statement → Bool × String
decide c s = joinᴴ (proj₁ (halves c s) ++ᴸ proj₂ (halves c s))

-- a report counts statements in `Main`'s order
indexOf : Statement → ℕ
indexOf left-to-rightˢ  = 0
indexOf timing-correctˢ = 1
indexOf batchableˢ      = 2
indexOf timed-faithfulˢ = 3
indexOf simulationˢ     = 4
indexOf arrival-runsˢ = 5
indexOf batched-sandwichˢ = 6
indexOf packets-name-arrivalsˢ = 7
indexOf same-clockˢ = 8
indexOf storeˢ = 9

-- one count per former, in `allFormers` order, plus the obs-fold count,
-- the count of cases bearing on contiguity and of those holding values
-- back at the fuel
Tally : Set
Tally = List ℕ × ℕ × ℕ × ℕ × ℕ

zeroTally : Tally
zeroTally = map (λ _ → 0) allFormers , 0 , 0 , 0 , 0

carries : Former → List Former → Bool
carries f []       = false
carries f (g ∷ gs) = sameFormer f g ∨ carries f gs

bumpEach : List Former → List Former → List ℕ → List ℕ
bumpEach fs []       cs       = cs
bumpEach fs (g ∷ gs) []       = []
bumpEach fs (g ∷ gs) (c ∷ cs) =
  (if carries g fs then suc c else c) ∷ bumpEach fs gs cs

-- a case's marks, whether it bears on contiguity, whether its batcher
-- holds values back at the fuel, whether its values group, and whether
-- an impl arrival matches no plain one
Seen : Set
Seen = Marks × Bool × Bool × Bool × Bool

bump : Seen → Tally → Tally
bump ((fs , o) , b , h , g , _) (cs , p , q , r , u) =
  bumpEach fs allFormers cs , (if o then suc p else p) , (if b then suc q else q)
  , (if h then suc r else r) , (if g then suc u else u)

-- ONE CHECK PER STATEMENT, so a report says which claim a program
-- breaks rather than that it breaks one.
check : ℕ → Bool → String → List (ℕ × String)
check k true  r = []
check k false r = (k , r) ∷ []

judgeOf : ℕ → Drawn → Statement → Bool × String → List (ℕ × String)
judgeOf f (e , d₀ , d₁) s (b , body) =
  check (indexOf s) b ("  " ++ statementName s ++ "\n    " ++ body ++ pasteRow f e d₀ d₁)


-- forcing a case's reports forces every verdict, since `check` matches
-- on each before it knows whether there is a report
forced : List (ℕ × String) → ℕ
forced []             = 0
forced ((k , r) ∷ rs) = k + lengthˢ r + forced rs

-- a case past its wall clock: one report of its own kind, after the
-- statements', carrying the row that reproduces it
TIMEOUT : ℕ
TIMEOUT = 10

timedOut : ℕ → ℕ → Drawn → List (ℕ × String)
timedOut s f (e , d₀ , d₁) =
  (TIMEOUT , "  timeout\n    no verdict within " ++ show s ++ "s" ++ rowIn "UNDECIDED" f e d₀ d₁) ∷ []

-- the reports are an ARGUMENT, so forcing them and returning them share
-- one evaluation
boundedBy : ℕ → List (ℕ × String) → List (ℕ × String) → List (ℕ × String)
boundedBy s rs d = within s (forced rs) rs d

-- every statement's cheap halves, then every statement's dear ones
ordered : Case → List Statement → List (Statement × (Bool × String))
ordered c ss = concatMap (λ s → map (s ,_) (proj₁ (halves c s))) ss
            ++ᴸ concatMap (λ s → map (s ,_) (proj₂ (halves c s))) ss

ranOut : List (ℕ × String) → Bool
ranOut []             = false
ranOut ((k , _) ∷ rs) = (k ≡ᵇ TIMEOUT) ∨ ranOut rs

boundedEach : ℕ → ℕ → Drawn → List (Statement × (Bool × String)) → List (ℕ × String)
boundedEach s f x []              = []
boundedEach s f x ((st , h) ∷ hs) with boundedBy s (judgeOf f x st h) (timedOut s f x)
... | r = if ranOut r then r else r ++ᴸ boundedEach s f x hs

bounded : ℕ → ℕ → Drawn → List Statement → List (ℕ × String)
bounded s f (e , d₀ , d₁) ss =
  boundedEach s f (e , d₀ , d₁) (ordered (cached "?" f e (mkSlots d₀ d₁)) ss)

-- A CASE BEARS ON CONTIGUITY WHEN TWO PLAIN ARRIVALS DELIVER VALUES:
-- only then can one impl arrival carry both, or a run interleave them,
-- so a green case that does not is a row that could not have failed.
-- Read off the untimed program's plain run under the case's clock, and
-- past it counted as bearing on nothing.
valued : {A : Set} → List (List A) → ℕ
valued []             = 0
valued ([] ∷ ps)      = valued ps
valued ((_ ∷ _) ∷ ps) = suc (valued ps)

bearsOn : ℕ → ℕ → Bool
bearsOn s n = within s n (2 ≤ᵇ n) false

bears : ℕ → ℕ → Drawn → Bool
bears s f (e , d₀ , d₁) = bearsOn s (valued (proj₁ (proj₂ (proj₂ (arrPlain (cached "?" f e (mkSlots d₀ d₁)))))))

-- A CASE TESTS THE ONE-PAST SLACK WHEN THE BATCHER HOLDS VALUES BACK AT
-- ITS FUEL: the joined run at the searched witness shorter than the
-- elaborated run's values, so only the joined run at one more fuel can
-- cover it.  That is `batched-sandwich`'s second prefix, which says
-- nothing anywhere else, read off the leaf's own sides rather than
-- `left-to-right`'s.  Past the case's clock it counts as holding nothing.
holdsBack : ℕ → List ℕ × List ℕ × List ℕ → Bool
holdsBack s (l , p , _) with length p ∸ length l
... | n = within s n (1 ≤ᵇ n) false

slack : ℕ → ℕ → Drawn → Bool
slack s f (e , d₀ , d₁) = holdsBack s (bsSides (cached "?" f e (mkSlots d₀ d₁)))

-- A CASE BEARS ON `batchable` WHEN ITS VALUES GROUP: the grouping the
-- statement compares against holds a batch of two values or two batches
-- holding any, so a batcher that split an instant or merged two could
-- answer differently.  A case short of that can still fail by a value
-- the batcher lost or invented, which `left-to-right` decides too.
-- Read off the grouped side under the case's clock, and past it counted
-- as grouping nothing.
groupsOn : List (List ℕ) → Bool
groupsOn bs = (2 ≤ᵇ valued bs) ∨ any (λ b → 2 ≤ᵇ length b) bs

groups : ℕ → ℕ → Drawn → Bool
groups s f (e , d₀ , d₁) with proj₂ (batchableSides (cached "?" f e (mkSlots d₀ d₁)))
... | bs = within s (length (concat bs)) (groupsOn bs) false

-- A CASE'S CLOCKS PART WHEN SOME IMPL ARRIVAL'S KEY IS NOT THE PLAIN
-- ARRIVAL'S at the same position.  Read only where `same-clock` is being
-- decided, since its timed half is the dear run; past the case's clock
-- it counts as parting nothing.
isClocked : Statement → Bool
isClocked same-clockˢ = true
isClocked _           = false

splits : List Statement → ℕ → ℕ → Drawn → Bool
splits ss s f (e , d₀ , d₁) with any isClocked ss
... | false = false
... | true  with cached "?" f e (mkSlots d₀ d₁)
...   | c with sameClockᵇ (arrPlain c) ∧ sameClockᵇ (arrTimed c)
...     | x = within s (if x then 0 else 1) (not x) false

-- A SWEEP MAY DECIDE ONLY THE CASES THAT BEAR.  Whether one does is
-- read before any statement is, so a sweep aimed at contiguity spends
-- its clocks on cases that could fail it; one that does not bear is
-- drawn, counted in the census and left undecided-by-choice.
judged : Bool → List Statement → ℕ → ℕ → Marks → Drawn → Seen × List (ℕ × String)
judged ob ss f s m x with bears s f x
... | b = (m , b , slack s f x , groups s f x , splits ss s f x) , (if ob ∧ not b then [] else bounded s f x ss)

-- ONE CASE IS ONE ACCEPTED DRAW.  A restriction's `reach` is the one
-- filter, and it is spent HERE so that every route naming a case by its
-- index -- the sweep, `skipN`, `showAt`, `runAt`, `sideAt` -- spends the
-- same draws on it; the flag says whether the last one met it.
drawOnce : ℕ → Gen (Marks × Drawn)
drawOnce d = genExp d >>=G λ e → genSlots >>=G λ ds →
  pureG (marksˢ e ⊕ elabMarksᵉ (elaborateImpl (κOf (proj₁ ds)) e) , e , proj₁ ds , proj₂ ds)

carriesTag : List Former → List ℕ → Bool
carriesTag fs t = any (λ g → eqListℕ (map toℕ (toList (formerTag g))) t) fs

reaches : Draw → Marks → Bool
reaches W m = all (carriesTag (proj₁ m)) (Draw.reach W)

drawFor : ℕ → ℕ → Gen (Bool × Marks × Drawn)
drawFor zero    d = askG >>=G λ W → drawOnce d >>=G λ x → pureG (reaches W (proj₁ x) , x)
drawFor (suc k) d = askG >>=G λ W → drawOnce d >>=G λ x →
  if reaches W (proj₁ x) then pureG (true , x) else drawFor k d

drawCase : ℕ → Gen (Bool × Marks × Drawn)
drawCase d = askG >>=G λ W → drawFor (Draw.tries W ∸ 1) d

-- AN UNMET REACH IS UNDECIDED, NOT RUN: the case is not in the region the
-- sweep was aimed at, so no statement is asked of it
unreached : ℕ → ℕ → Marks → Drawn → Seen × List (ℕ × String)
unreached f n m (e , d₀ , d₁) =
  (m , false , false , false , false) ,
  (TIMEOUT , "  unreached\n    no draw in " ++ show n ++ " tries carried every former the draw must reach"
             ++ rowIn "UNDECIDED" f e d₀ d₁) ∷ []

oneCase : Bool → List Statement → ℕ → ℕ → ℕ → Gen (Seen × List (ℕ × String))
-- THE DRAWN TREE IS WHAT IS COUNTED, PRINTED AND RUN.  Every check reads
-- the statement's sides at exactly the program a cached row names.
oneCase ob ss f s d = askG >>=G λ W → drawCase d >>=G λ where
  (true  , m , x) → pureG (judged ob ss f s m x)
  (false , m , x) → pureG (unreached f (Draw.tries W) m x)

-- every case drawn, in generation order, its reports still unforced:
-- drawing is cheap and upstream of every run, so the list is whole
-- before the first case is run
casesN : Bool → List Statement → ℕ → ℕ → ℕ → ℕ → Gen (List (Seen × List (ℕ × String)))
casesN ob ss f s zero    d = pureG []
casesN ob ss f s (suc k) d =
  oneCase ob ss f s d >>=G λ r → casesN ob ss f s k d >>=G λ rs → pureG (r ∷ rs)

-- EVERY failing case's reports, in generation order, and which recursion
-- constructors the corpus actually reached
joinT : Seen × List (ℕ × String) → Tally × List (ℕ × String) → Tally × List (ℕ × String)
joinT r acc = bump (proj₁ r) (proj₁ acc) , proj₂ r ++ᴸ proj₂ acc

tallyOf : List (Seen × List (ℕ × String)) → Tally × List (ℕ × String)
tallyOf []       = zeroTally , []
tallyOf (r ∷ rs) = joinT r (tallyOf rs)

------------------------------------------------------------------------
-- stdin parsing: "SEED [RUNS] [DEPTH] [SHOW-AT] [RUN-AT] [SIDE] [FUEL] [STATEMENT] [CASE] [BEARING] [SHRINK]"

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

-- every failing case's paste block, concatenated (each is self-delimited
-- by its own <<<PASTE / PASTE>>> markers, so gen-unit-tests.sh can split
-- them); "(all agree)" when the run turned up nothing
-- the census, on its own line and in `<tag> <count>` pairs: a sweep is a
-- run of many seeds, so the verdict on whether a former was reached AT
-- ALL belongs to the caller summing these, not to any one run
censusPairs : List Former → List ℕ → List String
censusPairs (f ∷ gs) (c ∷ cs) = formerTag f ∷ " " ∷ show c ∷ " " ∷ censusPairs gs cs
censusPairs _        _        = []

-- THE FIRST FEW, THEN A COUNT: a dev loop reads the top of the list,
-- and printing every report costs as much as finding them
ofKind : ℕ → List (ℕ × String) → List String
ofKind k []             = []
ofKind k ((j , r) ∷ fs) = if j ≡ᵇ k then r ∷ ofKind k fs else ofKind k fs

kinds : List String
kinds = map statementName (statements ++ᴸ same-clockˢ ∷ storeˢ ∷ []) ++ᴸ "timeout" ∷ []

counts : ℕ → List String → List (ℕ × String) → List String
counts k []       fs = []
counts k (t ∷ ts) fs = t ∷ " " ∷ show (length (ofKind k fs)) ∷ " " ∷ counts (suc k) ts fs

samples : ℕ → List (ℕ × String) → String
samples k fs = concatStr (take 2 (ofKind k fs))

-- A TIMEOUT IS UNDECIDED, NEVER A FAILURE (Anthony).  Any wall clock
-- has a case past it, so a clock cannot be what fails a sweep; what
-- fails one is a statement that answered and disagreed.  The timeouts
-- are still counted and their rows still printed, since a case nobody
-- has decided is where an undecided counterexample would be.
decided : List (ℕ × String) → List (ℕ × String)
decided []             = []
decided ((k , r) ∷ fs) = if k ≡ᵇ TIMEOUT then decided fs else (k , r) ∷ decided fs

agreeing : List (ℕ × String) → String
agreeing []      = "  (all agree)\n"
agreeing (_ ∷ _) = ""

dumpFails : List (ℕ × String) → String
dumpFails [] = "  (all agree)\n"
dumpFails fs = agreeing (decided fs) ++ concatStr (counts 0 kinds fs) ++ "\n"
  ++ samples 0 fs ++ samples 1 fs ++ samples 2 fs ++ samples 3 fs ++ samples 4 fs ++ samples 5 fs ++ samples 6 fs ++ samples 7 fs ++ samples 8 fs ++ samples 9 fs ++ samples TIMEOUT fs

-- ADVANCE THE GENERATOR WITHOUT RUNNING ANYTHING, so that a case which
-- costs more than the whole sweep it belongs to can still be READ.  Such
-- a case is invisible to every other route the harness has: the failure
-- report is what prints a program, and the run that would print this one
-- is the run that does not finish.  Skipping is exact rather than
-- approximate because generation is UPSTREAM of evaluation and consumes
-- the same randomness whether or not the program is then run -- so case
-- N reached this way is the same program case N is in a full sweep.
--
-- IT DRAWS THE SLOT TABLE TOO, AND MUST.  `oneCase` draws a program
-- and then a telescope; a skip that drew only the program would fall
-- one table out of phase per case, and every index after the first
-- would name a different run than the sweep did.  That is the whole
-- load-bearing claim of this function, so the two draws are kept in
-- step by construction.
skipN : ℕ → ℕ → Gen ℕ
skipN zero    d = pureG 0
skipN (suc k) d = drawCase d >>=G λ _ → skipN k d

-- the paste row of ONE case, named by its 1-based index
showAt : ℕ → ℕ → ℕ → Gen String
showAt f n d = skipN (n ∸ 1) d >>=G λ _ →
  drawCase d >>=G λ where
    (_ , _ , e , d₀ , d₁) → pureG (pasteRow f e d₀ d₁)

-- RUN ONE CASE, named the same way, so a case that hangs a sweep can be
-- timed and re-run alone rather than by bisecting the count
runAt : List Statement → ℕ → ℕ → ℕ → ℕ → Gen (Seen × List (ℕ × String))
runAt ss f s n d = skipN (n ∸ 1) d >>=G λ _ → oneCase false ss f s d

-- SHRINKING IS DONE ON THE DRAWS, NOT ON THE TREE.  A case is a function
-- of the randomness it consumes, so deleting, zeroing or halving that
-- prefix and drawing again is a shrink for every statement and every
-- restriction at once, and the program it lands on is well-typed because
-- the generator drew it.  A low draw picks an early arm and the early arms
-- are the leaves, so the search runs downhill.  A candidate is RUN only
-- when the program it draws prints strictly shorter (or as long over a
-- smaller prefix) than the incumbent, which is what bounds the search;
-- `n` caps the runs.
module Shrink (ss : List Statement) (f s d : ℕ) (W : Draw) (rest : List ℕ) where
  runOn : List ℕ → Seen × List (ℕ × String)
  runOn p = proj₁ (oneCase false ss f s d W (p ++ᴸ rest))

  failsOn : List ℕ → Bool
  failsOn p with decided (proj₂ (runOn p))
  ... | []    = false
  ... | _ ∷ _ = true

  size : List ℕ → ℕ
  size p with proj₁ (drawCase d W (p ++ᴸ rest))
  ... | (_ , _ , e , d₀ , d₁) = lengthˢ (pasteRow f e d₀ d₁)

  below : ℕ → List ℕ → List ℕ → Bool
  below sz p c = (suc (size c) ≤ᵇ sz) ∨ ((size c ≡ᵇ sz) ∧ (suc (sumℕ c) ≤ᵇ sumℕ p))

  setAt : ℕ → ℕ → List ℕ → List ℕ
  setAt i v xs = take i xs ++ᴸ (v ∷ drop (suc i) xs)

  nth : ℕ → List ℕ → ℕ
  nth i xs with drop i xs
  ... | []    = 0
  ... | x ∷ _ = x

  candidates : List ℕ → List (List ℕ)
  candidates p =
    concatMap (λ k → map (λ i → take i p ++ᴸ drop (i + k) p) (upTo (length p))) (8 ∷ 4 ∷ 2 ∷ 1 ∷ [])
    ++ᴸ map (λ i → setAt i 0 p) (upTo (length p))
    ++ᴸ map (λ i → setAt i ⌊ nth i p /2⌋ p) (upTo (length p))

  firstFail : ℕ → ℕ → List ℕ → List (List ℕ) → ℕ × List ℕ
  firstFail n       sz p []       = n , []
  firstFail zero    sz p (_ ∷ _)  = 0 , []
  firstFail (suc n) sz p (c ∷ cs) =
    if below sz p c
    then (if failsOn c then (n , c) else firstFail n sz p cs)
    else firstFail (suc n) sz p cs

  -- the passes are bounded by the run budget, which each one spends
  loop : ℕ → ℕ → List ℕ → ℕ × List ℕ
  loop zero    n p = n , p
  loop (suc k) n p with firstFail n (size p) p (candidates p)
  ... | n′ , []        = n′ , p
  ... | n′ , c@(_ ∷ _) = loop k n′ c

-- SHRINK ONE CASE, named as `runAt` names it: the smallest failing draw
-- the budget found, its reports with the paste row of the program it
-- draws, and how far it came
shrinkAt : List Statement → ℕ → ℕ → ℕ → ℕ → ℕ → Draw → List ℕ → String
shrinkAt ss f s n d budget W rs₀ with proj₂ (skipN (n ∸ 1) d W rs₀)
... | rs with length rs ∸ length (proj₂ (drawCase d W rs))
...   | used with Shrink.failsOn ss f s d W (drop used rs) (take used rs)
...     | false = "case " ++ show n ++ " does not fail; nothing to shrink\n"
...     | true  with Shrink.loop ss f s d W (drop used rs) budget budget (take used rs)
...       | left , p =
  "shrunk case " ++ show n ++ " in " ++ show (budget ∸ left) ++ " runs, printed size "
  ++ show (Shrink.size ss f s d W (drop used rs) (take used rs)) ++ " → "
  ++ show (Shrink.size ss f s d W (drop used rs) p) ++ "\n"
  ++ dumpFails (proj₂ (Shrink.runOn ss f s d W (drop used rs) p))

-- THE STATEMENT A NUMBER NAMES, in `Main`'s order, the simulation
-- fifth and its leaf sixth, the two assembled top lines' leaves seventh
-- and eighth, the two invariants ninth and tenth; zero is all the
-- statements
selected : ℕ → List Statement
selected (suc zero)                   = left-to-rightˢ ∷ []
selected (suc (suc zero))             = timing-correctˢ ∷ []
selected (suc (suc (suc zero)))       = batchableˢ ∷ []
selected (suc (suc (suc (suc zero)))) = timed-faithfulˢ ∷ []
selected (suc (suc (suc (suc (suc zero))))) = simulationˢ ∷ []
selected (suc (suc (suc (suc (suc (suc zero)))))) = arrival-runsˢ ∷ []
selected (suc (suc (suc (suc (suc (suc (suc zero))))))) = batched-sandwichˢ ∷ []
selected (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = packets-name-arrivalsˢ ∷ []
selected (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = same-clockˢ ∷ []
selected (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = storeˢ ∷ []
selected _                            = statements

-- the impl's raw run, decoded, for reading a batchable failure by
rawOf : Case → String
rawOf c = showStream (runᴵ (Case.kinds c) (Case.fuel c) (Case.prog c) (Case.slots c))

-- AND ONE SIDE OF IT, so a hang is attributed to the statement that owns
-- it: 1 to 10 that statement's sides, in `selected`'s numbering,
-- anything else the impl's raw run
sidesOf : ℕ → Case → String
sidesOf k c with selected k
... | s ∷ [] = proj₂ (decide c s)
... | _      = rawOf c

sideAt : ℕ → ℕ → ℕ → ℕ → Gen String
sideAt f k n d = skipN (n ∸ 1) d >>=G λ _ → drawCase d >>=G λ where
  (_ , _ , e , d₀ , d₁) → pureG (sidesOf k (cached "?" f e (mkSlots d₀ d₁)))

-- THE CORPUS, EVERY ROW WITH EVERY SIDE PRINTED WHETHER OR NOT THEY
-- AGREE.  A row is a probe before it is a guard, and a probe is read for
-- its shape as much as for its verdict -- which the bug-cache runner,
-- printing only failures, cannot show.  Zero generated cases asks for it.
lineOf : Statement → Bool × String → String
lineOf s (b , body) =
  "  " ++ statementName s ++ (if b then ": agree" else ": FAIL") ++ "\n    " ++ body ++ "\n"

showRow : List Statement → Case → String
showRow []       c = ""
showRow (s ∷ ss) c = lineOf s (decide c s) ++ showRow ss c

-- one row at a time, so a row that hangs is named by what printed before
-- it; `k` picks one row, 1-based, and 0 runs them all
-- and `side` names one statement of it, as it does for a generated case
sideRow : ℕ → Case → String
sideRow k c = Case.name c ++ ": " ++ sidesOf k c ++ "\n"

-- and a nonzero `f` runs every row at that fuel instead of its own
printRows : List Statement → ℕ → ℕ → ℕ → ℕ → List Case → IO Unit
printRows ss f sd k i []       = putStr ""
printRows ss f sd k i (c ∷ cs) =
  (if (k ≡ᵇ 0) ∨ (k ≡ᵇ i)
   then putStr (if sd ≡ᵇ 0 then Case.name c′ ++ "\n" ++ showRow ss c′ else sideRow sd c′)
   else putStr "") >>= λ _ →
  printRows ss f sd k (suc i) cs
  where
  c′ = if f ≡ᵇ 0 then c else record c { fuel = f }

-- EACH CASE IS REPORTED THE MOMENT IT IS DECIDED, on stderr, because the
-- summary can only be printed once the last case is: a sweep killed by
-- its budget otherwise leaves nothing behind, every case it had decided
-- included.  A case that does not agree streams its reports verbatim,
-- paste and undecided blocks and all, so a killed run's stream is read
-- by the same splitter as a finished run's summary.
verdictOf : List (ℕ × String) → String
verdictOf []         = "agree"
verdictOf rs@(_ ∷ _) with decided rs
... | []    = "undecided"
... | _ ∷ _ = "FAIL"

-- each case names its formers by the census's tags, so the stream reads
-- a flag against a former where the census only counts the two apart
streamCases : Bool → ℕ → ℕ → List (Seen × List (ℕ × String)) → IO Unit
streamCases ob n i []       = putErr ""
streamCases ob n i (r ∷ rs) =
  putErr ("case " ++ show i ++ "/" ++ show n ++ " "
          ++ (if ob ∧ not (proj₁ (proj₂ (proj₁ r))) then "degenerate" else verdictOf (proj₂ r)) ++ "\n"
          ++ "  formers" ++ concatStr (map (λ g → if carries g (proj₁ (proj₁ (proj₁ r))) then " " ++ formerTag g else "") allFormers) ++ "\n"
          ++ (if proj₁ (proj₂ (proj₁ r)) then "  bears on contiguity\n" else "")
          ++ (if proj₁ (proj₂ (proj₂ (proj₁ r))) then "  holds values back at the fuel\n" else "")
          ++ (if proj₁ (proj₂ (proj₂ (proj₂ (proj₁ r)))) then "  groups values\n" else "")
          ++ (if proj₂ (proj₂ (proj₂ (proj₂ (proj₁ r)))) then "  parts the two clocks\n" else "")
          ++ concatStr (map proj₂ (proj₂ r))) >>= λ _ →
  streamCases ob n (suc i) rs

-- the summary, over the tally of the cases the stream already forced
summaryOf : ℕ → ℕ → ℕ → ℕ → Tally × List (ℕ × String) → String
summaryOf seed d f runs (tally , fails) = concatStr
  (( "seed " ∷ show seed ∷ " depth " ∷ show d ∷ " fuel " ∷ show f ∷ " — ran " ∷ show runs
   ∷ " cases, " ∷ show (length (decided fails)) ∷ " failures, "
   ∷ show (length fails ∸ length (decided fails)) ∷ " undecided"
   ∷ "; obs-fold " ∷ show (proj₁ (proj₂ tally))
   ∷ "; two plain arrivals with values " ∷ show (proj₁ (proj₂ (proj₂ tally)))
   ∷ "; values held back at the fuel " ∷ show (proj₁ (proj₂ (proj₂ (proj₂ tally))))
   ∷ "; values grouped " ∷ show (proj₂ (proj₂ (proj₂ (proj₂ tally)))) ∷ "\ncensus " ∷ [])
   ++ᴸ censusPairs allFormers (proj₁ tally)
   ++ᴸ ("\n" ∷ dumpFails fails ∷ []))

-- the cases are an ARGUMENT, so the stream and the summary read one list
sweep : Bool → ℕ → ℕ → ℕ → ℕ → List (Seen × List (ℕ × String)) → IO Unit
sweep ob seed d f runs rs = streamCases ob runs 1 rs >>= λ _ → putStr (summaryOf seed d f runs (tallyOf rs))

------------------------------------------------------------------------
-- THE RESTRICTION, stdin's second line: one JSON object whose keys are
-- the knobs' names, each a weight per arm, plus `reach`, the former tags
-- every case must carry, and `tries`, the draws one case may spend on
-- it.  Every key, length and tag is checked, because a misspelt knob
-- read as "unrestricted" is a sweep aimed somewhere else that says it
-- was aimed here.
firstLine restLines : List ℕ → List ℕ
firstLine []       = []
firstLine (c ∷ cs) = if c ≡ᵇ 10 then [] else c ∷ firstLine cs
restLines []       = []
restLines (c ∷ cs) = if c ≡ᵇ 10 then cs else restLines cs

fromCodes : List ℕ → String
fromCodes cs = fromList (map fromℕ cs)

blank : List ℕ → Bool
blank = all (λ c → (c ≡ᵇ 32) ∨ (c ≡ᵇ 9) ∨ (c ≡ᵇ 10) ∨ (c ≡ᵇ 13))

keyed : List ℕ → List (List ℕ × JSON) → Maybe JSON
keyed k []             = nothing
keyed k ((j , v) ∷ ms) = if eqListℕ k j then just v else keyed k ms

numsOf : List JSON → Maybe (List ℕ)
numsOf []            = just []
numsOf (jnum n ∷ js) with numsOf js
... | just ns = just (n ∷ ns)
... | nothing = nothing
numsOf (_ ∷ _)       = nothing

strsOf : List JSON → Maybe (List (List ℕ))
strsOf []            = just []
strsOf (jstr t ∷ js) with strsOf js
... | just ts = just (t ∷ ts)
... | nothing = nothing
strsOf (_ ∷ _)       = nothing

knownKey : List ℕ → Bool
knownKey k = any (λ n → eqListℕ (toCodes (knobName n)) k) allKnobs
           ∨ eqListℕ (toCodes "reach") k ∨ eqListℕ (toCodes "tries") k

isTag : List ℕ → Bool
isTag t = carriesTag allFormers t

-- the first thing wrong with one member, as the message main prints
knobErr : List ℕ → JSON → Maybe String
knobErr k (jarr js) with numsOf js
... | nothing = just (fromCodes k ++ " is not a list of weights")
... | just ws =
  if not (any (λ n → eqListℕ (toCodes (knobName n)) k ∧ (length ws ≡ᵇ arity n)) allKnobs)
  then just (fromCodes k ++ " needs one weight per arm")
  else if sumℕ ws ≡ᵇ 0 then just (fromCodes k ++ " leaves no arm")
  else nothing
knobErr k _ = just (fromCodes k ++ " is not a list")

reachErr : JSON → Maybe String
reachErr (jarr js) with strsOf js
... | nothing = just "reach is not a list of former tags"
... | just ts = if all isTag ts then nothing else just "reach names a tag no former carries"
reachErr _ = just "reach is not a list"

triesErr : JSON → Maybe String
triesErr (jnum (suc _)) = nothing
triesErr _              = just "tries is not a positive number"

memberErr : List ℕ × JSON → Maybe String
memberErr (k , v) =
  if not (knownKey k) then just ("unknown key " ++ fromCodes k)
  else if eqListℕ (toCodes "tries") k then triesErr v
  else if eqListℕ (toCodes "reach") k then reachErr v
  else knobErr k v

firstErr : List (List ℕ × JSON) → Maybe String
firstErr []       = nothing
firstErr (m ∷ ms) with memberErr m
... | just e  = just e
... | nothing = firstErr ms

weightsIn : List (List ℕ × JSON) → Knob → List ℕ
weightsIn ms k with keyed (toCodes (knobName k)) ms
... | just (jarr js) with numsOf js
...   | just ws = ws
...   | nothing = []
weightsIn ms k | _ = []

drawIn : List (List ℕ × JSON) → Draw
drawIn ms = record
  { weights = weightsIn ms
  ; reach   = reachIn (keyed (toCodes "reach") ms)
  ; tries   = triesIn (keyed (toCodes "tries") ms) }
  where
  reachIn : Maybe JSON → List (List ℕ)
  reachIn (just (jarr js)) with strsOf js
  ... | just ts = ts
  ... | nothing = []
  reachIn _ = []
  -- a reach with no tries given gets enough to find a rare former
  triesIn : Maybe JSON → ℕ
  triesIn (just (jnum n)) = n
  triesIn _               = 1000

-- the restriction stdin names, or why it names none
drawOf : List ℕ → Draw ⊎ String
drawOf cs with blank cs
... | true  = inj₁ anyDraw
... | false with parseJSON cs
...   | just (jobj ms) with firstErr ms
...     | nothing = inj₁ (drawIn ms)
...     | just e  = inj₂ e
drawOf cs | false | _ = inj₂ "the restriction is not one JSON object"

run : List ℕ → Draw → IO Unit
run cs W =
  let seed  = parseNat cs
      runs  = numAt 1 200 cs
      d     = numAt 2 4 cs
      at    = numAt 3 0 cs
      only  = numAt 4 0 cs
      side  = numAt 5 0 cs
      fuelʳ = numAt 6 0 cs
      ss    = selected (numAt 7 0 cs)
      f     = if fuelʳ ≡ᵇ 0 then FUEL else fuelʳ
      secs  = numAt 8 CASE cs
      ob    = numAt 9 0 cs ≡ᵇ 1
      shr   = numAt 10 0 cs
  in if runs ≡ᵇ 0
     then printRows ss fuelʳ side only 1 cases
     else if not (side ≡ᵇ 0)
     then putStr (proj₁ (sideAt f side only d W (randList seed 2000000)) ++ "\n")
     else if not (only ≡ᵇ 0) ∧ not (shr ≡ᵇ 0)
     then putStr (shrinkAt ss f secs only d shr W (randList seed 2000000))
     else if not (only ≡ᵇ 0)
     then putStr (dumpFails (proj₂ (proj₁ (runAt ss f secs only d W (randList seed 2000000)))))
     else if not (at ≡ᵇ 0)
     then putStr (proj₁ (showAt f at d W (randList seed 2000000)))
     else sweep ob seed d f runs (proj₁ (casesN ob ss f secs runs d W (randList seed 2000000)))

main : IO Unit
main = getContents >>= λ s → go (drawOf (restLines (toCodes s))) (firstLine (toCodes s))
  where
  go : Draw ⊎ String → List ℕ → IO Unit
  go (inj₁ W) cs = run cs W
  go (inj₂ e) cs = putStr ("restriction: " ++ e ++ "\n")
