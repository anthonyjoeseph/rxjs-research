-- An all-Agda QuickCheck: generate random well-typed programs (exp tree +
-- scripted inputs) over a fixed 2-slot nat context, run them through the
-- evaluator, and check the two sides of the top line agree: the impl
-- pipeline's BATCHING RUN against spec-batchSimultaneous applied to the
-- spec pipeline's run, burst by burst, in raw values. A fast in-Agda dev
-- loop for the implementation.
--
--   agda --compile --compile-dir=_cli src/QuickCheck.agda
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
module QuickCheck where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Char using (toℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map; length; concat; take)
                      renaming (_++_ to _++ᴸ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_; toList)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Rx.Prim using (after_,_; Timed; ObservableInput; hot; cold; InstEvent; init; value; close; handoff; complete; InstEmit; _at_from_as_)
open import Rx.Exp using (Ty; natᵗ; obs; _×ᵗ_; isData; PrimOp; input; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ)
open import Rx.SExp using (SExp; STm; SFn; inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ; mergeAllˢ; switchAllˢ; exhaustAllˢ;
  μˢ; varˢ; deferˢ; varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ;
  caseˢ; foldˢ; primˢ; ifˢ; strmˢ)
open import Data.List.Membership.Propositional using (_∈_)
open import Rx.Protocol using (wellFormed?)
open import Rx.Emit-Eq using (eqBatches; eqBursts)
open import Spec using (spec-batchSimultaneous)
open import Spec.Unwrap using (unwrapSpec)
open import Implementation.Unit-Test.Prelude using (Γ₂; Case; mkSlots; cached; runOf; implBurstsOf; specBurstsOf;
  agrees; wellFormed)
open import Implementation.Unit-Test using (cases)
open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; Unit)

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
-- THE TREE THE SWEEP DRAWS IS THE AUTHOR'S, WHICH IS WHAT PUTS THE
-- BATCHING QUESTION IN RANGE AT ALL.  Both batchings read the protocol
-- off an ENVELOPE, and only an elaborated program carries one, so a
-- drawn `Exp` could be run and could not be ASKED.  The generator is
-- therefore indexed by `SExp`, and `Rx.Elaborate` is what stands
-- between it and the evaluator; the two formers the plain tree has and
-- the author's does not -- mint and batchSync -- leave with it, and
-- what reaches them now is the elaboration rather than a seed.
--
-- THE CONTEXT COMES FROM THE PRELUDE BECAUSE A CACHED ROW AND THE SEED
-- THAT FOUND IT HAVE TO BE ONE RUN.  `Γ₂` is what the author sees and
-- `Γ₂ᵉ` is where an elaborated program stands, each slot holding the
-- envelope over the author's type.

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
genSlotDef k = genB 4 >>=G λ c → genNat >>=G λ x → genNat >>=G λ y →
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
genScript = genB 4 >>=G λ c → genNat >>=G λ x → genNat >>=G λ y →
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

-- scan step (acc, cur) → acc + cur
genScanFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) natᵗ)
genScanFn = pureG (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl)))
                                    (sndˢ (varˢᵗ (here refl)))))

-- THE STEP THAT CHANGES AN EMIT'S VALUE COUNT, WHICH IS NOW A FLATTEN
-- AND NOT A STEP AT ALL.  `mapᵉ` and `scanᵉ` are both per-VALUE, so the
-- list they hand back is always as long as the one they were given, and
-- a sweep built only out of them never changes a count.  Zero-or-more
-- out is `mergeAllᵉ` over a step returning LITERAL SYNTAX — rxjs's own
-- `mergeMap(x => …)` — so this generates the step and the lane spends
-- it under a flattener.  The arms are a lattice over what happens to
-- the count: emptied, doubled, one longer, filtered, and unchanged.
--
-- THE IDENTITY ARM IS DELIBERATE, on the reasoning `genFn` records: a
-- generator whose every arm exercises the interesting shape cannot
-- produce the program that distinguishes a step which ignores its input
-- from one that does not.
genFanFn : ∀ {Δᵍ Δ Θ} → Gen (SFn Γ₂ Δᵍ Δ Θ natᵗ (obs natᵗ))
genFanFn = genB 5 >>=G λ c → genNat >>=G λ k →
  let x = varˢᵗ (here refl)
  in pureG
    (      if c ≡ᵇ 0 then strmˢ emptyˢ
      else if c ≡ᵇ 1 then strmˢ (ofˢ (x ∷ x ∷ []))
      else if c ≡ᵇ 2 then strmˢ (ofˢ (x ∷ natˢ k ∷ []))
      else if c ≡ᵇ 3 then
        ifˢ (primˢ ltᵖ (pairˢ x (natˢ k))) (strmˢ emptyˢ) (strmˢ (ofˢ (x ∷ [])))
      else strmˢ (ofˢ (x ∷ [])))

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
    (      if c ≡ᵇ 0 then strmˢ (mergeAllˢ nothing (ofˢ (acc ∷ [])))
      else if c ≡ᵇ 1 then acc
      else if c ≡ᵇ 2 then strmˢ (ofˢ (cur ∷ []))
      else if c ≡ᵇ 3 then strmˢ emptyˢ
      else if c ≡ᵇ 4 then strmˢ (switchAllˢ (ofˢ (acc ∷ [])))
      else strmˢ (mergeAllˢ nothing
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
genLeafAt g u sl = genB 3 >>=G λ c →
  if c ≡ᵇ 0 then genSlotRef sl
  else if c ≡ᵇ 1 then pureG emptyˢ
  else (genNat >>=G λ a → genNat >>=G λ b → pureG (ofˢ (natˢ a ∷ natˢ b ∷ [])))

genExpAt g u sl zero    = genLeafAt g u sl
genExpAt g u sl (suc d) = genB 12 >>=G λ c →
  if c ≡ᵇ 0 then genLeafAt g u sl
  else if c ≡ᵇ 1 then genLeafAt g u sl
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genExpAt g u sl d >>=G λ e → pureG (mapˢ f e))
  else if c ≡ᵇ 3 then
    (genScanFn >>=G λ f → genNat >>=G λ z → genExpAt g u sl d >>=G λ e →
     pureG (scanˢ f (natˢ z) e))
  else if c ≡ᵇ 4 then (genObsAt g u sl d >>=G λ t → pureG (mergeAllˢ nothing t))
  else if c ≡ᵇ 5 then
    -- the limit axis, which is where bounded concurrency gets sampled:
    -- 1 is the old concat, 2 and 3 are the middle nothing here could
    -- previously reach.  Two lanes with three parked inners is the
    -- smallest shape whose drain refills more than one lane in a
    -- single instant, so `genB 3` is the floor and not a taste
    (genB 3 >>=G λ k → genObsAt g u sl d >>=G λ t → pureG (mergeAllˢ (just (suc k)) t))
  else if c ≡ᵇ 6 then (genObsAt g u sl d >>=G λ t → pureG (switchAllˢ t))
  else if c ≡ᵇ 7 then (genObsAt g u sl d >>=G λ t → pureG (exhaustAllˢ t))
  else if c ≡ᵇ 8 then (genSpineG g u sl d >>=G λ b → pureG (μˢ b))
  else if c ≡ᵇ 9 then (genExpAt 0 (g + u) sl d >>=G λ b → pureG (gate g u b))
  else if c ≡ᵇ 10 then
    (genNat >>=G λ k → genExpAt g u sl d >>=G λ e → pureG (takeˢ (natˢ k) e))
  else
    (genFanFn >>=G λ f → genExpAt g u sl d >>=G λ e →
     pureG (mergeAllˢ nothing (mapˢ f e)))

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
  in genB 4 >>=G λ c →
     if c ≡ᵇ 0
     then (if d ≡ᵇ 0
           then (genObsScanFn >>=G λ f → genObsSeed sl >>=G λ z →
                 genExpAt g u sl d >>=G λ e → pureG (scanˢ f z e))
           else inners)
     else inners

-- past the gate: the var is in scope and this subtree plants exactly one
genSpineD w sl zero    = pureG (varˢ (here refl))
genSpineD w sl (suc d) = genB 9 >>=G λ c →
  if c ≡ᵇ 0 then pureG (varˢ (here refl))
  else if c ≡ᵇ 1 then (genFn >>=G λ f → genSpineD w sl d >>=G λ e → pureG (mapˢ f e))
  else if c ≡ᵇ 2 then
    (genScanFn >>=G λ f → genNat >>=G λ z → genSpineD w sl d >>=G λ e →
     pureG (scanˢ f (natˢ z) e))
  else if c ≡ᵇ 3 then
    (genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (mergeAllˢ nothing (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 4 then
    (genB 3 >>=G λ k → genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (mergeAllˢ (just (suc k)) (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 5 then
    (genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (switchAllˢ (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 6 then
    (genFanFn >>=G λ f → genSpineD w sl d >>=G λ e →
     pureG (mergeAllˢ nothing (mapˢ f e)))
  else if c ≡ᵇ 7 then
    (genNat >>=G λ k → genSpineD w sl d >>=G λ e →
     pureG (takeˢ (natˢ (suc k)) e))
  else
    (genSpineD w sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) sl d (suc extra) >>=G λ rest →
     pureG (exhaustAllˢ (ofˢ (strmˢ e ∷ rest))))

-- before the gate: the binder is guarded, so every route ends in a `deferᵉ`
genSpineG g u sl zero    = pureG (gate (suc g) u (varˢ (here refl)))
genSpineG g u sl (suc d) = genB 9 >>=G λ c →
  if c ≡ᵇ 0 then (genSpineD (g + u) sl d >>=G λ b → pureG (gate (suc g) u b))
  else if c ≡ᵇ 1 then (genSpineD (g + u) sl d >>=G λ b → pureG (gate (suc g) u b))
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genSpineG g u sl d >>=G λ e → pureG (mapˢ f e))
  else if c ≡ᵇ 3 then
    (genScanFn >>=G λ f → genNat >>=G λ z → genSpineG g u sl d >>=G λ e →
     pureG (scanˢ f (natˢ z) e))
  else if c ≡ᵇ 4 then
    (genSpineG g u sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u sl d (suc extra) >>=G λ rest →
     pureG (mergeAllˢ nothing (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 5 then
    (genSpineG g u sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u sl d (suc extra) >>=G λ rest →
     pureG (switchAllˢ (ofˢ (strmˢ e ∷ rest))))
  else if c ≡ᵇ 6 then
    (genFanFn >>=G λ f → genSpineG g u sl d >>=G λ e →
     pureG (mergeAllˢ nothing (mapˢ f e)))
  else if c ≡ᵇ 7 then
    (genNat >>=G λ k → genSpineG g u sl d >>=G λ e →
     pureG (takeˢ (natˢ (suc k)) e))
  else
    (genSpineG g u sl d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u sl d (suc extra) >>=G λ rest →
     pureG (exhaustAllˢ (ofˢ (strmˢ e ∷ rest))))

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
  fInput fOf fEmpty fTake fMap fScan fMergeAll fSwitchAll fExhaustAll
    fMu fVar fDefer fMint fBatchSync : Former

formerTag : Former → String
formerTag fInput      = "input"
formerTag fOf         = "of"
formerTag fEmpty      = "empty"
formerTag fTake       = "take"
formerTag fMap        = "map"
formerTag fScan       = "scan"
formerTag fMergeAll   = "mergeAll"
formerTag fSwitchAll  = "switchAll"
formerTag fExhaustAll = "exhaustAll"
formerTag fMu         = "mu"
formerTag fVar        = "varE"
formerTag fDefer      = "defer"
formerTag fMint       = "mint"
formerTag fBatchSync  = "batchSync"

allFormers : List Former
allFormers = fInput ∷ fOf ∷ fEmpty ∷ fTake ∷ fMap ∷ fScan ∷ fMergeAll
           ∷ fSwitchAll ∷ fExhaustAll ∷ fMu ∷ fVar ∷ fDefer ∷ fMint
           ∷ fBatchSync ∷ []

formerIx : Former → ℕ
formerIx fInput      = 0
formerIx fOf         = 1
formerIx fEmpty      = 2
formerIx fTake       = 3
formerIx fMap        = 4
formerIx fScan       = 5
formerIx fMergeAll   = 6
formerIx fSwitchAll  = 7
formerIx fExhaustAll = 8
formerIx fMu         = 9
formerIx fVar        = 10
formerIx fDefer      = 11
formerIx fMint       = 12
formerIx fBatchSync  = 13

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
-- the second component reads the CARRIED state's type, which is the former's
-- own accumulator: `isData (obs _)` is false, so it fires exactly when the
-- former re-binds something the run could subscribe
marksˢ (mapˢ f e)       = one fMap ⊕ marksˢᵗ f ⊕ marksˢ e
marksˢ (scanˢ {t = t} f z e) =
  one fScan ⊕ ([] , not (isData t)) ⊕ marksˢᵗ f ⊕ marksˢᵗ z ⊕ marksˢ e
marksˢ (mergeAllˢ _ e)  = one fMergeAll ⊕ marksˢ e
marksˢ (switchAllˢ e)   = one fSwitchAll ⊕ marksˢ e
marksˢ (exhaustAllˢ e)  = one fExhaustAll ⊕ marksˢ e
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

------------------------------------------------------------------------
-- a compact dump of both sides' bursts (for failure reports)

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

-- one burst's batches, bracketed, then the next burst
showBatches : List (List ℕ) → String
showBatches []       = ""
showBatches (b ∷ bs) = showVals b ++ " " ++ showBatches bs

showBursts : List (List (List ℕ)) → String
showBursts []         = "·"
showBursts (bs ∷ bss) = "[" ++ showBatches bs ++ "] " ++ showBursts bss

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

showSExp : ∀ {Δᵍ Δ Θ t} → SExp Γ₂ Δᵍ Δ Θ t → String
showSTm  : ∀ {Δᵍ Δ Θ t} → STm Γ₂ Δᵍ Δ Θ t → String

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
showSExp (mapˢ f e)      = "(mapˢ " ++ showSTm f ++ " " ++ showSExp e ++ ")"
showSExp (scanˢ f z e)   =
  "(scanˢ " ++ showSTm f ++ " " ++ showSTm z ++ " " ++ showSExp e ++ ")"
-- the limit prints as the `Maybe ℕ` it IS, not as the ∞ a reader would
-- prefer: a witness is printed to be PASTED, and the corpus is Agda
showSExp (mergeAllˢ nothing s)  = "(mergeAllˢ nothing " ++ showSExp s ++ ")"
showSExp (mergeAllˢ (just k) s) =
  "(mergeAllˢ (just " ++ show k ++ ") " ++ showSExp s ++ ")"
showSExp (switchAllˢ s)  = "(switchAllˢ " ++ showSExp s ++ ")"
showSExp (exhaustAllˢ s) = "(exhaustAllˢ " ++ showSExp s ++ ")"
showSExp (μˢ e)          = "(μˢ " ++ showSExp e ++ ")"
showSExp (varˢ x)        = "(varˢ " ++ showIx x ++ ")"
showSExp (deferˢ e)      = "(deferˢ " ++ showSExp e ++ ")"

------------------------------------------------------------------------
-- one case, a run, and reporting

-- THE FUEL IS AN EXPONENT FOR SOME PROGRAMS, WHICH IS WHY THE SWEEP HAS
-- TO BE BOUNDED FROM OUTSIDE.  A guarded fixpoint under an unbounded
-- `mergeAllᵉ` with no `takeᵉ` above it emits once per unit of fuel; one
-- whose step hands back MORE elements than it was given doubles instead,
-- and the corpus contains such programs because nothing in the generator
-- declines to draw one.  The cost is inside `evaluate↓` rather than in
-- the stream it returns, the drain forcing each cascade whole, so no
-- budget readable from here can decline the case after the fact — a cap
-- on the stream's length was tried and buys nothing, since the length is
-- reached only by paying for it.  `scripts/gen-unit-tests.sh` therefore
-- bounds a SEED in wall clock and reports the ones it could not run.
--
-- What retires it is the ROOT CAP, not a budget read from here: the
-- prelude's `capProg` puts a `takeᵉ` above every elaborated tree, which
-- unsubscribes the fixpoint instead of letting it be performed and then
-- discarded.  The wall-clock bound stays on as a backstop for whatever
-- the cap does not cut.
FUEL : ℕ
FUEL = 30

-- A PASTE-READY BUG-CACHE ROW: the block IS a row of
-- `Implementation.Unit-Test.cases`, trailing `∷` included, so the script
-- that appends it neither builds nor parses Agda.  The name is written
-- `"?"` rather than left blank, because a block pasted by hand has to
-- typecheck as it stands; the script substitutes the seed.  Line 2 --
-- the program -- is the dedup key.
--
-- ONE SHAPE FOR BOTH CHECKS, and that is what makes the key work: the
-- cache holds every row to BOTH properties, so a program that fails
-- either one wants the same row, and a program that fails both dedups
-- to it instead of being cached twice.
--
-- THE SLOT TABLE IS RENDERED RATHER THAN NAMED, because the sweep
-- DRAWS it: a row naming a constant table would be a DIFFERENT run
-- from the one that failed.  Both definitions are printed through the
-- same `showSExp` the program goes through, and `mkSlots` is in the
-- prelude so the corpus can see the name.
pasteRow : SExp Γ₂ [] [] [] natᵗ
         → Script → SExp Γ₂ [] [] [] natᵗ → String
pasteRow e d₀ d₁ =
  "\n-- <<<PASTE\n  cached \"?\" " ++ show FUEL ++ "\n          "
       ++ showSExp e ++ "\n          (mkSlots (" ++ showScript d₀ ++ ")\n"
       ++ "                   (" ++ showSExp d₁ ++ ")) ∷\n-- PASTE>>>\n"

report : String → SExp Γ₂ [] [] [] natᵗ
       → Script → SExp Γ₂ [] [] [] natᵗ
       → List (List (List ℕ)) → List (List (List ℕ)) → List (InstEmit ℕ) → String
report tag e d₀ d₁ impl spec raw =
  "  " ++ tag ++ "\n    impl = " ++ showBursts impl
       ++ "\n    spec = " ++ showBursts spec
       ++ "\n    raw  = " ++ showStream raw ++ pasteRow e d₀ d₁

-- a WellFormed violation of the evaluator's raw output
reportWF : SExp Γ₂ [] [] [] natᵗ
         → Script → SExp Γ₂ [] [] [] natᵗ
         → List (InstEmit ℕ) → String
reportWF e d₀ d₁ s =
  "  WF-FAIL\n    stream = " ++ showStream s ++ pasteRow e d₀ d₁

-- A SPEC INSTANT SPANNING TWO BURSTS, which no operator can repair.  The
-- top line applies the spec per burst, and that agrees with applying it
-- to the whole run exactly when no instant's emits fall in two bursts;
-- where they do, the per-burst spec splits a batch the whole-run spec
-- keeps, and the statement asks the operator for a batching the spec
-- itself does not give.  So it is reported apart from FAIL: it is a
-- finding about the statement, not a bug in the operator.
reportSpan : SExp Γ₂ [] [] [] natᵗ
           → Script → SExp Γ₂ [] [] [] natᵗ
           → List (List ℕ) → List (List (List ℕ)) → List (InstEmit ℕ) → String
reportSpan e d₀ d₁ whole bursts raw =
  "  SPAN-FAIL\n    whole  = " ++ showBatches whole
       ++ "\n    bursts = " ++ showBursts bursts
       ++ "\n    raw    = " ++ showStream raw ++ pasteRow e d₀ d₁

-- three checks on one generated program: impl ≡ spec per burst, no spec
-- instant spanning two bursts, and the raw stream satisfying the protocol
-- automaton (evaluate-well-formed, sampled).
--
-- THE THIRD CHECK WENT WITH THE THING IT SAMPLED, AND ITS COVERAGE IS
-- NOT LOST.  It reported a run that gave up at a descent guard, which
-- was the cheapest instantiation of the claim that no run does — and
-- the sweep's verdict over 4500 programs is recorded where that claim
-- was, since the guards it sampled are gone and the statement it
-- sampled is not stateable.  What it would have to sample now is a
-- proof obligation rather than an output, and nothing a generator
-- produces can fail one.
-- one count per former, in `allFormers` order, plus the obs-fold count
Tally : Set
Tally = List ℕ × ℕ

zeroTally : Tally
zeroTally = map (λ _ → 0) allFormers , 0

carries : Former → List Former → Bool
carries f []       = false
carries f (g ∷ gs) = sameFormer f g ∨ carries f gs

bumpEach : List Former → List Former → List ℕ → List ℕ
bumpEach fs []       cs       = cs
bumpEach fs (g ∷ gs) []       = []
bumpEach fs (g ∷ gs) (c ∷ cs) =
  (if carries g fs then suc c else c) ∷ bumpEach fs gs cs

bump : Marks → Tally → Tally
bump (fs , o) (cs , p) = bumpEach fs allFormers cs , (if o then suc p else p)

-- EACH RUN IS AN ARGUMENT, SO IT IS COMPUTED ONCE.  A `let` is
-- substituted at compile time, so a name used in three checks is three
-- evaluations; a function argument is one shared thunk.
verdict : SExp Γ₂ [] [] [] natᵗ → Script → SExp Γ₂ [] [] [] natᵗ
        → List (List (List ℕ)) → List (List (List ℕ))
        → List (InstEmit ℕ) → List (ℕ × String)
verdict e d₀ d₁ impl spec s =
  agreeFails ++ᴸ spanFails ++ᴸ wfFails
  where
  whole      = unwrapSpec (spec-batchSimultaneous s)
  agreeFails = if eqBursts impl spec then []
               else (0 , report "FAIL" e d₀ d₁ impl spec s) ∷ []
  spanFails  = if eqBatches (concat spec) whole then []
               else (2 , reportSpan e d₀ d₁ whole spec s) ∷ []
  wfFails    = if wellFormed? s then [] else (3 , reportWF e d₀ d₁ s) ∷ []

oneCase : ℕ → Gen (Marks × List (ℕ × String))
-- THE DRAWN TREE IS WHAT IS COUNTED AND WHAT IS PRINTED, AND THE CAP IS
-- NEITHER.  It is applied above the elaboration, so it is not a former
-- of the author's tree at all and cannot inflate a census; and a cached
-- row names the author's program, since the cap is the harness's and
-- `runOf` re-applies it wherever the row is run.
oneCase d = genExp d >>=G λ e → genSlots >>=G λ ds →
  let c = cached "?" FUEL e (mkSlots (proj₁ ds) (proj₂ ds))
  in pureG (marksˢ e , verdict e (proj₁ ds) (proj₂ ds)
                               (implBurstsOf c) (specBurstsOf c) (runOf c))

-- accumulate EVERY failing case's reports, in generation order, and tally
-- which recursion constructors the corpus actually reached
runN : ℕ → ℕ → Gen (Tally × List (ℕ × String))
runN zero    d = pureG (zeroTally , [])
runN (suc k) d = oneCase d >>=G λ r → runN k d >>=G λ acc →
  pureG (bump (proj₁ r) (proj₁ acc) , proj₂ r ++ᴸ proj₂ acc)

------------------------------------------------------------------------
-- stdin parsing: "SEED [RUNS] [DEPTH] [SHOW-AT] [RUN-AT] [SIDE]"

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
kinds = "FAIL" ∷ "-" ∷ "SPAN" ∷ "WF" ∷ []

counts : ℕ → List String → List (ℕ × String) → List String
counts k []       fs = []
counts k (t ∷ ts) fs = t ∷ " " ∷ show (length (ofKind k fs)) ∷ " " ∷ counts (suc k) ts fs

samples : ℕ → List (ℕ × String) → String
samples k fs = concatStr (take 2 (ofKind k fs))

dumpFails : List (ℕ × String) → String
dumpFails [] = "  (all agree)\n"
dumpFails fs = concatStr (counts 0 kinds fs) ++ "\n"
  ++ samples 0 fs ++ samples 1 fs ++ samples 2 fs ++ samples 3 fs

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
skipN (suc k) d = genExp d >>=G λ _ → genSlots >>=G λ _ → skipN k d

-- the paste row of ONE case, named by its 1-based index
showAt : ℕ → ℕ → Gen String
showAt n d = skipN (n ∸ 1) d >>=G λ _ →
  genExp d >>=G λ e → genSlots >>=G λ ds →
  pureG (pasteRow e (proj₁ ds) (proj₂ ds))

-- RUN ONE CASE, named the same way, so a case that hangs a sweep can be
-- timed and re-run alone rather than by bisecting the count
runAt : ℕ → ℕ → Gen (Marks × List (ℕ × String))
runAt n d = skipN (n ∸ 1) d >>=G λ _ → oneCase d

-- AND ONE SIDE OF IT, so a hang is attributed to the pipeline that owns
-- it: 1 the impl run, 2 the spec run, anything else the raw run
sideAt : ℕ → ℕ → ℕ → Gen String
sideAt k n d = skipN (n ∸ 1) d >>=G λ _ → genExp d >>=G λ e → genSlots >>=G λ ds →
  let c = cached "?" FUEL e (mkSlots (proj₁ ds) (proj₂ ds))
  in pureG (if k ≡ᵇ 1 then showBursts (implBurstsOf c)
            else if k ≡ᵇ 2 then showBursts (specBurstsOf c)
            else showStream (runOf c))

-- THE CORPUS, EVERY ROW WITH BOTH SIDES PRINTED WHETHER OR NOT THEY
-- AGREE.  A row is a probe before it is a guard, and a probe is read for
-- its shape as much as for its verdict -- which the bug-cache runner,
-- printing only failures, cannot show.  Zero generated cases asks for it.
showRow : Case → String
showRow c = Case.name c ++ (if agrees c then ": agree" else ": FAIL")
  ++ (if wellFormed c then "" else " WF")
  ++ "\n    impl = " ++ showBursts (implBurstsOf c)
  ++ "\n    spec = " ++ showBursts (specBurstsOf c)
  ++ "\n    raw  = " ++ showStream (runOf c) ++ "\n"

-- one row at a time, so a row that hangs is named by what printed before
-- it; `k` picks one row, 1-based, and 0 runs them all
-- and `side` names one pipeline of it, as it does for a generated case
sideRow : ℕ → Case → String
sideRow k c = Case.name c ++ ": " ++
  (if k ≡ᵇ 1 then showBursts (implBurstsOf c)
   else if k ≡ᵇ 2 then showBursts (specBurstsOf c)
   else showStream (runOf c)) ++ "\n"

-- and a nonzero `f` runs every row at that fuel instead of its own
printRows : ℕ → ℕ → ℕ → ℕ → List Case → IO Unit
printRows f sd k i []       = putStr ""
printRows f sd k i (c ∷ cs) =
  (if (k ≡ᵇ 0) ∨ (k ≡ᵇ i)
   then putStr (if sd ≡ᵇ 0 then showRow c′ else sideRow sd c′)
   else putStr "") >>= λ _ →
  printRows f sd k (suc i) cs
  where
  c′ = if f ≡ᵇ 0 then c else record c { fuel = f }

main : IO Unit
main = getContents >>= λ s →
  let cs    = toCodes s
      seed  = parseNat cs
      runs  = numAt 1 200 cs
      d     = numAt 2 4 cs
      at    = numAt 3 0 cs
      only  = numAt 4 0 cs
      side  = numAt 5 0 cs
      fuelʳ = numAt 6 0 cs
      res   = proj₁ (runN runs d (randList seed 2000000))
      tally = proj₁ res
      fails = proj₂ res
  in if runs ≡ᵇ 0
     then printRows fuelʳ side only 1 cases
     else if not (side ≡ᵇ 0)
     then putStr (proj₁ (sideAt side only d (randList seed 2000000)) ++ "\n")
     else if not (only ≡ᵇ 0)
     then putStr (dumpFails (proj₂ (proj₁ (runAt only d (randList seed 2000000)))))
     else if not (at ≡ᵇ 0)
     then putStr (proj₁ (showAt at d (randList seed 2000000)))
     else putStr (concatStr
       (( "seed " ∷ show seed ∷ " depth " ∷ show d ∷ " — ran " ∷ show runs
        ∷ " cases, " ∷ show (length fails) ∷ " failures"
        ∷ "; obs-fold " ∷ show (proj₂ tally) ∷ "\ncensus " ∷ [])
        ++ᴸ censusPairs allFormers (proj₁ tally)
        ++ᴸ ("\n" ∷ dumpFails fails ∷ [])))
