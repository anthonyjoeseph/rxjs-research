-- An all-Agda QuickCheck: generate random well-typed programs (exp tree +
-- scripted inputs) over a fixed 2-slot nat context, run them through the
-- evaluator, and check impl-batchSimultaneous ≡ spec-batchSimultaneous on
-- the resulting stream. A fast in-Agda dev loop for the implementation.
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
open import Data.List using (List; []; _∷_; map; length)
                      renaming (_++_ to _++ᴸ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_; toList)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Rx.Prim using (Timed; after_,_; ObservableInput; hot; cold; InstEvent; init; value; close; handoff;
  complete; InstEmit; _at_from_as_)
open import Rx.Exp using (Ty; natᵗ; obs; _×ᵗ_; isData; Ctx; Exp; Tm; Fn; PrimOp; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  batchSyncᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; unit̂; bool̂;
  nat̂; uniq̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; nilᵗ; consᵗ;
  foldᵗ; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ)
open import Data.List.Membership.Propositional using (_∈_)
open import Rx.Emit-Eq using (eqBatched)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Slots using (scripted; shared; Slot; Slots)
open import Rx.Protocol using (wellFormed?)
open import Implementation using (impl-batchSimultaneous)
open import Spec using (spec-batchSimultaneous)
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
-- the fixed context: two nat-typed slots

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

genFin2 : Gen (Fin 2)
genFin2 = genB 2 >>=G λ c → pureG (if c ≡ᵇ 0 then zero else suc zero)

-- input i : Exp … (lookup Γ₂ i); matching i lets lookup reduce to natᵗ.
-- Polymorphic in the μ-var contexts: a slot reference is legal wherever the
-- generator stands, binders open or not.
inputNat : ∀ {Δᵍ Δ Θ} → Fin 2 → Exp Γ₂ Δᵍ Δ Θ natᵗ
inputNat zero          = input zero
inputNat (suc zero)    = input (suc zero)
inputNat (suc (suc ()))

genNat : Gen ℕ
genNat = genB 10

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
genFn : ∀ {Δᵍ Δ Θ} → Gen (Fn Γ₂ Δᵍ Δ Θ natᵗ natᵗ)
genFn = genB 4 >>=G λ c → genNat >>=G λ k →
  pureG (if c ≡ᵇ 0 then varᵗ (here refl)
    else if c ≡ᵇ 1 then primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ k))
    else if c ≡ᵇ 2 then primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ k))
    else nat̂ k)

-- scan step (acc, cur) → acc + cur
genScanFn : ∀ {Δᵍ Δ Θ} → Gen (Fn Γ₂ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) natᵗ)
genScanFn = pureG (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl)))
                                    (sndᵗ (varᵗ (here refl)))))

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
genFanFn : ∀ {Δᵍ Δ Θ} → Gen (Fn Γ₂ Δᵍ Δ Θ natᵗ (obs natᵗ))
genFanFn = genB 5 >>=G λ c → genNat >>=G λ k →
  let x = varᵗ (here refl)
  in pureG
    (      if c ≡ᵇ 0 then strmᵗ emptyᵉ
      else if c ≡ᵇ 1 then strmᵗ (ofᵉ (x ∷ x ∷ []))
      else if c ≡ᵇ 2 then strmᵗ (ofᵉ (x ∷ nat̂ k ∷ []))
      else if c ≡ᵇ 3 then
        ifᵗ (primᵗ ltᵖ (pairᵗ x (nat̂ k))) (strmᵗ emptyᵉ) (strmᵗ (ofᵉ (x ∷ [])))
      else strmᵗ (ofᵉ (x ∷ [])))

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
genObsScanFn : ∀ {Δᵍ Δ Θ} → Gen (Fn Γ₂ Δᵍ Δ Θ (obs natᵗ ×ᵗ natᵗ) (obs natᵗ))
genObsScanFn = genB 6 >>=G λ c → genNat >>=G λ k →
  let acc = fstᵗ (varᵗ (here refl))
      cur = sndᵗ (varᵗ (here refl))
  in pureG
    (      if c ≡ᵇ 0 then strmᵗ (mergeAllᵉ nothing (ofᵉ (acc ∷ [])))
      else if c ≡ᵇ 1 then acc
      else if c ≡ᵇ 2 then strmᵗ (ofᵉ (cur ∷ []))
      else if c ≡ᵇ 3 then strmᵗ emptyᵉ
      else if c ≡ᵇ 4 then strmᵗ (switchAllᵉ (ofᵉ (acc ∷ [])))
      else strmᵗ (mergeAllᵉ nothing
             (ofᵉ (acc ∷ strmᵗ (ofᵉ (nat̂ k ∷ [])) ∷ []))))

-- the fold's own seed, at observable type.  `emptyᵉ` is the shallowest
-- one there is, so a climb read off a run seeded with it is the fold's
-- entirely
genObsSeed : ∀ {Δᵍ Δ Θ} → Gen (Tm Γ₂ Δᵍ Δ Θ (obs natᵗ))
genObsSeed = genB 3 >>=G λ c → genNat >>=G λ k → genFin2 >>=G λ i →
  pureG (      if c ≡ᵇ 0 then strmᵗ emptyᵉ
          else if c ≡ᵇ 1 then strmᵗ (ofᵉ (nat̂ k ∷ []))
          else strmᵗ (inputNat i))

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

gate : ∀ g u → Exp Γ₂ [] (nats (g + u)) [] natᵗ → Exp Γ₂ (nats g) (nats u) [] natᵗ
gate g u b = deferᵉ (subst (λ Δ → Exp Γ₂ [] Δ [] natᵗ) (sym (nats-++ g u)) b)

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
genExpAt   : ∀ g u → ℕ → Gen (Exp Γ₂ (nats g) (nats u) [] natᵗ)
genObsAt   : ∀ g u → ℕ → Gen (Exp Γ₂ (nats g) (nats u) [] (obs natᵗ))
genInners  : ∀ g u → ℕ → ℕ → Gen (List (Tm Γ₂ (nats g) (nats u) [] (obs natᵗ)))
genSpineG  : ∀ g u → ℕ → Gen (Exp Γ₂ (nats (suc g)) (nats u) [] natᵗ)
genSpineD  : ∀ w   → ℕ → Gen (Exp Γ₂ [] (nats (suc w)) [] natᵗ)

genLeafAt : ∀ g u → Gen (Exp Γ₂ (nats g) (nats u) [] natᵗ)
genLeafAt g u = genB 3 >>=G λ c →
  if c ≡ᵇ 0 then (genFin2 >>=G λ i → pureG (inputNat i))
  else if c ≡ᵇ 1 then pureG emptyᵉ
  else (genNat >>=G λ a → genNat >>=G λ b → pureG (ofᵉ (nat̂ a ∷ nat̂ b ∷ [])))

genExpAt g u zero    = genLeafAt g u
genExpAt g u (suc d) = genB 13 >>=G λ c →
  if c ≡ᵇ 0 then genLeafAt g u
  else if c ≡ᵇ 1 then genLeafAt g u
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genExpAt g u d >>=G λ e → pureG (mapᵉ f e))
  else if c ≡ᵇ 3 then (genB 4 >>=G λ k → genExpAt g u d >>=G λ e → pureG (takeᵉ (nat̂ k) e))
  else if c ≡ᵇ 4 then
    (genScanFn >>=G λ f → genNat >>=G λ s → genExpAt g u d >>=G λ e → pureG (scanᵉ f (nat̂ s) e))
  else if c ≡ᵇ 5 then (genObsAt g u d >>=G λ s → pureG (mergeAllᵉ nothing s))
  else if c ≡ᵇ 6 then
    -- the limit axis, which is where bounded concurrency gets sampled:
    -- 1 is the old concat, 2 and 3 are the middle nothing here could
    -- previously reach.  Two lanes with three parked inners is the
    -- smallest shape whose drain refills more than one lane in a
    -- single instant, so `genB 3` is the floor and not a taste
    (genB 3 >>=G λ k → genObsAt g u d >>=G λ s → pureG (mergeAllᵉ (just (suc k)) s))
  else if c ≡ᵇ 7 then (genObsAt g u d >>=G λ s → pureG (switchAllᵉ s))
  else if c ≡ᵇ 8 then (genObsAt g u d >>=G λ s → pureG (exhaustAllᵉ s))
  else if c ≡ᵇ 9 then (genSpineG g u d >>=G λ b → pureG (μᵉ b))
  else if c ≡ᵇ 10 then (genExpAt 0 (g + u) d >>=G λ b → pureG (gate g u b))
  else if c ≡ᵇ 11 then
    (genFanFn >>=G λ f → genExpAt g u d >>=G λ e →
     pureG (mergeAllᵉ nothing (mapᵉ f e)))
  else genLeafAt g u

genInners g u d zero    = pureG []
genInners g u d (suc n) =
  genExpAt g u d >>=G λ e → genInners g u d n >>=G λ rest → pureG (strmᵗ e ∷ rest)

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
genObsAt g u d =
  let inners = genB 2 >>=G λ extra → genInners g u d (suc (suc extra)) >>=G λ items →
                 pureG (ofᵉ items)
  in genB 4 >>=G λ c →
     if c ≡ᵇ 0
     then (if d ≡ᵇ 0
           then (genObsScanFn >>=G λ f → genObsSeed >>=G λ z → genExpAt g u d >>=G λ e →
                 pureG (scanᵉ f z e))
           else inners)
     else inners

-- past the gate: the var is in scope and this subtree plants exactly one
genSpineD w zero    = pureG (varᵉ (here refl))
genSpineD w (suc d) = genB 9 >>=G λ c →
  if c ≡ᵇ 0 then pureG (varᵉ (here refl))
  else if c ≡ᵇ 1 then (genFn >>=G λ f → genSpineD w d >>=G λ e → pureG (mapᵉ f e))
  else if c ≡ᵇ 2 then (genB 4 >>=G λ k → genSpineD w d >>=G λ e → pureG (takeᵉ (nat̂ k) e))
  else if c ≡ᵇ 3 then
    (genScanFn >>=G λ f → genNat >>=G λ s → genSpineD w d >>=G λ e → pureG (scanᵉ f (nat̂ s) e))
  else if c ≡ᵇ 4 then
    (genSpineD w d >>=G λ e → genB 2 >>=G λ extra → genInners 0 (suc w) d (suc extra) >>=G λ rest →
     pureG (mergeAllᵉ nothing (ofᵉ (strmᵗ e ∷ rest))))
  else if c ≡ᵇ 5 then
    (genB 3 >>=G λ k → genSpineD w d >>=G λ e → genB 2 >>=G λ extra →
     genInners 0 (suc w) d (suc extra) >>=G λ rest →
     pureG (mergeAllᵉ (just (suc k)) (ofᵉ (strmᵗ e ∷ rest))))
  else if c ≡ᵇ 6 then
    (genSpineD w d >>=G λ e → genB 2 >>=G λ extra → genInners 0 (suc w) d (suc extra) >>=G λ rest →
     pureG (switchAllᵉ (ofᵉ (strmᵗ e ∷ rest))))
  else if c ≡ᵇ 7 then
    (genFanFn >>=G λ f → genSpineD w d >>=G λ e →
     pureG (mergeAllᵉ nothing (mapᵉ f e)))
  else
    (genSpineD w d >>=G λ e → genB 2 >>=G λ extra → genInners 0 (suc w) d (suc extra) >>=G λ rest →
     pureG (exhaustAllᵉ (ofᵉ (strmᵗ e ∷ rest))))

-- before the gate: the binder is guarded, so every route ends in a `deferᵉ`
genSpineG g u zero    = pureG (gate (suc g) u (varᵉ (here refl)))
genSpineG g u (suc d) = genB 9 >>=G λ c →
  if c ≡ᵇ 0 then (genSpineD (g + u) d >>=G λ b → pureG (gate (suc g) u b))
  else if c ≡ᵇ 1 then (genSpineD (g + u) d >>=G λ b → pureG (gate (suc g) u b))
  else if c ≡ᵇ 2 then (genFn >>=G λ f → genSpineG g u d >>=G λ e → pureG (mapᵉ f e))
  else if c ≡ᵇ 3 then (genB 4 >>=G λ k → genSpineG g u d >>=G λ e → pureG (takeᵉ (nat̂ k) e))
  else if c ≡ᵇ 4 then
    (genScanFn >>=G λ f → genNat >>=G λ s → genSpineG g u d >>=G λ e → pureG (scanᵉ f (nat̂ s) e))
  else if c ≡ᵇ 5 then
    (genSpineG g u d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u d (suc extra) >>=G λ rest →
     pureG (mergeAllᵉ nothing (ofᵉ (strmᵗ e ∷ rest))))
  else if c ≡ᵇ 6 then
    (genSpineG g u d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u d (suc extra) >>=G λ rest →
     pureG (switchAllᵉ (ofᵉ (strmᵗ e ∷ rest))))
  else if c ≡ᵇ 7 then
    (genFanFn >>=G λ f → genSpineG g u d >>=G λ e →
     pureG (mergeAllᵉ nothing (mapᵉ f e)))
  else
    (genSpineG g u d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u d (suc extra) >>=G λ rest →
     pureG (exhaustAllᵉ (ofᵉ (strmᵗ e ∷ rest))))

genExp : ℕ → Gen (Exp Γ₂ [] [] [] natᵗ)
genExp d = genExpAt 0 0 d

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

marksᵉ  : ∀ {Δᵍ Δ Θ t} → Exp Γ₂ Δᵍ Δ Θ t → Marks
marksᵗ  : ∀ {Δᵍ Δ Θ t} → Tm Γ₂ Δᵍ Δ Θ t → Marks
marksᵗˢ : ∀ {Δᵍ Δ Θ t} → List (Tm Γ₂ Δᵍ Δ Θ t) → Marks

marksᵉ (input i)       = one fInput
marksᵉ (ofᵉ ts)        = one fOf ⊕ marksᵗˢ ts
marksᵉ emptyᵉ          = one fEmpty
marksᵉ (takeᵉ c e)     = one fTake ⊕ marksᵗ c ⊕ marksᵉ e
-- the second component reads the CARRIED state's type, which is the former's
-- own accumulator: `isData (obs _)` is false, so it fires exactly when the
-- former re-binds something the run could subscribe
marksᵉ (mapᵉ f e)      = one fMap ⊕ marksᵗ f ⊕ marksᵉ e
marksᵉ (scanᵉ {t = t} f z e) =
  one fScan ⊕ ([] , not (isData t)) ⊕ marksᵗ f ⊕ marksᵗ z ⊕ marksᵉ e
marksᵉ (mergeAllᵉ _ e) = one fMergeAll ⊕ marksᵉ e
marksᵉ (switchAllᵉ e)  = one fSwitchAll ⊕ marksᵉ e
marksᵉ (batchSyncᵉ e)  = one fBatchSync ⊕ marksᵉ e
marksᵉ (exhaustAllᵉ e) = one fExhaustAll ⊕ marksᵉ e
marksᵉ (μᵉ e)          = one fMu ⊕ marksᵉ e
marksᵉ (varᵉ x)        = one fVar
marksᵉ (deferᵉ e)      = one fDefer ⊕ marksᵉ e
marksᵉ (mintᵉ e)       = one fMint ⊕ marksᵉ e

marksᵗ (varᵗ x)      = noMarks
marksᵗ unit̂          = noMarks
marksᵗ (bool̂ _)      = noMarks
marksᵗ (nat̂ _)       = noMarks
marksᵗ uniq̂          = noMarks
marksᵗ (pairᵗ a b)   = marksᵗ a ⊕ marksᵗ b
marksᵗ (fstᵗ p)      = marksᵗ p
marksᵗ (sndᵗ p)      = marksᵗ p
marksᵗ (inlᵗ a)      = marksᵗ a
marksᵗ (inrᵗ a)      = marksᵗ a
marksᵗ (caseᵗ s l r) = marksᵗ s ⊕ marksᵗ l ⊕ marksᵗ r
marksᵗ (ifᵗ c a b)   = marksᵗ c ⊕ marksᵗ a ⊕ marksᵗ b
marksᵗ (primᵗ _ a)   = marksᵗ a
marksᵗ nilᵗ          = noMarks
marksᵗ (consᵗ a bs)  = marksᵗ a ⊕ marksᵗ bs
marksᵗ (foldᵗ l z f) = marksᵗ l ⊕ marksᵗ z ⊕ marksᵗ f
marksᵗ (strmᵗ e)     = marksᵉ e

marksᵗˢ []       = noMarks
marksᵗˢ (y ∷ ys) = marksᵗ y ⊕ marksᵗˢ ys

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

showPrim : ∀ {s t} → PrimOp s t → String
showPrim add  = "add"
showPrim sub  = "sub"
showPrim mul  = "mul"
showPrim eqᵖ  = "eqᵖ"
showPrim ltᵖ  = "ltᵖ"
showPrim eqᵘ  = "eqᵘ"
showPrim notᵖ = "notᵖ"

showExp : ∀ {Δᵍ Δ Θ t} → Exp Γ₂ Δᵍ Δ Θ t → String
showTm  : ∀ {Δᵍ Δ Θ t} → Tm Γ₂ Δᵍ Δ Θ t → String

showTmList : ∀ {Δᵍ Δ Θ t} → List (Tm Γ₂ Δᵍ Δ Θ t) → String
showTmList []       = "[]"
showTmList (x ∷ xs) = showTm x ++ " ∷ " ++ showTmList xs

-- a variable is rendered by its de Bruijn PATH, not just as "here": corpus D
-- builds templates with nested binders, and a witness that cannot say WHICH
-- binder a variable belongs to is not reproducible — which is the only reason
-- witnesses are printed at all
showIx : ∀ {t} {Θ : List Ty} → t ∈ Θ → String
showIx (here refl) = "(here refl)"
showIx (there x)   = "(there " ++ showIx x ++ ")"

showTm (varᵗ x)           = "(varᵗ " ++ showIx x ++ ")"
showTm unit̂               = "unit̂"
showTm (bool̂ b)           = "(bool̂ " ++ (if b then "true" else "false") ++ ")"
showTm (nat̂ n)            = "(nat̂ " ++ show n ++ ")"
showTm uniq̂               = "uniq̂"
showTm (pairᵗ a b)        = "(pairᵗ " ++ showTm a ++ " " ++ showTm b ++ ")"
showTm (fstᵗ p)           = "(fstᵗ " ++ showTm p ++ ")"
showTm (sndᵗ p)           = "(sndᵗ " ++ showTm p ++ ")"
showTm (inlᵗ a)           = "(inlᵗ " ++ showTm a ++ ")"
showTm (inrᵗ a)           = "(inrᵗ " ++ showTm a ++ ")"
showTm (caseᵗ s l r)      =
  "(caseᵗ " ++ showTm s ++ " " ++ showTm l ++ " " ++ showTm r ++ ")"
showTm (ifᵗ c a b)        =
  "(ifᵗ " ++ showTm c ++ " " ++ showTm a ++ " " ++ showTm b ++ ")"
showTm (primᵗ op a)       = "(primᵗ " ++ showPrim op ++ " " ++ showTm a ++ ")"
showTm nilᵗ               = "nilᵗ"
showTm (consᵗ a bs)       = "(consᵗ " ++ showTm a ++ " " ++ showTm bs ++ ")"
showTm (foldᵗ l z f)      =
  "(foldᵗ " ++ showTm l ++ " " ++ showTm z ++ " " ++ showTm f ++ ")"
showTm (strmᵗ e)          = "(strmᵗ " ++ showExp e ++ ")"

showExp (input i)       = "(input " ++ showFin i ++ ")"
showExp (ofᵉ items)     = "(ofᵉ (" ++ showTmList items ++ "))"
showExp emptyᵉ          = "emptyᵉ"
showExp (takeᵉ n e)     = "(takeᵉ " ++ showTm n ++ " " ++ showExp e ++ ")"
showExp (mapᵉ f e)      = "(mapᵉ " ++ showTm f ++ " " ++ showExp e ++ ")"
showExp (scanᵉ f s e)   = "(scanᵉ " ++ showTm f ++ " " ++ showTm s ++ " " ++ showExp e ++ ")"
-- the limit prints as the `Maybe ℕ` it IS, not as the ∞ a reader would
-- prefer: a witness is printed to be PASTED, and the corpus is Agda
showExp (mergeAllᵉ nothing s)  = "(mergeAllᵉ nothing " ++ showExp s ++ ")"
showExp (mergeAllᵉ (just k) s) =
  "(mergeAllᵉ (just " ++ show k ++ ") " ++ showExp s ++ ")"
showExp (switchAllᵉ s)  = "(switchAllᵉ " ++ showExp s ++ ")"
showExp (batchSyncᵉ s)  = "(batchSyncᵉ " ++ showExp s ++ ")"
showExp (exhaustAllᵉ s) = "(exhaustAllᵉ " ++ showExp s ++ ")"
showExp (μᵉ e)          = "(μᵉ " ++ showExp e ++ ")"
showExp (varᵉ x)        = "(varᵉ " ++ showIx x ++ ")"
showExp (deferᵉ e)      = "(deferᵉ " ++ showExp e ++ ")"
showExp (mintᵉ e)       = "(mintᵉ " ++ showExp e ++ ")"

-- slots render AFTER showExp because a shared slot's DEF is an expression and
-- must be printed: a corpus-B witness whose slots read "shared" is not
-- reproducible, which is the whole point of printing a witness
showSlot : ∀ {k} → Slot Γ₂ k natᵗ → String
showSlot (scripted i) = "scripted (" ++ showInput i ++ ")"
showSlot (shared d)   = "shared " ++ showExp d

showSlots : Slots Γ₂ → String
showSlots ins =
  "(λ { zero → " ++ showSlot (ins zero)
    ++ " ; (suc zero) → " ++ showSlot (ins (suc zero))
    ++ " ; (suc (suc ())) })"

------------------------------------------------------------------------
-- one case, a run, and reporting

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
pasteRow : Exp Γ₂ [] [] [] natᵗ → Slots Γ₂ → String
pasteRow e ins =
  "\n-- <<<PASTE\n  cached \"?\" " ++ show FUEL ++ "\n          "
       ++ showExp e ++ "\n          " ++ showSlots ins
       ++ " ∷\n-- PASTE>>>\n"

report : Exp Γ₂ [] [] [] natᵗ → Slots Γ₂
       → List (InstEmit (List ℕ)) → List (InstEmit (List ℕ)) → String
report e ins impl spec =
  "  FAIL\n    impl = " ++ showBatched impl
       ++ "\n    spec = " ++ showBatched spec ++ pasteRow e ins

-- a WellFormed violation of the evaluator's raw output
reportWF : Exp Γ₂ [] [] [] natᵗ → Slots Γ₂ → List (InstEmit ℕ) → String
reportWF e ins s =
  "  WF-FAIL\n    stream = " ++ showStream s ++ pasteRow e ins

-- two checks on one generated program: impl ≡ spec on the batched stream,
-- and the raw stream satisfies the protocol automaton
-- (evaluate-well-formed, sampled).
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

oneCase : ℕ → Gen (Marks × List String)
oneCase d = genSlots >>=G λ ins → genExp d >>=G λ e →
  let s    = evaluate↓ FUEL e ins
      impl = impl-batchSimultaneous s
      spec = spec-batchSimultaneous s
      agreeFails = if eqBatched impl spec then [] else report e ins impl spec ∷ []
      wfFails    = if wellFormed? s then [] else reportWF e ins s ∷ []
  in pureG (marksᵉ e , agreeFails ++ᴸ wfFails)

-- accumulate EVERY failing case's reports, in generation order, and tally
-- which recursion constructors the corpus actually reached
runN : ℕ → ℕ → Gen (Tally × List String)
runN zero    d = pureG (zeroTally , [])
runN (suc k) d = oneCase d >>=G λ r → runN k d >>=G λ acc →
  pureG (bump (proj₁ r) (proj₁ acc) , proj₂ r ++ᴸ proj₂ acc)

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

-- every failing case's paste block, concatenated (each is self-delimited
-- by its own <<<PASTE / PASTE>>> markers, so gen-unit-tests.sh can split
-- them); "(all agree)" when the run turned up nothing
-- the census, on its own line and in `<tag> <count>` pairs: a sweep is a
-- run of many seeds, so the verdict on whether a former was reached AT
-- ALL belongs to the caller summing these, not to any one run
censusPairs : List Former → List ℕ → List String
censusPairs (f ∷ gs) (c ∷ cs) = formerTag f ∷ " " ∷ show c ∷ " " ∷ censusPairs gs cs
censusPairs _        _        = []

dumpFails : List String → String
dumpFails []       = "  (all agree)\n"
dumpFails (f ∷ fs) = concatStr (f ∷ fs)

-- ADVANCE THE GENERATOR WITHOUT RUNNING ANYTHING, so that a case which
-- costs more than the whole sweep it belongs to can still be READ.  Such
-- a case is invisible to every other route the harness has: the failure
-- report is what prints a program, and the run that would print this one
-- is the run that does not finish.  Skipping is exact rather than
-- approximate because generation is UPSTREAM of evaluation and consumes
-- the same randomness whether or not the program is then run -- so case
-- N reached this way is the same program case N is in a full sweep.
skipN : ℕ → ℕ → Gen ℕ
skipN zero    d = pureG 0
skipN (suc k) d = genSlots >>=G λ _ → genExp d >>=G λ _ → skipN k d

-- the paste row of ONE case, named by its 1-based index
showAt : ℕ → ℕ → Gen String
showAt n d = skipN (n ∸ 1) d >>=G λ _ →
  genSlots >>=G λ ins → genExp d >>=G λ e → pureG (pasteRow e ins)

main : IO Unit
main = getContents >>= λ s →
  let cs    = toCodes s
      seed  = parseNat cs
      runs  = numAt 1 200 cs
      d     = numAt 2 4 cs
      at    = numAt 3 0 cs
      res   = proj₁ (runN runs d (randList seed 2000000))
      tally = proj₁ res
      fails = proj₂ res
  in if not (at ≡ᵇ 0)
     then putStr (proj₁ (showAt at d (randList seed 2000000)))
     else putStr (concatStr
       (( "seed " ∷ show seed ∷ " depth " ∷ show d ∷ " — ran " ∷ show runs
        ∷ " cases, " ∷ show (length fails) ∷ " failures"
        ∷ "; obs-fold " ∷ show (proj₂ tally) ∷ "\ncensus " ∷ [])
        ++ᴸ censusPairs allFormers (proj₁ tally)
        ++ᴸ ("\n" ∷ dumpFails fails ∷ [])))
