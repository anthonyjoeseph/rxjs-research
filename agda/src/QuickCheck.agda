-- An all-Agda QuickCheck: generate random well-typed programs (exp tree +
-- scripted inputs) over a fixed 2-slot nat context, run them through the
-- evaluator, and check impl-batchSimultaneous ≡ spec-batchSimultaneous on
-- the resulting stream. A fast in-Agda dev loop for the implementation.
--
--   agda --compile --compile-dir=_cli src/QuickCheck.agda
--   echo "<seed> [runs] [depth]" | ./_cli/QuickCheck
--
-- The fragment is monomorphic (all values ℕ — batching is value-agnostic)
-- and its map/scan fns never return observables (closeUnderFn never
-- forced). Repeated inner refs to a source inside an *All make diamonds —
-- multiple emits in one instant, the batcher's interesting case.
--
-- IT REACHES `μᵉ`, AND THAT IS WHAT PUTS THE SWEEP ON THE DESCENT. The
-- rank guard lives under recursion, so a μ-free generator could never
-- produce the shape the one open reading of `rank-sufficient` is about,
-- however many seeds it ran. Recursion is generated with its binder
-- scopes carried as indices rather than checked afterwards — the
-- generator's type is `Exp` at the two μ contexts, so a synchronous
-- self-reference is not a program it can emit and be rejected for; it is
-- one it cannot write down.  The summary line carries how many of the run's
-- programs actually carried each recursion constructor, because reaching the
-- region is the claim and it is a number.
module QuickCheck where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
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

open import Rx.Prim using (Timed; after_,_; ObservableInput; hot; cold;
                           InstEvent; init; value; close; handoff; complete;
                           CloseReason; cut; cutPending; exhausted; EmitKind;
                           subscribe; delivery; plumbing; InstEmit; _at_from_as_)
open import Rx.Exp using (Ty; natᵗ; obs; _×ᵗ_; Ctx; Exp; Tm; Fn; PrimOp; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  unit̂; bool̂; nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ;
  strmᵗ; varᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ)
open import Data.List.Membership.Propositional using (_∈_)
open import Rx.Evaluator using (evaluate; hasDry)
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

-- value functions (natᵗ → natᵗ): identity, +k, *k
genFn : ∀ {Δᵍ Δ Θ} → Gen (Fn Γ₂ Δᵍ Δ Θ natᵗ natᵗ)
genFn = genB 3 >>=G λ c → genNat >>=G λ k →
  pureG (if c ≡ᵇ 0 then varᵗ (here refl)
    else if c ≡ᵇ 1 then primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ k))
    else primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ k)))

-- scan step (acc, cur) → acc + cur
genScanFn : ∀ {Δᵍ Δ Θ} → Gen (Fn Γ₂ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) natᵗ)
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
genExpAt g u (suc d) = genB 12 >>=G λ c →
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
  else genLeafAt g u

genInners g u d zero    = pureG []
genInners g u d (suc n) =
  genExpAt g u d >>=G λ e → genInners g u d n >>=G λ rest → pureG (strmᵗ e ∷ rest)

genObsAt g u d =
  genB 2 >>=G λ extra → genInners g u d (suc (suc extra)) >>=G λ items →
  pureG (ofᵉ items)

-- past the gate: the var is in scope and this subtree plants exactly one
genSpineD w zero    = pureG (varᵉ (here refl))
genSpineD w (suc d) = genB 8 >>=G λ c →
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
  else
    (genSpineD w d >>=G λ e → genB 2 >>=G λ extra → genInners 0 (suc w) d (suc extra) >>=G λ rest →
     pureG (exhaustAllᵉ (ofᵉ (strmᵗ e ∷ rest))))

-- before the gate: the binder is guarded, so every route ends in a `deferᵉ`
genSpineG g u zero    = pureG (gate (suc g) u (varᵉ (here refl)))
genSpineG g u (suc d) = genB 8 >>=G λ c →
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
  else
    (genSpineG g u d >>=G λ e → genB 2 >>=G λ extra →
     genInners (suc g) u d (suc extra) >>=G λ rest →
     pureG (exhaustAllᵉ (ofᵉ (strmᵗ e ∷ rest))))

genExp : ℕ → Gen (Exp Γ₂ [] [] [] natᵗ)
genExp d = genExpAt 0 0 d

------------------------------------------------------------------------
-- WHICH RECURSION CONSTRUCTORS A PROGRAM ACTUALLY CARRIED.  A generator
-- that CAN emit `μᵉ` says nothing about a sweep; what the descent's rank
-- guard needs is that runs REACH the shape, and that is a number rather
-- than a claim.  Each case reports its program's three marks and the
-- summary line totals them, so a coverage receipt can name the region it
-- covered instead of the constructors that were added.

Marks : Set
Marks = Bool × Bool × Bool            -- μᵉ · varᵉ · deferᵉ

noMarks : Marks
noMarks = false , false , false

infixr 5 _⊕_
_⊕_ : Marks → Marks → Marks
(a , b , c) ⊕ (x , y , z) = (a ∨ x) , (b ∨ y) , (c ∨ z)

marksᵉ  : ∀ {Δᵍ Δ Θ t} → Exp Γ₂ Δᵍ Δ Θ t → Marks
marksᵗ  : ∀ {Δᵍ Δ Θ t} → Tm Γ₂ Δᵍ Δ Θ t → Marks
marksᵗˢ : ∀ {Δᵍ Δ Θ t} → List (Tm Γ₂ Δᵍ Δ Θ t) → Marks

marksᵉ (input i)       = noMarks
marksᵉ (ofᵉ ts)        = marksᵗˢ ts
marksᵉ emptyᵉ          = noMarks
marksᵉ (mapᵉ f e)      = marksᵗ f ⊕ marksᵉ e
marksᵉ (takeᵉ c e)     = marksᵗ c ⊕ marksᵉ e
marksᵉ (scanᵉ f z e)   = marksᵗ f ⊕ marksᵗ z ⊕ marksᵉ e
marksᵉ (mergeAllᵉ _ e) = marksᵉ e
marksᵉ (switchAllᵉ e)  = marksᵉ e
marksᵉ (exhaustAllᵉ e) = marksᵉ e
marksᵉ (μᵉ e)          = (true , false , false) ⊕ marksᵉ e
marksᵉ (varᵉ x)        = false , true , false
marksᵉ (deferᵉ e)      = (false , false , true) ⊕ marksᵉ e

marksᵗ (varᵗ x)      = noMarks
marksᵗ unit̂          = noMarks
marksᵗ (bool̂ _)      = noMarks
marksᵗ (nat̂ _)       = noMarks
marksᵗ (pairᵗ a b)   = marksᵗ a ⊕ marksᵗ b
marksᵗ (fstᵗ p)      = marksᵗ p
marksᵗ (sndᵗ p)      = marksᵗ p
marksᵗ (inlᵗ a)      = marksᵗ a
marksᵗ (inrᵗ a)      = marksᵗ a
marksᵗ (caseᵗ s l r) = marksᵗ s ⊕ marksᵗ l ⊕ marksᵗ r
marksᵗ (ifᵗ c a b)   = marksᵗ c ⊕ marksᵗ a ⊕ marksᵗ b
marksᵗ (primᵗ _ a)   = marksᵗ a
marksᵗ (strmᵗ e)     = marksᵉ e

marksᵗˢ []       = noMarks
marksᵗˢ (y ∷ ys) = marksᵗ y ⊕ marksᵗˢ ys

------------------------------------------------------------------------
-- comparison of two batched streams (impl vs spec fed the SAME evaluate
-- output, so ids match exactly — no renaming needed)

eqKind : EmitKind → EmitKind → Bool
eqKind subscribe subscribe = true
eqKind delivery  delivery  = true
eqKind plumbing  plumbing  = true
eqKind _         _         = false

eqReason : CloseReason → CloseReason → Bool
eqReason cut        cut        = true
eqReason cutPending cutPending = true
eqReason exhausted  exhausted  = true
eqReason _          _          = false

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

showPrim : ∀ {s t} → PrimOp s t → String
showPrim add  = "add"
showPrim sub  = "sub"
showPrim mul  = "mul"
showPrim eqᵖ  = "eqᵖ"
showPrim ltᵖ  = "ltᵖ"
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
showTm (strmᵗ e)          = "(strmᵗ " ++ showExp e ++ ")"

showExp (input i)       = "(input " ++ showFin i ++ ")"
showExp (ofᵉ items)     = "(ofᵉ (" ++ showTmList items ++ "))"
showExp emptyᵉ          = "emptyᵉ"
showExp (mapᵉ f e)      = "(mapᵉ " ++ showTm f ++ " " ++ showExp e ++ ")"
showExp (takeᵉ n e)     = "(takeᵉ " ++ showTm n ++ " " ++ showExp e ++ ")"
showExp (scanᵉ f s e)   = "(scanᵉ " ++ showTm f ++ " " ++ showTm s ++ " " ++ showExp e ++ ")"
showExp (mergeAllᵉ nothing s)  = "(mergeAllᵉ ∞ " ++ showExp s ++ ")"
showExp (mergeAllᵉ (just k) s) = "(mergeAllᵉ " ++ show k ++ " " ++ showExp s ++ ")"
showExp (switchAllᵉ s)  = "(switchAllᵉ " ++ showExp s ++ ")"
showExp (exhaustAllᵉ s) = "(exhaustAllᵉ " ++ showExp s ++ ")"
showExp (μᵉ e)          = "(μᵉ " ++ showExp e ++ ")"
showExp (varᵉ x)        = "(varᵉ " ++ showIx x ++ ")"
showExp (deferᵉ e)      = "(deferᵉ " ++ showExp e ++ ")"

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

-- a WellFormed violation of the evaluator's raw output. The {- WF -}
-- prefix keeps this block's dedup key (line 2, the program line)
-- distinct from the Agree block of the same program.
reportWF : Exp Γ₂ [] [] [] natᵗ → Slots Γ₂ → List (InstEmit ℕ) → String
reportWF e ins s =
  "  WF-FAIL\n    stream = " ++ showStream s
       ++ "\n-- <<<PASTE\n_ : WellFormedOutput " ++ show FUEL
       ++ "\n          {- WF -} " ++ showExp e ++ "\n          " ++ showSlots ins
       ++ "\n_ = refl\n-- PASTE>>>\n"

-- A DESCENT GUARD WAS EXHAUSTED, which is `rank-sufficient` instantiated and
-- found false.  It gets no PASTE markers on purpose: the bug cache's
-- invariant is impl ≡ spec, and a dry run is a counterexample to a POSTULATE
-- rather than a disagreement between two implementations of one batching.
-- The WF check catches it too — a `dried` close names a source nothing
-- inited — but only as a protocol violation, which is the wrong name for it.
reportDry : Exp Γ₂ [] [] [] natᵗ → Slots Γ₂ → String
reportDry e ins =
  "  DRY-FAIL — a descent guard was exhausted: a counterexample to\n"
       ++ "  rank-sufficient, NOT a bug-cache entry.\n    prog  = " ++ showExp e
       ++ "\n    slots = " ++ showSlots ins ++ "\n"

-- three checks on one generated program: impl ≡ spec on the batched stream,
-- the raw stream satisfies the protocol automaton (evaluate-well-formed,
-- sampled), and the run never went dry (rank-sufficient, instantiated)
Tally : Set
Tally = ℕ × ℕ × ℕ                     -- programs carrying μᵉ · varᵉ · deferᵉ

bump : Marks → Tally → Tally
bump (m , v , f) (a , b , c) =
  (if m then suc a else a) , (if v then suc b else b) , (if f then suc c else c)

oneCase : ℕ → Gen (Marks × List String)
oneCase d = genSlots >>=G λ ins → genExp d >>=G λ e →
  let s    = evaluate FUEL e ins
      impl = impl-batchSimultaneous s
      spec = spec-batchSimultaneous s
      agreeFails = if eqBatched impl spec then [] else report e ins impl spec ∷ []
      wfFails    = if wellFormed? s then [] else reportWF e ins s ∷ []
      dryFails   = if hasDry s then reportDry e ins ∷ [] else []
  in pureG (marksᵉ e , agreeFails ++ᴸ wfFails ++ᴸ dryFails)

-- accumulate EVERY failing case's reports, in generation order, and tally
-- which recursion constructors the corpus actually reached
runN : ℕ → ℕ → Gen (Tally × List String)
runN zero    d = pureG ((0 , 0 , 0) , [])
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
dumpFails : List String → String
dumpFails []       = "  (all agree)\n"
dumpFails (f ∷ fs) = concatStr (f ∷ fs)

main : IO Unit
main = getContents >>= λ s →
  let cs    = toCodes s
      seed  = parseNat cs
      runs  = numAt 1 200 cs
      d     = numAt 2 4 cs
      res   = proj₁ (runN runs d (randList seed 2000000))
      tally = proj₁ res
      fails = proj₂ res
  in putStr (concatStr
       ( "seed " ∷ show seed ∷ " depth " ∷ show d ∷ " — ran " ∷ show runs
       ∷ " cases, " ∷ show (length fails) ∷ " failures"
       ∷ "; μ " ∷ show (proj₁ tally)
       ∷ " var " ∷ show (proj₁ (proj₂ tally))
       ∷ " defer " ∷ show (proj₂ (proj₂ tally)) ∷ "\n"
       ∷ dumpFails fails ∷ []))
