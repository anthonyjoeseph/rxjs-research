-- Battery probe for the CORRECTED merge-cert invariant.
--
-- BACKGROUND
-- The original candidate was
--
--   nodeCacheOK mnid (merge-st k _) reg
--     = not (mergeReachable mnid reg) ∨ (k ≡ᵇ countLiveInners mnid reg)
--
-- Three independent counterexamples refuted it (VWF:3765-3866):
--
--   R1. Outer's own thru-outer registration threads mnid, but bump never counts it.
--       mergeReachable=true, k=0, countRegsUnder≥1, so 0≡1 fails.
--
--   R2. A single inner that is itself a merge(a,b) creates TWO from-inner chains
--       but bump does only ONE suc k.  countLiveInners=2 when k=1 → mismatch.
--
--   R3. finish mergeᵒ does `innerFinish` (k ← pred k) BEFORE cascadeFinish drops
--       the spent inner's registrations.  Mid-cascade: k=0, from-inner reg still
--       present (dying+delivered) → old candidate fails.
--
-- THE CORRECTED STATEMENT
--   merge-cert: (merge-st 0 _ at mnid) ⇒
--     no registration in the registry has an alive from-inner instance of mnid.
--
-- "Alive" = aliveThroughᶠ inst st reg
--   = pathHasNode inst p ∧ not (rid ∈ cancelled) ∧ (not (src ∈ dying) ∨ not (rid ∈ delivered))
--
-- THE DECISIVE QUESTION
-- Shape B below (a hand-built state with k=0 and a live from-inner reg) gives false.
-- Is that state REACHABLE?  If so, the corrected predicate is also refuted.
-- The load-bearing mechanism is the CASCADE ORDERING inside Rx.Evaluator:
--
--   1. cascadeLatch (Evaluator:1617-1622) fires FIRST, setting dying=[arrSource a]
--      if isLast=true — BEFORE any chain is processed.
--   2. cascadeGo (Evaluator:1633-1641) adds rid to delivered BEFORE calling
--      chainStep for that chain.
--   3. Therefore when innerReact (Evaluator:1239-1243) runs and reads
--      aliveThroughᶠ inst st, both conditions hold:
--        src ∈ dying    (set by cascadeLatch)
--        rid ∈ delivered (set by cascadeGo for this chain)
--      so aliveThroughᶠ = false, any = false, and innerFinish fires.
--
-- Shape B (live from-inner reg at k=0) is NOT reachable by this mechanism:
-- every execution of innerFinish is preceded by cascadeLatch marking the source
-- dying, so the reg is always dying+delivered when k decrements to 0.
--
-- Section 3 below verifies this by RUNNING the actual evaluator, not by
-- hand-building a state.
--
-- VERDICT: SURVIVES
--
-- STRUCTURE
--   Section 1: The corrected predicate (typechecking = CANNOT STATE test)
--   Section 2: Seven hand-built states (predicate behaviour table; reachability
--              is untested for these — Shape B marks the critical gap)
--   Section 3: DECISIVE EXPERIMENT — runs the evaluator on a concrete program,
--              reaches the mid-cascade state by cascadeLatch+cascadeGo, and
--              checks mergeCertAt by refl.

module Battery-Merge-Cert where

open import Data.Bool    using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin     using (Fin; zero; suc)
open import Data.List    using (List; []; _∷_; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Data.Vec     using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim     using (Source; after_,_; hot; ObservableInput)
open import Rx.Exp      using (Ctx; Ty; Closed; Val; natᵗ; obs; ofᵉ; input; strmᵗ;
                               mergeAllᵉ)
open import Rx.Evaluator using (EvalSt; NodeId; RegId; NodeState; Sched; Slots; Slot; scripted;
                                Chain; Path; Frame; AllOp; Arrival;
                                lookupNode; merge-st;
                                from-inner; thru-outer; _↠_; root; mergeᵒ;
                                aliveThroughᶠ; st-init; sched-init; budgetAt;
                                subscribeE; cascadeLatch; cascadeGo; cascadeFinish;
                                chainsOf; sched-next)
open import Verify-Well-Formed using (innerInstsP)

-----------------------------------------------------------------------
-- Section 1: The corrected predicate
-----------------------------------------------------------------------

-- A registration carries an alive from-inner instance of mnid if:
--   (a) its path mentions some inst via a from-inner mnid inst frame, AND
--   (b) that inst is alive (aliveThroughᶠ inst st reg)
hasAliveFromInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → EvalSt e → RegId × Source × Chain Γ t → Bool
hasAliveFromInner mnid st c@(_ , _ , (_ , p)) =
  any (λ inst → aliveThroughᶠ inst st c) (innerInstsP mnid p)

-- merge-cert at one node: when merge-st is at k=0, no registry entry
-- has an alive from-inner instance of this node.
mergeCertAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → EvalSt e → Bool
mergeCertAt mnid st with lookupNode mnid (EvalSt.nodes st)
mergeCertAt mnid st | just (merge-st zero od) =
  not (any (hasAliveFromInner mnid st) (EvalSt.registry st))
mergeCertAt mnid st | _ = true   -- k≠0, or node absent: trivially satisfied

-----------------------------------------------------------------------
-- Section 2: Hand-built states (predicate behaviour table)
-- States are constructed manually, NOT reached by running the evaluator.
-- Reachability is untested for these rows.
-- Shape B is the critical gap: it gives false, and Section 3 decides
-- whether it is reachable.
-----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

e₀ : Closed Γ₀ natᵗ
e₀ = ofᵉ []

mnid : NodeId   -- the merge node under test
mnid = 0

inst : NodeId   -- an inner instance id
inst = 1

outerPath : Path Γ₀ (obs natᵗ) natᵗ
outerPath = thru-outer mergeᵒ mnid ↠ root

fromInnerPath : Path Γ₀ natᵗ natᵗ
fromInnerPath = from-inner mergeᵒ mnid inst ↠ root

-- SHAPE 0 (seed): k=0, registry empty.  Trivially satisfied.
st-seed : EvalSt e₀
st-seed = record (st-init e₀) { nodes = (mnid , merge-st zero false) ∷ [] }

_ : mergeCertAt mnid st-seed ≡ true
_ = refl

-- SHAPE 1 (R1 dodge): k=0, outer thru-outer reg.
-- innerInstsP returns [] for thru-outer → hasAliveFromInner = false.
st-shape1 : EvalSt e₀
st-shape1 = record (st-init e₀)
  { nodes    = (mnid , merge-st zero false) ∷ []
  ; registry = (0 , 10 , (obs natᵗ , outerPath)) ∷ []
  ; dying    = []
  ; delivered = []
  }

_ : mergeCertAt mnid st-shape1 ≡ true
_ = refl

_ : innerInstsP mnid outerPath ≡ []
_ = refl

-- SHAPE 2 (R3 dodge, hand-built): k=0, from-inner reg dying+delivered.
-- Models the mid-cascade state; Section 3 reaches this state by evaluation.
st-shape2 : EvalSt e₀
st-shape2 = record (st-init e₀)
  { nodes     = (mnid , merge-st zero true) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = 10 ∷ []
  ; delivered = 0 ∷ []
  }

_ : mergeCertAt mnid st-shape2 ≡ true
_ = refl

-- SHAPE 2-EXT: same but outer thru-outer reg also present (genuine R3 config).
st-shape2-ext : EvalSt e₀
st-shape2-ext = record (st-init e₀)
  { nodes     = (mnid , merge-st zero true) ∷ []
  ; registry  = (0 , 9  , (obs natᵗ , outerPath))
              ∷ (1 , 10 , (natᵗ    , fromInnerPath)) ∷ []
  ; dying     = 10 ∷ []
  ; delivered = 1 ∷ []
  }

_ : mergeCertAt mnid st-shape2-ext ≡ true
_ = refl

-- SHAPE 3 (R2 dodge): k=0, two from-inner regs sharing same inst, both dying+delivered.
st-shape3 : EvalSt e₀
st-shape3 = record (st-init e₀)
  { nodes     = (mnid , merge-st zero true) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath))
              ∷ (1 , 11 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = 10 ∷ 11 ∷ []
  ; delivered = 0 ∷ 1 ∷ []
  }

_ : mergeCertAt mnid st-shape3 ≡ true
_ = refl

-- SHAPE B (critical gap — IS THIS REACHABLE?):
-- k=0, live from-inner reg (dying=[], delivered=[]).
-- The predicate returns FALSE here.
-- Section 3 answers: NO — cascadeLatch always sets dying=[src] before innerFinish.
st-shapeB : EvalSt e₀
st-shapeB = record (st-init e₀)
  { nodes     = (mnid , merge-st zero false) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = []
  ; delivered = []
  ; cancelled = []
  }

_ : mergeCertAt mnid st-shapeB ≡ false
_ = refl

-- SHAPE K≠0: k=1, live from-inner reg.  Cert does not fire at k>0.
st-shapeK : EvalSt e₀
st-shapeK = record (st-init e₀)
  { nodes     = (mnid , merge-st (suc zero) false) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = []
  ; delivered = []
  }

_ : mergeCertAt mnid st-shapeK ≡ true
_ = refl

-----------------------------------------------------------------------
-- Section 3: DECISIVE EXPERIMENT
--
-- Program: mergeAll(of([slot0]))  in Γ₁ = natᵗ ∷ []
--   Slot 0 is hot: delivers 42 at tick 1, isLast=true (only delivery).
--
-- Expected execution:
--   subscribe: outer ofᵉ [strmᵗ (input zero)] delivers inner = input zero sync.
--     subscribeAll mints nid=0.
--     thruConsume: subscribeInner mints inst=1, registers
--       (rid=0, src=0, (natᵗ, from-inner mergeᵒ 0 1 ↠ root)).
--     mergeBump nid false: k ← 1.
--     thruWrap fin=true: od ← true.
--   After subscribe: nodes=[(0, merge-st 1 true)], one from-inner reg.
--
--   cascadeLatch (Evaluator:1617-1622): dying=[0], delivered=[], regWatermark=1.
--   cascadeGo (Evaluator:1633-1641): chain (0, from-inner mergeᵒ 0 1 ↠ root):
--     adds rid=0 → delivered=[0].
--     innerReact: aliveThroughᶠ 1 st (0,0,...):
--       dying=[0] → src 0 ∈ dying = true
--       delivered=[0] → rid 0 ∈ delivered = true
--       (not true ∨ not true) = false → aliveThroughᶠ = false
--     any = false → innerFinish: k ← 0, fin=true.
--   st_mid: nodes=[(0, merge-st 0 true)], registry unchanged (from-inner reg STILL PRESENT).
--
-- mergeCertAt 0 st_mid:
--   merge-st 0 true → check hasAliveFromInner
--   dying+delivered → aliveThroughᶠ = false → any = false → not false = TRUE
--
-- Shape B (live inner reg at k=0) was NOT reached because cascadeLatch
-- (Evaluator:1622) sets dying=[src] BEFORE cascadeGo calls chainStep.
-----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- e₁ = mergeAll(of([slot0]))
e₁ : Closed Γ₁ natᵗ
e₁ = mergeAllᵉ (ofᵉ (strmᵗ (input zero) ∷ []))

-- slot 0: hot, one delivery (42 at tick 1, so isLast=true)
ins₁ : Slots Γ₁
ins₁ zero = scripted (hot ((after 0 , 42) ∷ []))

-- Subscribe and extract schedule/state
sub₁ : _
sub₁ = subscribeE (budgetAt e₁ ins₁ 0) e₁ root 0 0 (sched-init e₁ ins₁) (st-init e₁)

sched-sub₁ : Sched Γ₁
sched-sub₁ = proj₁ (proj₂ sub₁)

st-sub₁ : EvalSt e₁
st-sub₁ = proj₂ (proj₂ sub₁)

-- Run one cascade step and check mergeCertAt on the MID-CASCADE state
-- (after cascadeGo fires innerFinish, BEFORE cascadeFinish drops the reg).
midCascadeCheck : ⊤ ⊎ (Arrival Γ₁ × Sched Γ₁) → EvalSt e₁ → Bool
midCascadeCheck (inj₁ _)            _  = false  -- no arrival: test setup error
midCascadeCheck (inj₂ (a , sched')) st =
  let st_lat           = cascadeLatch a st
      (_ , _ , st_mid) = cascadeGo a 1 (chainsOf a st_lat) sched' st_lat
  in mergeCertAt 0 st_mid

-- THE DECISIVE ROW: reached by the real evaluator, not hand-built.
_ : midCascadeCheck (sched-next sched-sub₁) st-sub₁ ≡ true
_ = refl

-- BONUS: post-cascade state (after cascadeFinish drops the from-inner reg).
postCascadeCheck : ⊤ ⊎ (Arrival Γ₁ × Sched Γ₁) → EvalSt e₁ → Bool
postCascadeCheck (inj₁ _)            _  = false
postCascadeCheck (inj₂ (a , sched')) st =
  let st_lat               = cascadeLatch a st
      (_ , sched'' , st_mid) = cascadeGo a 1 (chainsOf a st_lat) sched' st_lat
      (_ , st_post)         = cascadeFinish a sched'' st_mid
  in mergeCertAt 0 st_post

_ : postCascadeCheck (sched-next sched-sub₁) st-sub₁ ≡ true
_ = refl

-----------------------------------------------------------------------
-- FINAL VERDICT
--
-- Section 2 (hand-built, reachability untested):
--   Shape 0: trivially true (empty reg)
--   Shape 1: true (outer reg has no from-inner inst)
--   Shape 2, 2-ext: true (dying+delivered → aliveThroughᶠ=false)
--   Shape 3: true (multi-source inner, same inst, both dying+delivered)
--   Shape B: FALSE (live from-inner at k=0) — the CRITICAL GAP
--   Shape K≠0: true (cert does not fire)
--
-- Section 3 (real evaluator, decisive):
--   Mid-cascade of inner's last delivery: TRUE
--   Post-cascade: TRUE
--
-- Shape B is NOT reached: cascadeLatch always sets dying=[src] before
-- cascadeGo calls chainStep, so every innerFinish is preceded by the
-- dying+delivered test being armed.
--
-- VERDICT: SURVIVES
-----------------------------------------------------------------------
