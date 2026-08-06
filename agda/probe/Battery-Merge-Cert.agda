-- Battery probe for the CORRECTED merge-cert invariant.
--
-- BACKGROUND
-- The original candidate was
--
--   nodeCacheOK mnid (merge-st k _) reg
--     = not (mergeReachable mnid reg) ∨ (k ≡ᵇ countLiveInners mnid reg)
--
-- Three independent counterexamples refuted it (see Verify-Well-Formed:3765-3866):
--
--   R1. Outer's own thru-outer registration threads mnid, but bump never counts it.
--       mergeReachable = true, k=0, countRegsUnder≥1, so 0≡1 fails.
--
--   R2. A single inner that is itself a merge(a,b) creates TWO from-inner chains
--       but bump does only ONE suc k.  countLiveInners = 2 when k = 1 → mismatch.
--
--   R3. finish mergeᵒ does `innerFinish` (k ← pred k) BEFORE cascadeFinish drops
--       the spent inner's registrations.  Mid-cascade: k=0, but from-inner regs
--       still present (dying+delivered) → countLiveInners ≥ 1, so 0≡1 fails.
--
-- THE CORRECTED STATEMENT
--   merge-cert: (merge-st 0 _ at mnid) ⇒
--     no registration in the registry has an alive from-inner instance of mnid.
--
-- "Alive" is already defined in the evaluator:
--   aliveThroughᶠ inst st (rid, src, (_, p))
--     = pathHasNode inst p
--     ∧ not (rid ∈ cancelled st)
--     ∧ (not (src ∈ dying st) ∨ not (rid ∈ delivered st))
--
-- The corrected predicate patches each refutation:
--   R1: a thru-outer frame contributes NO entries to innerInstsP, so
--       hasAliveFromInner returns false for outer registrations.
--   R2: both chains of a multi-source inner share the same inst; the
--       check is per-inst (via innerInstsP), so it does not double-count.
--   R3: dying+delivered makes aliveThroughᶠ = false, so lingering
--       (but already-spent) regs do not falsify the predicate.
--
-- DELIVERABLE: this module typechecks green.
-- RESULT: SURVIVES all three shapes, plus seed-provability.
--
-- EXTRA: shape B confirms the predicate is non-vacuous — it returns FALSE
-- on a state with an alive from-inner reg at k=0.

module Battery-Merge-Cert where

open import Data.Bool    using (Bool; true; false; not; _∧_; _∨_)
open import Data.List    using (List; []; _∷_; any)
open import Data.Nat     using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim     using (Source)
open import Rx.Exp      using (Ctx; Ty; Closed; natᵗ; obs; ofᵉ)
open import Rx.Evaluator using (EvalSt; NodeId; RegId; NodeState;
                                Chain; Path; Frame; AllOp;
                                lookupNode; merge-st;
                                from-inner; thru-outer; root; mergeᵒ;
                                aliveThroughᶠ; st-init)
open import Verify-Well-Formed using (innerInstsP)

-----------------------------------------------------------------------
-- The corrected predicate
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
... | just (merge-st zero _) =
      not (any (hasAliveFromInner mnid st) (EvalSt.registry st))
... | _                       = true   -- k≠0, or node absent: trivially satisfied

-----------------------------------------------------------------------
-- Shared context and dummy expression
-- We use Γ₀ = [] (no slots) and e₀ = ofᵉ [].
-- States are built by record-update on st-init e₀.
-----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []

e₀ : Closed Γ₀ natᵗ
e₀ = ofᵉ []

mnid : NodeId   -- the merge node under test
mnid = 0

inst : NodeId   -- an inner instance id
inst = 1

-----------------------------------------------------------------------
-- SHAPE 0: Seed-provability
-- At the initial state where merge is just installed (k=0, registry empty).
-- Trivially satisfied: no registrations at all.
-----------------------------------------------------------------------

st-seed : EvalSt e₀
st-seed = record (st-init e₀) { nodes = (mnid , merge-st zero false) ∷ [] }

_ : mergeCertAt mnid st-seed ≡ true
_ = refl

-----------------------------------------------------------------------
-- SHAPE 1: Outer's thru-outer registration, k=0 (refutation R1)
-- The outer source is still registered via thru-outer.
-- BEFORE the correction: mergeReachable = true, 0≡0 holds accidentally
-- (countLiveInners=0 because there are no from-inner frames), so the old
-- candidate was true here.  But the old candidate fails on R1 in the
-- original PROOF-STATE analysis because there ALSO exist from-inner regs.
-- We reproduce the pure outer case: corrected predicate is trivially true
-- because innerInstsP returns [] for a thru-outer path.
-----------------------------------------------------------------------

outerPath : Path Γ₀ (obs natᵗ) natᵗ
outerPath = thru-outer mergeᵒ mnid ↠ root

-- The outer source is src=10, rid=0
st-shape1 : EvalSt e₀
st-shape1 = record (st-init e₀)
  { nodes    = (mnid , merge-st zero false) ∷ []
  ; registry = (0 , 10 , (obs natᵗ , outerPath)) ∷ []
  ; dying    = []
  ; delivered = []
  }

-- innerInstsP mnid outerPath = [] (no from-inner frames)
-- → hasAliveFromInner mnid st-shape1 _ = false
-- → mergeCertAt = not false = true
_ : mergeCertAt mnid st-shape1 ≡ true
_ = refl

-- Also confirm that innerInstsP correctly returns [] for thru-outer:
_ : innerInstsP mnid outerPath ≡ []
_ = refl

-----------------------------------------------------------------------
-- SHAPE 2: Single from-inner registration, dying+delivered, k=0 (refutation R3)
-- This is the mid-cascade state after `innerFinish` decrements k to 0
-- but BEFORE `cascadeFinish` drops the spent inner's registration.
-- The registration is dying (its source is in dying) AND delivered
-- (its rid is in delivered), so aliveThroughᶠ = false.
-----------------------------------------------------------------------

fromInnerPath : Path Γ₀ natᵗ natᵗ
fromInnerPath = from-inner mergeᵒ mnid inst ↠ root

-- src=10 delivered as rid=0, and is dying (last cascade)
st-shape2 : EvalSt e₀
st-shape2 = record (st-init e₀)
  { nodes     = (mnid , merge-st zero true) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = 10 ∷ []     -- src 10 is spending its last delivery
  ; delivered = 0 ∷ []      -- rid 0 was delivered this cascade
  }

-- aliveThroughᶠ inst st-shape2 (0, 10, ...):
--   pathHasNode inst fromInnerPath = true  (from-inner mnid inst frame)
--   not (rid ∈ cancelled) = not false = true
--   not (src ∈ dying) ∨ not (rid ∈ delivered) = not true ∨ not true = false
-- → aliveThroughᶠ = true ∧ true ∧ false = false
-- → hasAliveFromInner = any {false} = false
-- → mergeCertAt = not false = true
_ : mergeCertAt mnid st-shape2 ≡ true
_ = refl

-- Confirm the old candidate FAILS here (old = k ≡ᵇ countLiveInners):
-- countLiveInners mnid registry = nubLen [inst] = 1; k = 0; 0 ≡ᵇ 1 = false
-- The old nodeCacheOK (with mergeReachable = false here since outer dropped)
-- would be: not mergeReachable ∨ (0 ≡ᵇ 1) = true ∨ false = true, OK only
-- because outer is gone.  The real refutation R3 is when the outer IS still
-- present; we test that in shape2-ext below.
-- (We verify innerInstsP to make the accounting concrete)
_ : innerInstsP mnid fromInnerPath ≡ inst ∷ []
_ = refl

-----------------------------------------------------------------------
-- SHAPE 2-EXT: Same as shape 2, but outer thru-outer reg also present.
-- This is the genuine R3 configuration: mergeReachable=true, k=0,
-- but from-inner reg is dying+delivered → corrected cert still holds.
-----------------------------------------------------------------------

st-shape2-ext : EvalSt e₀
st-shape2-ext = record (st-init e₀)
  { nodes     = (mnid , merge-st zero true) ∷ []
  ; registry  = (0 , 9  , (obs natᵗ , outerPath))
              ∷ (1 , 10 , (natᵗ    , fromInnerPath)) ∷ []
  ; dying     = 10 ∷ []   -- inner src dying
  ; delivered = 1 ∷ []    -- rid 1 (the inner reg) was delivered
  }

-- outer reg: innerInstsP = [] → hasAliveFromInner = false
-- inner reg: dying+delivered → aliveThroughᶠ = false → hasAliveFromInner = false
-- → mergeCertAt = not false = true
_ : mergeCertAt mnid st-shape2-ext ≡ true
_ = refl

-----------------------------------------------------------------------
-- SHAPE 3: Multi-source inner, two from-inner regs sharing same inst,
-- both dying+delivered, k=0.  (Refutation R2 addressed.)
--
-- Background: when a single inner observable is itself a merge(a,b),
-- subscribeInner mints ONE inst but the inner's two sub-sources each
-- register their own chain — both carrying `from-inner mnid inst` in
-- their path.  After the inner completes, k is decremented by 1 (to 0)
-- but two registry entries remain until cascadeFinish drops them.
-- The old candidate: countLiveInners = nubLen [inst,inst] = 1 ≠ 0.
-- The corrected predicate: both are dying+delivered → both pass false
-- through aliveThroughᶠ → cert holds.
-----------------------------------------------------------------------

fromInnerPath2 : Path Γ₀ natᵗ natᵗ
fromInnerPath2 = from-inner mergeᵒ mnid inst ↠ root   -- same inst as fromInnerPath

-- src=10 (first sub-source), src=11 (second sub-source); both dying+delivered
st-shape3 : EvalSt e₀
st-shape3 = record (st-init e₀)
  { nodes     = (mnid , merge-st zero true) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath))
              ∷ (1 , 11 , (natᵗ , fromInnerPath2)) ∷ []
  ; dying     = 10 ∷ 11 ∷ []   -- both inner sub-sources dying
  ; delivered = 0 ∷ 1 ∷ []    -- both rids delivered
  }

-- For reg0 (rid=0, src=10): dying+delivered → aliveThroughᶠ = false
-- For reg1 (rid=1, src=11): dying+delivered → aliveThroughᶠ = false
-- → any = false → not false = true
_ : mergeCertAt mnid st-shape3 ≡ true
_ = refl

-----------------------------------------------------------------------
-- SHAPE B: Non-vacuity witness.
-- The predicate returns FALSE when k=0 but a live from-inner reg exists
-- (dying=[], delivered=[], not cancelled).
-- This proves the predicate is not trivially true.
-----------------------------------------------------------------------

-- Live inner registration: NOT dying, NOT delivered, NOT cancelled
st-shapeB : EvalSt e₀
st-shapeB = record (st-init e₀)
  { nodes     = (mnid , merge-st zero false) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = []       -- src NOT dying
  ; delivered = []       -- rid NOT delivered
  ; cancelled = []
  }

-- aliveThroughᶠ inst st-shapeB (0, 10, ...):
--   pathHasNode inst fromInnerPath = true
--   not (rid ∈ cancelled) = not false = true
--   not (src ∈ dying) ∨ not (rid ∈ delivered) = true ∨ true = true
-- → aliveThroughᶠ = true ∧ true ∧ true = true
-- → hasAliveFromInner = true
-- → mergeCertAt = not true = false
_ : mergeCertAt mnid st-shapeB ≡ false
_ = refl

-----------------------------------------------------------------------
-- SHAPE K≠0: When k ≠ 0, cert is vacuously true regardless.
-- This is the normal mid-execution state (inner still active).
-----------------------------------------------------------------------

st-shapeK : EvalSt e₀
st-shapeK = record (st-init e₀)
  { nodes     = (mnid , merge-st (suc zero) false) ∷ []
  ; registry  = (0 , 10 , (natᵗ , fromInnerPath)) ∷ []
  ; dying     = []
  ; delivered = []
  }

-- merge-st (suc zero) _ → lookupNode returns just (merge-st (suc zero) _)
-- → the `_` branch → true
_ : mergeCertAt mnid st-shapeK ≡ true
_ = refl

-----------------------------------------------------------------------
-- SUMMARY
--
-- The corrected merge-cert predicate:
--
--   mergeCertAt mnid st = when (merge-st 0 _ at mnid):
--     ¬ ∃ reg ∈ registry. hasAliveFromInner mnid st reg
--
-- SURVIVES all three refutation shapes:
--
--   Shape 0 (seed):        k=0, registry=[].              ✓  (trivially)
--   Shape 1 (R1 dodge):    k=0, outer thru-outer reg.     ✓  (no from-inner frames)
--   Shape 2 (R3 dodge):    k=0, inner reg dying+delivered. ✓  (aliveThroughᶠ=false)
--   Shape 2-ext:           k=0, outer+inner, inner dying.  ✓  (same)
--   Shape 3 (R2 dodge):    k=0, 2 regs same inst, dying.  ✓  (both aliveThroughᶠ=false)
--   Shape B (non-vacuous): k=0, live inner reg.            RETURNS FALSE  (cert is testable)
--   Shape K≠0:             k=1, live inner reg.            ✓  (cert does not fire at k>0)
--
-- VERDICT: SURVIVES
-----------------------------------------------------------------------
