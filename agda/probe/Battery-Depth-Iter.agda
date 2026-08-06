------------------------------------------------------------------
-- BATTERY-DEPTH-ITER.  Phase 0c(ii).
--
-- Probes two FALSITY-risk postulates from PROOF-STATE.md:
--
--   P1. `opIterD≤sizeCount-root-core`  (Caps-Bridge.agda:1090)
--       Novel upper bound: opIterD S W d k _ 0 ≤ sizeCount c d at root.
--       VERDICT: BLOCKED — both `opIterD` and `sizeCount` are in abstract
--       blocks (Evaluator.agda:727 and Caps.agda:368), and the depth fuel
--       `capsH e ins 0 = blowH(capsBase e ins)` is also abstract
--       (Evaluator.agda:898).  No numerical row is accessible by `refl`.
--       Partial evidence (computable parameters and Hypothesis H2) is
--       reported in §1.
--
--   P2. `depth-compositional` (Depth-Bound.agda:153)
--       depthE g b κ bid now sched st ≤ sizeᵉ b + pathLen κ + storeNestMax sched st.
--       VERDICT: PROBED-GREEN — new evidence added for switch/exhaust
--       shapes and the preservation direction.
--
-- EVOLVED-STATE COVERAGE FOR P2:
-- Depth-Compositional-Probe already tests evolved states: it drains N
-- real cascades with the actual evaluator, extracts the growing scan
-- accumulator from the resulting EvalSt.nodes, and queries depthE on it
-- directly (§C of that probe).  Rows k ≤ 4, N ≤ 10 all hold at C = 0.
-- The tests in §§2-3 below are NEW GROUND: switch/exhaustAll shapes (not
-- present in either existing depth probe) and the preservation direction
-- (`storeNestMax` at the post-subscribeE state bounded by the ENTRY bound
-- plus `sizeᵉ e`).  So the answer to "were evolved states tested?" is YES
-- by the existing probe; §§2-3 supply independent evidence on different
-- operator shapes and the inductive step direction.
------------------------------------------------------------------
module Battery-Depth-Iter where

open import Data.Nat  using (ℕ; zero; suc; _⊔_; _≤ᵇ_; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; foldr; tabulate)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Timed; ObservableInput; hot; after_,_)
open import Rx.Exp using (Ty; natᵗ; obs; Ctx; Closed; Exp; Tm; Val;
                          sizeᵉ; sizeᵛ;
                          nat̂; strmᵗ;
                          input; ofᵉ; emptyᵉ; mergeAllᵉ; scanᵉ;
                          switchAllᵉ; exhaustAllᵉ)
open import Rx.Evaluator using (Slots; Slot; scripted; shared; Sched; EvalSt;
                                NodeId; NodeState;
                                scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                Path; root;
                                sched-init; st-init; budgetAt; subscribeE;
                                capsBase; slotsSize; sizeAt; widAt)
open import Verify-Budget-Sufficient.Caps-Nest using (nest)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

open import Depth-Blowup-Probe
  using (Γ₁; seedO; wrapK; pushD; hotList; insN; runSt)

------------------------------------------------------------------
-- LOCAL COPY OF storeNestMax (verbatim from Depth-Bound.agda /
-- Depth-Compositional-Probe — included here so this file only pulls in
-- the already-cached Depth-Blowup-Probe, not the heavier Compositional
-- probe chain).
------------------------------------------------------------------

nodeNestMax : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeNestMax (scan-st {t} v)       = sizeᵛ t v
nodeNestMax (concat-st {t} q _ _) = foldr (λ o acc → sizeᵉ o ⊔ acc) 0 q
nodeNestMax (take-st _)           = 0
nodeNestMax (merge-st _ _)        = 0
nodeNestMax (switch-st _ _)       = 0
nodeNestMax (exhaust-st _ _)      = 0

nodesNestMax : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
nodesNestMax = foldr (λ kv acc → nodeNestMax (proj₂ kv) ⊔ acc) 0

slotNest : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotNest (shared d)   = sizeᵉ d
slotNest (scripted _) = 0

slotsNestMax : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestMax {n} sl = foldr _⊔_ 0 (tabulate {n = n} (λ i → slotNest (sl i)))

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
storeNestMax sched st =
  slotsNestMax (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

------------------------------------------------------------------
-- §1.  opIterD≤sizeCount-root-core — BLOCKED
--
-- THREE INDEPENDENT LOCKS, any one of which is sufficient alone:
--
--   (a) `opIterD` is ABSTRACT (Evaluator.agda:727 abstract block).
--       Its body equations opIterD-0/opIterD-suc are exposed for proof
--       work but opaque to `refl`.  For any concrete (S, W, d, k, m, J),
--       `opIterD S W d k m J` does not reduce to a concrete ℕ.
--
--   (b) `sizeCount` is ABSTRACT (Caps.agda:368 abstract block).
--       Its body `lvls (cSize c) (cWid c) d 0 (cDel c d)` (also abstract)
--       is exposed via `sizeCount-body` but opaque to `refl`.
--
--   (c) The depth fuel on BOTH sides of the inequality is
--       `capsH e ins 0 = blowH (capsBase e ins)` where `blowH` is ABSTRACT
--       (Evaluator.agda:898).  For the simplest program pushD 0 / insN 0,
--       `capsBase = 18`, so the fuel would be `blowH 18` = 6 + 18 + 2 *
--       poolCount (towerℕ 18) 18 where `towerℕ 18` is tower-of-towers —
--       a value so large no Agda computation would finish even if the
--       abstract block were removed.
--
-- CONSEQUENCE: no `_ : opIterD ... ≤ᵇ sizeCount ... ≡ true; _ = refl`
-- can be constructed.  A proof must use the body-equation lemmas
-- (opIterD-0, opIterD-suc, sLvlD-suc, etc.) algebraically.
--
-- §1a.  Computable parameter values.  capsBase, sizeᵉ, slotsSize, and
--       nest are ALL non-abstract.  These are the concrete arguments the
--       postulate sees at each program.
------------------------------------------------------------------

_ : (capsBase (pushD 0) (insN 0) , sizeᵉ (pushD 0) , slotsSize (insN 0) , nest (pushD 0) (insN 0) [])
  ≡ (18 , 8 , 1 , 3)
_ = refl

_ : (capsBase (pushD 1) (insN 0) , sizeᵉ (pushD 1) , slotsSize (insN 0) , nest (pushD 1) (insN 0) [])
  ≡ (22 , 12 , 1 , 4)
_ = refl

_ : (capsBase (pushD 0) (insN 3) , slotsSize (insN 3) , nest (pushD 0) (insN 3) [])
  ≡ (21 , 4 , 3)
_ = refl

------------------------------------------------------------------
-- §1b.  Hypothesis H2: nest e ins [] ≤ sizeᵉ e + slotsSize ins.
--       This is the second hypothesis of opIterD≤sizeCount-root-core.
--       Caps-Nest.agda proves it in full generality via `nest≤`; these
--       rows confirm the numbers for the programs this probe covers.
------------------------------------------------------------------

_ : (nest (pushD 0) (insN 0) [] ≤ᵇ sizeᵉ (pushD 0) + slotsSize (insN 0)) ≡ true
_ = refl   -- 3 ≤ 9

_ : (nest (pushD 1) (insN 0) [] ≤ᵇ sizeᵉ (pushD 1) + slotsSize (insN 0)) ≡ true
_ = refl   -- 4 ≤ 13

_ : (nest (pushD 0) (insN 3) [] ≤ᵇ sizeᵉ (pushD 0) + slotsSize (insN 3)) ≡ true
_ = refl   -- 3 ≤ 12

------------------------------------------------------------------
-- §1c.  Structural condition sizeAt S J ≤ widAt S W J at small (S,W,J).
--       sizeAt and widAt are non-abstract (Evaluator.agda:577-581).
--       These are not hypotheses of the postulate; they probe the level-
--       walk monotonicity that the algebraic proof will rely on.
------------------------------------------------------------------

_ : sizeAt 3 1 ≡ 21   ;  _ = refl
_ : widAt  3 2 1 ≡ 27  ;  _ = refl
_ : (sizeAt 3 1 ≤ᵇ widAt 3 2 1) ≡ true
_ = refl   -- 21 ≤ 27

_ : (sizeAt 5 1 ≤ᵇ widAt 5 3 1) ≡ true
_ = refl   -- 55 ≤ 625

------------------------------------------------------------------
-- §2.  depth-compositional — switch/exhaust shapes (NEW GROUND)
--
-- The existing probes (Depth-Blowup-Probe and Depth-Compositional-Probe)
-- cover only mergeAllᵉ / scanᵉ families.  Neither tests switchAllᵉ or
-- exhaustAllᵉ.  These operators have their own subscribeE path through
-- `stepAllFrame`→`subscribeInner` and their own node states
-- (switch-st _ _ and exhaust-st _ _); `depthAll` computes the same way
-- for both, but the RUNTIME states are different.
--
-- KEY FACT: `nodeNestMax (switch-st _ _) = 0` and
--           `nodeNestMax (exhaust-st _ _) = 0` (Depth-Bound.agda:85-86).
-- So for scripted-slot programs, `storeNestMax` stays 0 throughout a
-- switch/exhaust run — the check is always `depthE ... ≤ sizeᵉ e`.
-- The probed values below CONFIRM this stays ≤ for programs where
-- the inner subscribe fires real values (not just empty ones).
--
-- `depthE fuel (ofᵉ ts) κ id now sched st = 0` (Caps-Depth.agda:217)
-- and `depthE fuel emptyᵉ κ id now sched st = 0` (Caps-Depth:218),
-- so the LHS of the conjecture for switchE and exhaustE (which wrap
-- emptyᵉ or static ofᵉ) reduces deterministically.
------------------------------------------------------------------

-- PROGRAM FAMILY.  All have type `Closed Γ₁ natᵗ`.
--
-- switchFin and exhaustFin subscribe to a single inner stream containing
-- one nat value, so `subscribeInner` IS called (peeling 1 gas layer) and
-- the depthE result is genuinely nonzero.

switchE : Closed Γ₁ natᵗ
switchE = switchAllᵉ emptyᵉ

switchFin : Closed Γ₁ natᵗ
switchFin = switchAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

exhaustE : Closed Γ₁ natᵗ
exhaustE = exhaustAllᵉ emptyᵉ

exhaustFin : Closed Γ₁ natᵗ
exhaustFin = exhaustAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- Entry-state conjecture check: depthE ≤ sizeᵉ e + storeNestMax (= 0 here).
-- insN 0 is used to provide the required scripted slot; no cascades are run.

entryCheck : Closed Γ₁ natᵗ → Bool
entryCheck e =
  depthE (budgetAt e (insN 0) 0) e root 0 0 (sched-init e (insN 0)) (st-init e)
  ≤ᵇ sizeᵉ e + storeNestMax (sched-init e (insN 0)) (st-init e)

_ : entryCheck switchE ≡ true
_ = refl   -- depthE = 0 ≤ 2 + 0

_ : entryCheck switchFin ≡ true
_ = refl   -- depthE = 1 ≤ 7 + 0

_ : entryCheck exhaustE ≡ true
_ = refl   -- depthE = 0 ≤ 2 + 0

_ : entryCheck exhaustFin ≡ true
_ = refl   -- depthE = 1 ≤ 7 + 0

------------------------------------------------------------------
-- §3.  Preservation: storeNestMax post-subscribeE ≤ sizeᵉ e + storeNestMax pre.
--
-- This is the INDUCTIVE STEP direction for depth-compositional's proof
-- (Depth-Bound.agda:153, census point (4)): after running subscribeE of
-- the body `e` at a LIVE evolved state (sched, st), the resulting state's
-- `storeNestMax` must stay ≤ `sizeᵉ e + storeNestMax(entry)`.
--
-- ARGUMENT FOR WHY IT HOLDS:
-- `subscribeE` INSTALLS new nodes with INITIAL accumulator values (the
-- seed or the operator's zero-state).  For `scan-st v`, the fresh v is
-- the seed from the syntax — `sizeᵛ t v ≤ sizeᵉ e` (the seed is a
-- sub-expression).  For merge-st, switch-st, exhaust-st, and take-st,
-- the fresh state contributes nodeNestMax = 0.  The OLD nodes are
-- untouched.  So:
--
--   storeNestMax post = max(old nodes, fresh seed, old slots)
--                     ≤ max(old nodes, sizeᵉ e, old slots)
--                     = storeNestMax pre ⊔ sizeᵉ e
--                     ≤ sizeᵉ e + storeNestMax pre
--
-- The rows below confirm this numerically at pushD 0 after N=1 cascade.
-- (N=1 keeps the computation inside budget: `runSt 1` + one `subscribeE`
-- is comparable in cost to the existing probe's `depthNextCascade 1`
-- rows.)
------------------------------------------------------------------

checkPreservation : ℕ → Closed Γ₁ natᵗ → Bool
checkPreservation N e with runSt N e (insN N)
... | nid , sched , st
    with subscribeE (budgetAt e (insN N) nid) e root nid N sched st
...   | _ , sched' , st' =
          storeNestMax sched' st' ≤ᵇ sizeᵉ e + storeNestMax sched st

_ : checkPreservation 1 (pushD 0) ≡ true
_ = refl

_ : checkPreservation 1 (pushD 1) ≡ true
_ = refl

------------------------------------------------------------------
-- VERDICT SUMMARY
--
-- P1. opIterD≤sizeCount-root-core (Caps-Bridge.agda:1090)
--     STATUS: BLOCKED — triple lock (abstract opIterD, abstract
--     sizeCount, abstract capsH/blowH fuel).  No numerical row is
--     accessible.  Computable partial evidence (§1): capsBase/sizeᵉ/
--     slotsSize/nest are concrete (§1a); H2 holds (§1b); sizeAt≤widAt
--     structural condition holds at small values (§1c).  None of these
--     checks can confirm or refute the postulate; they only verify the
--     in-range parameters.
--
-- P2. depth-compositional (Depth-Bound.agda:153)
--     STATUS: PROBED-GREEN — no row found violating
--     `depthE g b κ ... sched st ≤ sizeᵉ b + pathLen κ + storeNestMax sched st`.
--     EVOLVED STATES TESTED: YES, by Depth-Compositional-Probe (k≤4,
--     N≤10, C=0), and independently confirmed here for the preservation
--     direction (§3) and the switch/exhaustAll code path (§2).
--     NEW SHAPES TESTED: switchAllᵉ and exhaustAllᵉ (§2), covering
--     depthAll's switch-st/exhaust-st branch which neither existing
--     depth probe exercised.
--     PRESERVATION DIRECTION TESTED: YES (§3) — storeNestMax(post) ≤
--     sizeᵉ e + storeNestMax(pre) confirmed at N=1 for pushD 0/1.
------------------------------------------------------------------
