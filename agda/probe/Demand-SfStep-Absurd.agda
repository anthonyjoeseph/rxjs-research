-- ROADMAP: EVIDENCE — machine-checks the ruling in PROOF-STATE.md (2026-08-10
--   UPDATE §1): a constant demand ledger cannot be walked.
--   `stepFrame (map-f fn)` where fn is duplicating (occsᵗ = 2) grows sizeᵛ
--   above any fixed bound Dm, so the per-frame Vb conjunct of `demand-sf-step`
--   (the postulate that lived in the reverted Demand-Walk.agda) is FALSE.
--   The postulate's file was reverted before landing; this probe supplies the
--   machine-checked refutation the ruling noted as "not yet machine-checked".
--
-- DELETE WHEN: the PROOF-STATE.md ruling has been updated with a numeric
--   receipt (cite this probe's § 1 numbers) AND the caps-indexed walk
--   replaces the constant-Dm route.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Demand-SfStep-Absurd.agda &&
--   agda -i src -i probe probe/Demand-SfStep-Absurd.agda

module Demand-SfStep-Absurd where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; _≤ᵇ_)
open import Data.List    using (List; []; _∷_; all; map)
open import Data.Vec     using () renaming ([] to []ᵛ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty   using (⊥)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim     using (Gas; g0; Id; Tick)
open import Rx.Exp
  using (Ty; natᵗ; _×ᵗ_; Ctx; Closed; Val; Fn;
         pairᵗ; varᵗ; ofᵉ; applyFn; sizeᵛ)
open import Rx.Evaluator
  using (Frame; map-f; Path; root; Sched; EvalSt; Slots;
         _↠_; stepFrame; sched-init; st-init)

-- Measures: valB?, fnCapᵛ (lightest path; avoids Wet/Caps chain)
open import Verify-Budget-Sufficient.Measures
  using (valB?; fnCapᵛ)

-- Caps record for cSize accessor
open import Verify-Budget-Sufficient.Caps using (Caps)

-- Caps-Face: walkOK, frameStep
open import Verify-Budget-Sufficient.Caps-Face
  using (walkOK; frameStep; pathSz?)

-- Init-Caps: baseCaps, init-capsOK?-base
open import Verify-Budget-Sufficient.Init-Caps
  using (baseCaps; init-capsOK?-base)

-- Delivery-Walk: regP?
open import Verify-Budget-Sufficient.Delivery-Walk
  using (regP?)

-- Caps-Depth: depthFrame
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame)

-- Occurrences: pathOccs?
open import Verify-Budget-Sufficient.Occurrences
  using (pathOccs?)

----------------------------------------------------------------------
-- § 0  SETUP
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

-- Program: empty observable of type natᵗ ×ᵗ natᵗ.
-- sizeᵉ (ofᵉ []) = suc 0 = 1; slotsSize ins₀ = 0.
-- baseCaps e₀ ins₀ = caps 3 (suc (entryCeil 0 ins₀ e₀)) 2.
e₀ : Closed Γ₀ (natᵗ ×ᵗ natᵗ)
e₀ = ofᵉ []

sched₀ : Sched Γ₀
sched₀ = sched-init e₀ ins₀

st₀ : EvalSt e₀
st₀ = st-init e₀

-- The duplicating function: λ v → (v , v).
-- pair-fn : Fn Γ₀ [] [] [] natᵗ (natᵗ ×ᵗ natᵗ)
--         = Tm Γ₀ [] [] [natᵗ] (natᵗ ×ᵗ natᵗ)
-- applyFn pair-fn n = evalWith (pairᵗ (varᵗ z) (varᵗ z)) (n ∷ᵃ []ᵃ) = (n , n).
-- occsᵗ pair-fn = occsᵗ (varᵗ z) + occsᵗ (varᵗ z) = 1 + 1 = 2 (duplicating).
pair-fn : Fn Γ₀ [] [] [] natᵗ (natᵗ ×ᵗ natᵗ)
pair-fn = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

----------------------------------------------------------------------
-- § 1  ARITHMETIC CORE
--
-- CLAIM: A constant Dm cannot survive one map-f frame.
-- With fn = pair-fn (duplicating), v = 0, Dm = 1, Ψ = 0:
--   sizeᵛ natᵗ 0            = 1 = Dm   (fits at Dm)
--   sizeᵛ (natᵗ ×ᵗ natᵗ) (applyFn pair-fn 0)
--     = sizeᵛ (natᵗ ×ᵗ natᵗ) (0 , 0)
--     = suc (sizeᵛ natᵗ 0 + sizeᵛ natᵗ 0) = suc (1 + 1) = 3 > 1 = Dm
--
-- valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)
----------------------------------------------------------------------

-- LOAD-BEARING: sizeᵛ of input value = 1.
-- What would make this fail: sizeᵛ natᵗ formula changed.
_ : sizeᵛ {Γ = Γ₀} natᵗ 0 ≡ 1
_ = refl

-- LOAD-BEARING: sizeᵛ of output value = 3 (duplicating map doubles + 1).
-- What would make this fail: sizeᵛ (×ᵗ) or applyFn formula changed.
_ : sizeᵛ {Γ = Γ₀} (natᵗ ×ᵗ natᵗ) (applyFn pair-fn 0) ≡ 3
_ = refl

-- LOAD-BEARING: input value satisfies valB? 1 0.
-- What would make this fail: valB? or ≤ᵇ formula changed; 1 ≤ᵇ 1 = true.
applyFn-breaks-constant-bound-input : valB? {Γ = Γ₀} 1 0 natᵗ 0 ≡ true
applyFn-breaks-constant-bound-input = refl

-- LOAD-BEARING: output value VIOLATES valB? 1 0.
-- What would make this fail: sizeᵛ (natᵗ ×ᵗ natᵗ) or ≤ᵇ formula changed;
-- 3 ≤ᵇ 1 = false, so the first conjunct of valB? is false.
applyFn-breaks-constant-bound-output : valB? {Γ = Γ₀} 1 0 (natᵗ ×ᵗ natᵗ) (applyFn pair-fn 0) ≡ false
applyFn-breaks-constant-bound-output = refl

----------------------------------------------------------------------
-- § 2  STEPFRAME COMPUTATION
--
-- stepFrame (map-f fn) clause (Evaluator:1250):
--   stepFrame fuel id now (map-f fn) κ vals fin sched st
--     = map (applyFn fn) vals , [] , fin , sched , st
--
-- So proj₁ r = map (applyFn pair-fn) [0] = [(0 , 0)].
-- And all (valB? 1 0 (natᵗ ×ᵗ natᵗ)) [(0 , 0)]
--   = valB? 1 0 (natᵗ ×ᵗ natᵗ) (0 , 0) ∧ true
--   = false ∧ true = false.
----------------------------------------------------------------------

-- LOAD-BEARING: stepFrame (map-f fn) outputs the mapped values.
-- What would make this fail: stepFrame map-f clause changed.
_ : proj₁ (stepFrame {e = e₀} g0 0 0 (map-f pair-fn) root (0 ∷ []) false sched₀ st₀)
  ≡ applyFn pair-fn 0 ∷ []
_ = refl

-- LOAD-BEARING: the Vb output conjunct reduces to false for this instance.
-- This is the contradiction: demand-sf-step's Vb output conjunct would claim
-- all (valB? 1 0 u) (proj₁ r) ≡ true, but it reduces to false ≡ true (⊥).
-- What would make this fail: any of the reductions in § 1 or § 2 changed.
Vb-output-false :
  all (valB? {Γ = Γ₀} 1 0 (natᵗ ×ᵗ natᵗ))
      (proj₁ (stepFrame {e = e₀} g0 0 0 (map-f pair-fn) root (0 ∷ []) false sched₀ st₀))
  ≡ false
Vb-output-false = refl

----------------------------------------------------------------------
-- § 3  THE REFUTATION FUNCTION
--
-- The per-frame demand preservation claim for map-f pair-fn is false.
-- Any proof of the Vb output conjunct at this instance would give ⊥.
-- The `()` pattern works because the type reduces to (false ≡ true),
-- which is empty: false and true are distinct Bool constructors.
----------------------------------------------------------------------

-- LOAD-BEARING: the per-frame Vb claim is refuted at (pair-fn, [0], Dm=1).
-- Consequence: demand-sf-step (the postulate in reverted Demand-Walk.agda)
-- is FALSE — it would assert false ≡ true for this instance.
-- What would make this fail: Vb-output-false above is wrong (impossible by §1/§2).
demand-sf-step-Vb-absurd :
  all (valB? {Γ = Γ₀} 1 0 (natᵗ ×ᵗ natᵗ))
      (proj₁ (stepFrame {e = e₀} g0 0 0 (map-f pair-fn) root (0 ∷ []) false sched₀ st₀))
  ≡ true
  → ⊥
demand-sf-step-Vb-absurd ()

----------------------------------------------------------------------
-- § 4  HYPOTHESIS SATISFIABILITY AT THE INITIAL STATE
--
-- demand-sf-step had 5 hypotheses; all are satisfiable at J = 0,
-- c = baseCaps e₀ ins₀, sched₀ = sched-init e₀ ins₀, st₀ = st-init e₀.
-- This confirms the refutation is NOT vacuous: the postulate is false
-- at a REACHABLE STATE (the program's initial state), not just at
-- unreachable states where some hypothesis fails.
--
-- HYPS (from demand-sf-step's signature):
-- (1) walkOK c sl J sched st
--     = (Sched.slots sched ≡ sl) × (capsOK? (frameStep J c) sched st ≡ true)
-- (2) (pathSz? (cSize (frameStep J c)) (f ↠ path′) ∧ pathOccs? sz (f ↠ path′)) ≡ true
-- (3) all (valB? Dm Ψ s) vals ≡ true
-- (4) regP? (λ {v} p → pathSz? (cSize (frameStep J c)) p ∧ pathOccs? sz p)
--           (EvalSt.registry st) ≡ true
-- (5) depthFrame sf id now f path′ vals fin sched st ≤ d
----------------------------------------------------------------------

-- HYP 1 — walkOK.
-- At J=0: frameStep 0 c = c definitionally for c = baseCaps e₀ ins₀ (cReg*1 = cReg).
-- Sched.slots (sched-init e₀ ins₀) ≡ ins₀ is refl.
-- capsOK? (baseCaps e₀ ins₀) sched₀ st₀ ≡ true is init-capsOK?-base.
-- LOAD-BEARING: would fail if Sched.slots or capsOK? at init changed.
walkOK-init :
  walkOK (baseCaps e₀ ins₀) ins₀ 0 sched₀ st₀
walkOK-init = refl , init-capsOK?-base e₀ ins₀

-- HYP 2 — path size and occurrences.
-- B = Caps.cSize (frameStep 0 (baseCaps e₀ ins₀)) = 3 (cSize = 2 + 1 + 0 = 3;
--   frameStep 0 c = c definitionally since cReg * 1 = cReg for cReg = 2).
-- pathSz? 3 (map-f pair-fn ↠ root):
--   = frameSz? 3 (map-f pair-fn) ∧ ((suc 0 ≤ᵇ 3) ∧ pathSz? 3 root)
--   = (sizeᵗ pair-fn ≤ᵇ 3) ∧ (true ∧ true)
--   = (3 ≤ᵇ 3) ∧ true = true ∧ true = true.
-- pathOccs? 2 (map-f pair-fn ↠ root):
--   = (occsᵗ pair-fn ≤ᵇ 2) ∧ true = (2 ≤ᵇ 2) ∧ true = true.
-- LOAD-BEARING: would fail if sizeᵗ pair-fn > 3, occsᵗ pair-fn > 2, or cSize ≠ 3.
path-hyp :
  ( pathSz? (Caps.cSize (frameStep 0 (baseCaps e₀ ins₀))) (map-f pair-fn ↠ root)
  ∧ pathOccs? 2 (map-f pair-fn ↠ root) )
  ≡ true
path-hyp = refl

-- HYP 3 — input values satisfy the bound.
-- all (valB? 1 0 natᵗ) [0] = valB? 1 0 natᵗ 0 ∧ true = true ∧ true = true.
-- LOAD-BEARING: same as applyFn-breaks-constant-bound-input (§ 1).
vals-hyp : all (valB? {Γ = Γ₀} 1 0 natᵗ) (0 ∷ []) ≡ true
vals-hyp = refl

-- HYP 4 — registry ledger at initial state.
-- EvalSt.registry (st-init e₀) = []; all P [] = true by definition of all.
-- DEGENERATE: the registry is empty; no entry's path is checked.
-- What would make this fail: st-init initialising a non-empty registry.
reg-hyp :
  regP? (λ {v} p → pathSz? (Caps.cSize (frameStep 0 (baseCaps e₀ ins₀))) p
                    ∧ pathOccs? 2 p)
        (EvalSt.registry st₀) ≡ true
reg-hyp = refl

-- HYP 5 — depth bound.
-- depthFrame ... (map-f fn) ... = 0 (Caps-Depth:361: map-f clause = 0).
-- 0 ≤ 0 is z≤n.
-- LOAD-BEARING: would fail if depthFrame map-f clause changed to > 0.
depth-hyp :
  depthFrame g0 0 0 (map-f pair-fn) root (0 ∷ []) false sched₀ st₀ ≤ 0
depth-hyp = z≤n
