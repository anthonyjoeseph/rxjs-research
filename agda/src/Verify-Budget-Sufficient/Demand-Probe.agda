-- Gas-demand measurement: inject gasPad h g0 into subscribeE and find
-- the minimal h* at which each program stops drying.
-- MODULE_ROOT (see scripts/check-wiring.py): not imported by Main, not
-- compiled; checked by `make bug-cache`.  Probe receipts are in the
-- headers of the relevant postulates (cascadeGo-nodry in Burst-Walk).
module Verify-Budget-Sufficient.Demand-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin  using (Fin; zero)
import Data.Fin as F
open import Data.Nat  using (ℕ; suc; _+_; _^_; _≤ᵇ_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gs; gasPad; hot)
open import Rx.Exp  using (Ctx; Closed; natᵗ; obs; _×ᵗ_;
                            ofᵉ; scanᵉ; emptyᵉ;
                            mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                            strmᵗ; fstᵗ; sndᵗ; varᵗ; nat̂;
                            μᵉ; deferᵉ; input;
                            sizeᵉ; syncSizeᵉ; Tm; Fn)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; hasDry;
                                 Slots; Slot; shared; scripted; Path; root; EvalSt;
                                 Sched; opIterD; slotsSize)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop; slotHop-fix)
open import Verify-Budget-Sufficient.Measures using (dBound; regsLen?;
                                 burstHopD?; hopR; unconn; hasAtLeast-pad)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep;
                                 iterSize-infl)
open import Verify-Budget-Sufficient.Walk-Level using (WalkStmt)

----------------------------------------------------------------------
-- Context and slots: empty (no inputs)
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- Convenience runner
----------------------------------------------------------------------

runDry : ∀ {t} (h : ℕ) (e : Closed Γ₀ t) → Bool
runDry h e =
  hasDry (proj₁ (subscribeE (gasPad h g0) e root 0 0
                             (sched-init e ins₀) (st-init e)))

----------------------------------------------------------------------
-- Programs — series A: static ladders (calibration)
----------------------------------------------------------------------

-- A0: ofᵉ [1] — no *All, no μ → gas demand = 0 (never dries)
prog-A0 : Closed Γ₀ natᵗ
prog-A0 = ofᵉ (nat̂ 1 ∷ [])

-- A1: mergeAll(of [of[1]]) — one inner subscribe, depth 1
prog-A1 : Closed Γ₀ natᵗ
prog-A1 = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ []))

-- A2: two levels of mergeAll nesting
prog-A2 : Closed Γ₀ natᵗ
prog-A2 = mergeAllᵉ (ofᵉ (strmᵗ prog-A1 ∷ []))

-- A3: three levels
prog-A3 : Closed Γ₀ natᵗ
prog-A3 = mergeAllᵉ (ofᵉ (strmᵗ prog-A2 ∷ []))

----------------------------------------------------------------------
-- Programs — series B: the amplifier
-- scan fold f : (acc : obs natᵗ, val : natᵗ) → obs natᵗ
-- f (acc, _) = mergeAll([acc])    (wraps acc one merge-level deeper)
-- After k values: acc_k is k mergeAll-levels deep, plus a₀ = ofᵉ[0].
-- Gas demand for acc_k = k+1 peels.
----------------------------------------------------------------------

-- fold function f: takes the accumulator (fst of the pair) and wraps it
scan-f-B : Rx.Exp.Fn Γ₀ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
scan-f-B = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

-- initial accumulator: strmᵗ (ofᵉ [0]) evaluates to ofᵉ[0] : Closed Γ₀ natᵗ
scan-a0 : Rx.Exp.Tm Γ₀ [] [] [] (obs natᵗ)
scan-a0 = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

-- B1: k=1  (emits acc₁ = mergeAll([ofᵉ[0]]); depth 1 → h* = 2)
prog-B1 : Closed Γ₀ natᵗ
prog-B1 = mergeAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ [])))

-- B2: k=2  (deepest: acc₂ = mergeAll([acc₁]); depth 2 → h* = 3)
prog-B2 : Closed Γ₀ natᵗ
prog-B2 = mergeAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

-- B3: k=3  (deepest: acc₃ = mergeAll([acc₂]); depth 3 → h* = 4)
prog-B3 : Closed Γ₀ natᵗ
prog-B3 = mergeAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

-- B4: k=4  (deepest: acc₄; depth 4 → h* = 5)
prog-B4 : Closed Γ₀ natᵗ
prog-B4 = mergeAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ [])))

----------------------------------------------------------------------
-- Programs — series C: alternate outer operators at k=2
-- Same scan + fold; only outer *All changes.
-- At k=2 all four operators subscribe both inners synchronously
-- (acc₁ completes synchronously, so concat/exhaust can subscribe acc₂).
-- Predicted: same h* = 3 for all.
----------------------------------------------------------------------

prog-C-concat : Closed Γ₀ natᵗ
prog-C-concat = concatAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog-C-switch : Closed Γ₀ natᵗ
prog-C-switch = switchAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog-C-exhaust : Closed Γ₀ natᵗ
prog-C-exhaust = exhaustAllᵉ (scanᵉ scan-f-B scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

----------------------------------------------------------------------
-- Measurement pins — series A
-- Label: LOAD-BEARING — each pair would fail if h* shifted by ±1.
-- "true" row: run dries at h = h*-1 (LOAD-BEARING: fails if h* is smaller)
-- "false" row: run does not dry at h = h* (LOAD-BEARING: fails if h* is larger)
----------------------------------------------------------------------

-- A0: h* = 0 (never dries). No true-row (h*-1 = -1 doesn't exist).
-- LOAD-BEARING: would fail if A0 consumed any gas.
_ : runDry 0 prog-A0 ≡ false
_ = refl

-- A1: h* = 1
-- LOAD-BEARING: fails if h* ≠ 1.
_ : runDry 0 prog-A1 ≡ true
_ = refl
_ : runDry 1 prog-A1 ≡ false
_ = refl

-- A2: h* = 2
_ : runDry 1 prog-A2 ≡ true
_ = refl
_ : runDry 2 prog-A2 ≡ false
_ = refl

-- A3: h* = 3
_ : runDry 2 prog-A3 ≡ true
_ = refl
_ : runDry 3 prog-A3 ≡ false
_ = refl

----------------------------------------------------------------------
-- Measurement pins — series B
-- THE LOAD-BEARING QUESTION: does h* grow with k?
-- Each pair is LOAD-BEARING: fails if h* is not exactly k+1.
----------------------------------------------------------------------

-- B1: k=1, h* = 2
_ : runDry 1 prog-B1 ≡ true
_ = refl
_ : runDry 2 prog-B1 ≡ false
_ = refl

-- B2: k=2, h* = 3
_ : runDry 2 prog-B2 ≡ true
_ = refl
_ : runDry 3 prog-B2 ≡ false
_ = refl

-- B3: k=3, h* = 4
_ : runDry 3 prog-B3 ≡ true
_ = refl
_ : runDry 4 prog-B3 ≡ false
_ = refl

-- B4: k=4, h* = 5
_ : runDry 4 prog-B4 ≡ true
_ = refl
_ : runDry 5 prog-B4 ≡ false
_ = refl

----------------------------------------------------------------------
-- Measurement pins — series C (k=2, alternate outer operator)
-- Predicted h* = 3 for all three (same as B2 / mergeAll k=2).
-- LOAD-BEARING: fails if any operator demands different gas.
----------------------------------------------------------------------

-- C-concat: h* = 3
_ : runDry 2 prog-C-concat ≡ true
_ = refl
_ : runDry 3 prog-C-concat ≡ false
_ = refl

-- C-switch: h* = 3
_ : runDry 2 prog-C-switch ≡ true
_ = refl
_ : runDry 3 prog-C-switch ≡ false
_ = refl

-- C-exhaust: h* = 3
_ : runDry 2 prog-C-exhaust ≡ true
_ = refl
_ : runDry 3 prog-C-exhaust ≡ false
_ = refl

----------------------------------------------------------------------
-- Programs — series D: accumulator used TWICE per fold
-- scan-f-D (acc, _) = mergeAll([acc, acc])  ← two references to acc
-- After k steps: acc_k = mergeAll([acc_{k-1}, acc_{k-1}])
-- Width doubles per step (2^k leaves), but siblings share the SAME
-- gas in thruWalk — so depth, not width, drives gas demand.
-- Predicted: h*(D, k) = k+1, SAME as B.
----------------------------------------------------------------------

scan-f-D : Rx.Exp.Fn Γ₀ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
scan-f-D = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
                                  ∷ fstᵗ (varᵗ (here refl)) ∷ [])))

prog-D1 : Closed Γ₀ natᵗ
prog-D1 = mergeAllᵉ (scanᵉ scan-f-D scan-a0 (ofᵉ (nat̂ 1 ∷ [])))

prog-D2 : Closed Γ₀ natᵗ
prog-D2 = mergeAllᵉ (scanᵉ scan-f-D scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog-D3 : Closed Γ₀ natᵗ
prog-D3 = mergeAllᵉ (scanᵉ scan-f-D scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

----------------------------------------------------------------------
-- Programs — series E: double-wrap per step (two mergeAll layers)
-- scan-f-E (acc, _) = mergeAll([mergeAll([acc])])
-- Each step adds TWO mergeAll levels; acc_k has depth 2k.
-- Predicted growth: h*(E, k) = 2k+1  (additive, not multiplicative)
-- With k source values: acc deepest is acc_k at depth 2k; plus 1 for
-- the outer mergeAll's subscribeInner.
----------------------------------------------------------------------

scan-f-E : Rx.Exp.Fn Γ₀ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
scan-f-E = strmᵗ (mergeAllᵉ (ofᵉ
             (strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

prog-E1 : Closed Γ₀ natᵗ
prog-E1 = mergeAllᵉ (scanᵉ scan-f-E scan-a0 (ofᵉ (nat̂ 1 ∷ [])))

prog-E2 : Closed Γ₀ natᵗ
prog-E2 = mergeAllᵉ (scanᵉ scan-f-E scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog-E3 : Closed Γ₀ natᵗ
prog-E3 = mergeAllᵉ (scanᵉ scan-f-E scan-a0 (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

----------------------------------------------------------------------
-- Programs — series F: μ ladders
-- μᵉ body binds a guarded var; subscribeE g0 (μᵉ body) → dried.
-- subscribeE (gs fuel) (μᵉ body) → peels 1 → subscribeE fuel (unfoldμ body).
-- Bodies here ignore the recursive var → unfold terminates at ofᵉ.
-- Predicted: h*(F, n) = n (one peel per μ layer).
----------------------------------------------------------------------

prog-F1 : Closed Γ₀ natᵗ
prog-F1 = μᵉ (ofᵉ (nat̂ 1 ∷ []))

prog-F2 : Closed Γ₀ natᵗ
prog-F2 = μᵉ (μᵉ (ofᵉ (nat̂ 1 ∷ [])))

----------------------------------------------------------------------
-- Programs — series G: shared slot
-- Context Γ₁ has one natᵗ slot; ins₁ maps it to a shared observable.
-- input zero references that slot.
-- sharedConnect g0 → dried; sharedConnect (gs fuel) → peels 1,
-- subscribes the shared def (ofᵉ[1] → oneShotBurst, no dry).
-- Predicted: h*(G-single) = 1.
-- Second reference to same slot costs 0 (already in connectedShares),
-- but this cannot be distinguished via h* since siblings get the same
-- gas — documented as a structural fact, not a separate h* row.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

ins₁ : Slots Γ₁
ins₁ = λ { zero → shared (ofᵉ (nat̂ 1 ∷ [])) }

prog-G : Closed Γ₁ natᵗ
prog-G = input zero

runDry-G : ℕ → Bool
runDry-G h =
  hasDry (proj₁ (subscribeE (gasPad h g0) prog-G root
                             0 0
                             (sched-init prog-G ins₁)
                             (st-init   prog-G)))

----------------------------------------------------------------------
-- Programs — series H: deferᵉ costs no gas at subscribe time
-- subscribeE fuel (deferᵉ body) = schedules body for tick+1, no peel.
-- Outer mergeAll's subscribeInner still costs 1 peel.
-- Predicted: h*(H) = 1 (same as A1; body's gas demand is irrelevant
-- because deferᵉ returns before subscribing body in the initial step).
-- LOAD-BEARING: if deferᵉ subscription cost gas, h* would be ≥ 2.
----------------------------------------------------------------------

prog-H : Closed Γ₀ natᵗ
prog-H = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 1 ∷ []))) ∷ []))

----------------------------------------------------------------------
-- Measurement pins — series D
-- Finding: h*(D, k) = k+1, same as B. Width-doubling is free because
-- siblings receive the same gas (thruWalk does not deplete gas across
-- siblings); depth is the sole driver.
-- LOAD-BEARING: each pair fails if h* ≠ k+1.
----------------------------------------------------------------------

-- D1: k=1, h* = 2  (same as B1)
_ : runDry 1 prog-D1 ≡ true
_ = refl
_ : runDry 2 prog-D1 ≡ false
_ = refl

-- D2: k=2, h* = 3  (same as B2)
_ : runDry 2 prog-D2 ≡ true
_ = refl
_ : runDry 3 prog-D2 ≡ false
_ = refl

-- D3: k=3, h* = 4  (same as B3)
_ : runDry 3 prog-D3 ≡ true
_ = refl
_ : runDry 4 prog-D3 ≡ false
_ = refl

----------------------------------------------------------------------
-- Measurement pins — series E
-- Finding: h*(E, k) = 2k+1  (additive, slope 2 vs B's slope 1).
-- Double-wrap per step means two subscribeInner peels per acc level
-- rather than one.  Not multiplicative (k²): the inner mergeAll is
-- resolved inline, adding a constant 1 per nesting level, not k.
-- LOAD-BEARING: each pair fails if h* ≠ 2k+1.
----------------------------------------------------------------------

-- E1: k=1, h* = 3  (2*1+1)
_ : runDry 2 prog-E1 ≡ true
_ = refl
_ : runDry 3 prog-E1 ≡ false
_ = refl

-- E2: k=2, h* = 5  (2*2+1)
_ : runDry 4 prog-E2 ≡ true
_ = refl
_ : runDry 5 prog-E2 ≡ false
_ = refl

-- E3: k=3, h* = 7  (2*3+1)
_ : runDry 6 prog-E3 ≡ true
_ = refl
_ : runDry 7 prog-E3 ≡ false
_ = refl

----------------------------------------------------------------------
-- Measurement pins — series F
-- Finding: h*(F, n) = n (one peel per μ layer).
-- μ is the only expression besides subscribeInner and sharedConnect
-- that peels gas; each nested μ adds exactly one peel.
-- LOAD-BEARING: each pair fails if h* ≠ n.
----------------------------------------------------------------------

-- F1: one μ, h* = 1
_ : runDry 0 prog-F1 ≡ true
_ = refl
_ : runDry 1 prog-F1 ≡ false
_ = refl

-- F2: two μ, h* = 2
_ : runDry 1 prog-F2 ≡ true
_ = refl
_ : runDry 2 prog-F2 ≡ false
_ = refl

----------------------------------------------------------------------
-- Measurement pins — series G
-- Finding: sharedConnect costs exactly 1 gas peel.
-- LOAD-BEARING: fails if sharedConnect cost ≠ 1 (h*=0 or h*≥2).
-- NOTE: "second reference costs 0" confirmed by reading
-- subscribeSharedSlot (Evaluator.agda:1374) — already in
-- connectedShares → skips sharedConnect entirely.  Not measurable via
-- h* because siblings receive the same gas from thruWalk.
----------------------------------------------------------------------

-- G-single: one connect to shared slot, h* = 1
_ : runDry-G 0 ≡ true
_ = refl
_ : runDry-G 1 ≡ false
_ = refl

----------------------------------------------------------------------
-- Measurement pins — series H
-- Finding: h*(H) = 1 — deferᵉ costs 0 gas at subscribe time.
-- subscribeE fuel (deferᵉ body) does NOT emit dried for any fuel;
-- it only parks the body.  The sole gas cost is subscribeInner (1 peel).
-- LOAD-BEARING: fails if deferᵉ subscribe time cost were ≥ 1 gas peel.
----------------------------------------------------------------------

-- H: h* = 1
_ : runDry 0 prog-H ≡ true
_ = refl
_ : runDry 1 prog-H ≡ false
_ = refl

----------------------------------------------------------------------
-- Series P: registry and grown-inner probes
-- Tests conjuncts (hasDry) and (regsLen?) of subscribeE-walk-level.
--
-- WHY deferᵉ as base: all B/D/E-series use ofᵉ[nat̂ 0] as accumulator
-- seed, which produces empty registries at exit (ofᵉ fires synchronously
-- via oneShotBurst, no registration).  regsLen? [] = true vacuously for
-- any ℓ — those rows are DEGENERATE for conjunct (regsLen?).  Replacing
-- the base with strmᵗ(deferᵉ(ofᵉ[nat̂ 0])) forces a non-empty registry:
-- deferᵉ registers its body's source for async delivery, leaving a live
-- chain entry in the exit registry whose pathLen this probe measures.
--
-- sizeCapAt is abstract (depends on abstract fLvlD, Evaluator:746).
-- Ŝ = 5 is used for dBound; hopDᵉ and syncSizeᵉ compute at that Ŝ.
-- R̂ = 0 is used throughout; with U = 0 the suc R̂ * U term vanishes,
-- so R̂ is irrelevant to the numeral.
-- MECHANISM NOTE: sizeᵉ of the k=1 grown inner (acc₁) = 8 > Ŝ = 5.
-- The Ŝ-per-hop funding requires Ŝ ≥ sizeᵉ acc₁ = 8 to be non-vacuous
-- for the mechanism; Ŝ = 5 makes the hypothesis (sizeᵉ b ≤ Ŝ) vacuously
-- false at the acc₁ subscription point.  The dBound numeral is still
-- a valid upper bound on pathLen for these concrete runs, and the
-- regsLen? check confirms the conclusion holds regardless.
----------------------------------------------------------------------

-- Registry-checking runner: regsLen? ℓ against exit state's registry
runReg : ∀ (ℓ h : ℕ) (e : Closed Γ₀ natᵗ) → Bool
runReg ℓ h e =
  regsLen? ℓ (EvalSt.registry
    (proj₂ (proj₂ (subscribeE (gasPad h g0) e root 0 0
                               (sched-init e ins₀) (st-init e)))))

-- Deferred accumulator seed (compare scan-a0 = strmᵗ (ofᵉ [nat̂ 0]))
-- Using deferᵉ instead of ofᵉ: deferᵉ subscription registers a chain
-- entry, giving non-empty registry at exit for the path-length probe.
scan-a0-defer : Rx.Exp.Tm Γ₀ [] [] [] (obs natᵗ)
scan-a0-defer = strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ [])))

-- P-c: mergeAll(ofᵉ[deferᵉ(ofᵉ[0])]) — CALIBRATION
-- hasDry: CALIBRATION/DEGENERATE (h* = 1; same depth as A1, no scan growth)
-- regsLen?: LOAD-BEARING (1 registry entry at pathLen = 2; deferᵉ's frame
--   + the subscribeInner frame)
-- Ŝ-ceiling: this IS acc₁, the k=1 grown inner — its sizeᵉ = 8 is the
--   key mechanism measurement for both conjuncts
prog-P-c : Closed Γ₀ natᵗ
prog-P-c = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ []))) ∷ []))

-- P-a: mergeAll(scan(f-B, a0-defer, ofᵉ[1])) — k=1 scan
-- hasDry: LOAD-BEARING (grown inner acc₁ needs 2 gas peels; fails if scan
--   k=1 gas demand changes)
-- regsLen?: LOAD-BEARING (deferᵉ inside acc₁ registers at pathLen = 3;
--   fails if path depth of grown-inner registration changes)
prog-P-a : Closed Γ₀ natᵗ
prog-P-a = mergeAllᵉ (scanᵉ scan-f-B scan-a0-defer (ofᵉ (nat̂ 1 ∷ [])))

-- P-b: mergeAll(scan(f-B, a0-defer, ofᵉ[1,2])) — k=2 scan
-- hasDry: LOAD-BEARING (acc₂ requires 3 gas peels; fails if k=2 demand changes)
-- regsLen?: LOAD-BEARING (two registry entries: pathLen 3 from acc₁ and
--   pathLen 4 from acc₂→acc₁ chain; fails if nesting depth changes)
prog-P-b : Closed Γ₀ natᵗ
prog-P-b = mergeAllᵉ (scanᵉ scan-f-B scan-a0-defer (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

----------------------------------------------------------------------
-- Ŝ-ceiling witnesses: sizeᵉ/syncSizeᵉ of the grown inner values
-- acc₁ = prog-P-c (the k=1 accumulator value at runtime)
-- Both conjuncts' mechanism rests on sizeᵉ b ≤ Ŝ per hop.
----------------------------------------------------------------------

-- sizeᵉ of the k=1 grown inner = 8
-- LOAD-BEARING (hasDry + regsLen?): fails if acc₁'s syntactic size changes.
-- MECHANISM: needs Ŝ ≥ 8 for non-vacuous coverage; Ŝ = 5 used below is
-- conservative (dBound still bounds pathLen for concrete runs).
_ : sizeᵉ prog-P-c ≡ 8
_ = refl

-- syncSizeᵉ = s in dBound; pin to document the budget argument
-- LOAD-BEARING: fails if syncSizeᵉ formula changes for these programs
_ : syncSizeᵉ prog-P-c ≡ 5
_ = refl

_ : syncSizeᵉ prog-P-a ≡ 13
_ = refl

_ : syncSizeᵉ prog-P-b ≡ 14
_ = refl

----------------------------------------------------------------------
-- P-c measurement pins (CALIBRATION for hasDry; LOAD-BEARING for regsLen?)
-- Ŝ = 5, R̂ = 0, U = 0, r = hopDᵉ 5 prog-P-c = 1, s = 5
-- G = dBound 5 0 0 1 5 = 5 + 6*1 = 11
----------------------------------------------------------------------

-- hasDry: h* = 1 (CALIBRATION/DEGENERATE — no scan growth, same as A1)
_ : runDry 0 prog-P-c ≡ true
_ = refl
_ : runDry 1 prog-P-c ≡ false
_ = refl

-- regsLen?: max pathLen = 2 (LOAD-BEARING)
-- Fails if deferᵉ registration path length changes.
_ : runReg 2 1 prog-P-c ≡ true    -- max len ≤ 2 ✓
_ = refl
_ : runReg 1 1 prog-P-c ≡ false   -- not all ≤ 1 → max exactly 2
_ = refl

-- dBound numerals (CALIBRATION: fails if formula changes)
_ : hopDᵉ 5 (slotHop 5 ins₀) prog-P-c ≡ 1
_ = refl
_ : dBound 5 0 0 1 5 ≡ 11
_ = refl

-- margin check: max pathLen = 2 ≤ G = 11 (exercises regsLen? conjunct)
-- LOAD-BEARING (regsLen?): fails if max pathLen > G
_ : (2 ≤ᵇ 12) ≡ true    -- 2 ≤ suc 11 = 12
_ = refl

-- hasDry bound: h* = 1 ≤ suc G = 12 (exercises hasDry conjunct)
-- CALIBRATION/DEGENERATE: same depth as A1; no scan growth here
_ : (1 ≤ᵇ 12) ≡ true    -- 1 ≤ suc 11 = 12
_ = refl

----------------------------------------------------------------------
-- P-a measurement pins (LOAD-BEARING for hasDry and regsLen?)
-- k=1 scan; acc₁ = prog-P-c; sizeᵉ acc₁ = 8
-- Ŝ = 5, R̂ = 0, U = 0, r = hopDᵉ 5 prog-P-a = 244, s = 13
-- G = dBound 5 0 0 244 13 = 13 + 6*244 = 13 + 1464 = 1477
----------------------------------------------------------------------

-- hasDry: h* = 2 (bisection — acc₁ inside outer mergeAll needs 2 peels)
-- LOAD-BEARING (hasDry): fails if gas demand of mergeAll(scan k=1) changes
_ : runDry 1 prog-P-a ≡ true
_ = refl
_ : runDry 2 prog-P-a ≡ false
_ = refl

-- regsLen?: max pathLen = 3 (deferᵉ inside acc₁ at depth 3)
-- LOAD-BEARING (regsLen?): fails if the grown-inner path depth changes
_ : runReg 3 2 prog-P-a ≡ true    -- max len ≤ 3 ✓
_ = refl
_ : runReg 2 2 prog-P-a ≡ false   -- not all ≤ 2 → max exactly 3
_ = refl

-- dBound numerals
-- LOAD-BEARING: fails if hopDᵉ formula for scan(f-B) changes
_ : hopDᵉ 5 (slotHop 5 ins₀) prog-P-a ≡ 244
_ = refl
_ : dBound 5 0 0 244 13 ≡ 1477
_ = refl

-- margin check: max pathLen = 3 ≤ G = 1477 (margin 1474)
-- LOAD-BEARING (regsLen?): fails if max pathLen > G
_ : (3 ≤ᵇ 1478) ≡ true    -- 3 ≤ suc 1477 = 1478
_ = refl

-- hasDry bound: h* = 2 ≤ suc G = 1478
-- LOAD-BEARING (hasDry): fails if actual h* > G
_ : (2 ≤ᵇ 1478) ≡ true    -- 2 ≤ suc 1477 = 1478
_ = refl

----------------------------------------------------------------------
-- P-b measurement pins (LOAD-BEARING for hasDry and regsLen?)
-- k=2 scan; acc₁ at pathLen 3, acc₂→acc₁ at pathLen 4
-- Ŝ = 5, R̂ = 0, U = 0, r = hopDᵉ 5 prog-P-b = 244, s = 14
-- G = dBound 5 0 0 244 14 = 14 + 6*244 = 14 + 1464 = 1478
----------------------------------------------------------------------

-- hasDry: h* = 3 (acc₂ requires 3 gas peels through the nesting)
-- LOAD-BEARING (hasDry): fails if gas demand of mergeAll(scan k=2) changes
_ : runDry 2 prog-P-b ≡ true
_ = refl
_ : runDry 3 prog-P-b ≡ false
_ = refl

-- regsLen?: two entries, max pathLen = 4 (acc₂→acc₁→deferᵉ depth)
-- LOAD-BEARING (regsLen?): fails if the max path depth for k=2 changes
_ : runReg 4 3 prog-P-b ≡ true    -- max len ≤ 4 ✓
_ = refl
_ : runReg 3 3 prog-P-b ≡ false   -- not all ≤ 3 → max exactly 4
_ = refl

-- dBound numerals
-- hopDᵉ is same as prog-P-a: ofᵉ[nat̂ 1, nat̂ 2] contributes 0 hops,
-- scan-f-B and scan-a0-defer are unchanged
-- LOAD-BEARING: fails if scan hopDᵉ formula changes
_ : hopDᵉ 5 (slotHop 5 ins₀) prog-P-b ≡ 244
_ = refl
_ : dBound 5 0 0 244 14 ≡ 1478
_ = refl

-- margin check: max pathLen = 4 ≤ G = 1478 (margin 1474)
-- LOAD-BEARING (regsLen?): fails if max pathLen > G
_ : (4 ≤ᵇ 1479) ≡ true    -- 4 ≤ suc 1478 = 1479
_ = refl

-- hasDry bound: h* = 3 ≤ suc G = 1479
-- LOAD-BEARING (hasDry): fails if actual h* > G
_ : (3 ≤ᵇ 1479) ≡ true    -- 3 ≤ suc 1478 = 1479
_ = refl

----------------------------------------------------------------------
-- SERIES Q — THE MINIMAL-Ŝ HOP PROBE (2026-08-13), aimed at the live
-- edge named in `subscribeInner-walk`'s header (.Walk-Level): the walk
-- face's demand refill is Ŝ-SCALE while its value receipts are
-- LEVEL-scale, and NO hypothesis links the two.  Ŝ, R̂ and F are
-- quantified FREELY by the face, so the adversarial instantiation is
-- the SMALLEST one:
--
--   Ŝ := 0, R̂ := 0, F := 0, and U := 0 (no shares, empty slot store)
--     ⇒ G = dBound 0 0 0 (hopDᵉ 0 b) (syncSizeᵉ b)
--         = syncSizeᵉ b + hopDᵉ 0 b            (dBound's own definition)
--
-- and `gasPad (suc G) g0 hasAtLeast suc G` by `hasAtLeast-pad`, so the
-- gas hypothesis holds EXACTLY, with nothing spare.  Every other
-- hypothesis of the face is satisfiable here (root path, entry state,
-- caps taken as large as one likes — they are separate parameters).
-- So the face asserts these runs do NOT dry, and a `true` row REFUTES
-- IT — not merely the hop-edge leaf but WalkStmt itself.
--
-- WHY THIS FAMILY.  `sucG` is a SUM (a static syntactic size), while
-- gas demand tracks the within-instant nesting DEPTH, which for a scan
-- fold of depth d over a k-element list is a PRODUCT d·k.  A sum
-- cannot dominate a product forever, so if the mechanism is unsound
-- the crossover is reachable by raising d and k together.  The
-- B/D/E series above cannot see this: their folds have FIXED wrap
-- depth (1, 1, and 2), so both sides grow linearly per element and
-- the margin never closes.  Q varies d and k independently.
--
-- MEASURED, and the fit is exact on six points:
--     sucG (progD d k) = 5·d + k + 12
--   (19, 29, 31, 46, 50, 72 at (1,2) (3,2) (3,4) (6,4) (6,8) (10,10))
-- against a demand of d·k + 1.
----------------------------------------------------------------------

-- wrap a term d mergeAll-levels deeper
wrapD : ∀ {Θ} → ℕ → Tm Γ₀ [] [] Θ (obs natᵗ) → Tm Γ₀ [] [] Θ (obs natᵗ)
wrapD 0       t = t
wrapD (suc d) t = strmᵗ (mergeAllᵉ (ofᵉ (wrapD d t ∷ [])))

-- the fold that wraps the accumulator d levels per value
foldD : ℕ → Fn Γ₀ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
foldD d = wrapD d (fstᵗ (varᵗ (here refl)))

natsD : ℕ → List (Tm Γ₀ [] [] [] natᵗ)
natsD 0       = []
natsD (suc k) = nat̂ k ∷ natsD k

progD : ℕ → ℕ → Closed Γ₀ natᵗ
progD d k =
  mergeAllᵉ (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (ofᵉ (natsD k)))

-- the gas the face's demand hypothesis supplies at the minimal
-- instantiation: suc G, with G = syncSizeᵉ b + hopDᵉ 0 b
sucG : Closed Γ₀ natᵗ → ℕ
sucG b = suc (syncSizeᵉ b + hopDᵉ 0 (slotHop 0 ins₀) b)

-- the sum side, pinned.  LOAD-BEARING: each fails if syncSizeᵉ or
-- hopDᵉ moves, which is what the whole comparison rests on.
_ : sucG (progD 1 2) ≡ 19
_ = refl
_ : sucG (progD 3 2) ≡ 29
_ = refl
_ : sucG (progD 3 4) ≡ 31
_ = refl
_ : sucG (progD 6 4) ≡ 46
_ = refl
_ : sucG (progD 6 8) ≡ 50
_ = refl
_ : sucG (progD 10 10) ≡ 72
_ = refl

-- the demand side.  LOAD-BEARING: this is the row that validates the
-- d·k model, and it fails if demand is not at least d·k+1 = 13 here.
_ : runDry 12 (progD 3 4) ≡ true
_ = refl

-- ⚠ COST, MEASURED 2026-08-13 — AND THE CROSSOVER ROW IS A MULTI-HOUR
-- JOB, NOT A PIN.  `runDry` gives NO short-circuit in either direction:
-- `hasDry` reads the stream `subscribeE` RETURNS, so the whole run is
-- normalised before the first dry event can be seen.  (The cheap rows
-- above are cheap because their PROGRAMS are small — not, as first
-- assumed when this series was designed, because drying exits early.
-- That assumption is what made the crossover row look affordable.)
--
-- The cost is intrinsic to the family and it is QUADRATIC in k: `scanᵉ`
-- emits every intermediate accumulator, accᵢ carries d·i nested levels,
-- and the outer *All subscribes all of them — so a run normalises
-- d·k(k+1)/2 subscription levels.  At the cheapest crossing point that
-- is ~250-300, and (8,8) had burned 56 min CPU without finishing.
-- Nothing much cheaper exists: minimising d·k(k+1)/2 subject to the
-- crossing condition 5d + k + 12 ≤ d·k bottoms out around 250 for
-- (7,8)/(6,9)/(8,8), all within ~15% of each other.
--
-- So the family SAFE region is pinned above and the crossing region is
-- NOT MEASURED — deliberately, with the cost named rather than the row
-- quietly dropped.  Whoever runs it should detach it for hours, not
-- expect a pin.  What it would mean is in `subscribeInner-walk`'s header.
--
-- SAFE at these shapes, by three orders on the small ones and by 18 at
-- (3,4): sucG 31 vs demand 13.  The margin NARROWS as d·k grows against
-- 5d + k + 12, and the model puts the crossover just above (6,8) —
-- sucG 50 against demand 49.

----------------------------------------------------------------------
-- SERIES P EXTENSION (2026-08-14) — covering the three NOT-COVERED
-- shapes named in Walk-Level's PROBED receipt: (a) the compounding
-- regime (k ≥ 3 and nested scans), (b) share/connect edges in the
-- growth path, and (c) registry states with more than two entries.
--
-- These are DE-RISK rows.  A `true` bisection row REFUTES the
-- regsLen? or hasDry conjunct at Ŝ = 5; a `false` row confirms
-- the bound holds.  Ŝ = 5 is conservative (below acc₁'s sizeᵉ = 8),
-- so green here implies green at any faithful (larger) Ŝ.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- P-c3: k=3 B-series with deferᵉ seed (shapes a and c)
-- hasDry: h* = 4 (acc₃ chain requires 4 subscribeInner peels)
-- regsLen?: 3 entries at pathLen 3, 4, 5; max = 5
-- shape (a): k = 3 > 2
-- shape (c): 3 registry entries > 2
-- Ŝ = 5, R̂ = 0, U = 0, r = hopDᵉ 5 prog-P-c3 = 244, s = 15
-- G = dBound 5 0 0 244 15 = 15 + 6*244 = 1479
----------------------------------------------------------------------

prog-P-c3 : Closed Γ₀ natᵗ
prog-P-c3 = mergeAllᵉ (scanᵉ scan-f-B scan-a0-defer
                        (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

-- hasDry: h* = 4 — LOAD-BEARING
_ : runDry 3 prog-P-c3 ≡ true
_ = refl
_ : runDry 4 prog-P-c3 ≡ false
_ = refl

-- regsLen?: max pathLen = 5 — LOAD-BEARING (shape c: 3 entries)
_ : runReg 5 4 prog-P-c3 ≡ true
_ = refl
_ : runReg 4 4 prog-P-c3 ≡ false
_ = refl

-- dBound numerals
-- LOAD-BEARING: fails if hopDᵉ or syncSizeᵉ formula changes
_ : hopDᵉ 5 (slotHop 5 ins₀) prog-P-c3 ≡ 244
_ = refl
_ : syncSizeᵉ prog-P-c3 ≡ 15
_ = refl
_ : dBound 5 0 0 244 15 ≡ 1479
_ = refl

-- margin check: max pathLen = 5 ≤ G = 1479 (ratio ≈ 296)
-- LOAD-BEARING (regsLen?): fails if max pathLen > G
_ : (5 ≤ᵇ 1480) ≡ true
_ = refl

-- hasDry bound: h* = 4 ≤ suc G = 1480
-- LOAD-BEARING (hasDry): fails if actual h* > G
_ : (4 ≤ᵇ 1480) ≡ true
_ = refl

----------------------------------------------------------------------
-- P-c4: k=4 B-series with deferᵉ seed (shapes a and c)
-- hasDry: h* = 5 (acc₄ chain requires 5 subscribeInner peels)
-- regsLen?: 4 entries at pathLen 3, 4, 5, 6; max = 6
-- shape (a): k = 4 > 2
-- shape (c): 4 registry entries > 2
-- Ŝ = 5, R̂ = 0, U = 0, r = hopDᵉ 5 prog-P-c4 = 244, s = 16
-- G = dBound 5 0 0 244 16 = 16 + 6*244 = 1480
----------------------------------------------------------------------

prog-P-c4 : Closed Γ₀ natᵗ
prog-P-c4 = mergeAllᵉ (scanᵉ scan-f-B scan-a0-defer
                        (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ [])))

-- hasDry: h* = 5 — LOAD-BEARING
_ : runDry 4 prog-P-c4 ≡ true
_ = refl
_ : runDry 5 prog-P-c4 ≡ false
_ = refl

-- regsLen?: max pathLen = 6 — LOAD-BEARING (shape c: 4 entries)
_ : runReg 6 5 prog-P-c4 ≡ true
_ = refl
_ : runReg 5 5 prog-P-c4 ≡ false
_ = refl

-- dBound numerals
_ : hopDᵉ 5 (slotHop 5 ins₀) prog-P-c4 ≡ 244
_ = refl
_ : syncSizeᵉ prog-P-c4 ≡ 16
_ = refl
_ : dBound 5 0 0 244 16 ≡ 1480
_ = refl

-- margin check: max pathLen = 6 ≤ G = 1480 (ratio ≈ 247)
_ : (6 ≤ᵇ 1481) ≡ true
_ = refl

-- hasDry bound: h* = 5 ≤ suc G = 1481
_ : (5 ≤ᵇ 1481) ≡ true
_ = refl

----------------------------------------------------------------------
-- P-COMP2: nested scan (outer scan over inner scan's emissions)
-- shape (a) COMPOUNDING REGIME: hopDᵉ grows as a product of the two
-- scan's hopDᵉ values, giving the squaring/compounding behaviour.
--
-- scan-f-COMP: takes (acc : obs natᵗ, val : obs natᵗ) and merges both
-- inner scan: scanᵉ scan-f-B scan-a0-defer (ofᵉ [1,2]) → emits acc₀,acc₁,acc₂
-- outer scan: scanᵉ scan-f-COMP scan-a0-defer inner_scan
--
-- hopDᵉ 5 inner_scan = 3^5 * (1+0+0) = 243
-- hopDᵉ 5 outer_scan = 3^5 * (1+0+243) = 243 * 244 = 59292
-- hopDᵉ 5 prog-P-COMP2 = suc 59292 = 59293
-- dBound at Ŝ=5: G = syncSizeᵉ + 6*59293 — LARGE; margin ≫ h*
--
-- hasDry: h* = 4 (deepest path: outer→outer-acc₂→outer-acc₁→inner-acc₁→deferᵉ)
-- regsLen?: max pathLen = 5 (thru-outer ↠ from-inner^4 ↠ root)
----------------------------------------------------------------------

-- compound fold: merges accumulator (obs natᵗ) with incoming (obs natᵗ)
scan-f-COMP : Rx.Exp.Fn Γ₀ [] [] [] ((obs natᵗ) ×ᵗ (obs natᵗ)) (obs natᵗ)
scan-f-COMP = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
                                     ∷ sndᵗ (varᵗ (here refl)) ∷ [])))

prog-P-COMP2 : Closed Γ₀ natᵗ
prog-P-COMP2 = mergeAllᵉ
  (scanᵉ scan-f-COMP scan-a0-defer
         (scanᵉ scan-f-B scan-a0-defer (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ []))))

-- hasDry: h* = 4 — LOAD-BEARING (compounding does not deepen gas demand)
_ : runDry 3 prog-P-COMP2 ≡ true
_ = refl
_ : runDry 4 prog-P-COMP2 ≡ false
_ = refl

-- regsLen?: max pathLen = 5 — LOAD-BEARING
_ : runReg 5 4 prog-P-COMP2 ≡ true
_ = refl
_ : runReg 4 4 prog-P-COMP2 ≡ false
_ = refl

-- hopDᵉ at Ŝ=5: measures compounding growth (inner 243; outer 244× that)
-- LOAD-BEARING: fails if nested-scan hopDᵉ formula changes
_ : hopDᵉ 5 (slotHop 5 ins₀) (scanᵉ scan-f-B scan-a0-defer (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ []))) ≡ 243
_ = refl
_ : hopDᵉ 5 (slotHop 5 ins₀) prog-P-COMP2 ≡ 59293
_ = refl

-- margin check at Ŝ=5 (G grows with hopDᵉ; max pathLen = 5):
-- Even without pinning syncSizeᵉ: G ≥ 6*59293 = 355758; pathLen 5 ≪ G
-- LOAD-BEARING (regsLen?): 5 ≤ suc G trivially for any G ≥ 5
_ : (5 ≤ᵇ 355759) ≡ true
_ = refl

----------------------------------------------------------------------
-- P-S1: share in the growth path (shape b: share/connect edges)
-- Context Γ₁ (one nat slot mapped to shared(ofᵉ[1])).
-- scan-a0-share = strmᵗ(input zero): initial acc references shared slot.
-- acc₁ at runtime = mergeAll([input zero]) = mergeAll([shared observable]).
-- Subscribing acc₁ calls sharedConnect (1 peel), adding to the h* cost.
--
-- hasDry: h* = 3 (outer subscribeInner + acc₁'s subscribeInner + sharedConnect)
-- regsLen?: sharedConnect registers at (from-inner ↠ from-inner ↠ root)
--   → pathLen = 2 (same level as P-c calibration; no deferᵉ thru-outer added)
-- Ŝ = 5, R̂ = 0, U = 0, r = hopDᵉ 5 prog-P-S1 = 244, s = 13
-- G = dBound 5 0 0 244 13 = 1477
----------------------------------------------------------------------

-- Runners for Γ₁ context (share slot)
runDry₁ : ∀ {t} (h : ℕ) (e : Closed Γ₁ t) → Bool
runDry₁ h e =
  hasDry (proj₁ (subscribeE (gasPad h g0) e root 0 0
                             (sched-init e ins₁) (st-init e)))

runReg₁ : ∀ (ℓ h : ℕ) (e : Closed Γ₁ natᵗ) → Bool
runReg₁ ℓ h e =
  regsLen? ℓ (EvalSt.registry
    (proj₂ (proj₂ (subscribeE (gasPad h g0) e root 0 0
                               (sched-init e ins₁) (st-init e)))))

scan-a0-share : Rx.Exp.Tm Γ₁ [] [] [] (obs natᵗ)
scan-a0-share = strmᵗ (input zero)

prog-P-S1 : Closed Γ₁ natᵗ
prog-P-S1 = mergeAllᵉ
  (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))))
         scan-a0-share
         (ofᵉ (nat̂ 1 ∷ [])))

-- hasDry: h* = 3 (outer subscribeInner + acc₁ subscribeInner + sharedConnect)
-- LOAD-BEARING (hasDry): fails if sharedConnect cost changes or nesting depth changes
_ : runDry₁ 2 prog-P-S1 ≡ true
_ = refl
_ : runDry₁ 3 prog-P-S1 ≡ false
_ = refl

-- regsLen?: DEGENERATE — sharedConnect writes to connectedShares, NOT to
-- EvalSt.registry (the async delivery queue that regsLen? checks).  No deferᵉ
-- in prog-P-S1, so the registry is empty; regsLen? is vacuously true at any ℓ.
-- FINDING: the regsLen? conjunct is vacuous for share-only programs —
-- only deferᵉ subscription adds to EvalSt.registry.
_ : runReg₁ 0 3 prog-P-S1 ≡ true
_ = refl

-- dBound numerals
-- hopDᵉ: input zero contributes 0, so same formula as P-a
-- LOAD-BEARING: fails if shared-slot hopDᵉ formula changes
_ : hopDᵉ 5 (slotHop 5 ins₁) prog-P-S1 ≡ 244
_ = refl
_ : syncSizeᵉ prog-P-S1 ≡ 13
_ = refl
_ : dBound 5 0 0 244 13 ≡ 1477
_ = refl

-- margin check: max pathLen = 2 ≤ G = 1477 (ratio ≈ 739)
-- LOAD-BEARING (regsLen?): confirms conjunct holds at this shape
_ : (2 ≤ᵇ 1478) ≡ true
_ = refl

-- hasDry bound: h* = 3 ≤ suc G = 1478
-- LOAD-BEARING (hasDry): confirms conjunct holds
_ : (3 ≤ᵇ 1478) ≡ true
_ = refl

----------------------------------------------------------------------
-- SERIES W (2026-08-14) — the input clause's burstHopD? conjunct.
-- IT REFUTED THE OLD STATEMENT, AND IT NOW CERTIFIES THE NEW ONE, on
-- the SAME program: that is the whole value of keeping it.
--
-- THE REFUTATION, for the record (the old conjunct read
-- `burstHopD? F (hopDᵉ F prog-W)`, with hopD's input clause = 0):
--   · hopDᵉ V (input i) = 0                     — the old clause, ∀ V
--   · hopDᵛ V (obs t) e = hopDᵉ V e             — a stream-typed VALUE
--     carries its expression's hop depth
--   · sharedConnect passes the def's burst up via sharedPlumb, which
--     retags `kind` only — values untouched
--   · no entry hypothesis bounded the hop content of a slot's def:
--     slotsCaps? is size/width, INV? is size/fnCap.
-- So a slot of type (obs natᵗ) whose shared def emits the stream-value
-- strmᵗ (mergeAllᵉ emptyᵉ) — hop depth 1 — put a hop-1 value into the
-- connect burst against a bound of 0, at every F and every witness j′.
--
-- THE REPAIR, which is what the rows below now pin: hopD carries an
-- input environment η (Rx.Hop-Depth) and the walk face rides the
-- honest one, `slotHop F sl` (Rx.Slot-Hop).  At this very program
-- `slotHop F insᵂ zero` IS the def's hop, so the bound rises from 0 to
-- 1 and the conjunct comes out TRUE — with the hop-1 value it used to
-- reject now exactly at the bound.
--
-- REGION REACHED, and it is the point: the share/connect edge at an
-- OBS-TYPED slot — the exact region input-wet was FALSITY for, and the
-- one every earlier share probe missed by living at ground-typed slots
-- (whose values are hop-0, where the old conjunct held trivially).
-- NOT REACHED: slot defs whose own hop is large enough to test
-- slotHop-cap's quantitative margin — that bound is still unprobed.
----------------------------------------------------------------------

-- context: ONE slot of STREAM type — the shape no prior probe used
Γᵂ : Ctx 1
Γᵂ = (obs natᵗ) ∷ⱽ []ⱽ

-- the smuggled hop: a hop-1 expression carried as a VALUE
Yᵂ : Closed Γᵂ natᵗ
Yᵂ = mergeAllᵉ emptyᵉ

defᵂ : Closed Γᵂ (obs natᵗ)
defᵂ = ofᵉ (strmᵗ Yᵂ ∷ [])

insᵂ : Slots Γᵂ
insᵂ = λ { zero → shared defᵂ }

prog-W : Closed Γᵂ (obs natᵗ)
prog-W = input zero

schedᵂ : Sched Γᵂ
schedᵂ = sched-init prog-W insᵂ

stᵂ : EvalSt prog-W
stᵂ = st-init prog-W

-- THE OLD BOUND, kept as the refutation's own witness: with the
-- constant-0 environment the input clause still measures 0 at every
-- index.  LOAD-BEARING — it is what makes the row below a repair
-- rather than a coincidence of renaming.
_ : ∀ (V : ℕ) → hopDᵉ V (λ _ → 0) prog-W ≡ 0
_ = λ _ → refl

-- the smuggled value's hop depth is 1 at EVERY index — definitional
-- LOAD-BEARING: fails if mergeAllᵉ's hop contribution changes
_ : ∀ (V : ℕ) → hopDᵉ V (λ _ → 0) Yᵂ ≡ 1
_ = λ _ → refl

-- THE HONEST BOUND IS 1, NOT 0, AT EVERY INDEX — slotHop reads the
-- slot's own def.  LOAD-BEARING: this single number is the difference
-- between the refuted statement and the restated one.
_ : ∀ (V : ℕ) → hopDᵉ V (slotHop V insᵂ) prog-W ≡ 1
_ = λ _ → refl

-- and it is the FIXPOINT, not a coincidence of this program's shape:
-- the staged number equals the def's hop under the full environment.
-- LOAD-BEARING: fails if ηAt's stage recursion misses slot zero.
_ : ∀ (V : ℕ) →
    slotHop V insᵂ zero ≡ hopDᵉ V (slotHop V insᵂ) defᵂ
_ = λ V → slotHop-fix V insᵂ zero refl

-- THE CORE ROW, FLIPPED.  The conjunct that was FALSE at every
-- measurement index and every non-dry gas is now TRUE at both — same
-- program, same burst, same hop-1 value, honest bound.
-- LOAD-BEARING — this is the receipt that the restatement repairs the
-- refuted region, and it fails if slotHop stops seeing the def.
_ : ∀ (F : ℕ) (fl : Gas) →
    burstHopD? F (slotHop F insᵂ) (hopDᵉ F (slotHop F insᵂ) prog-W)
      (proj₁ (subscribeE (gs fl) prog-W root 0 0 schedᵂ stᵂ)) ≡ true
_ = λ _ _ → refl

-- and the OLD bound still rejects that same burst — so the row above
-- is a real repair, not a weakened test.
-- LOAD-BEARING: fails if the burst ever stops carrying the hop-1 value.
_ : ∀ (F : ℕ) (fl : Gas) →
    burstHopD? F (λ _ → 0) 0
      (proj₁ (subscribeE (gs fl) prog-W root 0 0 schedᵂ stᵂ)) ≡ false
_ = λ _ _ → refl

-- the burst is REAL, not dry — the failure is hop content, not gas
-- LOAD-BEARING (separates this from a dryness artifact)
_ : hasDry (proj₁ (subscribeE (gasPad 1 g0) prog-W root 0 0 schedᵂ stᵂ))
    ≡ false
_ = refl

-- boundary: at g0 the connect dries (the gas hypothesis is what
-- excludes this case; DEGENERATE for the refutation, pinned so the
-- row above is known to sit past the dry boundary)
_ : hasDry (proj₁ (subscribeE g0 prog-W root 0 0 schedᵂ stᵂ)) ≡ true
_ = refl

-- THE FULL INSTANTIATION that carried the refutation — WalkStmt
-- {e = prog-W} prog-W → ⊥, every hypothesis discharged at concrete or
-- verbatim values — IS DELETED, because the statement it refuted no
-- longer exists: WalkStmt's hop conjunct now reads the honest
-- environment and the rows above pin it TRUE on this very program.
-- Keeping a ⊥-derivation against a restated conjunct would not
-- typecheck, and re-deriving the restated conjunct FROM the face would
-- be circular.  What the instantiation established is preserved where
-- it is checkable: the flipped core row above, on the same program,
-- same burst, same value.
-- RECOVERY: git show 9c3527a restores the full ⊥-derivation, including
-- the symbolic instantiation recipe (L̂ := opIterD itself, Ŝ = F :=
-- cSize (frameStep L̂ cᵂ), G ℓ := the dBound term, g := gasPad (suc G)
-- g0) — worth having if any future walk-face restatement needs to be
-- re-refuted at this shape.

----------------------------------------------------------------------
-- SERIES S (2026-08-14) — slotHop-cap, the η leg's quantitative core.
--
-- THE REGION: stratification lets slot k's def read input (k-1), and
-- hopD's scan clause MULTIPLIES its body by (2 + pm)^V.  So a chain of
-- shared slots is an AMPLIFIER TOWER, and it is the shape the cap has
-- to survive.  These rows build the tower and measure it.
--
-- ⚠ WHAT THIS REFUTES: slotHop-cap's own header (and the analysis that
-- dictated it) claimed the margin was "thin BY CONSTRUCTION", with the
-- telescope reaching exponent order V^(V+1) — hopR's own order.  THAT
-- IS WRONG, and the arithmetic error is instructive: `slotsSize sl ≤ V`
-- caps the TOTAL slot size at V, so a telescope cannot hold V slots of
-- size V.  Each amplifier link costs ~14 units of size, so a legal
-- telescope holds at most ~V/14 links, and the compound exponent is
-- O(V²) — against hopR's (1+V)^(1+V).  Amplification is exponential in
-- V²; the cap is exponential in V^V.  The gap is superexponential and
-- WIDENS with chain depth, because every extra link raises V too.
--
-- ⚠ WHY THERE IS NO ≤ᵇ ROW: the comparison is NOT computable in this
-- region, and that is a property of the region, not a gap in effort.
-- A telescope big enough to amplify forces V ≥ 16, and hopR 16 =
-- 18^(17^17) has ~10^21 digits.  Where hopR IS computable (V ≤ 6) the
-- telescope is too small to hold a single scan, so every row there is
-- DEGENERATE.  Hence the split below: the left side is pinned exactly,
-- and the right side is reached through its EXPONENT, which computes.
-- CONCLUSION-SIDE blocked, HYPOTHESIS-SIDE fine — the two are separate
-- questions and only the conclusion's magnitude is out of reach.
----------------------------------------------------------------------

Γˢ : Ctx 2
Γˢ = (obs natᵗ) ∷ⱽ (obs natᵗ) ∷ⱽ []ⱽ

-- slot 0's def: no inputs (stratification allows none below zero)
dˢ0 : Closed Γˢ (obs natᵗ)
dˢ0 = mergeAllᵉ emptyᵉ

scan-fˢ : Rx.Exp.Fn Γˢ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
scan-fˢ = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

scan-zˢ : Rx.Exp.Tm Γˢ [] [] [] (obs natᵗ)
scan-zˢ = strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ [])))

-- slot 1's def: SCANS OVER INPUT 0 — the amplifying link
dˢ1 : Closed Γˢ (obs natᵗ)
dˢ1 = scanᵉ scan-fˢ scan-zˢ (mergeAllᵉ (input zero))

insˢ : Slots Γˢ
insˢ = λ { zero → shared dˢ0 ; (F.suc zero) → shared dˢ1 }

-- the target the walk face measures: the downstream slot itself
bˢ : Closed Γˢ (obs natᵗ)
bˢ = input (F.suc zero)

-- the TIGHTEST legal budget: V := slotsSize.  This is the worst case
-- for the cap — any larger V only inflates hopR.
Vˢ : ℕ
Vˢ = slotsSize insˢ

-- HYPOTHESIS SIDE, all three discharged at Vˢ.  LOAD-BEARING: if any
-- of these failed, every row below would say nothing about the cap.
_ : (2 ≤ᵇ Vˢ) ≡ true
_ = refl
_ : (slotsSize insˢ ≤ᵇ Vˢ) ≡ true
_ = refl
_ : (sizeᵉ bˢ ≤ᵇ Vˢ) ≡ true
_ = refl

-- the tower is genuinely built: 16 units of slot, forcing V = 16
_ : Vˢ ≡ 16
_ = refl

-- the base link's hop, and the amplified link's.  LOAD-BEARING: the
-- second is the compound the cap must dominate, and it is 3^(V+1) —
-- one scan factor (2+pm)^V = 3^16 times the base's (1 + 0 + suc 1).
_ : slotHop Vˢ insˢ zero ≡ 1
_ = refl
_ : hopDᵉ Vˢ (slotHop Vˢ insˢ) bˢ ≡ 129140163
_ = refl

-- THE MARGIN, in the only terms that compute.  hopR V = (2+V)^((1+V)^(1+V)),
-- so it suffices that the compound sit under 2 ^ ((1+V)^(1+V)).
-- LOAD-BEARING both: the first fails if the compound grows past 2^27,
-- the second fails if hopR's exponent ever drops below 27.
_ : (129140163 ≤ᵇ 2 ^ 27) ≡ true
_ = refl
_ : (27 ≤ᵇ suc Vˢ ^ suc Vˢ) ≡ true
_ = refl

-- ⚠ RESIDUE, stated so it is not mistaken for closed: the step from
-- those two rows to the cap is `2 ^ 27 ≤ (2+V) ^ ((1+V)^(1+V))`, i.e.
-- ^-monotonicity in base and exponent.  That is a PROOF, not a pin,
-- and it is the shape the general discharge would take: bound the
-- compound by (2+V)^(O(V²)), then spend V² ≤ (1+V)^(1+V).

-- ── DEPTH 2: does the gap NARROW as the tower grows?  This is the
-- question a single link cannot answer, and the answer is no — every
-- extra link costs slot size, which raises V, which raises hopR's
-- exponent (1+V)^(1+V) far faster than it raises the compound.

Γᵗ : Ctx 3
Γᵗ = (obs natᵗ) ∷ⱽ (obs natᵗ) ∷ⱽ (obs natᵗ) ∷ⱽ []ⱽ

dᵗ0 : Closed Γᵗ (obs natᵗ)
dᵗ0 = mergeAllᵉ emptyᵉ

scan-fᵗ : Rx.Exp.Fn Γᵗ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
scan-fᵗ = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

scan-zᵗ : Rx.Exp.Tm Γᵗ [] [] [] (obs natᵗ)
scan-zᵗ = strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ [])))

dᵗ1 : Closed Γᵗ (obs natᵗ)
dᵗ1 = scanᵉ scan-fᵗ scan-zᵗ (mergeAllᵉ (input zero))

-- the SECOND amplifier, stacked on the first
dᵗ2 : Closed Γᵗ (obs natᵗ)
dᵗ2 = scanᵉ scan-fᵗ scan-zᵗ (mergeAllᵉ (input (F.suc zero)))

insᵗ : Slots Γᵗ
insᵗ = λ { zero → shared dᵗ0
         ; (F.suc zero) → shared dᵗ1
         ; (F.suc (F.suc zero)) → shared dᵗ2 }

bᵗ : Closed Γᵗ (obs natᵗ)
bᵗ = input (F.suc (F.suc zero))

Vᵗ : ℕ
Vᵗ = slotsSize insᵗ

_ : (2 ≤ᵇ Vᵗ) ≡ true
_ = refl
_ : (slotsSize insᵗ ≤ᵇ Vᵗ) ≡ true
_ = refl
_ : (sizeᵉ bᵗ ≤ᵇ Vᵗ) ≡ true
_ = refl

_ : Vᵗ ≡ 30
_ = refl

-- the two-link compound.  LOAD-BEARING: fails if either scan factor or
-- the chain's composition changes.
_ : hopDᵉ Vᵗ (slotHop Vᵗ insᵗ) bᵗ ≡ 127173474825649022325147488901
_ = refl

-- THE SAME MARGIN, one link deeper — and it is WIDER, not thinner.
-- LOAD-BEARING both.
_ : (127173474825649022325147488901 ≤ᵇ 2 ^ 97) ≡ true
_ = refl
_ : (97 ≤ᵇ suc Vᵗ ^ suc Vᵗ) ≡ true
_ = refl

-- THE TREND, which is the finding.  Writing hopR V = (2+V)^E(V) with
-- E(V) = (1+V)^(1+V), and the compound as ≤ 2^c:
--   depth 1:  V = 16,  c = 27,  E = 17^17 ≈ 8.3e20   →  E/c ≈ 3e19
--   depth 2:  V = 30,  c = 97,  E = 31^31 ≈ 1.7e46   →  E/c ≈ 1.8e44
-- One extra link widens the ratio by twenty-five orders of magnitude.
-- The reason is structural, not lucky: a link BUYS a factor (2+pm)^V
-- (adding O(V) to c) but COSTS ~14 slot-size, and `slotsSize sl ≤ V`
-- makes that cost raise V — which raises E super-exponentially.  So c
-- is O(V²) while E is V^V, and no legal telescope can close that.

----------------------------------------------------------------------
-- SERIES T (2026-08-14) — the FIXPOINT at a staged slot: the one thing
-- series W and series S each half-covered and neither closed.
--
-- THE GAP, precisely.  slotHop-fix is the equation input-wet's input
-- clause spends, and it is ASSEMBLED from two postulates (hopD-η-congᵉ,
-- ηAt-agrees, Rx.Slot-Hop).  Until now:
--   · series W pins the fixpoint, but at slot ZERO — where
--     `ηAt V sl 0 = λ _ → 0` and both postulates are vacuous (there is
--     no index below 0, so ηAt-agrees quantifies over nothing).
--   · series S stages at k = 2 and gets big honest numbers, but it only
--     ever evaluates the STAGED side; it never asks whether that number
--     equals the def's hop under the FULL environment.
-- So the staging recursion had been exercised and the fixpoint had been
-- pinned, but never both at once — and ηAt-agrees says something only
-- where they meet.  These rows are that intersection.
--
-- WHY IT IS LOAD-BEARING RATHER THAN A FORMALITY: the classic failure
-- of a staged environment is an off-by-one in `if toℕ i ≡ᵇ k`, and it
-- is INVISIBLE at slot 0.  Under it slot 1 would read the environment's
-- 0 for `input zero` instead of slot 0's true hop 1, and the rows below
-- would read 1 where they now read 2.  The contrast row pins that the
-- naive environment really does give the wrong number here, so the
-- fixpoint rows are separating two live alternatives, not confirming a
-- tautology.
----------------------------------------------------------------------

-- ── MINIMAL, DIAGNOSTIC: two slots, hops 1 and 2, no scan — the
-- numbers are small enough to read, so a staging bug is legible.
Γᵁ : Ctx 2
Γᵁ = (obs natᵗ) ∷ⱽ (obs natᵗ) ∷ⱽ []ⱽ

-- slot 0: closed, hop 1 (series W's def, in a wider context)
dᵁ0 : Closed Γᵁ (obs natᵗ)
dᵁ0 = ofᵉ (strmᵗ (mergeAllᵉ emptyᵉ) ∷ [])

-- slot 1: READS input zero — the stratification actually being used.
-- Its hop is `suc (η zero)`, so it is a direct probe of the environment.
dᵁ1 : Closed Γᵁ (obs natᵗ)
dᵁ1 = ofᵉ (strmᵗ (mergeAllᵉ (input zero)) ∷ [])

insᵁ : Slots Γᵁ
insᵁ = λ { zero → shared dᵁ0 ; (F.suc zero) → shared dᵁ1 }

-- the stage-0 slot is unchanged from series W
-- LOAD-BEARING: fails if slotHop stops reading slot 0's own def.
_ : ∀ (V : ℕ) → slotHop V insᵁ zero ≡ 1
_ = λ _ → refl

-- THE CONTRAST, and it is what makes the next row separate something:
-- under the naive constant-0 environment slot 1's def measures 1 — the
-- WRONG number, one short, exactly the off-by-one a staging bug gives.
-- LOAD-BEARING: if this were also 2 the fixpoint rows would be vacuous.
_ : ∀ (V : ℕ) → hopDᵉ V (λ _ → 0) dᵁ1 ≡ 1
_ = λ _ → refl

-- the staged environment gets it RIGHT: slot 1 sees slot 0's hop 1 and
-- adds its own hop edge.  LOAD-BEARING — this is the staging recursion
-- doing real work, and it is 2 only if `ηAt`'s `≡ᵇ` branch fires at the
-- right index.
_ : ∀ (V : ℕ) → slotHop V insᵁ (F.suc zero) ≡ 2
_ = λ _ → refl

-- ★ THE FIXPOINT AT A STAGED SLOT, BY refl — INDEPENDENT of both
-- postulates.  This is the row the series had been missing: the staged
-- number equals the def's hop under the FULL environment, at an index
-- where the stage is not the constant 0.
-- LOAD-BEARING: fails under any off-by-one in ηAt's staging.
_ : ∀ (V : ℕ) → slotHop V insᵁ (F.suc zero)
              ≡ hopDᵉ V (slotHop V insᵁ) dᵁ1
_ = λ _ → refl

-- and the SAME equation through slotHop-fix — which spends ηAt-agrees
-- at k = 1, i.e. in the region where it quantifies over a nonempty set
-- of indices.  Agreement between this and the refl row above is a
-- consistency check on the assembly, not a second proof of it.
_ : ∀ (V : ℕ) → slotHop V insᵁ (F.suc zero)
              ≡ hopDᵉ V (slotHop V insᵁ) dᵁ1
_ = λ V → slotHop-fix V insᵁ (F.suc zero) refl

-- ── AT SCALE: the same fixpoint on series S's amplifier telescope,
-- where the staged numbers are ~1.3e29 and the stage runs to k = 2.
-- Small-number agreement can hide an arithmetic mismatch that only
-- appears once the scan factors are in play.
-- LOAD-BEARING both: each fails if ηAt's stage disagrees with the
-- fixpoint at its own index.
_ : slotHop Vᵗ insᵗ (F.suc zero) ≡ hopDᵉ Vᵗ (slotHop Vᵗ insᵗ) dᵗ1
_ = refl

_ : slotHop Vᵗ insᵗ (F.suc (F.suc zero))
  ≡ hopDᵉ Vᵗ (slotHop Vᵗ insᵗ) dᵗ2
_ = refl

-- the k = 2 stage through the assembly, at scale
_ : slotHop Vᵗ insᵗ (F.suc (F.suc zero))
  ≡ hopDᵉ Vᵗ (slotHop Vᵗ insᵗ) dᵗ2
_ = slotHop-fix Vᵗ insᵗ (F.suc (F.suc zero)) refl


-- ── HETEROGENEOUS: a SCRIPTED slot below a shared one, which is the
-- ordinary telescope shape (a plain input feeding a derived const) and
-- the one the rows above skip by making every slot shared.  It tests a
-- different path through ηAt: the stage must carry slotHopD's
-- `scripted _ = 0` clause across, and slot 2's def must read slot 1's
-- hop past slot 0 rather than off the nearest neighbour.
Γᵛ : Ctx 3
Γᵛ = natᵗ ∷ⱽ (obs natᵗ) ∷ⱽ (obs natᵗ) ∷ⱽ []ⱽ

-- slot 0: SCRIPTED, hop 0 by slotHopD's first clause
dᵛ1 : Closed Γᵛ (obs natᵗ)
dᵛ1 = ofᵉ (strmᵗ (mergeAllᵉ emptyᵉ) ∷ [])

-- slot 2 reaches PAST the scripted slot to read slot 1
dᵛ2 : Closed Γᵛ (obs natᵗ)
dᵛ2 = ofᵉ (strmᵗ (mergeAllᵉ (input (F.suc zero))) ∷ [])

insᵛ : Slots Γᵛ
insᵛ = λ { zero → scripted (hot [])
         ; (F.suc zero) → shared dᵛ1
         ; (F.suc (F.suc zero)) → shared dᵛ2 }

-- the scripted slot contributes 0 — LOAD-BEARING: fails if slotHopD's
-- scripted clause is ever made to read the script's values
_ : ∀ (V : ℕ) → slotHop V insᵛ zero ≡ 0
_ = λ _ → refl

_ : ∀ (V : ℕ) → slotHop V insᵛ (F.suc zero) ≡ 1
_ = λ _ → refl

-- slot 2 reads slot 1's hop ACROSS the scripted slot: 2, not 1.
-- LOAD-BEARING: a stage that dropped the shared hop when a scripted
-- slot sits below it would give 1 here.
_ : ∀ (V : ℕ) → slotHop V insᵛ (F.suc (F.suc zero)) ≡ 2
_ = λ _ → refl

-- ★ the fixpoint on the heterogeneous telescope, by refl and through
-- the assembly.  LOAD-BEARING both.
_ : ∀ (V : ℕ) → slotHop V insᵛ (F.suc (F.suc zero))
              ≡ hopDᵉ V (slotHop V insᵛ) dᵛ2
_ = λ _ → refl

_ : ∀ (V : ℕ) → slotHop V insᵛ (F.suc (F.suc zero))
              ≡ hopDᵉ V (slotHop V insᵛ) dᵛ2
_ = λ V → slotHop-fix V insᵛ (F.suc (F.suc zero)) refl
