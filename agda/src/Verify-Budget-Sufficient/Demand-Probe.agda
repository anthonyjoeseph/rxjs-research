-- Gas-demand measurement: inject gasPad h g0 into subscribeE and find
-- the minimal h* at which each program stops drying.
-- MODULE_ROOT (see scripts/check-wiring.py): not imported by Main, not
-- compiled; checked by `make bug-cache`.  Probe receipts are in the
-- headers of the relevant postulates (cascadeGo-nodry in Burst-Walk).
module Verify-Budget-Sufficient.Demand-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Fin  using (Fin; zero)
open import Data.Nat  using (ℕ; suc; _+_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; gasPad)
open import Rx.Exp  using (Ctx; Closed; natᵗ; obs; _×ᵗ_;
                            ofᵉ; scanᵉ;
                            mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                            strmᵗ; fstᵗ; varᵗ; nat̂;
                            μᵉ; deferᵉ; input;
                            sizeᵉ; syncSizeᵉ; Tm; Fn)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; hasDry;
                                 Slots; Slot; shared; Path; root; EvalSt)
open import Rx.Hop-Depth using (hopDᵉ)
open import Verify-Budget-Sufficient.Measures using (dBound; regsLen?)

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
_ : hopDᵉ 5 prog-P-c ≡ 1
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
_ : hopDᵉ 5 prog-P-a ≡ 244
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
_ : hopDᵉ 5 prog-P-b ≡ 244
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
sucG b = suc (syncSizeᵉ b + hopDᵉ 0 b)

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
