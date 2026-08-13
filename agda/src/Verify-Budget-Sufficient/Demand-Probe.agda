-- Gas-demand measurement: inject gasPad h g0 into subscribeE and find
-- the minimal h* at which each program stops drying.
-- MODULE_ROOT (see scripts/check-wiring.py): not imported by Main, not
-- compiled; checked by `make bug-cache`.  Probe receipts are in the
-- headers of the relevant postulates (cascadeGo-nodry in Burst-Walk §8).
module Verify-Budget-Sufficient.Demand-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Fin  using (Fin; zero)
open import Data.Nat  using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; gasPad)
open import Rx.Exp  using (Ctx; Closed; natᵗ; obs; _×ᵗ_;
                            ofᵉ; scanᵉ;
                            mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                            strmᵗ; fstᵗ; varᵗ; nat̂;
                            μᵉ; deferᵉ; input)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; hasDry;
                                 Slots; Slot; shared; Path; root)

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
