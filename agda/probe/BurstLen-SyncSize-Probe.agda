-- BurstLen-SyncSize-Probe.agda  (2026-08-06)
--
-- QUESTION: does burstLen (proj₁ (subscribeE g e κ id now sched st)) ≤ syncSizeᵉ e
-- hold for all programs e?
--
-- Probes by `refl`:
--   § 1 — deferᵉ emptyᵉ: THE REFUTATION (LOAD-BEARING)
--   § 2 — scan₁, scan₂, scan₃ (doubling-scan): holds (LOAD-BEARING)
--
-- TABLE (all rows with source):
--   program          | burstLen | syncSizeᵉ | bound holds?  | row label
--   deferᵉ emptyᵉ   |    2     |     1     |   2 > 1  NO   | LOAD-BEARING
--   scan₁ (k=1)     |    5     |    14     |   5 ≤ 14 YES  | LOAD-BEARING
--   scan₂ (k=2)     |    6     |    15     |   6 ≤ 15 YES  | LOAD-BEARING
--   scan₃ (k=3)     |    7     |    16     |   7 ≤ 16 YES  | LOAD-BEARING
--
-- DEGENERATE rows excluded: emptyᵉ alone has burstLen = 4 (one InstEmit
-- with events [init, close, complete] = 3 events; suc 3 = 4) and
-- syncSizeᵉ emptyᵉ = 1 → also a refutation, same mechanism.
--
-- VERDICT: OUTCOME (b) REFUTATION.
-- deferᵉ emptyᵉ refutes the bound.  STOP, do not repair.
-- Per task: if (b), the three dry postulates in Anchor-Dry-Probe.agda
-- are false as written.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/BurstLen-SyncSize-Probe.agda &&
--   agda -i src -i probe probe/BurstLen-SyncSize-Probe.agda
--
-- IMPORT SAFETY: Evaluator.agda interface is cached (used by Battery-Reached-Sizes).
-- Measures.agda interface is cached at 08:40, source unchanged from HEAD.
-- All heavy modules deserialise, not rechecked.

module BurstLen-SyncSize-Probe where

open import Data.Nat      using (ℕ; zero; suc; _+_)
open import Data.List     using (List; []; _∷_)
open import Data.Vec      using () renaming ([] to []ᵛ)
open import Data.Product  using (proj₁)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Gas; gs; g0)
open import Rx.Exp
  using (Ty; Ctx; obs; natᵗ; _×ᵗ_; Val; Closed; Fn; Tm;
         varᵗ; fstᵗ; nat̂; strmᵗ;
         ofᵉ; emptyᵉ; mergeAllᵉ; scanᵉ; deferᵉ;
         syncSizeᵉ)
open import Rx.Evaluator
  using (Slots; subscribeE; sched-init; st-init; root)
open import Verify-Budget-Sufficient.Measures using (burstLen)

----------------------------------------------------------------------
-- SETUP
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

smallGas : Gas
smallGas = gs (gs (gs g0))

----------------------------------------------------------------------
-- § 1  THE REFUTATION — deferᵉ emptyᵉ
--
-- subscribeE _ (deferᵉ body) _ id now sched st =
--   ((init src ∷ []) at id from src as subscribe) ∷ []
--
-- ONE InstEmit, events = [init src], length = 1.
-- burstLen = suc(length [init src]) = suc 1 = 2.
-- syncSizeᵉ (deferᵉ _) = 1 by definition.
-- 2 > 1  →  REFUTATION.
----------------------------------------------------------------------

deferProg : Closed Γ₀ (obs natᵗ)
deferProg = deferᵉ emptyᵉ

-- LOAD-BEARING: syncSizeᵉ (deferᵉ _) = 1 by definition.
-- Failure mode: would mean syncSizeᵉ ≥ 2, weakening the refutation.
_ : syncSizeᵉ deferProg ≡ 1
_ = refl

-- LOAD-BEARING: subscribeE on deferᵉ emits exactly one InstEmit
-- with events = [init src], so burstLen = suc 1 = 2.
-- Failure mode: evaluator's deferᵉ clause changed structure.
_ : burstLen (proj₁ (subscribeE smallGas deferProg root 0 0
                       (sched-init deferProg ins₀)
                       (st-init deferProg))) ≡ 2
_ = refl    -- REFUTATION: 2 > syncSizeᵉ deferProg = 1

----------------------------------------------------------------------
-- § 2  SCAN PROGRAMS — bound holds but refutation already stands
--
-- The doubling-scan programs from Battery-Reached-Sizes.agda.
-- For scan over k-element source (ofᵉ with k nat̂ values):
--   burstLen = k + 4
--   syncSizeᵉ = k + 13
--   k + 4 ≤ k + 13  (bound holds, gap = 9)
--
-- These rows show the bound is NOT universally false; it holds for
-- scan programs while failing for deferᵉ.
----------------------------------------------------------------------

-- Mirror of Battery-Reached-Sizes.agda step/seed.
step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ emptyᵉ

scan₁ : Closed Γ₀ (obs natᵗ)
scan₁ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ []))

scan₂ : Closed Γ₀ (obs natᵗ)
scan₂ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))

scan₃ : Closed Γ₀ (obs natᵗ)
scan₃ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ []))

-- LOAD-BEARING: syncSizeᵉ scan₁ = 14 (k=1, formula k+13).
-- Failure mode: step/seed syncSize computation changed.
_ : syncSizeᵉ scan₁ ≡ 14
_ = refl

-- LOAD-BEARING: burstLen scan₁ burst = 5 (k=1, formula k+4).
-- pushBurst result: [init, close, value acc₁, complete] = 4 events → suc 4 = 5.
-- Failure mode: pushBurst or oneShotBurst structure changed.
_ : burstLen (proj₁ (subscribeE smallGas scan₁ root 0 0
                       (sched-init scan₁ ins₀)
                       (st-init scan₁))) ≡ 5
_ = refl    -- 5 ≤ 14 = syncSizeᵉ scan₁: bound HOLDS for scan₁

-- LOAD-BEARING: burstLen scan₂ burst = 6 (k=2).
_ : burstLen (proj₁ (subscribeE smallGas scan₂ root 0 0
                       (sched-init scan₂ ins₀)
                       (st-init scan₂))) ≡ 6
_ = refl    -- 6 ≤ 15 = syncSizeᵉ scan₂: bound HOLDS for scan₂

-- LOAD-BEARING: burstLen scan₃ burst = 7 (k=3).
_ : burstLen (proj₁ (subscribeE smallGas scan₃ root 0 0
                       (sched-init scan₃ ins₀)
                       (st-init scan₃))) ≡ 7
_ = refl    -- 7 ≤ 16 = syncSizeᵉ scan₃: bound HOLDS for scan₃

----------------------------------------------------------------------
-- VERDICT: OUTCOME (b) REFUTATION
--
-- The bound `burstLen ≤ syncSizeᵉ e` is FALSE.
-- Concrete witness: deferProg = deferᵉ emptyᵉ.
--   burstLen = 2, syncSizeᵉ = 1, 2 > 1.
--
-- WHY NOT VACUOUS: the burstLen = 2 row is non-trivial — the
-- one InstEmit has events = [init src] (length 1, not 0), so
-- burstLen = suc 1 = 2 rather than 0.  The syncSizeᵉ = 1 row
-- would need to be 2 or more to save the bound; by definition
-- of syncSizeᵉ (deferᵉ _) = 1, it is not.
--
-- SHAPES COVERED:
--   deferᵉ emptyᵉ (refutation), scan with k=1,2,3 source values (bound holds).
-- SHAPES NOT COVERED:
--   μᵉ programs, mapᵉ, takeᵉ, mergeAllᵉ/concatAllᵉ standalone,
--   input i (scripted sources), shared slots.
-- None of these gaps affect the refutation — one counterexample suffices.
--
-- NOTE ON THE THREE DRY POSTULATES (Anchor-Dry-Probe.agda):
-- The task states they "are false as written" on a refutation here.
-- The dry postulates bound values at sizeCapAt (a tower-of-towers),
-- not at syncSizeᵉ.  Whether they are independently true or false
-- is a separate question; the task's instruction is to stop here.
----------------------------------------------------------------------
