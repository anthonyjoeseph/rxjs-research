-- ROADMAP: tier-1 #1/#2 — `chainStep-demand` / `foldPath-demand` (Anchor-Dry.agda:84,99).
-- DELETE WHEN: the three Anchor-Dry demand postulates are discharged (tier-1 #1/#2/#3)  [T1]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- Demand-Coverage-Probe.agda  (2026-08-10)
--
-- QUESTION: what do chainStep-demand (Anchor-Dry:84) and foldPath-demand
-- (Anchor-Dry:99) assert, and which pieces are decidable/provable at
-- concrete programs?
--
-- POSTULATE ANATOMY (shared bound):
--   B  = sizeCapAt e sl id                           abstract
--   Dm = (2 * B + 12) * towerℕ (suc sz)             astronomical
--   Conclusion: burstB? Dm Ψ (proj₁ (chainStep.../foldPath...)) ≡ true
--     burstB? N Ψ str = all (λ em → all (eventB? N Ψ) (InstEmit.events em)) str
--     eventB? N Ψ (value v) = valB? N Ψ u v   -- stuck at abstract N
--     eventB? N Ψ (init/close/handoff/complete) = true  (free)
--
-- THE BOUND IS ASTRONOMICAL.  B ≥ 2 (2≤sizeCapAt), towerℕ n ≥ 1
-- (1≤towerℕ), so Dm ≥ (2·2+12)·1 = 16.  Any output with sizeᵛ ≤ 16
-- gives a DEGENERATE bound row — it could not have failed.
--
-- PROGRAMS:
--   FP-A  foldPath, u = t = natᵗ, path = root, vals = [0], evs = [],
--         fin = false.  Output: [delivery([value 0])].  N_FP = 1.
--   CS-A  chainStep, arr_A = {elemTy = natᵗ, payload = 0, isLast = false}.
--         path = root.  Output: [delivery([value 0])].  N_CS = 1.
--
-- FINDINGS (detailed per section):
--   FULLY COMPUTABLE by refl (initial state, no-slot programs):
--     proj₁ (foldPath g0 0 0 0 0 root [0] [] false sched₀ st₀): § 1.
--     proj₁ (chainStep 0 arr_A root sched₀ st₀): § 3.
--     INV? Ψ B sched₀ st₀ (Hyp 1): vacuous empty-list state.
--     capsOK? (capsAt e ins₀ 0) sched₀ st₀ (Hyp 2): same.
--     pathB? B Ψ root (Hyp 3/4): root case → true by definition.
--     pathOccs? sz root (Hyp 4/5): root case → true by definition.
--     sizeᵛ natᵗ 0 = 1 and fnCapᵛ natᵗ 0 = 0: refl.
--     ΨAt e ins₀ = 0: refl (no-function program).
--   STUCK (abstract B/Dm):
--     all (valB? B Ψ natᵗ) [0]: (1 ≤ᵇ B) stuck; symbolic route (§2): 1 ≤ 2 ≤ B.
--     burstB? Dm Ψ str: (1 ≤ᵇ Dm) stuck; symbolic (§5): 1 ≤ 16 ≤ Dm.
--   HONEST ASSESSMENT:
--     The SIZE BOUND ROW (§5) is DEGENERATE: N = 1 fits under Dm ≥ 16
--     trivially.  The row proves nothing about whether Dm is correctly
--     sized for programs with larger output values.  It tests only the
--     lower bound arithmetic chain.
--     The EVALUATOR COMPUTATION ROWS (§1, §3) are LOAD-BEARING: they
--     verify the actual foldPath/chainStep root-path behavior.
--     The HYPOTHESIS ROWS (§2, §4) are LOAD-BEARING for the computable
--     predicates (INV?, capsOK?, pathB?, pathOccs?); the valB? row is
--     STUCK and discharged symbolically.
--   NOT COVERED:
--     Programs with sizeᵛ > 16 (post-step evolved states; Battery-Obs-Growth
--     shows scan accumulators at k=1,2,3 have sizes 13, 37, 85, but
--     reaching those states requires driving the evaluator past init).
--     Non-root paths (share-sink, f ↠ path'): these call stepFrame and
--     potentially subscribeE — the cases where output can grow above B.
--     The stuck first conjunct of valB? / all(valB?) at abstract B.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Demand-Coverage-Probe.agda &&
--   agda -i src -i probe probe/Demand-Coverage-Probe.agda

module Demand-Coverage-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; *-monoʳ-≤; *-mono-≤; +-monoˡ-≤)
open import Data.List    using (List; []; _∷_)
open import Data.Product using (proj₁)
open import Data.Vec     using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim
  using (Gas; g0; towerℕ; Id; Source;
         _at_from_as_; delivery; value)
open import Rx.Exp
  using (Ty; Ctx; Closed; Val; natᵗ;
         ofᵉ; nat̂; sizeᵉ; sizeᵛ)
open import Rx.Evaluator
  using (Slots; slotsSize; Path; root; Arrival;
         chainStep; foldPath;
         sched-init; st-init; EvalSt; Sched)

-- Wet → Caps → Keeps-Ring → Measures all public.
open import Verify-Budget-Sufficient.Wet
  using (INV?; ΨAt; sizeCapAt; valB?; pathB?; fnCapᵛ;
         2≤sizeCapAt)

open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; capsAt)

open import Verify-Budget-Sufficient.Occurrences
  using (pathOccs?)

open import Verify-Budget-Sufficient.Caps
  using (1≤towerℕ)

----------------------------------------------------------------------
-- § 0  SETUP — empty context, no-slot program
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

-- ofᵉ [nat̂ 0] : Closed Γ₀ natᵗ.
-- sizeᵉ e_base = suc(1 + 1) = 3 (sizeᵗˢ[nat̂ 0] = 1 + 1 = 2).
e_base : Closed Γ₀ natᵗ
e_base = ofᵉ (nat̂ 0 ∷ [])

sched₀ : Sched Γ₀
sched₀ = sched-init e_base ins₀

st₀ : EvalSt e_base
st₀ = st-init e_base

-- Arrival for chainStep-demand.
-- Val Γ₀ natᵗ = ℕ, so payload = 0 : ℕ.
arr_A : Arrival Γ₀
arr_A = record
  { tick = 0 ; ordinal = 0 ; source = 0
  ; elemTy = natᵗ ; payload = 0
  ; isLast = false }

-- Named nat value to avoid inline type annotations.
n₀ : Val Γ₀ natᵗ
n₀ = 0

-- Named root path at natᵗ so {t} can be inferred.
root-nat : Path Γ₀ natᵗ natᵗ
root-nat = root

----------------------------------------------------------------------
-- § 1  FOLDPATH-DEMAND — output computation, path = root
--
-- foldPath root clause (Evaluator.agda:1547):
--   ((evs ++ map value vals ++ (if fin then [complete] else [])) at id
--    from envSrc as delivery) ∷ []  ,  sched  ,  st
--
-- For evs=[], vals=[0:natᵗ], fin=false, id=0, envSrc=0:
--   proj₁ result = ([value 0] at 0 from 0 as delivery) ∷ []
--
-- NOTE: sf = g0 is NOT inspected by the root clause (Evaluator:1547
-- pattern matches on path, not sf), so the Gas argument is irrelevant.
----------------------------------------------------------------------

fp_A : _
fp_A = foldPath {e = e_base}
         g0 0 0 0 0
         root-nat
         (n₀ ∷ []) [] false sched₀ st₀

-- LOAD-BEARING: foldPath root wraps input values as a delivery stream.
-- What would make this fail: root clause changed; ++ not definitionally
-- equal on these concrete lists; if-false reduction changed.
_ : proj₁ fp_A ≡
    ((value n₀ ∷ []) at 0 from 0 as delivery) ∷ []
_ = refl

-- LOAD-BEARING: sizeᵛ of the output value = 1.
-- What would make this fail: sizeᵛ natᵗ formula changed.
_ : sizeᵛ {Γ = Γ₀} natᵗ n₀ ≡ 1
_ = refl

-- LOAD-BEARING: ΨAt (fn-cap bound) = 0 for this no-function program.
-- What would make this fail: fnCapᵉ or slotsFnCap nonzero for ofᵉ/nat̂.
_ : ΨAt e_base ins₀ ≡ 0
_ = refl

-- LOAD-BEARING: fnCapᵛ natᵗ n₀ = 0.
-- What would make this fail: fnCapᵛ counting functions in nat values.
_ : fnCapᵛ {Γ = Γ₀} natᵗ n₀ ≡ 0
_ = refl

----------------------------------------------------------------------
-- § 2  FOLDPATH-DEMAND — hypothesis coverage at FP-A's initial state
--
-- Hypotheses at (e_base, ins₀, id=0, path=root, vals=[0], evs=[], fin=false):
--   Hyp 1: INV? Ψ B sched₀ st₀ ≡ true
--   Hyp 2: capsOK? (capsAt e sl 0) sched₀ st₀ ≡ true
--   Hyp 3: pathB? B Ψ root ≡ true
--   Hyp 4: pathOccs? sz root ≡ true
--   Hyp 5: all (valB? B Ψ natᵗ) [0] ≡ true  ← STUCK (abstract B)
--   Hyp 6: all (eventB? B Ψ) [] ≡ true       ← vacuously true by refl
----------------------------------------------------------------------

-- HYP 1 — LOAD-BEARING: INV? at initial empty state.
-- live=[], nodes=[], registry=[]; zero-case of ≤ᵇ absorbs abstract B/Ψ.
-- What would make this fail: non-empty initial state, or ≤ᵇ not zero-vacuous.
_ : INV? (ΨAt e_base ins₀) (sizeCapAt e_base ins₀ 0) sched₀ st₀ ≡ true
_ = refl

-- HYP 2 — LOAD-BEARING: capsOK? at initial empty state.
-- What would make this fail: capsOK? requiring non-trivial registry/nodes.
_ : capsOK? (capsAt e_base ins₀ 0) sched₀ st₀ ≡ true
_ = refl

-- HYP 3 — LOAD-BEARING: pathB? root = true (first clause of pathB?).
-- What would make this fail: root case no longer unconditionally true.
_ : pathB? (sizeCapAt e_base ins₀ 0) (ΨAt e_base ins₀) root-nat ≡ true
_ = refl

-- HYP 4 — LOAD-BEARING: pathOccs? root = true (first clause of pathOccs?).
-- What would make this fail: root case no longer unconditionally true.
_ : pathOccs? (sizeᵉ e_base + slotsSize ins₀) root-nat ≡ true
_ = refl

-- HYP 5 — STUCK.
-- all (valB? B Ψ natᵗ) [0] = valB? B Ψ natᵗ 0 ∧ true
--   = (sizeᵛ natᵗ 0 ≤ᵇ B) ∧ (fnCapᵛ natᵗ 0 ≤ᵇ Ψ) ∧ true
--   = (1 ≤ᵇ B) ∧ (0 ≤ᵇ 0) ∧ true
-- STUCK: (1 ≤ᵇ B) with B = sizeCapAt abstract (sizeCount sealed at Caps:368).
-- SYMBOLIC ROUTE: 1 ≤ 2 ≤ B.
-- LOAD-BEARING: would fail if 2≤sizeCapAt were incorrect.
hyp5-1≤B : ∀ (id : Id) → 1 ≤ sizeCapAt e_base ins₀ id
hyp5-1≤B id = ≤-trans (s≤s z≤n) (2≤sizeCapAt e_base ins₀ id)

-- HYP 6 — DEGENERATE: all p [] = true by definition (first clause of all).
-- evs = [] so there are no events to check; the bound is untested.

----------------------------------------------------------------------
-- § 3  CHAINSTEP-DEMAND — output computation, path = root
--
-- chainStep {n} {e} id arr path sched st (Evaluator.agda:1592):
--   = foldPath (budgetAt e sl id) n id (arrTick arr) (arrSource arr)
--              path (arrVal arr ∷ [])
--              (if isLast arr then [close(source) exhausted] else [])
--              (isLast arr) sched st
--
-- For arr_A (isLast=false, tick=0, source=0, payload=0), n=0, id=0:
--   = foldPath (budgetAt e_base ins₀ 0) 0 0 0 0 root [0] [] false sched₀ st₀
--   = ([value 0] at 0 from 0 as delivery) ∷ []
--
-- NOTE: budgetAt involves abstract blowH (via capsHgo) but the root clause
-- of foldPath does NOT inspect sf; Agda pattern-matches on `root` without
-- reducing budgetAt.  The refl below confirms this.
----------------------------------------------------------------------

cs_A : _
cs_A = chainStep {e = e_base} 0 arr_A
         root-nat
         sched₀ st₀

-- LOAD-BEARING: chainStep at root with nat arrival = same delivery as foldPath.
-- What would make this fail: chainStep not calling foldPath; n=0 gas affecting
-- root clause; isLast=false not suppressing close event.
_ : proj₁ cs_A ≡
    ((value n₀ ∷ []) at 0 from 0 as delivery) ∷ []
_ = refl

----------------------------------------------------------------------
-- § 4  CHAINSTEP-DEMAND — hypothesis coverage at CS-A's initial state
--
-- Hypotheses: same Hyps 1,2,4,5 as §2 (same state, same root path).
-- Hyp 3 is DIFFERENT: valB? B Ψ (arrTy arr_A) (arrVal arr_A) ≡ true.
-- arrTy arr_A = natᵗ (field), arrVal arr_A = 0 (payload).
-- = valB? B Ψ natᵗ 0 — STUCK (same as §2 Hyp 5, same symbolic route).
--
-- Hyps 1,2,4,5 by refl: IDENTICAL to §2.
----------------------------------------------------------------------

-- HYP 1 — LOAD-BEARING (same as §2).
_ : INV? (ΨAt e_base ins₀) (sizeCapAt e_base ins₀ 0) sched₀ st₀ ≡ true
_ = refl

-- HYP 2 — LOAD-BEARING (same as §2).
_ : capsOK? (capsAt e_base ins₀ 0) sched₀ st₀ ≡ true
_ = refl

-- HYP 4 — LOAD-BEARING: pathB? root = true (same as §2 HYP 3).
_ : pathB? (sizeCapAt e_base ins₀ 0) (ΨAt e_base ins₀) root-nat ≡ true
_ = refl

-- HYP 5 — LOAD-BEARING: pathOccs? root = true (same as §2 HYP 4).
_ : pathOccs? (sizeᵉ e_base + slotsSize ins₀) root-nat ≡ true
_ = refl

-- HYP 3 — STUCK (same structure as §2 Hyp 5 above).
-- arrTy arr_A = natᵗ; arrVal arr_A = 0; same symbolic route applies.

----------------------------------------------------------------------
-- § 5  SYMBOLIC BOUND — Dm ≥ 16, hence N = 1 ≤ Dm
--
-- Route (mirrors SubInner-Demand-Probe §4):
--   B = sizeCapAt e sl id ≥ 2   [2≤sizeCapAt]
--   T = towerℕ (suc sz)  ≥ 1   [1≤towerℕ]
--   16 = (2·2+12)·1 ≤ (2·B+12)·T = Dm
--   N_FP = N_CS = 1 ≤ 16 ≤ Dm.
--
-- COVERAGE ASSESSMENT:
--   Dm-ge-16 is LOAD-BEARING: tests 2≤sizeCapAt, 1≤towerℕ, and the
--   arithmetic chain (*-mono-≤, +-monoˡ-≤, *-monoʳ-≤).
--   N≤Dm is DEGENERATE: 1 ≤ 16 trivially; sizeᵛ = 1 ≪ Dm.
--   These rows say nothing about whether Dm is the right scale for
--   programs with output sizeᵛ > 16.
----------------------------------------------------------------------

-- PROVED: Dm ≥ 16 for any program, slot, instant id.
-- LOAD-BEARING: would fail if any of the four arithmetic lemmas or
-- 2≤sizeCapAt / 1≤towerℕ were incorrect.
Dm-ge-16 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id)
  → 16 ≤ (2 * sizeCapAt e sl id + 12) * towerℕ (suc (sizeᵉ e + slotsSize sl))
Dm-ge-16 e sl id =
  *-mono-≤
    (+-monoˡ-≤ 12 (*-monoʳ-≤ 2 (2≤sizeCapAt e sl id)))
    (1≤towerℕ (suc (sizeᵉ e + slotsSize sl)))

-- DEGENERATE: 1 ≤ Dm follows from Dm ≥ 16.  sizeᵛ natᵗ 0 = 1 ≪ Dm.
N≤Dm : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id)
  → 1 ≤ (2 * sizeCapAt e sl id + 12) * towerℕ (suc (sizeᵉ e + slotsSize sl))
N≤Dm e sl id = ≤-trans (s≤s z≤n) (Dm-ge-16 e sl id)
