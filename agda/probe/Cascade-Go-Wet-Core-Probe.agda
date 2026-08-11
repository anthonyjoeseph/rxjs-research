-- ROADMAP: tier-0 T0-1 — cascadeGo-wet-core falsity probe.
-- DELETE WHEN: cascadeGo-wet-core is either proved (tier-0 T0-1 DONE) or
--   restated after a refutation.
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".
--
-- Cascade-Go-Wet-Core-Probe.agda  (2026-08-11)
--
-- QUESTION: do the 2-conjunct conclusion of `cascadeGo-wet-core`
-- (Wet.agda:4499) hold for concrete programs by refl?
--
-- THE POSTULATE has 2 leading hypotheses (latch-bounded, finish-bounded),
-- then 6 concrete inputs (a, id, chains, sched, st, INV?, valB?, pathB?)
-- and a 2-conjunct conclusion:
--
--   (1) hasDry (proj₁ r) ≡ false
--   (2) INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
--           (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
--           (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
--
-- THE KEY RISK: the caps face's `j` index handles per-cascade GROWTH
-- (each chain step raises the caps), and cascadeGo-wet-core must mirror
-- this.  The naive per-chainStep fixed-bound decomposition is REFUTED
-- (`caps-frame-boundary-absurd`).  The fold-threaded statement's truth is
-- genuinely open, not merely unproven.
--
-- PROBE STRATEGY: run `cascadeGo` on concrete programs at the empty
-- initial state (n=0, emptyᵉ).  The empty initial state is the key
-- enabler: all INV? conjuncts reduce to `all _ []` or `0 ≤ᵇ _` forms
-- that are `true` definitionally regardless of the abstract `sizeCapAt`.
-- The hasDry conjunct is fully computable for paths that do not call
-- subscribeE (root and map-f paths don't use the budget Gas at all).
--
-- PROGRAMS:
--   emptyᵉ : Closed Γ₀ natᵗ, no slots, Ψ=0, slotsSize=0
--
-- ARRIVALS:
--   a₀: tick=0 ordinal=0 source=0 elemTy=natᵗ payload=0 isLast=false
--   a₁: tick=0 ordinal=0 source=0 elemTy=natᵗ payload=0 isLast=true
--
-- TESTED SHAPES:
--   §1 chains=[]                       — DEGENERATE (identity)
--   §2 chains=[(0,root)], isLast=false — LOAD-BEARING for conjunct 1
--   §3 chains=[(0,root)], isLast=true  — LOAD-BEARING for conjunct 1
--
-- NOT COVERED:
--   from-inner/thru-outer paths: these call subscribeInner/subscribeE
--   which use the budget Gas.  budgetAt contains abstract blowH
--   (Evaluator:898), so the computation is stuck for those paths.
--   INV? at suc id with non-empty nodes/registry: boundedNode B v
--   needs `sizeᵛ t v ≤ᵇ B` where B is abstract (sizeCapAt), so
--   `1 ≤ᵇ abstract` is stuck.  Non-trivial INV? for conjunct 2 is
--   not machine-checkable by refl at any concrete program.
--   The genuinely load-bearing INV? case — where cascadeGo changes
--   nodes or registry — requires from-inner/thru-outer paths and
--   cannot be reached with a refl probe.
--
-- FINDINGS (2026-08-11):
--   All 6 checked rows GREEN by refl.  No refutation found.
--   Conjunct 1 (hasDry) LOAD-BEARING in §2 and §3 — would fail if
--   chainStep emitted close _ dried instead of close _ exhausted,
--   or if hasDry misclassified a delivery event.
--   Conjunct 2 (INV?) DEGENERATE in all tested shapes — the state
--   changes are to the `delivered` field, which no INV? conjunct reads.
--   The abstract sizeCapAt forces all non-trivial size checks to the
--   `0 ≤ᵇ _` form, which holds vacuously.
--
-- PROOF-LYING GUARD applied throughout:
--   (a) VACUOUS ROWS — §1 is explicitly labelled DEGENERATE.
--   (b) LOAD-BEARING labels — §2 and §3 name their failure mode.
--   (c) NOT AN ASSEMBLY READ — this probe runs cascadeGo directly,
--       not cascadeGo-wet-core; the postulate's preconditions are
--       noted but not machine-checked (valB? and pathB? are omitted
--       since they can't be checked by refl at abstract B).
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Cascade-Go-Wet-Core-Probe.agda &&
--   agda -i src -i probe probe/Cascade-Go-Wet-Core-Probe.agda

module Cascade-Go-Wet-Core-Probe where

open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.List    using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Source; Tick)
  renaming (Ordinal to RxOrdinal)
open import Rx.Exp
  using (Ty; Ctx; Closed; Val; natᵗ; emptyᵉ)
open import Rx.Evaluator
  using (Slots; Path; root; cascadeGo; Arrival;
         sched-init; st-init; EvalSt; Sched; RegId;
         hasDry; Stream)
-- Wet → Caps public → Keeps-Ring public → Measures public,
-- so INV?, ΨAt, sizeCapAt all arrive through the re-export chain.
open import Verify-Budget-Sufficient.Wet
  using (INV?; ΨAt; sizeCapAt)

----------------------------------------------------------------------
-- § 0  SETUP — empty context, no-slot program
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

-- Slots Γ₀ = ∀ (i : Fin 0) → ..., which is λ () by absurdity.
ins₀ : Slots Γ₀
ins₀ ()

-- The simplest closed program: the empty observable.
progA : Closed Γ₀ natᵗ
progA = emptyᵉ

-- The initial scheduler: live=[], slots=ins₀, all counters zero.
-- Sched.live sched-init progA ins₀ = concat (tabulate{0} _) = [].
schedA : Sched Γ₀
schedA = sched-init progA ins₀

-- The initial state: registry=[], nodes=[], all counters zero.
stA : EvalSt progA
stA = st-init progA

-- Arrival a₀: isLast=false (source still has more pending values).
-- payload : Val Γ₀ natᵗ = ℕ, so 0 is a valid payload.
a₀ : Arrival Γ₀
a₀ = record
  { tick = 0 ; ordinal = 0 ; source = 0
  ; elemTy = natᵗ ; payload = 0 ; isLast = false }

-- Arrival a₁: isLast=true (source completes with this arrival).
-- Causes chainStep to include close src exhausted in the events list.
a₁ : Arrival Γ₀
a₁ = record
  { tick = 0 ; ordinal = 0 ; source = 0
  ; elemTy = natᵗ ; payload = 0 ; isLast = true }

----------------------------------------------------------------------
-- KNOWN FACTS (not machine-checkable by refl, stated for context):
--
-- ΨAt progA ins₀ = fnCapᵉ emptyᵉ + slotsFnCap ins₀ = 0 + 0 = 0.
-- sizeCapAt progA ins₀ 0 = Caps.cSize (capsAt progA ins₀ 0) — ABSTRACT
--   (through opIterD/sizeCount abstract blocks, Evaluator:727/Caps:368).
-- sizeCapAt progA ins₀ 1 = Caps.cSize (capsAt progA ins₀ 1) — ABSTRACT.
-- 2 ≤ sizeCapAt e sl id by 2≤sizeCapAt, so valB?-precondition holds
--   (sizeᵛ natᵗ 0 = 1 ≤ sizeCapAt progA ins₀ 0), but NOT by refl.
-- pathB? B Ψ root = true definitionally (pathB? root _ _ = true).
-- all (λ rc → pathB? B Ψ (proj₂ rc)) [(0, root)] = true, any B Ψ.
--
-- WHY INV? REDUCES TO true BY refl AT THE EMPTY STATE:
-- All six conjuncts of INV? reduce without knowing sizeCapAt's value:
--   stBounded? B schedA stA = all _ [] ∧ all _ [] = true (live=[], nodes=[])
--   fnCapBounded? 0 schedA stA = all _ [] ∧ all _ [] = true
--   length [] ≤ᵇ B = 0 ≤ᵇ B = true  (left-arg=0, first clause of ≤ᵇ)
--   regsB? B 0 [] = all _ [] = true
--   slotsSize ins₀ ≤ᵇ B = 0 ≤ᵇ B = true  (tabulate{0}=[], sum[]=0)
--   slotsFnCap ins₀ ≤ᵇ 0 = 0 ≤ᵇ 0 = true
-- The 0 ≤ᵇ _ reduction fires on the LEFT argument, so B's opacity is
-- irrelevant.  After cascadeGo on root-only chains, the state's
-- `delivered` list changes but no INV? conjunct reads `delivered`.
-- So INV? at suc id holds by the same reasoning.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- § 1  DEGENERATE — chains = []
--
-- cascadeGo a₀ 0 [] schedA stA = [] , schedA , stA  (identity)
-- hasDry [] = false definitionally.
-- INV? at suc id holds because state is unchanged and empty.
-- FAILURE MODE (why this is DEGENERATE): cascadeGo with empty chains
-- is the identity function — there is nothing to fail.
----------------------------------------------------------------------

r₁ : Stream Γ₀ natᵗ × Sched Γ₀ × EvalSt progA
r₁ = cascadeGo a₀ 0 [] schedA stA

-- DEGENERATE: hasDry [] = false by the first clause of hasDry.
-- Could not fail regardless of the arrival or state.
_ : hasDry (proj₁ r₁) ≡ false
_ = refl

-- DEGENERATE: cascadeGo a₀ 0 [] _ st = st, so this is just
-- INV? 0 (sizeCapAt progA ins₀ 1) schedA stA, which holds by the
-- 0 ≤ᵇ _ argument above.  State is completely unchanged.
_ : INV? (ΨAt progA (Sched.slots (proj₁ (proj₂ r₁))))
         (sizeCapAt progA (Sched.slots (proj₁ (proj₂ r₁))) 1)
         (proj₁ (proj₂ r₁))
         (proj₂ (proj₂ r₁)) ≡ true
_ = refl

----------------------------------------------------------------------
-- § 2  LOAD-BEARING — chains=[(0,root)], isLast=false
--
-- any (_ ≡ᵇ 0) [] = false (cancelled=[] in stA), so chainStep fires.
-- chainStep 0 a₀ root schedA (record stA { delivered = [0] })
--   = foldPath (budgetAt progA ins₀ 0) 0 0 0 0 root [0] [] false _ _
--   = ([value 0] at 0 from 0 as delivery) ∷ []
--     , schedA , record stA { delivered = [0] }
-- (The root clause of foldPath ignores the Gas argument entirely.)
-- cascadeGo on remaining [] = identity.
-- Total: r₂ = ([delivery event] , schedA , record stA{delivered=[0]})
--
-- LOAD-BEARING for conjunct 1: hasDry fails if chainStep emits
-- close _ dried (dryEvent checks for dried specifically).  The root
-- clause of foldPath builds close src exhausted (not dried) when
-- isLast=true, and for isLast=false emits no close at all.  So for
-- any root-path chain, hasDry ≡ false is a real constraint.
--
-- DEGENERATE for conjunct 2: EvalSt.delivered changes but no INV?
-- conjunct reads delivered.  The sched is unchanged.  INV? at suc id
-- holds by the same 0 ≤ᵇ _ argument as §1 — no new nodes, no new
-- registry entries, no live source changes.
----------------------------------------------------------------------

r₂ : Stream Γ₀ natᵗ × Sched Γ₀ × EvalSt progA
r₂ = cascadeGo a₀ 0 ((0 , root) ∷ []) schedA stA

-- LOAD-BEARING: would fail if cascadeGo emitted a close _ dried event
-- (e.g., if gas g0 hit a subscribeInner bound through the path).
-- For path=root, foldPath takes the root clause: no subscribeInner,
-- no dried events.  Failure mode: if close dried somehow appeared in
-- a delivery event from the root clause, this check catches it.
_ : hasDry (proj₁ r₂) ≡ false
_ = refl

-- DEGENERATE: delivered=[0] is the only state change; INV? ignores it.
-- Holds by 0 ≤ᵇ _ and all _ [].
_ : INV? (ΨAt progA (Sched.slots (proj₁ (proj₂ r₂))))
         (sizeCapAt progA (Sched.slots (proj₁ (proj₂ r₂))) 1)
         (proj₁ (proj₂ r₂))
         (proj₂ (proj₂ r₂)) ≡ true
_ = refl

----------------------------------------------------------------------
-- § 3  LOAD-BEARING — chains=[(0,root)], isLast=true
--
-- isLast=true: chainStep includes close src exhausted in evs.
-- foldPath root clause builds:
--   evs ++ map value vals ++ [complete]
--   = [close 0 exhausted] ++ [value 0] ++ [complete]
--
-- dryEvent (close _ dried) = true; dryEvent (close _ exhausted) = false.
-- So hasDry of this delivery event is false — it's exhausted, not dried.
--
-- LOAD-BEARING for conjunct 1: this directly tests the dried/exhausted
-- distinction.  If CloseReason.exhausted and CloseReason.dried were
-- confused (or if dryEvent matched on exhausted too), this would fail.
--
-- DEGENERATE for conjunct 2: same as §2; delivered=[0] is the only
-- state change, INV? ignores it.
----------------------------------------------------------------------

r₃ : Stream Γ₀ natᵗ × Sched Γ₀ × EvalSt progA
r₃ = cascadeGo a₁ 0 ((0 , root) ∷ []) schedA stA

-- LOAD-BEARING: checks that close exhausted ≠ close dried.
-- dryEvent (close _ dried) = true by the first (and only matching)
-- clause of dryEvent.  dryEvent (close _ exhausted) = false by the
-- catch-all.  Failure mode: if dryEvent matched exhausted, this fails.
_ : hasDry (proj₁ r₃) ≡ false
_ = refl

-- DEGENERATE: delivered=[0]; INV? unchanged by the same 0 ≤ᵇ _ argument.
_ : INV? (ΨAt progA (Sched.slots (proj₁ (proj₂ r₃))))
         (sizeCapAt progA (Sched.slots (proj₁ (proj₂ r₃))) 1)
         (proj₁ (proj₂ r₃))
         (proj₂ (proj₂ r₃)) ≡ true
_ = refl

----------------------------------------------------------------------
-- § 4  COVERAGE SUMMARY AND OPEN QUESTIONS
--
-- ROWS CHECKED (6 total):
--   §1: hasDry []            ≡ false  (DEGENERATE — trivial)
--   §1: INV? at suc id       ≡ true   (DEGENERATE — state unchanged)
--   §2: hasDry root isLast=F ≡ false  (LOAD-BEARING — no dried emitted)
--   §2: INV? at suc id       ≡ true   (DEGENERATE — delivered only)
--   §3: hasDry root isLast=T ≡ false  (LOAD-BEARING — exhausted ≠ dried)
--   §3: INV? at suc id       ≡ true   (DEGENERATE — delivered only)
--
-- SHAPES NOT COVERED (machine-checkable limit reached):
--   (a) from-inner and thru-outer paths: these call innerReact/thruWalk
--       which use the Gas argument. budgetAt contains abstract blowH
--       (Evaluator:898), so the computation is stuck.
--   (b) Non-trivial state (non-empty nodes/registry): boundedNode B ns
--       for scan-st needs sizeᵛ t v ≤ᵇ (abstract B), which is 1 ≤ᵇ B
--       and does NOT reduce (requires B to be a concrete numeral).
--   (c) Multi-chain cascades with non-trivial fan-out: not reachable
--       because the interesting fan-out happens through from-inner paths.
--
-- CONCLUSION:
--   No refutation found on tested shapes.
--   The statement appears TRUE on root-path cascades.
--   The hasDry conjunct is confirmed: chainStep on root paths emits only
--   value + exhausted events (dried is never emitted by the evaluator's
--   machine rules — Evaluator:343 states this explicitly).
--   The INV? conjunct is effectively untested for the case where the
--   caps GROW (from-inner path with subscribeE call): that is the case
--   where `suc id` matters versus `id`, and it remains unprobed.
----------------------------------------------------------------------
