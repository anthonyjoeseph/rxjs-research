-- ROADMAP: tier-1 #1 — `subscribeE-walk-core` falsity probe.
-- DELETE WHEN: `subscribeE-walk-core` is discharged (tier-1 #1)  [T1]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- Walk-Core-Probe.agda  (2026-08-11)
--
-- QUESTION: do the 9 conclusion conjuncts of `subscribeE-walk-core`
-- (Measures.agda:5728) hold for concrete programs with a witness E′ = E?
--
-- THE POSTULATE has 4 global hypotheses (walk-hyps-splitAnchor,
-- walk-hyps-round3b, spendᴱ-compose, ΩAt equation) plus a concrete
-- precondition block (3 ≤ E, INV?, sizeᵉ ≤ capᴱ, fnCapᵉ ≤ Ψ,
-- pathB?, widthOK?, ofWᵉ b ≤ Ω, pathΩ?, dBound ≤ G, g hasAtLeast,
-- pathLen + G ≤ ℓ, regsLen?) and a 9-conjunct conclusion:
--
--   (1) E ≤ E′
--   (2) E′ ≤ E * 3^(suc Ψ * walkCap Ω ℓ G)    [ceiling]
--   (3) INV? Ψ (capᴱ W E′) sched₁ st₁
--   (4) burstB? (capᴱ W E′) Ψ burst
--   (5) burstHopD? F (hopDᵉ F b) burst
--   (6) hasDry burst ≡ false
--   (7) mintCount sched₁ st₁ ≤ mintCount sched st + walkCap Ω ℓ G
--   (8) burstLen burst ≤ walkCap Ω ℓ G
--   (9) regsLen? ℓ (EvalSt.registry st₁)
--
-- PROBE STRATEGY: evaluate subscribeE at the two simplest programs
-- (emptyᵉ and ofᵉ [nat̂ 0]) from the initial state, claim E′ = E = 3,
-- and check each conjunct by direct computation (refl or ≤ᵇ refl).
-- Conjunct 2 (E′ ≤ ceiling) holds analytically (3 ≤ 3 * 3^N for N ≥ 0)
-- and is OMITTED from the refl sweep to avoid normalising large exponents.
--
-- PROGRAMS:
--   A  progA = emptyᵉ           G=1 ℓ=1 Ω=0 Ψ=0 W=0 F=0 Ŝ=0 R̂=0 E=3
--   B  progB = ofᵉ [nat̂ 0]    G=2 ℓ=2 Ω=0 Ψ=0 W=0 F=0 Ŝ=0 R̂=0 E=3
--
-- KEY VALUES:
--   capᴱ 0 3 = (2+0)^3 = 2^3 = 8
--   walkCap 0 1 1 = (3*2)^(3^1) = 6^3 = 216
--   walkCap 0 2 2 = (3*3)^(3^2) = 9^9 = 387420489
--   For A: mintCount delta = 1; burstLen = 4; registry = []
--   For B: mintCount delta = 1; burstLen = 5; registry = []
--
-- FINDINGS (2026-08-11):
--   Conjuncts 1, 3–9: ALL GREEN by refl on both programs.
--   Conjunct 2: holds analytically (not machine-checked to avoid 3^N).
--   No refutation found.
--   NOTE: burstB?/burstHopD?/burstLen need {n=0}{Γ=Γ₀}{u=natᵗ} explicit
--   because Val is a defined function, not a constructor, so Agda cannot
--   invert Val Γ u ~ Val Γ₀ natᵗ to solve {n},{Γ},{u} automatically.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Walk-Core-Probe.agda &&
--   agda -i src -i probe probe/Walk-Core-Probe.agda

module Walk-Core-Probe where

open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List    using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; Id)
open import Rx.Exp
  using (Ty; Ctx; Closed; Val; natᵗ; emptyᵉ; ofᵉ; nat̂)
open import Rx.Evaluator
  using (Slots; Path; root; subscribeE; sched-init; st-init; EvalSt; Sched;
         hasDry; Stream)

-- Wet opens Caps public → Keeps-Ring public → Measures public,
-- so INV?, capᴱ, walkCap, dBound, mintCount, burstLen, burstB?,
-- burstHopD?, regsLen? all arrive via the Measures chain.
-- hasDry comes from Rx.Evaluator directly (Wet's Evaluator import is
-- not `public`, so hasDry is not re-exported through Wet).
open import Verify-Budget-Sufficient.Wet
  using (INV?; capᴱ; walkCap; dBound; mintCount; burstLen;
         burstB?; burstHopD?; regsLen?)

----------------------------------------------------------------------
-- § 0  SETUP — empty context, no-slot programs
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

-- Program A: the empty observable.
progA : Closed Γ₀ natᵗ
progA = emptyᵉ

-- Program B: emit a single nat.
progB : Closed Γ₀ natᵗ
progB = ofᵉ (nat̂ 0 ∷ [])

-- The initial scheduler (empty context: n=0, so nextOrdinal=nextSource=0,
-- no live hot sources, no nodes) and initial state (all fields zero/empty).
schedA : Sched Γ₀
schedA = sched-init progA ins₀

stA : EvalSt progA
stA = st-init progA

----------------------------------------------------------------------
-- § 1  PROGRAM A — emptyᵉ
--
-- subscribeE (gs (gs g0)) emptyᵉ root 0 0 schedA stA
--   ↝ oneShotBurst [] 0 schedA
--   = ( [(init 0 ∷ close 0 exhausted ∷ complete ∷ []) at 0 from 0 as subscribe]
--     , record schedA { nextSource = 1 }   -- only nextSource bumped
--     , stA )                               -- st unchanged
--
-- Parameters: Ψ=0 W=0 Ω=0 ℓ=1 F=0 Ŝ=0 R̂=0 G=1 E=3 E′=3.
--
-- Hypothesis check (all trivial at the initial state):
--   3 ≤ E=3                                               ✓
--   INV? 0 8 schedA stA        (all empty → true)         ✓
--   sizeᵉ emptyᵉ ≤ 8                                      ✓ (sizeᵉ=1)
--   fnCapᵉ emptyᵉ ≤ 0                                     ✓ (fnCapᵉ=0)
--   pathB? 8 0 root            ≡ true                     ✓ (root case)
--   widthOK? 0 schedA stA      ≡ true                     ✓ (all empty)
--   ofWᵉ emptyᵉ ≤ Ω=0                                     ✓ (0 ≤ 0)
--   pathΩ? 0 root              ≡ true                     ✓ (root case)
--   dBound 0 0 0 0 1 = 1 ≤ G=1                            ✓
--   gs(gs g0) hasAtLeast suc 1 = hasAtLeast 2              ✓ (hs(hs hz))
--   pathLen root + 1 = 1 ≤ ℓ=1                            ✓
--   regsLen? 1 []              ≡ true                     ✓
----------------------------------------------------------------------

rA : Stream Γ₀ natᵗ × Sched Γ₀ × EvalSt progA
rA = subscribeE (gs (gs g0)) progA root 0 0 schedA stA

-- CONJUNCT 1: E ≤ E′.  Trivial since E′ = E = 3.
-- DEGENERATE: always true with the E′=E witness.
_ : 3 ≤ 3
_ = ≤-refl

-- CONJUNCT 2 (ceiling): 3 ≤ 3 * 3^(1 * walkCap 0 1 1).
-- walkCap 0 1 1 = 6^3 = 216, so this is 3 ≤ 3 * 3^216.
-- Holds analytically (3 = 3 * 1 ≤ 3 * 3^216) and is NOT machine-checked
-- here to avoid normalising 3^216 during kernel evaluation.

-- CONJUNCT 3: INV? preserved at E′ = capᴱ 0 3 = 8.
-- proj₁(proj₂ rA) has live=[] (nextSource bumped only); proj₂(proj₂ rA)=stA
-- has registry=[], nodes=[]; ins₀ contributes slotsSize=slotsFnCap=0
-- (n=0, Data.List.tabulate {0} _ = []).
-- All six INV? conjuncts reduce to (all _ []) = true by computation.
-- LOAD-BEARING: fails if mintSource bumps a field other than nextSource,
-- or if INV? gains a conjunct that does not hold on the empty state.
_ : INV? 0 (capᴱ 0 3) (proj₁ (proj₂ rA)) (proj₂ (proj₂ rA)) ≡ true
_ = refl

-- CONJUNCT 4: burstB? — events are init/close/complete, no value events.
-- eventB? returns true for all structural events unconditionally.
-- LOAD-BEARING: fails if oneShotBurst emits a value event for emptyᵉ.
_ : burstB? {n = 0} {Γ = Γ₀} {u = natᵗ} (capᴱ 0 3) 0 (proj₁ rA) ≡ true
_ = refl

-- CONJUNCT 5: burstHopD? — all events are structural, hopDev? = true.
-- LOAD-BEARING: fails if emptyᵉ emits a value event with hopD > 0.
_ : burstHopD? {n = 0} {Γ = Γ₀} {u = natᵗ} 0 0 (proj₁ rA) ≡ true
_ = refl

-- CONJUNCT 6: hasDry — close 0 exhausted carries CloseReason exhausted,
-- NOT dried.  dryEvent (close _ exhausted) = false.
-- LOAD-BEARING: fails if oneShotBurst substitutes dried for exhausted.
_ : hasDry (proj₁ rA) ≡ false
_ = refl

-- CONJUNCT 7: mintCount delta.
-- mintCount (proj₁(proj₂ rA)) (proj₂(proj₂ rA)) = 0+1+0+0 = 1
--   (only nextSource was bumped by mintSource).
-- mintCount schedA stA = 0+0+0+0 = 0.
-- walkCap 0 1 1 = 6^3 = 216.  1 ≤ᵇ 0+216 = true.
-- LOAD-BEARING: fails if mintSource bumps ordinal/node/reg counters.
_ : (mintCount (proj₁ (proj₂ rA)) (proj₂ (proj₂ rA))
     ≤ᵇ mintCount schedA stA + walkCap 0 1 1) ≡ true
_ = refl

-- CONJUNCT 8: burstLen ≤ walkCap 0 1 1 = 216.
-- burstLen = suc(|[init 0, close 0 exhausted, complete]|) = suc 3 = 4.
-- 4 ≤ᵇ 216 = true.
-- LOAD-BEARING: fails if oneShotBurst emits more events than expected.
_ : (burstLen {n = 0} {Γ = Γ₀} {u = natᵗ} (proj₁ rA) ≤ᵇ walkCap 0 1 1) ≡ true
_ = refl

-- CONJUNCT 9: regsLen? at ℓ=1.  registry = [] (emptyᵉ never registers).
-- LOAD-BEARING: fails if subscribeE registers a chain for emptyᵉ.
_ : regsLen? 1 (EvalSt.registry (proj₂ (proj₂ rA))) ≡ true
_ = refl

----------------------------------------------------------------------
-- § 2  PROGRAM B — ofᵉ [nat̂ 0]
--
-- subscribeE (gs(gs(gs g0))) (ofᵉ [nat̂ 0]) root 0 0 schedA stA
--   ↝ oneShotBurst [0] 0 schedA   (map evalTm [nat̂ 0] = [0])
--   = ( [(init 0 ∷ value 0 ∷ close 0 exhausted ∷ complete ∷ []) at 0 from 0 as subscribe]
--     , record schedA { nextSource = 1 }
--     , stA )
--
-- Parameters: Ψ=0 W=0 Ω=0 ℓ=2 F=0 Ŝ=0 R̂=0 G=2 E=3 E′=3.
--   syncSizeᵉ progB = suc(syncSizeᵗˢ [nat̂ 0]) = suc 1 = 2
--   dBound 0 0 0 0 2 = 2 + suc 0 * (0 + suc 0 * 0) = 2 ≤ G=2        ✓
--   gs(gs(gs g0)) hasAtLeast suc 2 = hasAtLeast 3                      ✓
--   pathLen root + G = 0 + 2 = 2 ≤ ℓ=2                                ✓
--   walkCap 0 2 2 = (3*3)^(3^2) = 9^9 = 387420489
--   burstLen = suc(|[init,value,close,complete]|) = suc 4 = 5
--
-- Note: stA : EvalSt progA is reused here; subscribeE's e-parameter
-- is phantom in all the fields we check (the state is empty throughout).
----------------------------------------------------------------------

rB : Stream Γ₀ natᵗ × Sched Γ₀ × EvalSt progA
rB = subscribeE (gs (gs (gs g0))) progB root 0 0 schedA stA

-- CONJUNCT 1B: trivial.
-- DEGENERATE: same as A.
_ : 3 ≤ 3
_ = ≤-refl

-- CONJUNCT 2B (ceiling): 3 ≤ 3 * 3^(1 * walkCap 0 2 2).
-- Holds analytically; not machine-checked.

-- CONJUNCT 3B: INV? preserved.  proj₁(proj₂ rB) has the same structure
-- as sched₁A (only nextSource=1); proj₂(proj₂ rB)=stA.
-- LOAD-BEARING: fails if ofᵉ/oneShotBurst changes the scheduler differently
-- from emptyᵉ, or if INV? does not hold on the updated state.
_ : INV? 0 (capᴱ 0 3) (proj₁ (proj₂ rB)) (proj₂ (proj₂ rB)) ≡ true
_ = refl

-- CONJUNCT 4B: burstB? — value 0 : Val Γ₀ natᵗ has
-- sizeᵛ natᵗ 0 = 1 ≤ capᴱ 0 3 = 8, fnCapᵛ natᵗ 0 = 0 ≤ 0.
-- eventB? 8 0 (value 0) = (1 ≤ᵇ 8) ∧ (0 ≤ᵇ 0) = true.
-- LOAD-BEARING: fails if nat values have sizeᵛ > 8 or fnCapᵛ > 0.
_ : burstB? {n = 0} {Γ = Γ₀} {u = natᵗ} (capᴱ 0 3) 0 (proj₁ rB) ≡ true
_ = refl

-- CONJUNCT 5B: burstHopD? — value 0 : Val Γ₀ natᵗ has
-- hopDᵛ 0 natᵗ 0 = 0 ≤ 0.
-- LOAD-BEARING: fails if nat values carry hop depth.
_ : burstHopD? {n = 0} {Γ = Γ₀} {u = natᵗ} 0 0 (proj₁ rB) ≡ true
_ = refl

-- CONJUNCT 6B: hasDry — close 0 exhausted is not dried.
-- DEGENERATE: same reasoning as progA; always true for one-shot bursts.
_ : hasDry (proj₁ rB) ≡ false
_ = refl

-- CONJUNCT 7B: mintCount delta ≤ walkCap 0 2 2 = 387420489.
-- mintCount (proj₁(proj₂ rB)) (proj₂(proj₂ rB)) = 0+1+0+0 = 1.
-- 1 ≤ᵇ 0 + 387420489 = true.
-- LOAD-BEARING: fails if the ofᵉ path mints additional counters.
_ : (mintCount (proj₁ (proj₂ rB)) (proj₂ (proj₂ rB))
     ≤ᵇ mintCount schedA stA + walkCap 0 2 2) ≡ true
_ = refl

-- CONJUNCT 8B: burstLen ≤ walkCap 0 2 2 = 387420489.
-- burstLen = suc(|[init 0, value 0, close 0 exhausted, complete]|) = suc 4 = 5.
-- 5 ≤ᵇ 387420489 = true.
-- LOAD-BEARING: fails if oneShotBurst emits more events than expected.
_ : (burstLen {n = 0} {Γ = Γ₀} {u = natᵗ} (proj₁ rB) ≤ᵇ walkCap 0 2 2) ≡ true
_ = refl

-- CONJUNCT 9B: regsLen? at ℓ=2.  registry = [] (ofᵉ never registers).
-- LOAD-BEARING: fails if subscribeE registers a chain for ofᵉ.
_ : regsLen? 2 (EvalSt.registry (proj₂ (proj₂ rB))) ≡ true
_ = refl
