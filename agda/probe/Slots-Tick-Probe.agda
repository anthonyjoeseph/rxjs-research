-- Probe for two Caps-Bridge.agda deferrals: B2 (`cReg ≤ cSize` at a
-- level) and S2 (`slots-tick`, the raw `Sched.slots` equality across a
-- cascade).  See PROOF-STATE.md Task #16 and Caps-Bridge.agda's header.
--
-- B2 is a genuine arithmetic fact (not vacuous): the base case holds
-- because cReg₀ = cSize₀ ∸ 1, and the inductive step is `frameStep`'s
-- own per-j increment argument (mirroring `2≤capsAt-size`/
-- `1≤capsAt-reg`'s shape) — the size axis's `S ≤ X` inflation
-- (iterSize-infl) dominates the registration axis's `Rc*S` growth
-- because the size step's `2*S*X` term already outgrows both `X` and
-- `Rc*S` once `S ≥ 1` (always true — `2≤capsAt-size` gives `S ≥ 2`).
--
-- S2's grep-level claim ("no function in the delivery clique ever
-- rewrites `Sched.slots`") turns out to ALREADY BE A PROVEN FACT one
-- layer down, not a new proof this probe owes:
--
--   · `Verify-Budget-Sufficient.Keeps-Ring` carries a `Keeps` invariant
--     (`slotsEq` + connected-shares monotonicity) through the ENTIRE
--     subscribe clique (subscribeE-keeps, subscribeInner-keeps,
--     thruConsume-keeps, thruWalk-keeps, thruWrap-keeps,
--     concatDrain-keeps, innerFinish-keeps, innerReact-keeps,
--     takeDispatch-keeps, switchKill-keeps, stepFrame-keeps,
--     pushBurst-keeps, subscribeAll-keeps, sharedConnect-keeps,
--     sharedSlot-keeps) and extracts `subscribeE-slots` as its
--     corollary (Keeps-Ring.agda:952) — reachable here via the public
--     chain `Wet → Caps → Keeps-Ring`.
--   · `Verify-Budget-Sufficient.Caps-Face` carries the delivery side's
--     analogue by hand — `foldPath-slots` / `dispatchShare-slots` /
--     `shareGo-slots` (Caps-Face.agda:3690-3749), which already
--     consume `stepFrame-keeps` at the one seam (a `f ↠ p` frame step)
--     where the delivery clique re-enters the subscribe clique —
--     reachable here via the public chain
--     `Subscribe-Face → Caps-Face → Delivery-Walk → Caps → Keeps-Ring`.
--   · `Verify-Budget-Sufficient.Measures` carries the two boundary
--     special cases the header promised: `pop-slots` (the schedule
--     pop) and `finish-slots` (`cascadeFinish` — Measures.agda:493,
--     "the finish never touches the slots either (record updates
--     only)").
--
-- What is missing above `foldPath-slots` and `finish-slots` is just
-- `chainStep` and `cascadeGo` — two thin wrappers `cascade` composes
-- them through — so THIS is the entire new proof: two small lemmas
-- and the target itself, built from existing, already-proven facts.
-- No re-derivation of the clique, and NO postulate.
module Slots-Tick-Probe where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤n+m; n≤1+n;
         *-mono-≤; *-monoʳ-≤; +-mono-≤; *-comm; *-distribˡ-+;
         *-identityʳ; +-identityʳ)
open import Data.List    using (List; []; _∷_; any)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)

open import Rx.Prim      using (Id; Tick; close; exhausted)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Rx.Frame-Width using (entryCeil)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; RegId; Path;
                                arrTy; arrVal; arrSource; arrTick; cascade;
                                cascadeGo; cascadeFinish; cascadeLatch;
                                chainStep; chainsOf; foldPath; budgetAt;
                                slotsSize; sizeStep; capsBase)

-- the whole caps recurrence (capsAt / frameStep / frameBlowup / Caps
-- and their existing supply lemmas) plus, via its public chain, the
-- WHOLE subscribe-clique `Keeps` proof and `subscribeE-slots`/
-- `finish-slots`/`pop-slots`
open import Verify-Budget-Sufficient.Wet

-- the delivery side's own slots corollaries (`foldPath-slots`,
-- `dispatchShare-slots`, `shareGo-slots`), reachable via Caps-Face
open import Verify-Budget-Sufficient.Subscribe-Face

------------------------------------------------------------------
-- B2 : Caps.cReg (capsAt e sl id) ≤ Caps.cSize (capsAt e sl id)
------------------------------------------------------------------

-- id = 0 SANITY CHECK, done by inspection as the header promised:
-- capsAt e sl zero = frameBlowup c₀ (capsBase e sl), where
--   c₀ = caps (2 + sizeᵉ e + slotsSize sl) (suc (entryCeil n sl e))
--             (suc (sizeᵉ e + slotsSize sl))
-- so cReg₀ = suc (sizeᵉ e + slotsSize sl) and cSize₀ = 2 + sizeᵉ e +
-- slotsSize sl = suc (suc (sizeᵉ e + slotsSize sl)).  Writing
-- k = sizeᵉ e + slotsSize sl, the claim at the PRE-BLOWUP triple is
-- `suc k ≤ suc (suc k)`, TRUE (not the false-at-zero case the repo's
-- law warns about — the base triple is never (0,0,0); `capsAt`'s zero
-- clause hard-codes a "2 +"/"suc" floor on both fields).
-- `frameStep-reg≤size` below then carries this fact through the
-- blowup's iteration, so the FULL id = 0 case (post-blowup) also holds.

-- THE ARITHMETIC CORE.  One `sizeStep` unfolds to a sum containing
-- `2 * (S * X)`, which already dominates both the registration
-- increment `Rc * S` (via `Rc ≤ S` and `S ≤ X`) and the carried
-- registration count `R` (via `R ≤ X` and `X ≤ S * X` since `S ≥ 1`).
2X≡X+X : ∀ (X : ℕ) → 2 * X ≡ X + X
2X≡X+X X = cong (X +_) (+-identityʳ X)

sizeStep-eqn : ∀ (S X : ℕ) → sizeStep S X ≡ S + (S * X + S * X)
sizeStep-eqn S X =
  begin
    S * suc (2 * X)
  ≡⟨ *-distribˡ-+ S 1 (2 * X) ⟩
    S * 1 + S * (2 * X)
  ≡⟨ cong (_+ S * (2 * X)) (*-identityʳ S) ⟩
    S + S * (2 * X)
  ≡⟨ cong (λ y → S + S * y) (2X≡X+X X) ⟩
    S + S * (X + X)
  ≡⟨ cong (S +_) (*-distribˡ-+ S X X) ⟩
    S + (S * X + S * X)
  ∎
  where open ≡-Reasoning

-- THE PER-j STEP: frameStep's own recurrence carries `cReg ≤ cSize`
-- forward, given only `1 ≤ cSize c` (always available: `capsAt`'s own
-- `2≤capsAt-size` is strictly stronger) and the SAME fact at `c` itself.
frameStep-reg≤size : ∀ (c : Caps) (j : ℕ) → 1 ≤ Caps.cSize c →
  Caps.cReg c ≤ Caps.cSize c →
  Caps.cReg (frameStep j c) ≤ Caps.cSize (frameStep j c)
frameStep-reg≤size c zero hS h =
  subst (λ x → Caps.cReg x ≤ Caps.cSize x) (sym (frameStep-0 c)) h
frameStep-reg≤size c (suc j) hS h = final
  where
  S  = Caps.cSize c
  X  = Caps.cSize (frameStep j c)
  R  = Caps.cReg (frameStep j c)
  Rc = Caps.cReg c

  IH : R ≤ X
  IH = frameStep-reg≤size c j hS h

  S≤X : S ≤ X
  S≤X = iterSize-infl S hS j S

  Rc*S≤S*X : Rc * S ≤ S * X
  Rc*S≤S*X = ≤-trans (*-mono-≤ h ≤-refl) (*-monoʳ-≤ S S≤X)

  step1 : R + Rc * S ≤ X + S * X
  step1 = +-mono-≤ IH Rc*S≤S*X

  X≤S*X : X ≤ S * X
  X≤S*X =
    ≤-trans (≤-reflexive (sym (*-identityʳ X)))
            (≤-trans (*-monoʳ-≤ X hS) (≤-reflexive (*-comm X S)))

  step2 : X + S * X ≤ S * X + S * X
  step2 = +-mono-≤ X≤S*X ≤-refl

  step3 : S * X + S * X ≤ S + (S * X + S * X)
  step3 = m≤n+m (S * X + S * X) S

  chain : R + Rc * S ≤ S + (S * X + S * X)
  chain = ≤-trans step1 (≤-trans step2 step3)

  result : R + Rc * S ≤ sizeStep S X
  result = subst (λ y → R + Rc * S ≤ y) (sym (sizeStep-eqn S X)) chain

  final : Caps.cReg (frameStep (suc j) c) ≤ Caps.cSize (frameStep (suc j) c)
  final = subst₂ _≤_ (frameStep-reg-suc c j) (sym (frameStep-size-suc c j)) result

-- B2 ITSELF, by induction on id, bootstrapped from the base triple's
-- own `cReg₀ ≤ cSize₀` (a `suc k ≤ suc (suc k)` fact) and carried
-- through every subsequent frameBlowup by `frameStep-reg≤size`.
B2-cReg≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Caps.cReg (capsAt e sl id) ≤ Caps.cSize (capsAt e sl id)
B2-cReg≤cSize {n = n} e sl zero =
  frameStep-reg≤size c₀ (sizeCount c₀ (capsBase e sl)) 1≤S₀ hReg₀
  where
  c₀ = caps (2 + sizeᵉ e + slotsSize sl) (suc (entryCeil n sl e))
            (suc (sizeᵉ e + slotsSize sl))
  1≤S₀ : 1 ≤ Caps.cSize c₀
  1≤S₀ = ≤-trans (s≤s z≤n) (s≤s (s≤s z≤n))
  hReg₀ : Caps.cReg c₀ ≤ Caps.cSize c₀
  hReg₀ = s≤s (n≤1+n (sizeᵉ e + slotsSize sl))
B2-cReg≤cSize e sl (suc id) =
  frameStep-reg≤size (capsAt e sl id) (sizeCount (capsAt e sl id) (capsH e sl id))
                     (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))
                     (B2-cReg≤cSize e sl id)

------------------------------------------------------------------
-- S2 : slots-tick — the raw Sched.slots equality across a cascade.
--
-- The whole delivery clique's slots-preservation is already proven
-- (see the header): `foldPath-slots` (Caps-Face.agda) covers
-- everything below `chainStep`, and `finish-slots` (Measures.agda)
-- covers `cascadeFinish`.  `chainStep` and `cascadeGo` are thin
-- wrappers with no case split of their own that touches `Sched`
-- (chainStep is one call into foldPath; cascadeGo's only branch is
-- "cancelled, skip" vs "deliver via chainStep, recurse"), so both
-- lemmas below are direct compositions, and `cascade`'s own two-step
-- shape (`cascadeGo` then `cascadeFinish`) makes `slots-tick` one more.
------------------------------------------------------------------

chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st))) ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st

cascadeGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))) ≡ Sched.slots sched₀
cascadeGo-slots a id [] sched₀ st₀ = refl
cascadeGo-slots a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true = cascadeGo-slots a id chains sched₀ st₀
... | false =
      let (emits , sched₁ , st₁) =
            chainStep id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      in trans (cascadeGo-slots a id chains sched₁ st₁)
               (chainStep-slots id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }))

-- THE TARGET, S2's exact signature from Caps-Bridge.agda.
slots-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascade a id sched st))) ≡ Sched.slots sched
slots-tick a id sched st =
  let (emits , sched′ , st′) = cascadeGo a id (chainsOf a st) sched (cascadeLatch a st)
  in trans (finish-slots a sched′ st′)
           (cascadeGo-slots a id (chainsOf a st) sched (cascadeLatch a st))
