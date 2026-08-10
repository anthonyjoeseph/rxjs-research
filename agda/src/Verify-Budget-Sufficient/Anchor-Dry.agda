------------------------------------------------------------------
-- ANCHOR-DRY: the reachability-sourced dry family — now ONE leg.
--
-- 2026-08-10: `chainStep-demand` and `foldPath-demand` (and their dry
-- wrappers) are GONE from this module, replaced by the cascade-level
-- `cascadeGo-burst-dry` (.Burst-Walk) — a REAL DEFINITION over the
-- proven Delivery-Walk instantiated at a two-flavour ledger (caps
-- half level-indexed, Ψ half constant), with ONE frame-local
-- postulate (`stepFrame-burst-face`) behind it.  The tower constant
-- Dm = (2·B + 12) · towerℕ (suc sz) is OFF THE PATH for those two:
-- `capsAt-suc-full` lands the walk's burst directly on Ŝ.  See
-- .Burst-Walk's header for the route, and PROOF-STATE's tier-1 block
-- for the two designs refuted/mis-stated on the way (the constant-Dm
-- walk, machine-refuted; v1's two flawed bridge postulates).
--
-- WHAT REMAINS HERE is the SUBSCRIBE-side leg, which the delivery
-- walk does not cover (subscribeInner is a frame's INTERIOR, not a
-- delivery):
--
--   subscribeInner-demand (POSTULATE): one inner subscription's
--     values are valB?-good at Dm, given INV?/capsOK?-good state,
--     B-bounded inputs, and the occurrence hypothesis
--     pathOccs? sz κ (sz = sizeᵉ e + slotsSize sl; rationale in
--     .Occurrences' header).  Still stated at the tower Dm — this leg
--     keeps the numeric demand model until it too is rebuilt over a
--     walk face: its content is the same family as
--     stepFrame-burst-face's from-inner/thru-outer cases
--     (.Burst-Walk § 2), so whichever is discharged first should
--     absorb the other.
--   supply (PROVEN): Dm ≤ Ŝ = sizeCapAt e sl (suc id), by
--     tick-covers-instant (one caps tick multiplies by ≥ 2^count,
--     count-covers-tower).
--   subscribeInner-dry (DEFINITION): demand widened to Ŝ.
--   dry-hop (DEFINITION): hop-edge's size premise from valB?.
--
-- HARD CONSTRAINT, unchanged: no capᴱ anywhere — the bounds source
-- from capsAt/sizeCapAt, never the ledger receipt (GAP 4;
-- `walk-hyps-absurd` is the machine proof).
--
-- CONSUMER: hypotheses of `dry-tick-core` (.Caps-Bridge), alongside
-- cascadeGo-burst-dry.  Telescope source: subscribeInner thruConsume
-- sites, Evaluator.agda:1109-1196.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Anchor-Dry where

open import Data.Bool    using (Bool; true)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List    using (List; all)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; towerℕ)
open import Rx.Exp  using (Ty; Ctx; Closed; Val; obs; sizeᵛ; sizeᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; Slots; AllOp; NodeId; Path;
         subscribeInner; slotsSize)

-- Wet → Caps → Keeps-Ring → Measures (all public): INV?, ΨAt,
-- sizeCapAt, capsAt, valB?, burstB?, pathB?, eventB?, valB-sz,
-- valsB?-widen, burstB?-widen.
open import Verify-Budget-Sufficient.Wet

-- Named explicitly: Caps-Face and Wet share Measures names.
open import Verify-Budget-Sufficient.Caps-Face using (capsOK?)

open import Verify-Budget-Sufficient.Tick-Headroom
  using (tick-covers-instant)

open import Verify-Budget-Sufficient.Occurrences
  using (pathOccs?)

------------------------------------------------------------------
-- § 1  THE ONE REMAINING DEMAND POSTULATE — the subscribe-side leg.
------------------------------------------------------------------

postulate
  -- PROBED 2026-08-08 (agda/probe/SubInner-Demand-Probe.agda): 20
  -- LOAD-BEARING rows over merge/exhaust programs A/B at
  -- EVALUATOR-REACHED init states — no refutation.  The second valB?
  -- conjunct is FULLY covered; the first only SYMBOLICALLY, via
  -- Dm ≥ 16 (from 2 ≤ sizeCapAt and 1 ≤ towerℕ), because
  -- towerℕ (suc sz) is not an evaluable numeral past sz = 4.
  -- NOT COVERED, and each is a real gap rather than an oversight:
  -- inners with sizeᵛ > 16, the stuck sizeᵛ ≤ᵇ B conjunct of Hyp 3,
  -- and ALL post-step states.  Its two ex-siblings (chainStep-demand,
  -- foldPath-demand) were retired 2026-08-10 for the walk route.
  subscribeInner-demand : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        sz = sizeᵉ e + slotsSize sl
        Dm = (2 * B + 12) * towerℕ (suc sz)
    in INV? Ψ B sched st ≡ true →
       capsOK? (capsAt e sl id) sched st ≡ true →
       valB? B Ψ (obs u) o ≡ true →
       pathB? B Ψ κ ≡ true →
       pathOccs? sz κ ≡ true →
       all (valB? Dm Ψ u)
           (proj₁ (proj₂ (subscribeInner g op allNid κ id now o sched st))) ≡ true

------------------------------------------------------------------
-- § 2  THE DRY LEG — a real definition: demand widened to the
--       anchor Ŝ = sizeCapAt e sl (suc id) by tick-covers-instant.
--       (sizeCapAt e sl (suc id) is definitionally
--       Caps.cSize (capsAt e sl (suc id)), Wet.agda.)
------------------------------------------------------------------

subscribeInner-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      sz = sizeᵉ e + slotsSize sl
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     capsOK? (capsAt e sl id) sched st ≡ true →
     valB? B Ψ (obs u) o ≡ true →
     pathB? B Ψ κ ≡ true →
     pathOccs? sz κ ≡ true →
     all (valB? Ŝ Ψ u)
         (proj₁ (proj₂ (subscribeInner g op allNid κ id now o sched st))) ≡ true
subscribeInner-dry {e = e} {u = u} g op allNid κ id now o sched st hI hC hV hP hPO =
  valsB?-widen {Ψ = ΨAt e (Sched.slots sched)} u
    (proj₁ (proj₂ (subscribeInner g op allNid κ id now o sched st)))
    (tick-covers-instant e (Sched.slots sched) id)
    (subscribeInner-demand g op allNid κ id now o sched st hI hC hV hP hPO)

------------------------------------------------------------------
-- § 3  THE DISCHARGE LEMMA — closes hop-edge's second premise
--       (`sizeᵛ (obs u) o ≤ Ŝ`, Wet.agda) from valB? at B composed
--       with any B ≤ Ŝ (sizeCapAt-mono at the call site).
------------------------------------------------------------------

dry-hop : ∀ {n} {Γ : Ctx n} {u : Ty} (B Ŝ Ψ : ℕ) (o : Val Γ (obs u)) →
  B ≤ Ŝ →
  valB? B Ψ (obs u) o ≡ true →
  sizeᵛ (obs u) o ≤ Ŝ
dry-hop B Ŝ Ψ o B≤Ŝ h = ≤-trans (valB-sz B Ψ _ o h) B≤Ŝ
