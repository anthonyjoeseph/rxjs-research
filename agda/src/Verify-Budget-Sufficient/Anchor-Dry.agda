------------------------------------------------------------------
-- ANCHOR-DRY: the reachability-sourced dry family (Phase 1b step 3).
--
-- Landed from probe/Anchor-Dry-Probe.agda, FACTORED on landing: each
-- dry statement is now a real DEFINITION over a DEMAND postulate plus
-- the proven headroom theorem `tick-covers-instant` (.Tick-Headroom).
-- The factoring localises the anchor's one remaining open surface —
-- the demand model — as three greppable postulates at the explicit
-- numeric form, and makes the whole headroom chain (count-covers-tower
-- and everything under it) consumed in code.
--
--   demand (POSTULATE): one instant's outputs are valB?/burstB?-good
--     at Dm = (2·B + 12) · towerℕ (suc sz), given INV?/capsOK?-good
--     state, B-bounded inputs, AND the new occurrence hypothesis
--     pathOccs? sz path ≡ true (sz = sizeᵉ e + slotsSize sl).
--
--     WHY THE OCCURRENCE HYPOTHESIS (Exp.agda:254-257, 266-270):
--     subΘExp for mapᵉ/scanᵉ pushes the input type into Θloc before
--     descending; subΘTm on varᵗ x leaves it (inj₁) or replaces it
--     with a closed term of occsᵗ = 0 (inj₂).  Without this bound,
--     the demand proof's copy-fanout factor could reach B (growing
--     each tick) rather than staying ≤ sz; pathOccs? sz path pins
--     it to the static program size so the tower formula holds.
--     Consumer of pathOccs? is the caller (Caps-Bridge.agda) via the
--     structural argument that registered functions are subterms of e.
--
--     This is the measured-not-proven content (Battery-Obs-Growth's
--     a′ ≤ 2a + v + 11 recurrence, Battery-Nesting-Escalation's
--     per-instant count tower).
--   supply (PROVEN): Dm ≤ Ŝ = sizeCapAt e sl (suc id), by
--     tick-covers-instant — one caps tick multiplies by ≥ 2^count and
--     the count is tower-sized (count-covers-tower).
--   dry (DEFINITION): demand widened to Ŝ via valsB?/burstB?-widen.
--
-- HARD CONSTRAINT, unchanged from the probe: no capᴱ anywhere — the
-- bounds source from capsAt/sizeCapAt, never the ledger receipt
-- (GAP 4; `walk-hyps-absurd` is the machine proof).
--
-- CONSUMER: threaded as hypotheses of `dry-tick-core` (.Caps-Bridge),
-- supplied at the `dry-tick` assembly — the caps↔wet bridging layer,
-- which is where capsOK?-conditioned facts belong (.Wet deliberately
-- reads nothing from the caps face).
--
-- TELESCOPE SOURCES (evaluator call sites), unchanged:
--   chainStep      Evaluator.agda:1592
--   foldPath       Evaluator.agda:1542
--   subscribeInner thruConsume sites Evaluator.agda:1109-1196
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
  using (Sched; EvalSt; Arrival; Slots; AllOp; NodeId; Path;
         chainStep; foldPath; subscribeInner;
         arrTy; arrVal; slotsSize)

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
-- § 1  THE THREE DEMAND POSTULATES — the anchor's open surface.
------------------------------------------------------------------

postulate
  chainStep-demand : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        sz = sizeᵉ e + slotsSize sl
        Dm = (2 * B + 12) * towerℕ (suc sz)
    in INV? Ψ B sched st ≡ true →
       capsOK? (capsAt e sl id) sched st ≡ true →
       valB? B Ψ (arrTy a) (arrVal a) ≡ true →
       pathB? B Ψ path ≡ true →
       pathOccs? sz path ≡ true →
       burstB? Dm Ψ (proj₁ (chainStep id a path sched st)) ≡ true

  foldPath-demand : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        sz = sizeᵉ e + slotsSize sl
        Dm = (2 * B + 12) * towerℕ (suc sz)
    in INV? Ψ B sched st ≡ true →
       capsOK? (capsAt e sl id) sched st ≡ true →
       pathB? B Ψ path ≡ true →
       pathOccs? sz path ≡ true →
       all (valB? B Ψ u) vals ≡ true →
       all (eventB? B Ψ) evs ≡ true →
       burstB? Dm Ψ (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st)) ≡ true

  -- PROBED 2026-08-08 (agda/probe/SubInner-Demand-Probe.agda): 20
  -- LOAD-BEARING rows over merge/exhaust programs A/B at
  -- EVALUATOR-REACHED init states — no refutation.  The second valB?
  -- conjunct is FULLY covered; the first only SYMBOLICALLY, via
  -- Dm ≥ 16 (from 2 ≤ sizeCapAt and 1 ≤ towerℕ), because
  -- towerℕ (suc sz) is not an evaluable numeral past sz = 4.
  -- NOT COVERED, and each is a real gap rather than an oversight:
  -- inners with sizeᵛ > 16, the stuck sizeᵛ ≤ᵇ B conjunct of Hyp 3,
  -- and ALL post-step states.  Its two siblings above are the
  -- unprobed ones; do not read this receipt as covering them.
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
-- § 2  THE DRY FAMILY — real definitions: demand widened to the
--       anchor Ŝ = sizeCapAt e sl (suc id) by tick-covers-instant.
--       (sizeCapAt e sl (suc id) is definitionally
--       Caps.cSize (capsAt e sl (suc id)), Wet.agda.)
------------------------------------------------------------------

chainStep-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      sz = sizeᵉ e + slotsSize sl
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     capsOK? (capsAt e sl id) sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     pathB? B Ψ path ≡ true →
     pathOccs? sz path ≡ true →
     burstB? Ŝ Ψ (proj₁ (chainStep id a path sched st)) ≡ true
chainStep-dry {e = e} id a path sched st hI hC hV hP hPO =
  burstB?-widen {Ψ = ΨAt e (Sched.slots sched)}
    (proj₁ (chainStep id a path sched st))
    (tick-covers-instant e (Sched.slots sched) id)
    (chainStep-demand id a path sched st hI hC hV hP hPO)

foldPath-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      sz = sizeᵉ e + slotsSize sl
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     capsOK? (capsAt e sl id) sched st ≡ true →
     pathB? B Ψ path ≡ true →
     pathOccs? sz path ≡ true →
     all (valB? B Ψ u) vals ≡ true →
     all (eventB? B Ψ) evs ≡ true →
     burstB? Ŝ Ψ (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st)) ≡ true
foldPath-dry {e = e} sf gas id now envSrc path vals evs fin sched st hI hC hP hPO hV hE =
  burstB?-widen {Ψ = ΨAt e (Sched.slots sched)}
    (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st))
    (tick-covers-instant e (Sched.slots sched) id)
    (foldPath-demand sf gas id now envSrc path vals evs fin sched st hI hC hP hPO hV hE)

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
