-- WF-FOLD PROBE (2026-08-05, v2 / REDO).  Converts the monolithic subscribeE-wf
-- postulate (Verify-Well-Formed.agda:1097) into a real definition that calls the
-- REAL proven lemmas imported from Verify-Well-Formed.
--
-- v1 MISTAKE: re-declared BurstInv and re-postulated the five proven lemmas
-- locally, making it a standalone model rather than a rehearsal of the real wiring.
-- That version proved Agda's termination checker accepts the mirror recursion, but
-- called only the probe's own shadow postulates, wiring ZERO orphans.
--
-- v2 FIX: open import Verify-Well-Formed and call the REAL lemmas.  VWF.agdai is
-- from 23:09, after all V-B-S source modifications (20:05), so it is valid and
-- will deserialise rather than recheck.
--
-- TERMINATION: lexicographic (Gas, Closed Γ u), mirroring subscribeE.
--   · mapᵉ / scanᵉ: fuel unchanged, b decreases structurally.
--   · μᵉ (gs fuel): Gas decreases.
--   · μᵉ g0: dryBurst → hasDry = true → ⊥-elim.
--   · takeᵉ: behind subscribeE-takeᵉ-wf (WITH-ABSTRACTION issue, see below).
--   · varᵉ (): absurd.
--   · all others: leaf postulates.
--
-- WITH-ABSTRACTION NOTE (for takeᵉ):
-- `with evalTm count in ecEq` abstracts evalWith count All.[] throughout the
-- context.  After the | suc k branch, the postulate's expected type normalises to
-- (proj₁ (pushBurst ...)) but nodry's type stays as | evalWith — unification fails.
-- LANDING FIX: where-clause helper taking ec : ℕ and ecEq : evalTm count ≡ ec as
-- separate non-with arguments.  b is structurally smaller than takeᵉ count b.
--
-- REAL LEMMAS CALLED:
--   · oneShotBurst-wf  — CALLED at ofᵉ and emptyᵉ clauses
--   · subscribeE-map-wf  — CALLED at mapᵉ clause
--   · subscribeE-scan-wf — CALLED at scanᵉ clause
--   · subscribeE-take-wf — NOT directly called (takeᵉ postulated for with-abstraction)
--   · initReg-wf         — NOT called (input/defer fully postulated); imported for shape
--
-- SHAPE MISMATCHES FOUND (real types, not shadow types):
--   · subscribeE-map-wf (VWF:1920) does NOT return valsLast?
--     subscribeE-wf conclusion REQUIRES it: map-valsLast-push gap needed.
--   · subscribeE-scan-wf (VWF:2003) does NOT return valsLast?
--     subscribeE-wf conclusion REQUIRES it: scan-valsLast-push gap needed.
--   · BurstInv id sched st S ≠ BurstInv id sched₁ st₁ S at record-type index level
--     (even though EvalSt.registry and Sched.live reduce definitionally):
--     scan-binv-adapt and take-binv-adapt gap postulates needed.
--   · burst-done-false: BurstInv does not carry ProtocolSt.done S ≡ false;
--     needed at ofᵉ / emptyᵉ calls to oneShotBurst-wf.

module Wf-Fold-Probe where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Empty   using (⊥-elim)
open import Data.Fin     using (Fin)
open import Data.List    using (List; []; _∷_; map; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Rx.Prim using (Gas; g0; gs; Id; Tick; Source)
open import Rx.Exp  using (Ctx; Ty; Closed; Val; Fn; Tm; obs; _×ᵗ_; natᵗ;
                           input; ofᵉ; emptyᵉ; mapᵉ; scanᵉ; takeᵉ; μᵉ; varᵉ;
                           deferᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                           unfoldμ; evalTm; _≟ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; Stream; NodeId; NodeState;
                                RegId; Chain; LiveSource; AllOp;
                                lookupNode; scan-st; take-st;
                                subscribeE; hasDry; oneShotBurst;
                                installNode; mintNode;
                                map-f; scan-f; take-f; thru-outer; _↠_;
                                memberSource)
open import Rx.Protocol  using (ProtocolSt; runProtocol; valsLast?; countIn)

-- REAL PROVEN LEMMAS from Verify-Well-Formed.
-- Using `using` clause to avoid pulling all of VWF's internal re-opens into scope.
-- NOTE: subscribeE-wf is NOT listed — VWF's subscribeE-wf is the monolithic
-- postulate we are converting; the probe defines its own function of the same name.
open import Verify-Well-Formed using
  ( BurstInv
  ; oneShotBurst-wf
  ; initReg-wf
  ; subscribeE-map-wf
  ; subscribeE-scan-wf
  ; subscribeE-take-wf
  )

-- ════════════════════════════════════════════════════════════════
-- § 1  RESULT TYPE ALIAS
-- ════════════════════════════════════════════════════════════════

WfResult : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) → Set
WfResult fuel b κ id now sched st S =
  Σ ProtocolSt λ S′ →
    let r = subscribeE fuel b κ id now sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (valsLast? (proj₁ r) ≡ true)

-- ════════════════════════════════════════════════════════════════
-- § 2  GAP POSTULATES
--      All are REAL GAPS against the actual lemma types.
-- ════════════════════════════════════════════════════════════════

postulate
  -- SHARED GAP: BurstInv does not carry done ≡ false (walk-order fact).
  -- Needed by oneShotBurst-wf at ofᵉ / emptyᵉ.
  -- SUSPECT: true only at the right walk position, not from BurstInv alone.
  burst-done-false : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false

  -- mapᵉ GAP 1: hasDry propagates inward through the map push.
  map-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ false

  -- mapᵉ GAP 2: pushBurst map frame preserves valsLast?.
  -- REAL SHAPE MISMATCH: subscribeE-map-wf (VWF:1920) does NOT return valsLast?;
  -- subscribeE-wf's conclusion REQUIRES it.
  map-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ true →
    valsLast? (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ true

  -- scanᵉ GAP 1: hasDry propagates inward through the scan push.
  scan-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                  (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
           ≡ false

  -- scanᵉ GAP 2: fresh scan node (with updated acc) survives subscribeE b.
  scan-nodeP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    let nid = proj₁ (mintNode sched)
        r₀  = subscribeE fuel b (scan-f f nid ↠ κ) id now (proj₂ (mintNode sched))
                (installNode nid (scan-st (evalTm seed)) st)
    in Σ (Val Γ u) λ acc →
         lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (scan-st acc)

  -- scanᵉ GAP 3: pushBurst scan-f preserves valsLast?.
  -- REAL SHAPE MISMATCH: subscribeE-scan-wf (VWF:2003) does NOT return valsLast?;
  -- subscribeE-wf's conclusion REQUIRES it.
  scan-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                     (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
              ≡ true →
    valsLast? (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ true

  -- BurstInv ADAPTATION (scan): mintNode / installNode don't touch registry or
  -- Sched.live, so all four BurstInv fields are preserved at the FIELD TYPE level.
  -- But Agda does NOT fire this at the record-type INDEX level — it compares whole
  -- sched / st objects, not their projections.
  -- Provable inline as: record { live-matches = BurstInv.live-matches binv; ... }
  scan-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    BurstInv id (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st) S

  -- BurstInv ADAPTATION (take): same reason.
  take-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) (k : ℕ) →
    evalTm count ≡ suc k →
    BurstInv id sched st S →
    BurstInv id (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st) S

  -- takeᵉ GAP: fresh take node survives subscribeE b's burst exactly.
  take-nodeP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
    evalTm count ≡ suc k →
    let nid = proj₁ (mintNode sched)
        r₀  = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
                (installNode nid (take-st (suc k)) st)
    in lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (take-st (suc k))

  -- takeᵉ GAP: subscribeE never writes dying.
  take-dyF : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
    evalTm count ≡ suc k →
    let nid = proj₁ (mintNode sched)
        r₀  = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
                (installNode nid (take-st (suc k)) st)
    in ∀ s → memberSource s (EvalSt.dying (proj₂ (proj₂ r₀))) ≡ false

-- ════════════════════════════════════════════════════════════════
-- § 3  PER-CLAUSE POSTULATES FOR BLOCKED CLAUSES
-- ════════════════════════════════════════════════════════════════

postulate
  -- ALL input clauses (hot/cold/shared).
  -- The shared/new subcase recurses on the def stored in the slot (gas-decrement edge).
  subscribeE-input-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (input i) κ id now sched st)) ≡ false →
    WfResult fuel (input i) κ id now sched st S

  -- deferᵉ: init + register, no inner burst at subscribe time.
  subscribeE-defer-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (body : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (deferᵉ body) κ id now sched st)) ≡ false →
    WfResult fuel (deferᵉ body) κ id now sched st S

  -- subscribeAll-wf: lifts a subscribeE-wf for the inner b (routed through a
  -- thru-outer frame) to the outer *All expression.  Real type stated here so
  -- grep finds it.
  subscribeAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (op : AllOp) (initialState : NodeState Γ)
    (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel b (thru-outer op (proj₁ (mintNode sched)) ↠ κ) id now
                              (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) initialState st)))
           ≡ false →
    WfResult fuel b (thru-outer op (proj₁ (mintNode sched)) ↠ κ) id now
             (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) initialState st) S →
    WfResult fuel (mergeAllᵉ b) κ id now sched st S

  subscribeE-mergeAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (mergeAllᵉ b) κ id now sched st)) ≡ false →
    WfResult fuel (mergeAllᵉ b) κ id now sched st S

  subscribeE-concatAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (concatAllᵉ b) κ id now sched st)) ≡ false →
    WfResult fuel (concatAllᵉ b) κ id now sched st S

  subscribeE-switchAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (switchAllᵉ b) κ id now sched st)) ≡ false →
    WfResult fuel (switchAllᵉ b) κ id now sched st S

  subscribeE-exhaustAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (exhaustAllᵉ b) κ id now sched st)) ≡ false →
    WfResult fuel (exhaustAllᵉ b) κ id now sched st S

  -- takeᵉ WHOLE CASE.
  -- WITH-ABSTRACTION NOTE: `with evalTm count in ecEq` abstracts evalWith count
  -- All.[] throughout the context.  After | suc k branch, the postulate's expected
  -- type normalises to (proj₁ (pushBurst ...)) but nodry's type stays as | evalWith
  -- — unification fails.  Entire takeᵉ case must live outside any `with evalTm`.
  -- LANDING FIX: where-clause helper with ec : ℕ and ecEq : evalTm count ≡ ec as
  -- separate non-with arguments; suc case calls subscribeE-wf fuel b (take-f nid ↠ κ).
  -- subscribeE-take-wf (VWF:3060) shape verified to match; recursion termination:
  -- b is a structural subterm of takeᵉ count b.
  subscribeE-takeᵉ-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ false →
    WfResult fuel (takeᵉ count b) κ id now sched st S

-- ════════════════════════════════════════════════════════════════
-- § 4  SMALL HELPER
-- ════════════════════════════════════════════════════════════════

private
  true≢false : ∀ {A : Set} → true ≡ false → A
  true≢false ()

-- ════════════════════════════════════════════════════════════════
-- § 5  subscribeE-wf — THE REAL DEFINITION
--
-- Uses the REAL BurstInv from Verify-Well-Formed (imported above, not re-declared).
-- Calls REAL oneShotBurst-wf, subscribeE-map-wf, subscribeE-scan-wf.
-- Any shape mismatch = a FINDING documented in the header.
-- ════════════════════════════════════════════════════════════════

subscribeE-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  hasDry (proj₁ (subscribeE fuel b κ id now sched st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = subscribeE fuel b κ id now sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (valsLast? (proj₁ r) ≡ true)

-- ── input ────────────────────────────────────────────────────────────────────
subscribeE-wf fuel (input i) κ id now sched st S binv nodry =
  subscribeE-input-wf fuel i κ id now sched st S binv nodry

-- ── ofᵉ: REAL oneShotBurst-wf called here ────────────────────────────────────
-- oneShotBurst-wf returns (S′, run, binv′) with no valsLast?.
-- valsLast? (proj₁ (oneShotBurst vals id sched)) = true by computation (refl).
subscribeE-wf fuel (ofᵉ ts) κ id now sched st S binv nodry =
  let vals = map evalTm ts
      (S′ , run , binv′) = oneShotBurst-wf vals id sched st S binv
                             (burst-done-false id sched st S binv)
  in S′ , run , binv′ , refl

-- ── emptyᵉ: same shape as ofᵉ ────────────────────────────────────────────────
subscribeE-wf fuel emptyᵉ κ id now sched st S binv nodry =
  let (S′ , run , binv′) = oneShotBurst-wf [] id sched st S binv
                             (burst-done-false id sched st S binv)
  in S′ , run , binv′ , refl

-- ── mapᵉ: REAL subscribeE-map-wf called here ─────────────────────────────────
-- Gap: map-valsLast-push bridges inner valsLast? to outer (VWF:1920 has no valsLast?).
subscribeE-wf fuel (mapᵉ f b) κ id now sched st S binv nodry =
  let (S′ , run₀ , binv₀ , vl₀) =
        subscribeE-wf fuel b (map-f f ↠ κ) id now sched st S binv
          (map-nodry-push fuel f b κ id now sched st nodry)
      (S″ , run , binv″) =
        subscribeE-map-wf fuel f b κ id now sched st S binv (S′ , run₀ , binv₀)
  in S″ , run , binv″ , map-valsLast-push fuel f b κ id now sched st vl₀

-- ── takeᵉ: postulated (WITH-ABSTRACTION; see § 3) ────────────────────────────
subscribeE-wf fuel (takeᵉ count b) κ id now sched st S binv nodry =
  subscribeE-takeᵉ-wf fuel count b κ id now sched st S binv nodry

-- ── scanᵉ: REAL subscribeE-scan-wf called here ───────────────────────────────
-- Gap: scan-valsLast-push bridges inner valsLast? to outer (VWF:2003 has no valsLast?).
subscribeE-wf fuel (scanᵉ f seed b) κ id now sched st S binv nodry =
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₁    = installNode nid (scan-st (evalTm seed)) st
      (S′ , run₀ , binv₀ , vl₀) =
        subscribeE-wf fuel b (scan-f f nid ↠ κ) id now sched₁ st₁ S
          (scan-binv-adapt fuel f seed b κ id now sched st S binv)
          (scan-nodry-push fuel f seed b κ id now sched st nodry)
      (S″ , run , binv″) =
        subscribeE-scan-wf fuel f seed b κ id now sched st S binv
          (S′ , run₀ , binv₀ , scan-nodeP fuel f seed b κ id now sched st)
  in S″ , run , binv″ , scan-valsLast-push fuel f seed b κ id now sched st vl₀

-- ── *All ─────────────────────────────────────────────────────────────────────
subscribeE-wf fuel (mergeAllᵉ b)   κ id now sched st S binv nodry =
  subscribeE-mergeAll-wf  fuel b κ id now sched st S binv nodry
subscribeE-wf fuel (concatAllᵉ b)  κ id now sched st S binv nodry =
  subscribeE-concatAll-wf fuel b κ id now sched st S binv nodry
subscribeE-wf fuel (switchAllᵉ b)  κ id now sched st S binv nodry =
  subscribeE-switchAll-wf fuel b κ id now sched st S binv nodry
subscribeE-wf fuel (exhaustAllᵉ b) κ id now sched st S binv nodry =
  subscribeE-exhaustAll-wf fuel b κ id now sched st S binv nodry

-- ── μᵉ g0: dryBurst → hasDry = true → ⊥ ─────────────────────────────────────
subscribeE-wf g0 (μᵉ body) κ id now sched st S binv nodry =
  ⊥-elim (true≢false nodry)

-- ── μᵉ (gs fuel): RECURSIVE CALL, Gas decreases ──────────────────────────────
-- subscribeE (gs fuel) (μᵉ body) κ ... reduces definitionally to
-- subscribeE fuel (unfoldμ body) κ ..., so nodry and output type pass through.
subscribeE-wf (gs fuel) (μᵉ body) κ id now sched st S binv nodry =
  subscribeE-wf fuel (unfoldμ body) κ id now sched st S binv nodry

-- ── varᵉ (): absurd ───────────────────────────────────────────────────────────
subscribeE-wf fuel (varᵉ ()) κ id now sched st S binv nodry

-- ── deferᵉ ───────────────────────────────────────────────────────────────────
subscribeE-wf fuel (deferᵉ body) κ id now sched st S binv nodry =
  subscribeE-defer-wf fuel body κ id now sched st S binv nodry
