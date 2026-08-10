-- ROADMAP: TIER 2 — the five live VWF push postulates (VWF.agda:1119-1163).
-- DELETE WHEN: the five VWF push postulates are discharged  [T5]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- BATTERY: VWF propagation postulates (Verify-Well-Formed.agda:1105-1174)
-- Task 0f: probe all six gap postulates with concrete refl checks and
-- supply the inline proof for scan-binv-adapt.
--
-- IMPORT STRATEGY: Rx.Evaluator, Rx.Protocol, Rx.Exp, Rx.Prim only.
-- Verify-Well-Formed is NOT imported — its .agdai depends on the
-- currently-modified Verify-Budget-Sufficient.* modules via Caps-Bridge.
-- BurstInv, countRegs, sameTy, liveTypeOK?, regTyped? are copied locally
-- with the same bodies as VWF.agda so the inline proof can typecheck.
--
-- FINDINGS (see each section):
--
--  map-nodry-push    (:1115) PROBED-TRUE.  Both outer (mapᵉ) and inner
--    (map-f path) subscribeE return hasDry = false at the concrete test.
--    The implication is non-vacuous: the hypothesis case is also false.
--
--  map-valsLast-push (:1124) PROBED-TRUE.  valsLast? = true on both
--    inner and outer at the concrete test.  SHAPE NOTE: the postulate
--    bridges a real gap — subscribeE-map-wf's conclusion omits valsLast?.
--
--  scan-nodry-push   (:1131) PROBED-TRUE.  Same as map case; both outer
--    (scanᵉ) and inner (scan-f path) return hasDry = false.
--
--  scan-nodeP        (:1141) PROBED-TRUE.  After subscribeE on ofᵉ [5],
--    the scan node survives unchanged at (scan-st (evalTm seed)).
--
--  scan-valsLast-push(:1154) PROBED-TRUE.  valsLast? = true on both
--    inner and outer.  Same shape note as map-valsLast-push.
--
--  scan-binv-adapt   (:1168) INLINE PROOF SUPPLIED.  The comment in
--    VWF.agda is correct: the record { field = BurstInv.field binv }
--    pattern typechecks by Agda's eta-reduction on record projections:
--      EvalSt.registry (installNode nid ns st) = EvalSt.registry st
--      Sched.live (proj₂ (mintNode sched))     = Sched.live sched
--    Both verified by refl below.  The inline proof is §4 in this file.

module Battery-VWF-Prop where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin     using (Fin)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; _≡ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Rx.Prim using (Id; Tick; Source; Gas; g0; gs;
                            InstEmit; InstEvent; _at_from_as_;
                            value; init; close; handoff; complete;
                            EmitKind; subscribe; delivery; plumbing;
                            CloseReason; exhausted; dried)
open import Rx.Exp  using (Ty; Ctx; Val; Closed; Fn; obs;
                            applyFn; evalTm;
                            mapᵉ; scanᵉ; ofᵉ;
                            Tm; natᵗ; _×ᵗ_; _≟ᵗ_; nat̂)
open import Rx.Evaluator using (
  NodeId; NodeState; EvalSt; Sched;
  Path; Chain; Frame; Stream;
  LiveSource; RegId;
  lookupNode; setNode;
  subscribeE; register; installNode; mintNode;
  root; _↠_; map-f; scan-f;
  sched-init; st-init;
  scan-st; hasDry; dryEvent)
open import Rx.Protocol using (ProtocolSt; Owed; countIn; valsLast?; hasValue)
-- Ctx n = Vec Ty n.  Vec.[] is the empty-Ctx constructor,
-- distinct from Data.List.[] which is also named [].
-- import (not open) to keep qualified access only.
import Data.Vec as Vec

----------------------------------------------------------------------
-- § 1  LOCAL COPIES OF VWF.agda PREDICATES
----------------------------------------------------------------------
-- Copied verbatim from Verify-Well-Formed.agda:130-134 and :460-474.
-- Needed to define the local BurstInv without importing VWF.

countRegs : ∀ {n} {Γ : Ctx n} {t}
          → Source → List (RegId × Source × Chain Γ t) → ℕ
countRegs s [] = zero
countRegs s ((_ , x , _) ∷ r) =
  if s ≡ᵇ x then suc (countRegs s r) else countRegs s r

sameTy : Ty → Ty → Bool
sameTy s u with s ≟ᵗ u
... | yes _ = true
... | no  _ = false

liveTypeOK? : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveTypeOK? s u []       = true
liveTypeOK? s u (l ∷ ls) =
  (if LiveSource.source l ≡ᵇ s then sameTy u (LiveSource.elemTy l) else true)
    ∧ liveTypeOK? s u ls

regTyped? : ∀ {n} {Γ : Ctx n} {t}
          → List (RegId × Source × Chain Γ t)
          → List (LiveSource Γ) → Bool
regTyped? []                      live = true
regTyped? ((_ , s , (u , _)) ∷ r) live = liveTypeOK? s u live ∧ regTyped? r live

----------------------------------------------------------------------
-- § 2  LOCAL BurstInv RECORD
----------------------------------------------------------------------
-- Copied from Verify-Well-Formed.agda:758-767.
-- Only the four proof-carrying fields; the NB comments are omitted.

record BurstInv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                (id : Id) (sched : Sched Γ) (st : EvalSt e)
                (S : ProtocolSt) : Set where
  field
    live-matches  : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    reg-typed     : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low   : ProtocolSt.horizon S ≤ id
    current-frame : (ProtocolSt.current S ≡ nothing)
                  ⊎ (ProtocolSt.current S ≡ just (id , []))

----------------------------------------------------------------------
-- § 3  ETA-REDUCTION FACTS (the mechanism behind scan-binv-adapt)
----------------------------------------------------------------------
-- installNode only mutates EvalSt.nodes; registry is unchanged.
-- mintNode   only mutates Sched.nextNode;  live    is unchanged.
-- Both hold by definitional equality — no rewrite needed.

registry-installNode-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (ns : NodeState Γ) (st : EvalSt e) →
  EvalSt.registry (installNode nid ns st) ≡ EvalSt.registry st
registry-installNode-eq nid ns st = refl

sched-live-mintNode-eq : ∀ {n} {Γ : Ctx n}
  (sched : Sched Γ) →
  Sched.live (proj₂ (mintNode sched)) ≡ Sched.live sched
sched-live-mintNode-eq sched = refl

----------------------------------------------------------------------
-- § 4  INLINE PROOF OF scan-binv-adapt (VWF.agda:1168)
----------------------------------------------------------------------
-- The proof is the inline record term the comment already describes.
-- It typechecks because the BurstInv field types reduce via § 3's
-- two eta equalities: Agda's definitional equality handles record
-- projections on record constructors without explicit rewrites.
--
-- This proof is for the LOCAL BurstInv above, but the body is
-- IDENTICAL to what belongs in the src/ postulate once it is replaced
-- by a real definition — the types are the same up to the module the
-- record is declared in.

scan-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
  (b : Closed Γ s) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  BurstInv id (proj₂ (mintNode sched))
             (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st) S
scan-binv-adapt fuel f seed b κ id now sched st S binv = record
  { live-matches  = BurstInv.live-matches binv
  ; reg-typed     = BurstInv.reg-typed binv
  ; horizon-low   = BurstInv.horizon-low binv
  ; current-frame = BurstInv.current-frame binv
  }

-- More general version (same proof body, any nid / node state):
scan-binv-adapt-gen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  ∀ (nid : NodeId) (ns : NodeState Γ) →
  BurstInv id (proj₂ (mintNode sched)) (installNode nid ns st) S
scan-binv-adapt-gen id sched st S binv nid ns = record
  { live-matches  = BurstInv.live-matches binv
  ; reg-typed     = BurstInv.reg-typed binv
  ; horizon-low   = BurstInv.horizon-low binv
  ; current-frame = BurstInv.current-frame binv
  }

----------------------------------------------------------------------
-- § 5  CONCRETE HELPERS — map test program
----------------------------------------------------------------------
-- mapᵉ (nat̂ 42) (ofᵉ [5]) : Closed [] natᵗ
-- Function nat̂ 42 maps every input to 42 (constant function).
-- sched₀ᵐ / st₀ᵐ are indexed by the outer mapᵉ expression.

private
  -- Type annotations use Vec.[] (Data.Vec.[]) as Ctx 0 to disambiguate
  -- from Data.List.[] which Agda would otherwise resolve for [].
  e-map    : Closed Vec.[] natᵗ
  e-map    = mapᵉ (nat̂ 42) (ofᵉ (nat̂ 5 ∷ []))

  sched₀ᵐ : Sched Vec.[]
  sched₀ᵐ = sched-init e-map (λ ())

  st₀ᵐ    : EvalSt e-map
  st₀ᵐ    = st-init e-map

  -- ofᵉ [5] used as the inner expression b in the scan subscribeE call.
  e-scan   : Closed Vec.[] natᵗ
  e-scan   = ofᵉ (nat̂ 5 ∷ [])

  sched₀ˢ : Sched Vec.[]
  sched₀ˢ = sched-init e-scan (λ ())

  st₀ˢ    : EvalSt e-scan
  st₀ˢ    = st-init e-scan

----------------------------------------------------------------------
-- § 6  hasDry CHECKS (map-nodry-push : VWF.agda:1115,
--                     scan-nodry-push : VWF.agda:1131)
----------------------------------------------------------------------
-- Postulate direction for map-nodry-push:
--   hasDry (outer: subscribeE (mapᵉ f b)) = false
--   → hasDry (inner: subscribeE b (map-f f ↠ κ)) = false
-- Both sides are false at the concrete test, so the implication is
-- satisfied and non-vacuous (the antecedent is independently false).

-- OUTER (mapᵉ): the pushed burst has close exhausted, not dried.
map-outer-nodry : hasDry (proj₁ (subscribeE (gs g0) e-map root 0 0 sched₀ᵐ st₀ᵐ))
               ≡ false
map-outer-nodry = refl

-- INNER (b with map-f path): ofᵉ returns the raw burst, close exhausted.
map-inner-nodry : hasDry (proj₁ (subscribeE (gs g0)
                   (ofᵉ (nat̂ 5 ∷ []))
                   (map-f (nat̂ 42) ↠ root) 0 0 sched₀ᵐ st₀ᵐ))
               ≡ false
map-inner-nodry = refl

-- Postulate direction for scan-nodry-push:
--   hasDry (outer: subscribeE (scanᵉ f seed b)) = false
--   → hasDry (inner: subscribeE b (scan-f f nid ↠ κ)) = false
--
-- For the inner call, use a fresh nid and an installNode-extended st:

private
  nid-test : NodeId
  nid-test = proj₁ (mintNode sched₀ˢ)

  sched₁ˢ  : Sched Vec.[]
  sched₁ˢ  = proj₂ (mintNode sched₀ˢ)

  st₁ˢ     : EvalSt e-scan
  -- Use 0 directly (Val Vec.[] natᵗ = ℕ by reduction; avoids
  -- evalTm (nat̂ 0) meta on nat̂'s Δᵍ/Δ/Θ context lists).
  st₁ˢ     = installNode nid-test (scan-st 0) st₀ˢ

  -- OUTER scan test: expression indexed by scanᵉ, not just ofᵉ
  e-scan-outer : Closed (Vec.[]) natᵗ
  e-scan-outer = scanᵉ (nat̂ 7) (nat̂ 0) (ofᵉ (nat̂ 5 ∷ []))
  sched₀ˢᵒ    : Sched (Vec.[])
  sched₀ˢᵒ    = sched-init e-scan-outer (λ ())
  st₀ˢᵒ       : EvalSt e-scan-outer
  st₀ˢᵒ       = st-init e-scan-outer

scan-inner-nodry : hasDry (proj₁ (subscribeE (gs g0) e-scan
                   (scan-f (nat̂ 7) nid-test ↠ root) 0 0 sched₁ˢ st₁ˢ))
               ≡ false
scan-inner-nodry = refl

-- OUTER scan (subscribeE on the full scanᵉ expression):
scan-outer-nodry :
  hasDry (proj₁ (subscribeE (gs g0) e-scan-outer root 0 0 sched₀ˢᵒ st₀ˢᵒ))
  ≡ false
scan-outer-nodry = refl

----------------------------------------------------------------------
-- § 7  valsLast? CHECKS (map-valsLast-push : :1124,
--                         scan-valsLast-push : :1154)
----------------------------------------------------------------------
-- Postulate direction for map-valsLast-push:
--   valsLast? inner = true → valsLast? outer = true
-- Both are true (single emit = trivially valsLast?).

map-inner-valsLast : valsLast? (proj₁ (subscribeE (gs g0)
                      (ofᵉ (nat̂ 5 ∷ []))
                      (map-f (nat̂ 42) ↠ root) 0 0 sched₀ᵐ st₀ᵐ))
                  ≡ true
map-inner-valsLast = refl

map-outer-valsLast : valsLast? (proj₁ (subscribeE (gs g0) e-map root 0 0 sched₀ᵐ st₀ᵐ))
                  ≡ true
map-outer-valsLast = refl

-- SHAPE NOTE: map-valsLast-push is a REAL gap, not a duplicate.
-- subscribeE-map-wf (~VWF.agda:2173) is proven without valsLast? in
-- its conclusion.  The postulate bridges from the INNER wf result
-- (which the induction hypothesis gives) to the OUTER.  These refl
-- checks confirm the statement is non-vacuous and locally correct.

scan-inner-valsLast : valsLast? (proj₁ (subscribeE (gs g0) e-scan
                       (scan-f (nat̂ 7) nid-test ↠ root) 0 0 sched₁ˢ st₁ˢ))
                   ≡ true
scan-inner-valsLast = refl

scan-outer-valsLast :
  valsLast? (proj₁ (subscribeE (gs g0) e-scan-outer root 0 0 sched₀ˢᵒ st₀ˢᵒ))
  ≡ true
scan-outer-valsLast = refl

----------------------------------------------------------------------
-- § 8  scan-nodeP CHECK (VWF.agda:1141)
----------------------------------------------------------------------
-- After subscribeE on ofᵉ [5] with a scan-f path, the scan node
-- survives at the seed value.  (ofᵉ ignores its path argument and
-- returns state unchanged, so the node is at acc = evalTm seed = 0.)

scan-nodeP-check :
  let r₀ = subscribeE (gs g0) e-scan
              (scan-f (nat̂ 7) nid-test ↠ root)
              0 0 sched₁ˢ st₁ˢ
  in lookupNode nid-test (EvalSt.nodes (proj₂ (proj₂ r₀)))
   ≡ just (scan-st 0)
scan-nodeP-check = refl

-- Stated as an existential to match the postulate's shape:
scan-nodeP-exists :
  let r₀ = subscribeE (gs g0) e-scan
              (scan-f (nat̂ 7) nid-test ↠ root)
              0 0 sched₁ˢ st₁ˢ
  in Σ ℕ λ acc →       -- Val [] natᵗ = ℕ; avoids Vec/List [] ambiguity
       lookupNode nid-test (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (scan-st acc)
scan-nodeP-exists = 0 , refl

----------------------------------------------------------------------
-- § 9  SHAPE MISMATCH NOTE (map/scan-valsLast-push)
----------------------------------------------------------------------
-- Both map-valsLast-push and scan-valsLast-push are CORRECTLY stated
-- as implications (inner true → outer true).  They are not duplicate
-- postulates — subscribeE-map-wf and subscribeE-scan-wf are proven
-- obligations that OMIT valsLast? from their conclusions, and
-- subscribeE-wf REQUIRES it.  These two postulates are the correct
-- bridge statements that fill the gap at the assembly level.
--
-- Evidence: the refl checks in §7 confirm the statement is satisfied
-- (and non-vacuous) for the concrete test program.  No shape change
-- is needed; the postulates are correctly stated.
