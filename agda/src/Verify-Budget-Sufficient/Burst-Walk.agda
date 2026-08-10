------------------------------------------------------------------
-- BURST-WALK: the two-flavour burst ledger over the Delivery-Walk —
-- tier-1 #1/#2's content, landed at Ŝ with no tower constant.
--
-- Landed from probe/Caps-Burst-Walk-Probe.agda (2026-08-10), which
-- was v2 of the route: v1's two bridging postulates were BOTH
-- mis-stated (one concluded fnCap facts from hypotheses carrying no
-- fnCap information; one lacked the plen/gas guards that keep its
-- arithmetic true), and v0 — demand ledgers CONSTANT in the walk
-- level — was MACHINE-REFUTED (a duplicating map-f doubles sizeᵛ, so
-- no fixed bound survives one frame; receipt in PROOF-STATE's tier-1
-- block, 2026-08-10).
--
-- THE DESIGN, in one paragraph.  `valB? B Ψ`'s two conjuncts have
-- OPPOSITE characters: the SIZE half grows per frame and must ride
-- the walk's caps level (`valsCaps? (frameStep J c) sl`), while the
-- FNCAP half is frame-invariant ("Ψ never grows — caseW is
-- substitution-invariant", .Measures) and rides CONSTANT.  The walk
-- carries the conjunction; `Res.burst` returns both flavours; § 4
-- recombines them pointwise into `burstB? (cSize c′) Ψ` — a real
-- proof.  Stating the receipt at the CASCADE level (walk entered at
-- J = 0) makes the landing-level bound the exact arithmetic
-- `cascadeGo-caps` (.Caps-Face:4901) already proves, cribbed term for
-- term; then `capsAt-suc-full` (.Caps:893, refl) lands the widened
-- caps half on `capsAt e sl (suc id)`, whose cSize IS the dry target
-- Ŝ = sizeCapAt e sl (suc id).  Dm = (2·B + 12) · towerℕ (suc sz)
-- appears NOWHERE — the anchor's content is no longer a second,
-- measured-not-proven numeric model, but the same "landing level fits
-- sizeCount" obligation the caps machinery exists to prove.
--
-- WHAT REPLACED WHAT.  `cascadeGo-burst-dry` (§ 7) replaces BOTH
-- `chainStep-demand` and `foldPath-demand` (ex-.Anchor-Dry § 1) and
-- their dry wrappers: the per-chain/per-fold granularity those carried
-- came from the original demand decomposition, but their one consumer
-- (`dry-tick-core`, .Caps-Bridge) drives the whole CASCADE, and at
-- cascade level the receipt is strictly cheaper (no per-fold level
-- arithmetic at nonzero walk base).  If the eventual dry-tick grind
-- turns out to need per-chain receipts mid-cascade, they come from
-- re-entering this same walk at the mid-cascade level — the cost that
-- reappears then is the nonzero-base level bound, and the design note
-- for it is v1's `fold-level-fits` REPAIRED with `suc plen ≤ S` and a
-- gas guard (PROOF-STATE, tier-1 update).
--
-- THE ONE OPEN POSTULATE is `stepFrame-burst-face` (§ 2).  Its
-- walkOK/valsCaps?/pathSz?/level conjuncts ARE `FrameFace`
-- (.Caps-Face:4655) — the PROVEN `stepFrame-face` — at the same
-- witness.  Genuinely new: the emitted-EVENTS caps half (FrameFace
-- bounds output VALUES only), and the Ψ halves — the wet face of one
-- frame, whose from-inner/thru-outer content is the same family as
-- `subscribeInner-demand` (.Anchor-Dry).
--
-- Also home to frameBΨ?/pathBΨ?/regsBΨ?, RELOCATED from .Caps-Bridge
-- (they were defined there, downstream of this module's consumers).
------------------------------------------------------------------
module Verify-Budget-Sufficient.Burst-Walk where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _≤ᵇ_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ)
open import Data.List    using (List; []; _∷_; _++_; all; map; length)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent;
                           value; init; close; handoff; complete;
                           InstEmit)
open import Rx.Exp  using (Ty; Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; Slots; Arrival; RegId; Chain; Path; Frame;
         _↠_; root; share-sink;
         map-f; scan-f; take-f; from-inner; thru-outer; Stream;
         stepFrame; cascadeGo; dropSource; shareLatch; shareFinish; slotsSize;
         arrTy; arrVal; fLvlD; regAt)

-- re-exports .Caps (frameStep, capsAt, sizeCount, the mono kit) and
-- .Deliveries (delivN) public
open import Verify-Budget-Sufficient.Delivery-Walk
  using (Walk-Hyps; module Walk; regP?; chP?; Caps; frameStep; delivN;
         capsAt; capsH; sizeCount; cDel; cDel-body; sizeCount-body;
         lvls-mono; dWalkᶜ-mono; capsAt-suc-full;
         2≤capsAt-size; 1≤capsAt-reg;
         ∧-intro; ∧-true; all-++-intro)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthCascade)

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; walkOK; walkOK-finish; slotsCaps?;
         valCaps?; valsCaps?; eventCaps?; burstCaps?;
         eventsCaps?-widen; burstCaps?-widen; valsCaps?-lvl;
         pathSz?-len; pathSz?-tail; pathSz?-widen;
         capsOK?-count; capsOK?-delivered; capsOK?-regs; shareLatch-caps;
         frameStep-mono-j; frameStep-0)

open import Verify-Budget-Sufficient.Wet
  using (burstB?; eventB?; valB?; sizeCapAt; ΨAt;
         fnCapBounded?; fcB-live; fcB-nodes; sweepLive-fnCap;
         fnCapᵛ; caseWᵗ; fnCapᵗ)

------------------------------------------------------------------
-- § 0  THE Ψ LEDGER — the fnCap halves of valB?/eventB?/burstB? and
-- frameB?, split out so they can ride the walk CONSTANT while the
-- size halves ride the level.  frameBΨ?/pathBΨ?/regsBΨ? RELOCATE here
-- from Caps-Bridge on landing (Caps-Bridge:215-229; it sits
-- downstream of this module's consumers, so they must move up).
------------------------------------------------------------------

valΨ? : ∀ {n} {Γ : Ctx n} → ℕ → (u : Ty) → Val Γ u → Bool
valΨ? Ψ u v = fnCapᵛ u v ≤ᵇ Ψ

valsΨ? : ∀ {n} {Γ : Ctx n} {s} → ℕ → List (Val Γ s) → Bool
valsΨ? {s = s} Ψ = all (valΨ? Ψ s)

eventΨ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → InstEvent (Val Γ u) → Bool
eventΨ? {u = u} Ψ (value v) = valΨ? Ψ u v
eventΨ? Ψ (init _)    = true
eventΨ? Ψ (close _ _) = true
eventΨ? Ψ (handoff _) = true
eventΨ? Ψ complete    = true

eventsΨ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → List (InstEvent (Val Γ u)) → Bool
eventsΨ? Ψ = all (eventΨ? Ψ)

burstΨ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → Stream Γ u → Bool
burstΨ? Ψ = all (λ em → all (eventΨ? Ψ) (InstEmit.events em))

frameBΨ? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameBΨ? Ψ (map-f fn)         = (caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ
frameBΨ? Ψ (scan-f fn _)      = (caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ
frameBΨ? Ψ (take-f _)         = true
frameBΨ? Ψ (from-inner _ _ _) = true
frameBΨ? Ψ (thru-outer _ _)   = true

pathBΨ? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathBΨ? Ψ root           = true
pathBΨ? Ψ (share-sink i) = true
pathBΨ? Ψ (f ↠ p)        = frameBΨ? Ψ f ∧ pathBΨ? Ψ p

regsBΨ? : ∀ {n} {Γ : Ctx n} {t} → ℕ
        → List (RegId × Source × Chain Γ t) → Bool
regsBΨ? Ψ = all (λ en → pathBΨ? Ψ (proj₂ (proj₂ (proj₂ en))))

------------------------------------------------------------------
-- § 1  THE TWO-FLAVOUR LEDGERS, named once so the face postulate and
-- the Walk-Hyps instantiation are definitionally the same predicates.
------------------------------------------------------------------

-- VbB sits OUTSIDE the t-anonymous-module: it never mentions t, and an
-- unmentioned module implicit is an unsolvable meta at every use site
VbB : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → ℕ → ℕ → ∀ {s} → List (Val Γ s) → Bool
VbB c sl Ψ J vs = valsCaps? (frameStep J c) sl vs ∧ valsΨ? Ψ vs

module _ {n} {Γ : Ctx n} {t : Ty} where

  PbB : Caps → ℕ → ℕ → ∀ {u} → Path Γ u t → Bool
  PbB c Ψ J p = pathSz? (Caps.cSize (frameStep J c)) p ∧ pathBΨ? Ψ p

  EbB : Caps → Slots Γ → ℕ → ℕ → List (InstEvent (Val Γ t)) → Bool
  EbB c sl Ψ J es = all (eventCaps? (frameStep J c) sl) es ∧ eventsΨ? Ψ es

  BbB : Caps → Slots Γ → ℕ → ℕ → Stream Γ t → Bool
  BbB c sl Ψ J str = burstCaps? (frameStep J c) sl str ∧ burstΨ? Ψ str

OKB : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Caps → Slots Γ → ℕ → ℕ → Sched Γ → EvalSt e → Set
OKB c sl Ψ J sched st =
  walkOK c sl J sched st × (fnCapBounded? Ψ sched st ≡ true)

------------------------------------------------------------------
-- § 2  THE ONE OPEN OBLIGATION: one frame preserves both flavours.
--
-- The walkOK / valsCaps? / pathSz? / level conjuncts ARE `FrameFace`
-- (Caps-Face:4655) at the same witness — the PROVEN `stepFrame-face`.
-- Genuinely new content: the emitted-EVENTS caps half (FrameFace
-- bounds output VALUES, `proj₁ r`, and says nothing about
-- `proj₁ (proj₂ r)`), and the Ψ halves — the wet face of one frame.
-- Its map-f case is `fnCapᵛ (applyFn fn v) ≤ Ψ` from
-- `frameBΨ?`'s `caseWᵗ ⊔ fnCapᵗ ≤ Ψ` (substitution-invariance);
-- its from-inner/thru-outer cases are the same family as
-- `subscribeInner-demand` (.Anchor-Dry).
--
-- CALL-SITE ARGUMENTS THIS ABSORBS: none yet.
------------------------------------------------------------------

postulate
  stepFrame-burst-face : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
    2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    ∀ (J : ℕ) {s u} (sf : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    PbB c Ψ J (f ↠ path′) ≡ true →
    VbB c sl Ψ J vals ≡ true →
    regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
    depthFrame sf id now f path′ vals fin sched st ≤ d →
    let r  = stepFrame sf id now f path′ vals fin sched st
        s′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
        t′ = proj₂ (proj₂ (proj₂ (proj₂ r)))
    in Σ ℕ λ j′ → (J + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) d J)
      × OKB {e = e} c sl Ψ (J + j′) s′ t′
      × (VbB c sl Ψ (J + j′) (proj₁ r) ≡ true)
      × (regP? (PbB c Ψ (J + j′)) (EvalSt.registry t′) ≡ true)
      × (EbB c sl Ψ (J + j′) (proj₁ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- § 3  THE Ψ-STATE FACTS the walk's OK closure needs — all REAL.
-- consᵈ and shareLatch touch only delivered/completedSources/dying,
-- fields fnCapBounded? never reads, so those two are transparent.
-- shareFinish sweeps live and filters the registry: sweepLive-fnCap
-- (Wet:514) is exactly the live half, and nodes ride through.
------------------------------------------------------------------

fnCapB-latch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ : ℕ) (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  fnCapBounded? Ψ sched st ≡ true →
  fnCapBounded? Ψ sched (shareLatch i fin st) ≡ true
fnCapB-latch Ψ i false sched st h = h
fnCapB-latch Ψ i true  sched st h = h

fnCapB-finish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ : ℕ) (i : Fin n) (fin : Bool)
  (out : Stream Γ t × Sched Γ × EvalSt e) →
  fnCapBounded? Ψ (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) ≡ true →
  fnCapBounded? Ψ (proj₁ (proj₂ (shareFinish i fin out)))
                  (proj₂ (proj₂ (shareFinish i fin out))) ≡ true
fnCapB-finish Ψ i false out h = h
fnCapB-finish Ψ i true  out h =
  ∧-intro
    (sweepLive-fnCap Ψ
      (dropSource (toℕ i) (EvalSt.registry (proj₂ (proj₂ out))))
      (Sched.live (proj₁ (proj₂ out)))
      (fcB-live Ψ (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) h))
    (fcB-nodes Ψ (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) h)

------------------------------------------------------------------
-- § 4  RECOMBINATION — the two flavours ARE `burstB? (cSize c′) Ψ`,
-- pointwise, a REAL PROOF.  This replaces v1's false bridge: the Ψ
-- information comes from the walk's own Ψ ledger, not from thin air.
------------------------------------------------------------------

eventB?-halves : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
  (ev : InstEvent (Val Γ u)) →
  eventCaps? c′ sl ev ≡ true → eventΨ? Ψ ev ≡ true →
  eventB? (Caps.cSize c′) Ψ ev ≡ true
eventB?-halves c′ sl Ψ (value v) hc hp = ∧-intro (proj₁ (∧-true _ _ hc)) hp
eventB?-halves c′ sl Ψ (init _)    _ _ = refl
eventB?-halves c′ sl Ψ (close _ _) _ _ = refl
eventB?-halves c′ sl Ψ (handoff _) _ _ = refl
eventB?-halves c′ sl Ψ complete    _ _ = refl

eventsB?-halves : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
  (es : List (InstEvent (Val Γ u))) →
  all (eventCaps? c′ sl) es ≡ true → eventsΨ? Ψ es ≡ true →
  all (eventB? (Caps.cSize c′) Ψ) es ≡ true
eventsB?-halves c′ sl Ψ []       _  _  = refl
eventsB?-halves c′ sl Ψ (e ∷ es) hc hp =
  ∧-intro (eventB?-halves c′ sl Ψ e (proj₁ (∧-true _ _ hc)) (proj₁ (∧-true _ _ hp)))
          (eventsB?-halves c′ sl Ψ es (proj₂ (∧-true _ _ hc)) (proj₂ (∧-true _ _ hp)))

burstB?-halves : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
  (str : Stream Γ u) →
  burstCaps? c′ sl str ≡ true → burstΨ? Ψ str ≡ true →
  burstB? (Caps.cSize c′) Ψ str ≡ true
burstB?-halves c′ sl Ψ []         _  _  = refl
burstB?-halves c′ sl Ψ (em ∷ ems) hc hp =
  ∧-intro (eventsB?-halves c′ sl Ψ (InstEmit.events em)
            (proj₁ (∧-true _ _ hc)) (proj₁ (∧-true _ _ hp)))
          (burstB?-halves c′ sl Ψ ems (proj₂ (∧-true _ _ hc)) (proj₂ (∧-true _ _ hp)))

------------------------------------------------------------------
-- § 5  THE LEDGER GLUE — pointwise conjunctions over the registry and
-- chain lists, so the caller supplies the two flavours separately.
------------------------------------------------------------------

regP?-∧ : ∀ {n} {Γ : Ctx n} {t} (P Q : ∀ {u} → Path Γ u t → Bool)
  (rs : List (RegId × Source × Chain Γ t)) →
  regP? P rs ≡ true → regP? Q rs ≡ true →
  regP? (λ {v} p → P {v} p ∧ Q p) rs ≡ true
regP?-∧ P Q []       h₁ h₂ = refl
regP?-∧ P Q (r ∷ rs) h₁ h₂
  with ∧-true (P (proj₂ (proj₂ (proj₂ r)))) (regP? P rs) h₁
     | ∧-true (Q (proj₂ (proj₂ (proj₂ r)))) (regP? Q rs) h₂
... | a₁ , b₁ | a₂ , b₂ = ∧-intro (∧-intro a₁ a₂) (regP?-∧ P Q rs b₁ b₂)

chP?-∧ : ∀ {n} {Γ : Ctx n} {s t} (P Q : ∀ {u} → Path Γ u t → Bool)
  (ps : List (RegId × Path Γ s t)) →
  chP? P ps ≡ true → chP? Q ps ≡ true →
  chP? (λ {v} p → P {v} p ∧ Q p) ps ≡ true
chP?-∧ P Q []       h₁ h₂ = refl
chP?-∧ P Q (r ∷ rs) h₁ h₂
  with ∧-true (P (proj₂ r)) (chP? P rs) h₁
     | ∧-true (Q (proj₂ r)) (chP? Q rs) h₂
... | a₁ , b₁ | a₂ , b₂ = ∧-intro (∧-intro a₁ a₂) (chP?-∧ P Q rs b₁ b₂)

------------------------------------------------------------------
-- § 6  THE INSTANTIATION — every closure fact a real proof.
------------------------------------------------------------------

module BurstWalk
  {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ d : ℕ)
  (2≤S : 2 ≤ Caps.cSize c) (1≤R : 1 ≤ Caps.cReg c)
  (slC : slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true)
  (slSz : slotsSize sl ≤ Caps.cSize c)
  where

  S = Caps.cSize c
  W = Caps.cWid  c
  R = Caps.cReg  c

  -- EXPLICIT LEDGER PROJECTIONS.  The ∧-true splits cannot be left to
  -- unification: the conjuncts are function applications the unifier
  -- will not invert (hit twice now), so every split names its sides.
  pbC : ∀ (J : ℕ) {u} (p : Path Γ u t) → PbB c Ψ J p ≡ true →
        pathSz? (Caps.cSize (frameStep J c)) p ≡ true
  pbC J p h = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) p) (pathBΨ? Ψ p) h)

  pbΨ : ∀ (J : ℕ) {u} (p : Path Γ u t) → PbB c Ψ J p ≡ true → pathBΨ? Ψ p ≡ true
  pbΨ J p h = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) p) (pathBΨ? Ψ p) h)

  vbC : ∀ (J : ℕ) {s} (vs : List (Val Γ s)) → VbB c sl Ψ J vs ≡ true →
        valsCaps? (frameStep J c) sl vs ≡ true
  vbC J vs h = proj₁ (∧-true (valsCaps? (frameStep J c) sl vs) (valsΨ? Ψ vs) h)

  vbΨ : ∀ (J : ℕ) {s} (vs : List (Val Γ s)) → VbB c sl Ψ J vs ≡ true →
        valsΨ? Ψ vs ≡ true
  vbΨ J vs h = proj₂ (∧-true (valsCaps? (frameStep J c) sl vs) (valsΨ? Ψ vs) h)

  ebC : ∀ (J : ℕ) (es : List (InstEvent (Val Γ t))) → EbB c sl Ψ J es ≡ true →
        all (eventCaps? (frameStep J c) sl) es ≡ true
  ebC J es h = proj₁ (∧-true (all (eventCaps? (frameStep J c) sl) es) (eventsΨ? Ψ es) h)

  ebΨ : ∀ (J : ℕ) (es : List (InstEvent (Val Γ t))) → EbB c sl Ψ J es ≡ true →
        eventsΨ? Ψ es ≡ true
  ebΨ J es h = proj₂ (∧-true (all (eventCaps? (frameStep J c) sl) es) (eventsΨ? Ψ es) h)

  bbC : ∀ (J : ℕ) (str : Stream Γ t) → BbB c sl Ψ J str ≡ true →
        burstCaps? (frameStep J c) sl str ≡ true
  bbC J str h = proj₁ (∧-true (burstCaps? (frameStep J c) sl str) (burstΨ? Ψ str) h)

  bbΨ : ∀ (J : ℕ) (str : Stream Γ t) → BbB c sl Ψ J str ≡ true →
        burstΨ? Ψ str ≡ true
  bbΨ J str h = proj₂ (∧-true (burstCaps? (frameStep J c) sl str) (burstΨ? Ψ str) h)

  vsC-all : ∀ (c′ : Caps) {s} (vs : List (Val Γ s)) →
    valsCaps? c′ sl vs ≡ true → all (valCaps? c′ sl s) vs ≡ true
  vsC-all c′ {s} vs h =
    proj₁ (∧-true (all (valCaps? c′ sl s) vs) (length vs Data.Nat.≤ᵇ suc (Caps.cWid c′)) h)

  -- `map value` carries both payload halves into the event ledger
  mv-caps : ∀ (c′ : Caps) (vs : List (Val Γ t)) →
    all (valCaps? c′ sl t) vs ≡ true →
    all (eventCaps? c′ sl) (map value vs) ≡ true
  mv-caps c′ []       h = refl
  mv-caps c′ (v ∷ vs) h =
    ∧-intro (proj₁ (∧-true _ _ h)) (mv-caps c′ vs (proj₂ (∧-true _ _ h)))

  mv-Ψ : ∀ (vs : List (Val Γ t)) →
    valsΨ? Ψ vs ≡ true → eventsΨ? Ψ (map value vs) ≡ true
  mv-Ψ []       h = refl
  mv-Ψ (v ∷ vs) h =
    ∧-intro (proj₁ (∧-true _ _ h)) (mv-Ψ vs (proj₂ (∧-true _ _ h)))

  ft-caps : ∀ (c′ : Caps) (fin : Bool) →
    all (eventCaps? {Γ = Γ} {u = t} c′ sl)
        (if fin then complete ∷ [] else []) ≡ true
  ft-caps c′ true  = refl
  ft-caps c′ false = refl

  ft-Ψ : ∀ (fin : Bool) →
    eventsΨ? {Γ = Γ} {u = t} Ψ (if fin then complete ∷ [] else []) ≡ true
  ft-Ψ true  = refl
  ft-Ψ false = refl

  burstH : Walk-Hyps e S W R d
  burstH = record
    { OK        = OKB {e = e} c sl Ψ
    ; Pb        = PbB c Ψ
    ; Vb        = VbB c sl Ψ
    ; Eb        = EbB c sl Ψ
    ; Bb        = BbB c sl Ψ
    ; e-nil     = λ _ → refl
    ; e-close   = λ _ _ _ → refl
    ; e-app     = λ J es₁ es₂ h₁ h₂ →
                    ∧-intro (all-++-intro _ es₁ es₂ (ebC J es₁ h₁) (ebC J es₂ h₂))
                            (all-++-intro _ es₁ es₂ (ebΨ J es₁ h₁) (ebΨ J es₂ h₂))
    ; e-widen   = λ {J} {J′} le es h →
                    ∧-intro (eventsCaps?-widen sl es (frameStep-mono-j c 2≤S le)
                              (ebC J es h))
                            (ebΨ J es h)
    ; b-nil     = λ _ → refl
    ; b-app     = λ J s₁ s₂ h₁ h₂ →
                    ∧-intro (all-++-intro _ s₁ s₂ (bbC J s₁ h₁) (bbC J s₂ h₂))
                            (all-++-intro _ s₁ s₂ (bbΨ J s₁ h₁) (bbΨ J s₂ h₂))
    ; b-widen   = λ {J} {J′} le str h →
                    ∧-intro (burstCaps?-widen sl str (frameStep-mono-j c 2≤S le)
                              (bbC J str h))
                            (bbΨ J str h)
    ; b-deliv   = λ J id src evs vals fin hE hV →
                    ∧-intro
                      (∧-intro (all-++-intro _ evs _ (ebC J evs hE)
                                 (all-++-intro _ (map value vals) _
                                   (mv-caps (frameStep J c) vals
                                     (vsC-all (frameStep J c) vals (vbC J vals hV)))
                                   (ft-caps (frameStep J c) fin)))
                               refl)
                      (∧-intro (all-++-intro _ evs _ (ebΨ J evs hE)
                                 (all-++-intro _ (map value vals) _
                                   (mv-Ψ vals (vbΨ J vals hV))
                                   (ft-Ψ fin)))
                               refl)
    ; b-handoff = λ J id src evs i hE →
                    ∧-intro
                      (∧-intro (all-++-intro _ evs _ (ebC J evs hE) refl) refl)
                      (∧-intro (all-++-intro _ evs _ (ebΨ J evs hE) refl) refl)
    ; p-len     = λ J p h → pathSz?-len (Caps.cSize (frameStep J c)) p (pbC J p h)
    ; p-tail    = λ J f p h →
                    ∧-intro (pathSz?-tail (Caps.cSize (frameStep J c)) f p
                              (pbC J (f ↠ p) h))
                            (proj₂ (∧-true (frameBΨ? Ψ f) (pathBΨ? Ψ p)
                              (pbΨ J (f ↠ p) h)))
    ; p-widen   = λ {J} {J′} le p h →
                    ∧-intro (pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le))
                              (pbC J p h))
                            (pbΨ J p h)
    ; v-widen   = λ {J} {J′} le vs h →
                    ∧-intro (valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le)
                              (vbC J vs h))
                            (vbΨ J vs h)
    ; ok-reg    = λ J sched st ok →
                    capsOK?-count (frameStep J c) sched st (proj₂ (proj₁ ok))
    ; ok-cons   = λ J rid sched st ok →
                    ( ( proj₁ (proj₁ ok)
                      , capsOK?-delivered (frameStep J c) rid sched st
                          (proj₂ (proj₁ ok)) )
                    , proj₂ ok )
    ; ok-latch  = λ J i fin sched st ok →
                    ( ( proj₁ (proj₁ ok)
                      , shareLatch-caps (frameStep J c) i fin sched st
                          (proj₂ (proj₁ ok)) )
                    , fnCapB-latch Ψ i fin sched st (proj₂ ok) )
    ; ok-finish = λ J i fin out ok →
                    ( walkOK-finish c sl J i fin out (proj₁ ok)
                    , fnCapB-finish Ψ i fin out (proj₂ ok) )
    ; sf-step   = stepFrame-burst-face {e = e} c sl Ψ d 2≤S 1≤R slC slSz
    }

  module V = Walk {e = e} S W R d 2≤S burstH

------------------------------------------------------------------
-- § 7  THE PAYOFF — tier-1 #1/#2's content, at Ŝ, with no Dm.
--
-- The level arithmetic is `cascadeGo-caps`'s own (Caps-Face:4901),
-- cribbed term for term: Res.cnt through dWalkᶜ-mono and cDel-body,
-- Res.hi through lvls-mono and sizeCount-body.  Then capsAt-suc-full
-- lands the widened caps half on capsAt (suc id) — whose cSize IS
-- sizeCapAt e sl (suc id) — and § 4 recombines with the constant Ψ
-- half.  The consumer (dry-tick-core's telescope, .Caps-Bridge) owns
-- every hypothesis: caps facts from the caps-tick chain, Ψ facts by
-- projection from INV? (valB-fc, regsB?, pathBΨ?-of), the depth from
-- cascade-depth-capsH.
------------------------------------------------------------------

cascadeGo-burst-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      c  = capsAt e sl id
  in
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? c sched st ≡ true →
  fnCapBounded? Ψ sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  valΨ? Ψ (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  all (λ rc → pathBΨ? Ψ (proj₂ rc)) chains ≡ true →
  regsBΨ? Ψ (EvalSt.registry st) ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  depthCascade a id chains sched st ≤ capsH e sl id →
  burstB? (sizeCapAt e sl (suc id)) Ψ
          (proj₁ (cascadeGo a id chains sched st)) ≡ true
cascadeGo-burst-dry {n = n} {e = e} id a chains sched st
                    slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD =
  burstB?-halves (capsAt e sl (suc id)) sl Ψ (proj₁ cg)
    (subst (λ x → burstCaps? x sl (proj₁ cg) ≡ true)
           (sym (capsAt-suc-full e sl id))
           (burstCaps?-widen sl (proj₁ cg)
              (frameStep-mono-j c 2≤S lvl-fits)
              (BW.bbC (BW.V.Res.lvl GO) (proj₁ cg) (BW.V.Res.burst GO))))
    (BW.bbΨ (BW.V.Res.lvl GO) (proj₁ cg) (BW.V.Res.burst GO))
  where
  sl  = Sched.slots sched
  Ψ   = ΨAt e sl
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  1≤R = 1≤capsAt-reg e sl id
  cg  = cascadeGo a id chains sched st

  module BW = BurstWalk {e = e} c sl Ψ d 2≤S 1≤R slC slSz

  inv0 : capsOK? (frameStep 0 c) sched st ≡ true
  inv0 = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv

  GO = BW.V.cascadeGo-go 0 a id chains sched st
         ( ((refl , inv0) , hFC)
         , regP?-∧ (pathSz? (Caps.cSize (frameStep 0 c))) (pathBΨ? Ψ)
             (EvalSt.registry st) (capsOK?-regs c sched st inv) rΨ )
         (chP?-∧ (pathSz? (Caps.cSize (frameStep 0 c))) (pathBΨ? Ψ) chains pS pΨ)
         (∧-intro (∧-intro (∧-intro vC refl) refl) (∧-intro vΨ refl))
         hD

  D = delivN st (proj₂ (proj₂ cg))

  cnt-cdel : D ≤ cDel c d
  cnt-cdel =
    ≤-trans (BW.V.Res.cnt GO)
      (≤-trans (dWalkᶜ-mono n (Caps.cSize c) (length chains)
                  (regAt (Caps.cSize c) (Caps.cReg c) 0)
                  2≤S ≤-refl ≤-refl ≤-refl n≤S ≤-refl
                  (≤-trans lenB (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))))
               (≤-reflexive (sym (cDel-body c d))))

  lvl-fits : BW.V.Res.lvl GO ≤ sizeCount c d
  lvl-fits =
    ≤-trans (≤-trans (BW.V.Res.hi GO)
                     (lvls-mono D (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl cnt-cdel))
            (≤-reflexive (sym (sizeCount-body c d)))
