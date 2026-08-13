------------------------------------------------------------------
-- BURST-WALK: the two-flavour burst ledger over the Delivery-Walk —
-- the walk/cascade burst content, landed at Ŝ with no tower constant.
--
-- Landed from probe/Caps-Burst-Walk-Probe.agda (2026-08-10), which
-- was v2 of the route: v1's two bridging postulates were BOTH
-- mis-stated (one concluded fnCap facts from hypotheses carrying no
-- fnCap information; one lacked the plen/gas guards that keep its
-- arithmetic true), and v0 — demand ledgers CONSTANT in the walk
-- level — was MACHINE-REFUTED (2026-08-10; the probe is deleted at
-- 83b29c1, this paragraph is the receipt).  The refutation: at
-- fn = pairᵗ (varᵗ x) (varᵗ x), Dm = 1, Ψ = 0, one payload 0 : natᵗ,
-- `sizeᵛ natᵗ 0 = 1` fits the bound and `sizeᵛ (applyFn fn 0) = 3`
-- does not — both by refl — so a level-constant Vb's OUTPUT conjunct
-- reduces to false and the claim closes by ().  NOT VACUOUS: all five
-- hypotheses discharged at st-init of a concrete program (four rows
-- LOAD-BEARING; the empty-registry row DEGENERATE).  NOT COVERED: the
-- real Dm = (2·B + 12) · towerℕ (suc sz), which is no evaluable
-- numeral — that it too is no fixed point of a doubling map is
-- reasoning, not a row.  The general lesson: the walk THREADS its
-- ledger through every frame, so Walk's *-widen fields are not
-- decoration — they are the walk telling you the ledger must GROW
-- WITH THE LEVEL.
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
-- gas guard.
--
-- THE FRAME FACE IS NOT A POSTULATE.  `stepFrame-burst-face` (§ 5b) is
-- an ASSEMBLY over the PROVEN `stepFrame-face` (.Caps-Face:4678) plus
-- five per-frame WET leaves (§ 2).  Four of its six conjuncts come off
-- that one call — the level bound and `capsOK?` verbatim, `valsCaps?`
-- verbatim, and `regP? (pathSz? …)` via `capsOK?-regs` on that same
-- `capsOK?`.  ALL THREE STATE-LOCAL LEAVES ARE PROVEN — map-f (§ 2.4),
-- take-f (§ 2.4b), scan-f (§ 2.4c) — leaving `wet-inner` and `wet-thru`,
-- the two *All edges, which carry the real content: the same family as
-- `subscribeInner-demand` (.Anchor-Dry).
--
-- Also home to frameBΨ?/pathBΨ?/regsBΨ?, RELOCATED from .Caps-Bridge
-- (they were defined there, downstream of this module's consumers).
------------------------------------------------------------------
module Verify-Budget-Sufficient.Burst-Walk where

open import Data.Bool    using (Bool; true; false; T; if_then_else_; _∧_; not)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _≤_; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.List    using (List; []; _∷_; _++_; map; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Unit    using (⊤; tt)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Nullary using (yes; no)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; gs; g0; Id; Tick; Source; InstEvent;
                           value; init; close; handoff; complete;
                           InstEmit)
open import Rx.Exp  using (Ty; Ctx; Closed; Val; obs; Fn; applyFn; _×ᵗ_; _≟ᵗ_)
open import Rx.Evaluator
  using (Sched; EvalSt; Slots; Arrival; RegId; Chain; Path; Frame;
         _↠_; root; share-sink;
         map-f; scan-f; take-f; from-inner; thru-outer; Stream;
         stepFrame; cascadeGo; dropSource; shareLatch; shareFinish; slotsSize;
         hasDry;
         arrTy; arrVal; fLvlD; regAt; subscribeInner; subscribeE;
         splitBurst; splitEvents; sLvlD;
         AllOp; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
         NodeId; NodeState; takeDispatch; takeVals; cutThrough;
         lookupNode; setNode; sweepLive; pathHasNode; memberSource; scanVals;
         innerFinish; concatDrain; aliveThroughᶠ;
         mergeBump; switchKill; thruConsume; thruWalk; thruWrap;
         scan-st; take-st; merge-st; concat-st; switch-st; exhaust-st)

-- re-exports .Caps (frameStep, capsAt, sizeCount, the mono kit) and
-- .Deliveries (delivN) public
open import Verify-Budget-Sufficient.Delivery-Walk
  using (Walk-Hyps; module Walk; regP?; chP?; Caps; frameStep; delivN;
         capsAt; capsH; sizeCount; cDel; cDel-body; sizeCount-body;
         lvls-mono; dWalkᶜ-mono; capsAt-suc-full;
         2≤capsAt-size; 1≤capsAt-reg;
         ∧-intro; ∧-true; all-++-intro)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthCascade; depthInner; depthFin)

open import Verify-Budget-Sufficient.Caps-Nest using (nest)

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; walkOK; walkOK-finish; slotsCaps?;
         valCaps?; valsCaps?; eventCaps?; burstCaps?;
         eventsCaps?-widen; burstCaps?-widen; valsCaps?-lvl;
         pathSz?-len; pathSz?-tail; pathSz?-widen;
         capsOK?-count; capsOK?-delivered; capsOK?-regs; shareLatch-caps;
         frameStep-mono-j; frameStep-0; stepFrame-face; frameBud)

open import Verify-Budget-Sufficient.Wet
  using (burstB?; eventB?; valB?; sizeCapAt; ΨAt;
         fnCapBounded?; fcB-live; fcB-nodes; sweepLive-fnCap;
         fnCapᵛ; fnCapᵉ; caseWᵗ; fnCapᵗ; applyFn-fnCap; pathLen; T-to; T⇒≡true;
         fnCapLive; fnCapNode; setNode-fnCap; scanVals-fnCap)

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
-- § 2  ONE FRAME PRESERVES BOTH FLAVOURS — no longer one postulate.
--
-- 2026-08-10: `stepFrame-burst-face` was a MONOLITH; it is now a REAL
-- ASSEMBLY (§ 5b) over the already-proven caps face plus five per-frame
-- WET leaves, of which the three STATE-LOCAL ones are proven here and
-- the two *All edges remain.
--
-- WHAT THE CAPS SIDE ALREADY GIVES.  `stepFrame-face` (Caps-Face:4678)
-- picks a j′ and reports the level bound, `capsOK?`, `valsCaps?` and
-- the emitted-events caps half, all at J+j′.  One more conjunct falls
-- straight out of that `capsOK?`: `regP? (pathSz? …)` IS
-- `capsOK?-regs`.  So five of the assembly's six obligations are
-- discharged by machinery that exists.
--
-- WHAT IS LEFT is the WET face of one frame (`WetFace`, § 2.2): five
-- Ψ-only conjuncts, all frame-invariant — no level index anywhere.
--
-- THE EVENTS CAPS HALF MOVED TO `FrameFace` (2026-08-10).  It sat here
-- first, at the assembly's j′ with the two caps receipts as hypotheses
-- — and in that form the two *All leaves were UNPROVABLE: an emitted
-- root delivery is pinned by no state or vals receipt, so a program
-- whose inner delivers one large root value while its post-state stays
-- small meets every hypothesis at j′ = 0 and fails the conclusion.
-- The conjunct's actual suppliers (`innerFinish-caps`,
-- `subscribeInner-caps` — Subscribe-Face, PROVEN) mint it at the SAME
-- j′ as the state receipts, and `stepFrame-face` is the only route
-- that witness travels — so the conjunct now rides FrameFace and the
-- wet face is Ψ-pure.  This was the fourth mis-stated bridge on this
-- route, caught by census rather than by a dead grind.
------------------------------------------------------------------

-- § 2.1  THE siC HYPOTHESIS, named once: `stepFrame-face`'s own first
-- argument.  It is a PARAMETER rather than an import because the
-- supplier (`subscribeInner-caps`, Subscribe-Face:951, PROVEN) lives in
-- the 44-minute module and importing it here would cost this module its
-- fast loop.  Caps-Bridge, which imports both, applies it.
SiCFace : Set
SiCFace =
  ∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
    (c′ : Caps) (dep bud j′ : ℕ) (g′ : Gas) (op′ : AllOp) (allNid′ : NodeId)
    (κ′ : Path Γ′ u′ t′) (id′ : Id) (now′ : Tick) (o′ : Val Γ′ (obs u′))
    (sl′ : Slots Γ′) (sched′ : Sched Γ′) (st′ : EvalSt e′) →
    2 ≤ Caps.cSize c′ →
    1 ≤ Caps.cReg c′ →
    Sched.slots sched′ ≡ sl′ →
    slotsCaps? (Caps.cSize c′) (Caps.cWid c′) sl′ ≡ true →
    slotsSize sl′ ≤ Caps.cSize c′ →
    capsOK? (frameStep j′ c′) sched′ st′ ≡ true →
    valCaps? (frameStep j′ c′) sl′ (obs u′) o′ ≡ true →
    pathSz? (Caps.cSize (frameStep j′ c′)) κ′ ≡ true →
    suc (pathLen κ′) ≤ Caps.cSize (frameStep j′ c′) →
    nest o′ sl′ (EvalSt.connectedShares st′) ≤ bud →
    depthInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′ ≤ dep →
    let r′ = subscribeInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′
    in Σ ℕ λ j₂ →
       (capsOK? (frameStep (j′ + j₂) c′)
                (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r′)))))
                (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r′))))) ≡ true)
       × (valsCaps? (frameStep (j′ + j₂) c′) sl′ (proj₁ (proj₂ r′)) ≡ true)
       × (all (eventCaps? (frameStep (j′ + j₂) c′) sl′)
              (proj₁ (proj₂ (proj₂ r′))) ≡ true)
       × (suc (j′ + j₂) ≤ sLvlD (Caps.cSize c′) (Caps.cWid c′) dep (suc bud) (suc j′))

-- § 2.1b  THE ifc HYPOTHESIS, named once: `stepFrame-face`'s second
-- argument.  It is a PARAMETER rather than an import because the
-- supplier (`innerFinish-caps`, Subscribe-Face:1760, PROVEN) lives in
-- the 44-minute module and importing it here would cost this module its
-- fast loop.  Caps-Bridge, which imports both, applies it.
IfcFace : Set
IfcFace =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    frameBud c j ≤ bud →
    depthFin g op allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
    let r = innerFinish g op allNid inst κ id now vals sched st
              (lookupNode allNid (EvalSt.nodes st))
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)

-- § 2.2  THE WET FACE — exactly what `stepFrame-face` does NOT say.
-- Ψ-pure: no caps, no level index, no growth witness.
WetFace : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) →
  List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e → Set
WetFace sl Ψ r =
  let sched′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
      st′    = proj₂ (proj₂ (proj₂ (proj₂ r)))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)

-- § 2.3  THE OBLIGATIONS STILL OPEN.  The three STATE-LOCAL frames are
-- proven — map-f (§ 2.4), take-f (§ 2.4b), scan-f (§ 2.4c) — and the
-- from-inner edge is now a REAL DEFINITION all the way down to ONE
-- postulate: `wet-inner` (§ 2.4d) proves the two inert paths,
-- `wet-innerFinish` (§ 2.4e) proves merge/switch/exhaust/mismatch and
-- reduces concat+yes through the PROVEN `concatDrain-Ψ` walk to
-- `subscribeInner-Ψ` below — the Ψ face of the one function all three
-- *All-edge postulates bottom out in (`wet-thru` and
-- `subscribeInner-demand` (.Anchor-Dry) are the other two).
--
-- Ψ-PURE SINCE 2026-08-10 (the FrameFace move, § 2 header): no level
-- index, no caps receipts.  What remains says only that a subscribe
-- PRESERVES the Ψ ledger — the same invariant `INV?`'s Ψ half claims
-- for whole subscribes (subscribeE-wet, tier 2) — so its proof is the
-- Ψ mirror of Subscribe-Face's proven caps clique, with the gas edge
-- into `subscribeE` as the one real recursion.
--
-- CALL-SITE ARGUMENTS THESE ABSORB: none — every index is pinned by
-- WetFace above.

-- § 2.3a  subscribeE-Ψ — THE PENDING POSTULATE.
-- Proof sketch: Ψ = fnCapᵉ e + slotsFnCap sl is set once at init.
-- Slots never change (nextNode/live/ordinals never write the slots
-- field).  fnCapBounded? reads only .live and .nodes; every new live
-- entry fnCap ≤ Ψ (cold values come from a slot; deferᵉ body IS b
-- whose fnCapᵉ b ≤ Ψ); new nodes are take-st/scan-st/… all trivially
-- ≤ Ψ.  regP? grows only via `register` with path derived from κ;
-- pathBΨ? Ψ κ ≡ true guarantees each new entry.  burstΨ?: base cases
-- emit only init/close/complete (Ψ-bounded by definition); map/scan
-- use applyFn-fnCap; the *All family recurses through subscribeInner
-- (mutual structure — handled by the same descent as subscribeE-caps).
postulate
  subscribeE-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    fnCapBounded? Ψ sched st ≡ true →
    regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
    (fnCapᵉ b ≤ᵇ Ψ) ≡ true →
    pathBΨ? Ψ κ ≡ true →
    let r = subscribeE g b κ id now sched st
    in (Sched.slots (proj₁ (proj₂ r)) ≡ sl)
     × (fnCapBounded? Ψ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
     × (burstΨ? Ψ (proj₁ r) ≡ true)

-- § 2.3b  SPLIT LEMMAS — helpers for subscribeInner-Ψ's gs clause.
-- Landed from probe/SubscribeInner-Psi-Probe.agda.  Pattern mirrors
-- splitBurst-vals-caps / splitBurst-bk-caps (Caps-Face:5015-5032):
-- pass xs to all-++-intro explicitly so Agda unifies directly with
-- the splitBurst (em ∷ ems) → proj₁/proj₂ reduction.

-- Ψ-bounded values from splitEvents; {A} is the bs-element type.
private
  splitEvents-vals-Ψ : ∀ {n} {Γ : Ctx n} {u} {A : Set} (Ψ : ℕ)
    (events : List (InstEvent (Val Γ u))) →
    all (eventΨ? Ψ) events ≡ true →
    valsΨ? Ψ (proj₁ (splitEvents {A = A} events)) ≡ true
  splitEvents-vals-Ψ Ψ [] _ = refl
  splitEvents-vals-Ψ {u = u} {A = A} Ψ (value v ∷ es) h =
    ∧-intro (proj₁ (∧-true (valΨ? Ψ u v) (all (eventΨ? Ψ) es) h))
            (splitEvents-vals-Ψ {A = A} Ψ es
              (proj₂ (∧-true (valΨ? Ψ u v) (all (eventΨ? Ψ) es) h)))
  splitEvents-vals-Ψ {A = A} Ψ (init _ ∷ es) h =
    splitEvents-vals-Ψ {A = A} Ψ es h
  splitEvents-vals-Ψ {A = A} Ψ (close _ _ ∷ es) h =
    splitEvents-vals-Ψ {A = A} Ψ es h
  splitEvents-vals-Ψ {A = A} Ψ (handoff _ ∷ es) h =
    splitEvents-vals-Ψ {A = A} Ψ es h
  splitEvents-vals-Ψ {A = A} Ψ (complete ∷ es) h =
    splitEvents-vals-Ψ {A = A} Ψ es h

  splitBurst-vals-Ψ : ∀ {n} {Γ : Ctx n} {u} {A : Set} (Ψ : ℕ)
    (burst : Stream Γ u) →
    burstΨ? Ψ burst ≡ true →
    valsΨ? Ψ (proj₁ (splitBurst {A = A} burst)) ≡ true
  splitBurst-vals-Ψ Ψ [] _ = refl
  splitBurst-vals-Ψ {u = u} {A = A} Ψ (em ∷ ems) h =
    all-++-intro _ (proj₁ (splitEvents {A = A} (InstEmit.events em))) _
      (splitEvents-vals-Ψ {A = A} Ψ (InstEmit.events em) (proj₁ (∧-true _ _ h)))
      (splitBurst-vals-Ψ {A = A} Ψ ems (proj₂ (∧-true _ _ h)))

  -- unconditional: splitEvents puts only init/close/handoff in bs
  splitEvents-eventsΨ : ∀ {n} {Γ : Ctx n} {u t} (Ψ : ℕ)
    (events : List (InstEvent (Val Γ u))) →
    eventsΨ? {u = t} Ψ (proj₁ (proj₂ (splitEvents {A = Val Γ t} events))) ≡ true
  splitEvents-eventsΨ Ψ [] = refl
  splitEvents-eventsΨ {t = t} Ψ (value _ ∷ es) =
    splitEvents-eventsΨ {t = t} Ψ es
  splitEvents-eventsΨ {t = t} Ψ (init _ ∷ es) =
    ∧-intro refl (splitEvents-eventsΨ {t = t} Ψ es)
  splitEvents-eventsΨ {t = t} Ψ (close _ _ ∷ es) =
    ∧-intro refl (splitEvents-eventsΨ {t = t} Ψ es)
  splitEvents-eventsΨ {t = t} Ψ (handoff _ ∷ es) =
    ∧-intro refl (splitEvents-eventsΨ {t = t} Ψ es)
  splitEvents-eventsΨ {t = t} Ψ (complete ∷ es) =
    splitEvents-eventsΨ {t = t} Ψ es

  splitBurst-eventsΨ : ∀ {n} {Γ : Ctx n} {u t} (Ψ : ℕ) (burst : Stream Γ u) →
    eventsΨ? {u = t} Ψ (proj₁ (proj₂ (splitBurst {A = Val Γ t} burst))) ≡ true
  splitBurst-eventsΨ Ψ [] = refl
  splitBurst-eventsΨ {Γ = Γ} {t = t} Ψ (em ∷ ems) =
    all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ t} (InstEmit.events em)))) _
      (splitEvents-eventsΨ {t = t} Ψ (InstEmit.events em))
      (splitBurst-eventsΨ {t = t} Ψ ems)

-- § 2.3c  subscribeInner-Ψ — NOW A REAL DEFINITION.
-- g0: nextNode bumped; Sched.slots unchanged (record-update transparent);
--   fnCapBounded? reads only .live/.nodes, not .nextNode; vals=[];
--   events=[close drySource dried], eventsΨ? Ψ [close _ _] = true.
-- gs: subscribeE-Ψ supplies all three invariants + burstΨ?; then
--   splitBurst-vals-Ψ and splitBurst-eventsΨ deliver the two output
--   conjuncts from the burst.
subscribeInner-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  valΨ? Ψ (obs u) o ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = subscribeInner g op allNid κ id now o sched st
      sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
      st′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ (proj₂ r))) ≡ true)
subscribeInner-Ψ sl Ψ g0 op allNid κ id now o sched st slEq fc rg oΨ pΨ =
  slEq , fc , rg , refl , refl
subscribeInner-Ψ {Γ = Γ} {t = t} sl Ψ (gs fuel) op allNid κ id now o sched st
                 slEq fc rg oΨ pΨ
  with subscribeE fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
                  (record sched { nextNode = suc (Sched.nextNode sched) }) st
     | subscribeE-Ψ sl Ψ fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
                   (record sched { nextNode = suc (Sched.nextNode sched) }) st
                   slEq fc rg oΨ pΨ
... | (burst , _ , _) | (slEq′ , fc′ , rg′ , bΨ) =
  slEq′ , fc′ , rg′
  , splitBurst-vals-Ψ {A = Val Γ t} Ψ burst bΨ
  , splitBurst-eventsΨ {t = t} Ψ burst

-- § 2.4  THE MAP LEAF — a REAL PROOF.  `stepFrame` on a map-f touches
-- no state and emits no events, so five of the six conjuncts pass
-- straight through; the sixth is `applyFn-fnCap` (Wet:232) pointwise
-- against the chain's own `caseWᵗ ⊔ fnCapᵗ ≤ Ψ`.

regP?-Ψ : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (Ψ J : ℕ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regP? (PbB c Ψ J) rs ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) rs ≡ true
regP?-Ψ c Ψ J []       h = refl
regP?-Ψ c Ψ J (r ∷ rs) h
  with ∧-true (PbB c Ψ J (proj₂ (proj₂ (proj₂ r)))) (regP? (PbB c Ψ J) rs) h
... | hd , tl =
  ∧-intro (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c))
                                  (proj₂ (proj₂ (proj₂ r))))
                         (pathBΨ? Ψ (proj₂ (proj₂ (proj₂ r)))) hd))
          (regP?-Ψ c Ψ J rs tl)

map-Ψ : ∀ {n} {Γ : Ctx n} {s u} (Ψ : ℕ) (fn : Fn Γ [] [] [] s u)
  (vs : List (Val Γ s)) →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ →
  valsΨ? Ψ vs ≡ true →
  valsΨ? Ψ (map (applyFn fn) vs) ≡ true
map-Ψ Ψ fn []       hfn h = refl
map-Ψ {s = s} Ψ fn (v ∷ vs) hfn h
  with ∧-true (valΨ? Ψ s v) (valsΨ? Ψ vs) h
... | hv , hvs =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (applyFn-fnCap Ψ fn v
             (≤ᵇ⇒≤ (fnCapᵛ s v) Ψ (T-to hv)) hfn)))
          (map-Ψ Ψ fn vs hfn hvs)

wet-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (sf : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (map-f fn ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (stepFrame sf id now (map-f fn) path′ vals fin sched st)
wet-map c sl Ψ J sf id now fn path′ vals fin sched st ok pb vb rg =
    proj₁ (proj₁ ok)
  , proj₂ ok
  , map-Ψ Ψ fn vals
      (≤ᵇ⇒≤ (caseWᵗ fn ⊔ fnCapᵗ fn) Ψ
        (T-to (proj₁ (∧-true (frameBΨ? Ψ (map-f fn)) (pathBΨ? Ψ path′)
                 (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c))
                                         (map-f fn ↠ path′))
                                (pathBΨ? Ψ (map-f fn ↠ path′)) pb))))))
      (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb))
  , regP?-Ψ c Ψ J (EvalSt.registry st) rg
  , refl

-- THE INERT RESULT.  Six of `stepFrame`'s take branches and six of its
-- scan branches return `[] , [] , fin , sched , st` — nothing moved, so
-- every conjunct is a projection.  Top-level because a `with`-clause's
-- `where` is not in scope for its siblings, which is what the scan leaf
-- needs (its dispatch is a `with`, not a helper: `stepFrame`'s scan
-- branch reduces only once `lookupNode` itself is matched)
wet-nil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace {e = e} {u = u} sl Ψ ([] , [] , fin , sched , st)
wet-nil c sl Ψ J fin sched st ok rg =
    proj₁ (proj₁ ok) , proj₂ ok , refl
  , regP?-Ψ c Ψ J (EvalSt.registry st) rg , refl

------------------------------------------------------------------
-- § 2.4b  THE TAKE LEAF — also a REAL PROOF.  `takeDispatch` keeps a
-- PREFIX of the payloads, and on a cut it FILTERS the registry, SWEEPS
-- the live set and writes back `take-st zero`.  Every conjunct is a
-- passthrough or a one-line induction.  (The events CAPS half — once
-- the hard-looking conjunct here, closed by `cutThrough-closes-caps` —
-- now rides `FrameFace`, where the caps side's own `takeDispatch-caps`
-- supplies it.)

-- takeVals keeps a PREFIX, so every kept payload was already Ψ-good.
-- Clause-for-clause the mirror of `takeVals-caps` (Caps-Face:5290)
takeVals-Ψ : ∀ {n} {Γ : Ctx n} {s} (Ψ k : ℕ) (vals : List (Val Γ s)) →
  valsΨ? Ψ vals ≡ true →
  valsΨ? Ψ (proj₁ (takeVals k vals)) ≡ true
takeVals-Ψ Ψ zero          vals     h = refl
takeVals-Ψ Ψ (suc k)       []       h = refl
takeVals-Ψ Ψ (suc zero)    (v ∷ vs) h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-Ψ Ψ (suc (suc k)) (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-Ψ Ψ (suc k) vs (proj₂ (∧-true _ _ h)))

-- the cut is a FILTER on the registry, so ANY pointwise path predicate
-- survives it.  Stated for a general P deliberately: the caps side wants
-- the same fact and can crib this rather than re-derive it
cutThrough-keptP : ∀ {n} {Γ : Ctx n} {t} (P : ∀ {u} → Path Γ u t → Bool)
  (nid : NodeId) (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regP? P reg ≡ true →
  regP? P (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-keptP P nid d wm dy []                     h = refl
cutThrough-keptP P nid d wm dy ((rid , src , ch) ∷ r) h
  with ∧-true (P (proj₂ ch)) (regP? P r) h
... | hd , tl with pathHasNode nid (proj₂ ch)
                 | cutThrough-keptP P nid d wm dy r tl
...   | true  | ih = ih
...   | false | ih = ∧-intro hd ih

-- a cut mints ONLY `close` events, on which eventΨ? is `true`
cutThrough-closes-Ψ : ∀ {n} {Γ : Ctx n} {t} (Ψ : ℕ)
  (nid : NodeId) (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  eventsΨ? Ψ (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closes-Ψ Ψ nid d wm dy []                     = refl
cutThrough-closes-Ψ Ψ nid d wm dy ((rid , src , ch) ∷ r)
  with pathHasNode nid (proj₂ ch) | cutThrough nid d wm dy r
     | cutThrough-closes-Ψ Ψ nid d wm dy r
... | false | _ | ih = ih
... | true  | _ | ih with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

wet-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (sf : Gas) (id : Id) (now : Tick)
  (nid : NodeId) (path′ : Path Γ s t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (take-f nid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (stepFrame sf id now (take-f nid) path′ vals fin sched st)
wet-take {e = e} {s = s} c sl Ψ J sf id now nid path′ vals fin sched st
         ok pb vb rg =
  go (lookupNode nid (EvalSt.nodes st))
  where
  vΨ : valsΨ? Ψ vals ≡ true
  vΨ = proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)

  rΨ : regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true
  rΨ = regP?-Ψ c Ψ J (EvalSt.registry st) rg

  go : (mns : Maybe (NodeState _)) →
       WetFace {e = e} {u = s} sl Ψ (takeDispatch nid vals fin sched st mns)
  -- THE CUT: the registry is filtered and the live set swept, both of
  -- which only DROP entries; the node write is `take-st zero`, on which
  -- `fnCapNode` is `true` outright
  go (just (take-st k)) with proj₂ (proj₂ (takeVals k vals))
  ... | true  = proj₁ (proj₁ ok)
              , ∧-intro (sweepLive-fnCap Ψ
                          (proj₁ (cutThrough nid (EvalSt.delivered st)
                                    (EvalSt.regWatermark st) (EvalSt.dying st)
                                    (EvalSt.registry st)))
                          (Sched.live sched)
                          (fcB-live Ψ sched st (proj₂ ok)))
                        (setNode-fnCap Ψ nid (take-st zero) (EvalSt.nodes st) refl
                          (fcB-nodes Ψ sched st (proj₂ ok)))
              , takeVals-Ψ Ψ k vals vΨ
              , cutThrough-keptP (λ {v} p → pathBΨ? Ψ p) nid (EvalSt.delivered st)
                  (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st) rΨ
              , cutThrough-closes-Ψ Ψ nid (EvalSt.delivered st)
                  (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st)
  -- NO CUT: the counter is written back and nothing else moves
  ... | false = proj₁ (proj₁ ok)
              , ∧-intro (fcB-live Ψ sched st (proj₂ ok))
                        (setNode-fnCap Ψ nid
                          (take-st (proj₁ (proj₂ (takeVals k vals))))
                          (EvalSt.nodes st) refl
                          (fcB-nodes Ψ sched st (proj₂ ok)))
              , takeVals-Ψ Ψ k vals vΨ
              , rΨ , refl
  go (just (scan-st _))       = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go (just (merge-st _ _))    = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go (just (concat-st _ _ _)) = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go (just (switch-st _ _))   = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go (just (exhaust-st _ _))  = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go nothing                  = wet-nil {u = s} c sl Ψ J fin sched st ok rg

------------------------------------------------------------------
-- § 2.4c  THE SCAN LEAF — also a REAL PROOF, cribbed from
-- `stepFrame-scan-wet` (Wet:441), the same clause proven against the
-- capᴱ ledger.  The one difference that matters: the caps half is NOT
-- re-derived (the assembly already holds it), so this needs only the
-- fnCap half of the node lookup — hence `lookupNode-fnCap` below rather
-- than the two-sided `lookupNode-B`, whose `boundedNode` premise
-- nothing at this level can pay.

-- the fnCap-ONLY half of `lookupNode-B` (Wet:416)
NodeΨ : ∀ {n} {Γ : Ctx n} → ℕ → Maybe (NodeState Γ) → Set
NodeΨ Ψ nothing   = ⊤
NodeΨ Ψ (just ns) = fnCapNode Ψ ns ≡ true

lookupNode-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  NodeΨ Ψ (lookupNode nid nodes)
lookupNode-fnCap Ψ nid []            h = tt
lookupNode-fnCap Ψ nid ((k , ns) ∷ r) h with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ h)
... | false = lookupNode-fnCap Ψ nid r (proj₂ (∧-true _ _ h))

-- All ↔ all, the Ψ direction only (Wet's allB-* pair carries the size
-- half alongside, which this leaf never sees)
allΨ-to : ∀ {n} {Γ : Ctx n} {s} (Ψ : ℕ) (vs : List (Val Γ s)) →
  valsΨ? Ψ vs ≡ true → All (λ v → fnCapᵛ s v ≤ Ψ) vs
allΨ-to Ψ []       h = []ᵃ
allΨ-to Ψ (v ∷ vs) h =
  ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true _ _ h))) ∷ᵃ allΨ-to Ψ vs (proj₂ (∧-true _ _ h))

allΨ-of : ∀ {n} {Γ : Ctx n} {s} (Ψ : ℕ) (vs : List (Val Γ s)) →
  All (λ v → fnCapᵛ s v ≤ Ψ) vs → valsΨ? Ψ vs ≡ true
allΨ-of Ψ []       h          = refl
allΨ-of Ψ (v ∷ vs) (p ∷ᵃ ps) = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ p)) (allΨ-of Ψ vs ps)

wet-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (sf : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (path′ : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (scan-f fn nid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (stepFrame sf id now (scan-f fn nid) path′ vals fin sched st)
wet-scan {s = s} {u = u} c sl Ψ J sf id now fn nid path′ vals fin sched st
         ok pb vb rg
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-fnCap Ψ nid (EvalSt.nodes st) (fcB-nodes Ψ sched st (proj₂ ok))
... | nothing                | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
... | just (take-st _)       | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
... | just (merge-st _ _)    | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
... | just (concat-st _ _ _) | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
... | just (switch-st _ _)   | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
... | just (exhaust-st _ _)  | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
-- the accumulator type must match the frame's output type, and when it
-- does not the branch is inert too
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = wet-nil {u = u} c sl Ψ J fin sched st ok rg
...   | yes refl =
      proj₁ (proj₁ ok)
    , ∧-intro (fcB-live Ψ sched st (proj₂ ok))
              (setNode-fnCap Ψ nid (scan-st (proj₂ run)) (EvalSt.nodes st)
                (T⇒≡true _ (≤⇒≤ᵇ (proj₁ fcRun)))
                (fcB-nodes Ψ sched st (proj₂ ok)))
    , allΨ-of Ψ (proj₁ run) (proj₂ fcRun)
    , regP?-Ψ c Ψ J (EvalSt.registry st) rg , refl
  where
  run   = scanVals fn ac vals
  capfn = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (frameBΨ? Ψ (scan-f fn nid))
                                        (pathBΨ? Ψ path′)
            (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c))
                                    (scan-f fn nid ↠ path′))
                           (pathBΨ? Ψ (scan-f fn nid ↠ path′)) pb)))))
  vΨ    = proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)
  fcRun = scanVals-fnCap Ψ fn ac vals capfn
            (≤ᵇ⇒≤ _ _ (T-to nb)) (allΨ-to Ψ vals vΨ)

------------------------------------------------------------------
-- § 2.4d  THE FROM-INNER LEAF — an assembly over ONE postulate.
--
-- `innerReact` (Evaluator:1233) passes its payloads through UNTOUCHED
-- on two of its three paths: the not-finished path (`fin = false`), and
-- the ABSORBED path (`fin = true`, but some registration under this
-- inner instance is still live, so the completion is swallowed).  Only
-- the completion moves state.  Same move as the § 5b split, one level
-- down.

-- the INERT result generalised: payloads pass through, state and events
-- untouched.  `wet-nil` is this at `[]`
wet-pass : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (vs : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  valsΨ? Ψ vs ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace {e = e} {u = u} sl Ψ (vs , [] , fin , sched , st)
wet-pass c sl Ψ J vs fin sched st ok hv rg =
    proj₁ (proj₁ ok) , proj₂ ok , hv
  , regP?-Ψ c Ψ J (EvalSt.registry st) rg , refl

------------------------------------------------------------------
-- § 2.4e  THE COMPLETION PATH — a REAL DEFINITION down to
-- `subscribeInner-Ψ` (§ 2.3).  Mirrors the caps side's proven
-- decomposition (`innerFinish-caps` over `concatDrain-caps` over
-- `subscribeInner-caps`, Subscribe-Face): merge/switch/exhaust rewrite
-- one node field on which `fnCapNode` is `true` outright, every
-- mismatched read is the evaluator's catch-all pass, and concat+yes is
-- the drain.

-- the drain walk: one `subscribeInner-Ψ` receipt per queued inner,
-- threading the Ψ state invariant; the residue queue is a suffix of
-- the input, so its bound rides along rather than being re-derived
concatDrain-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (allNid : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  all (λ o → fnCapᵉ o ≤ᵇ Ψ) q ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = concatDrain g allNid κ id now q sched st
      sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
      st′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
   × (all (λ o → fnCapᵉ o ≤ᵇ Ψ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
concatDrain-Ψ sl Ψ g allNid κ id now [] sched st slEq fc rg qB pB =
  slEq , fc , rg , refl , refl , refl
concatDrain-Ψ sl Ψ g allNid κ id now (o ∷ q) sched st slEq fc rg qB pB
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-Ψ sl Ψ g concatᵒ allNid κ id now o sched st slEq fc rg
         (proj₁ (∧-true (fnCapᵉ o ≤ᵇ Ψ) (all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) q) qB)) pB
-- the inner completed synchronously: keep draining the tail
... | (inst , vs , bs , true , sched₁ , st₁) | (slEq₁ , fc₁ , rg₁ , vsΨ , bsΨ)
  with concatDrain g allNid κ id now q sched₁ st₁
     | concatDrain-Ψ sl Ψ g allNid κ id now q sched₁ st₁ slEq₁ fc₁ rg₁
         (proj₂ (∧-true (fnCapᵉ o ≤ᵇ Ψ) (all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) q) qB)) pB
...   | (vs′ , bs′ , act , q′ , sched₂ , st₂) | (slEq₂ , fc₂ , rg₂ , vsΨ′ , bsΨ′ , qB′) =
      slEq₂ , fc₂ , rg₂
    , all-++-intro _ vs vs′ vsΨ vsΨ′
    , all-++-intro _ bs bs′ bsΨ bsΨ′
    , qB′
-- the inner stayed open: the drain stops with the tail as residue
concatDrain-Ψ sl Ψ g allNid κ id now (o ∷ q) sched st slEq fc rg qB pB
    | (inst , vs , bs , false , sched₁ , st₁) | (slEq₁ , fc₁ , rg₁ , vsΨ , bsΨ) =
      slEq₁ , fc₁ , rg₁ , vsΨ , bsΨ
    , proj₂ (∧-true (fnCapᵉ o ≤ᵇ Ψ) (all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) q) qB)

-- FROM-INNER's completion, per (op, node-read) clause.  `fin` is
-- already pinned `true` and the absorb test already resolved by
-- `wet-inner` (§ 2.4d), which is this definition's one consumer
wet-innerFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (allNid instNid : NodeId)
  (path′ : Path Γ s t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (from-inner op allNid instNid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (innerFinish sf op allNid instNid path′ id now vals sched st
                  (lookupNode allNid (EvalSt.nodes st)))

-- MERGE: decrement the counter — `fnCapNode Ψ (merge-st _ _)` is `true`
wet-innerFinish c sl Ψ J sf id now mergeᵒ allNid instNid path′ vals sched st ok pb vb rg
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od) =
      proj₁ (proj₁ ok)
    , ∧-intro (fcB-live Ψ sched st (proj₂ ok))
              (setNode-fnCap Ψ allNid (merge-st (pred k) od) (EvalSt.nodes st) refl
                (fcB-nodes Ψ sched st (proj₂ ok)))
    , proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)
    , regP?-Ψ c Ψ J (EvalSt.registry st) rg
    , refl
... | nothing                = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (scan-st _)       = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (take-st _)       = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (concat-st _ _ _) = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (switch-st _ _)   = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (exhaust-st _ _)  = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg

-- CONCAT: the drain — the one clause with real content
wet-innerFinish {s = s} c sl Ψ J sf id now concatᵒ allNid instNid path′ vals sched st ok pb vb rg
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-fnCap Ψ allNid (EvalSt.nodes st) (fcB-nodes Ψ sched st (proj₂ ok))
... | nothing                | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (scan-st _)       | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (take-st _)       | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (merge-st _ _)    | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (switch-st _ _)   | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (exhaust-st _ _)  | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (concat-st {w} q act od) | nb with w ≟ᵗ s
...   | no _     = wet-pass c sl Ψ J vals false sched st ok
                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                    (valsΨ? Ψ vals) vb)) rg
...   | yes refl =
        proj₁ D
      , ∧-intro (fcB-live Ψ sched′ st′ (proj₁ (proj₂ D)))
                (setNode-fnCap Ψ allNid (concat-st q′ act′ od) (EvalSt.nodes st′)
                  q′B (fcB-nodes Ψ sched′ st′ (proj₁ (proj₂ D))))
      , all-++-intro _ vals (proj₁ dr)
          (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb))
          (proj₁ (proj₂ (proj₂ (proj₂ D))))
      , proj₁ (proj₂ (proj₂ D))
      , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ D))))
    where
    D = concatDrain-Ψ sl Ψ sf allNid path′ id now q sched st
          (proj₁ (proj₁ ok)) (proj₂ ok)
          (regP?-Ψ c Ψ J (EvalSt.registry st) rg)
          nb
          (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c))
                           (from-inner concatᵒ allNid instNid ↠ path′))
                         (pathBΨ? Ψ (from-inner concatᵒ allNid instNid ↠ path′)) pb))
    dr     = concatDrain sf allNid path′ id now q sched st
    act′   = proj₁ (proj₂ (proj₂ dr))
    q′     = proj₁ (proj₂ (proj₂ (proj₂ dr)))
    sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
    st′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
    q′B    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ D))))

-- SWITCH: clear the current-inner slot if this was it —
-- `fnCapNode Ψ (switch-st _ _)` is `true`
wet-innerFinish c sl Ψ J sf id now switchᵒ allNid instNid path′ vals sched st ok pb vb rg
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (scan-st _)       = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (take-st _)       = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (merge-st _ _)    = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (concat-st _ _ _) = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (exhaust-st _ _)  = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (switch-st nothing od) = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (switch-st (just cur) od) with cur ≡ᵇ instNid
...   | false = wet-pass c sl Ψ J vals false sched st ok
                  (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                 (valsΨ? Ψ vals) vb)) rg
...   | true  =
        proj₁ (proj₁ ok)
      , ∧-intro (fcB-live Ψ sched st (proj₂ ok))
                (setNode-fnCap Ψ allNid (switch-st nothing od) (EvalSt.nodes st) refl
                  (fcB-nodes Ψ sched st (proj₂ ok)))
      , proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)
      , regP?-Ψ c Ψ J (EvalSt.registry st) rg
      , refl

-- EXHAUST: clear the busy flag — `fnCapNode Ψ (exhaust-st _ _)` is `true`
wet-innerFinish c sl Ψ J sf id now exhaustᵒ allNid instNid path′ vals sched st ok pb vb rg
  with lookupNode allNid (EvalSt.nodes st)
... | just (exhaust-st act od) =
      proj₁ (proj₁ ok)
    , ∧-intro (fcB-live Ψ sched st (proj₂ ok))
              (setNode-fnCap Ψ allNid (exhaust-st false od) (EvalSt.nodes st) refl
                (fcB-nodes Ψ sched st (proj₂ ok)))
    , proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)
    , regP?-Ψ c Ψ J (EvalSt.registry st) rg
    , refl
... | nothing                = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (scan-st _)       = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (take-st _)       = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (merge-st _ _)    = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (concat-st _ _ _) = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg
... | just (switch-st _ _)   = wet-pass c sl Ψ J vals false sched st ok
                                 (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                (valsΨ? Ψ vals) vb)) rg

wet-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (allNid instNid : NodeId)
  (path′ : Path Γ s t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (from-inner op allNid instNid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (stepFrame sf id now (from-inner op allNid instNid) path′ vals fin sched st)
-- NOT FINISHED: nothing happens at all
wet-inner c sl Ψ J sf id now op a i path′ vals false sched st ok pb vb rg =
  wet-pass c sl Ψ J vals false sched st ok
    (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)) rg
wet-inner c sl Ψ J sf id now op a i path′ vals true sched st ok pb vb rg
  with any (aliveThroughᶠ i st) (EvalSt.registry st)
-- ABSORBED: a registration under this inner is still live, so the
-- completion is swallowed and the payloads pass through
... | true  = wet-pass c sl Ψ J vals false sched st ok
                (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                               (valsΨ? Ψ vals) vb)) rg
... | false = wet-innerFinish c sl Ψ J sf id now op a i path′ vals sched st
                ok pb vb rg

------------------------------------------------------------------
-- § 2.4f  THE THRU-OUTER LEAF.  `stepFrame (thru-outer op nid) =
-- thruWrap op nid fin (thruWalk …)`.  Helpers in dependency order:
-- mergeBump-fnCap, switchKill-Ψ, concatConsume-Ψ, thruConsume-Ψ,
-- thruWalk-Ψ, thruWrap-Ψ, then the assembly `wet-thru`.

mergeBump-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (nid : NodeId) (done : Bool)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) (mergeBump nid done nodes) ≡ true
mergeBump-fnCap Ψ nid done nodes h with lookupNode nid nodes
... | just (merge-st k od) =
    setNode-fnCap Ψ nid (merge-st (if done then k else suc k) od) nodes refl h
... | just (scan-st _)       = h
... | just (take-st _)       = h
... | just (switch-st _ _)   = h
... | just (concat-st _ _ _) = h
... | just (exhaust-st _ _)  = h
... | nothing                = h

switchKill-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (Ψ : ℕ) (cur : Maybe NodeId)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  let r      = switchKill cur sched st
      sched′ = proj₁ (proj₂ r)
      st′    = proj₂ (proj₂ r)
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (eventsΨ? Ψ (proj₁ r) ≡ true)
switchKill-Ψ sl Ψ nothing sched st slEq fc rg =
  slEq , fc , rg , refl
switchKill-Ψ sl Ψ (just v) sched st slEq fc rg =
  slEq
  , ∧-intro
      (sweepLive-fnCap Ψ kept (Sched.live sched) (fcB-live Ψ sched st fc))
      (fcB-nodes Ψ sched st fc)
  , cutThrough-keptP (λ {w} p → pathBΨ? Ψ p) v
      (EvalSt.delivered st) (EvalSt.regWatermark st)
      (EvalSt.dying st) (EvalSt.registry st) rg
  , cutThrough-closes-Ψ Ψ v
      (EvalSt.delivered st) (EvalSt.regWatermark st)
      (EvalSt.dying st) (EvalSt.registry st)
  where
  kept = proj₁ (cutThrough v (EvalSt.delivered st) (EvalSt.regWatermark st)
                  (EvalSt.dying st) (EvalSt.registry st))

concatConsume-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  valΨ? Ψ (obs u) o ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = thruConsume g concatᵒ nid κ id now o sched st
      sched′ = proj₁ (proj₂ (proj₂ r))
      st′    = proj₂ (proj₂ (proj₂ r))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
concatConsume-Ψ {u = u} sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-fnCap Ψ nid (EvalSt.nodes st) (fcB-nodes Ψ sched st fc)
... | just (concat-st {w} q true od) | qB with w ≟ᵗ u
...   | yes refl =
    slEq
    , ∧-intro (fcB-live Ψ sched st fc)
               (setNode-fnCap Ψ nid (concat-st (q ++ o ∷ []) true od)
                  (EvalSt.nodes st)
                  (all-++-intro _ q (o ∷ []) qB (∧-intro oΨ refl))
                  (fcB-nodes Ψ sched st fc))
    , rg , refl , refl
...   | no _     = slEq , fc , rg , refl , refl
concatConsume-Ψ {u = u} sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (concat-st q false od) | _ =
  slEq₁
  , ∧-intro (fcB-live Ψ sched₁ st₁ fc₁)
             (setNode-fnCap Ψ nid (concat-st {t = u} [] (not done) od)
                (EvalSt.nodes st₁) refl (fcB-nodes Ψ sched₁ st₁ fc₁))
  , rg₁ , vsΨ , bsΨ
  where
  R      = subscribeInner g concatᵒ nid κ id now o sched st
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  SI     = subscribeInner-Ψ sl Ψ g concatᵒ nid κ id now o sched st slEq fc rg oΨ pΨ
  slEq₁  = proj₁ SI
  fc₁    = proj₁ (proj₂ SI)
  rg₁    = proj₁ (proj₂ (proj₂ SI))
  vsΨ    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsΨ    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | nothing                | _ = slEq , fc , rg , refl , refl
concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (scan-st _)       | _ = slEq , fc , rg , refl , refl
concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (take-st _)       | _ = slEq , fc , rg , refl , refl
concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (merge-st _ _)    | _ = slEq , fc , rg , refl , refl
concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (switch-st _ _)   | _ = slEq , fc , rg , refl , refl
concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (exhaust-st _ _)  | _ = slEq , fc , rg , refl , refl

thruConsume-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  valΨ? Ψ (obs u) o ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = thruConsume g op nid κ id now o sched st
      sched′ = proj₁ (proj₂ (proj₂ r))
      st′    = proj₂ (proj₂ (proj₂ r))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
thruConsume-Ψ sl Ψ g concatᵒ nid κ id now o sched st slEq fc rg oΨ pΨ =
  concatConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
thruConsume-Ψ sl Ψ g mergeᵒ nid κ id now o sched st slEq fc rg oΨ pΨ =
  slEq₁
  , ∧-intro (fcB-live Ψ sched₁ st₁ fc₁)
             (mergeBump-fnCap Ψ nid done (EvalSt.nodes st₁) (fcB-nodes Ψ sched₁ st₁ fc₁))
  , rg₁ , vsΨ , bsΨ
  where
  R      = subscribeInner g mergeᵒ nid κ id now o sched st
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  SI     = subscribeInner-Ψ sl Ψ g mergeᵒ nid κ id now o sched st slEq fc rg oΨ pΨ
  slEq₁  = proj₁ SI
  fc₁    = proj₁ (proj₂ SI)
  rg₁    = proj₁ (proj₂ (proj₂ SI))
  vsΨ    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsΨ    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
thruConsume-Ψ sl Ψ g switchᵒ nid κ id now o sched st slEq fc rg oΨ pΨ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
  slEq₂
  , ∧-intro (fcB-live Ψ sched₂ st₂ fc₂)
             (setNode-fnCap Ψ nid (switch-st (if done then nothing else just inst) od)
                (EvalSt.nodes st₂) refl (fcB-nodes Ψ sched₂ st₂ fc₂))
  , rg₂
  , vsΨ
  , all-++-intro _ closes bs (proj₂ (proj₂ (proj₂ SK))) bsΨ
  where
  KILL   = switchKill cur sched st
  closes = proj₁ KILL
  sched₁ = proj₁ (proj₂ KILL)
  st₁    = proj₂ (proj₂ KILL)
  SK     = switchKill-Ψ sl Ψ cur sched st slEq fc rg
  slEq₁  = proj₁ SK
  fc₁    = proj₁ (proj₂ SK)
  rg₁    = proj₁ (proj₂ (proj₂ SK))
  R      = subscribeInner g switchᵒ nid κ id now o sched₁ st₁
  sched₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  inst   = proj₁ R
  bs     = proj₁ (proj₂ (proj₂ R))
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  SI     = subscribeInner-Ψ sl Ψ g switchᵒ nid κ id now o sched₁ st₁ slEq₁ fc₁ rg₁ oΨ pΨ
  slEq₂  = proj₁ SI
  fc₂    = proj₁ (proj₂ SI)
  rg₂    = proj₁ (proj₂ (proj₂ SI))
  vsΨ    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsΨ    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
... | nothing                = slEq , fc , rg , refl , refl
... | just (scan-st _)       = slEq , fc , rg , refl , refl
... | just (take-st _)       = slEq , fc , rg , refl , refl
... | just (merge-st _ _)    = slEq , fc , rg , refl , refl
... | just (concat-st _ _ _) = slEq , fc , rg , refl , refl
... | just (exhaust-st _ _)  = slEq , fc , rg , refl , refl
thruConsume-Ψ sl Ψ g exhaustᵒ nid κ id now o sched st slEq fc rg oΨ pΨ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st false od) =
  slEq₁
  , ∧-intro (fcB-live Ψ sched₁ st₁ fc₁)
             (setNode-fnCap Ψ nid (exhaust-st (not done) od)
                (EvalSt.nodes st₁) refl (fcB-nodes Ψ sched₁ st₁ fc₁))
  , rg₁ , vsΨ , bsΨ
  where
  R      = subscribeInner g exhaustᵒ nid κ id now o sched st
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  SI     = subscribeInner-Ψ sl Ψ g exhaustᵒ nid κ id now o sched st slEq fc rg oΨ pΨ
  slEq₁  = proj₁ SI
  fc₁    = proj₁ (proj₂ SI)
  rg₁    = proj₁ (proj₂ (proj₂ SI))
  vsΨ    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsΨ    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
... | just (exhaust-st true od)  = slEq , fc , rg , refl , refl
... | nothing                    = slEq , fc , rg , refl , refl
... | just (scan-st _)           = slEq , fc , rg , refl , refl
... | just (take-st _)           = slEq , fc , rg , refl , refl
... | just (merge-st _ _)        = slEq , fc , rg , refl , refl
... | just (concat-st _ _ _)     = slEq , fc , rg , refl , refl
... | just (switch-st _ _)       = slEq , fc , rg , refl , refl

thruWalk-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  valsΨ? Ψ vals ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = thruWalk g op nid κ id now vals sched st
      sched′ = proj₁ (proj₂ (proj₂ r))
      st′    = proj₂ (proj₂ (proj₂ r))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
thruWalk-Ψ sl Ψ g op nid κ id now [] sched st slEq fc rg vsΨ pΨ =
  slEq , fc , rg , refl , refl
thruWalk-Ψ sl Ψ g op nid κ id now (o ∷ os) sched st slEq fc rg vsΨ pΨ
  with thruConsume g op nid κ id now o sched st
     | thruConsume-Ψ sl Ψ g op nid κ id now o sched st
         slEq fc rg (proj₁ (∧-true _ _ vsΨ)) pΨ
... | (vs , bs , sched₁ , st₁) | (slEq₁ , fc₁ , rg₁ , vsΨ₁ , bsΨ₁)
  with thruWalk g op nid κ id now os sched₁ st₁
     | thruWalk-Ψ sl Ψ g op nid κ id now os sched₁ st₁
         slEq₁ fc₁ rg₁ (proj₂ (∧-true _ _ vsΨ)) pΨ
... | (vs′ , bs′ , sched₂ , st₂) | (slEq₂ , fc₂ , rg₂ , vsΨ₂ , bsΨ₂) =
  slEq₂ , fc₂ , rg₂
  , all-++-intro _ vs vs′ vsΨ₁ vsΨ₂
  , all-++-intro _ bs bs′ bsΨ₁ bsΨ₂

thruWrap-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (r : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  Sched.slots (proj₁ (proj₂ (proj₂ r))) ≡ sl →
  fnCapBounded? Ψ (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p)
        (EvalSt.registry (proj₂ (proj₂ (proj₂ r)))) ≡ true →
  valsΨ? Ψ (proj₁ r) ≡ true →
  eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true →
  let w  = thruWrap op nid fin r
      ws = proj₁ (proj₂ (proj₂ (proj₂ w)))
      wt = proj₂ (proj₂ (proj₂ (proj₂ w)))
  in (Sched.slots ws ≡ sl)
   × (fnCapBounded? Ψ ws wt ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry wt) ≡ true)
   × (valsΨ? Ψ (proj₁ w) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ w)) ≡ true)
thruWrap-Ψ sl Ψ op nid false (vs , bs , sched , st) slEq fc rg vsΨ bsΨ =
  slEq , fc , rg , vsΨ , bsΨ
thruWrap-Ψ sl Ψ mergeᵒ nid true (vs , bs , sched , st) slEq fc rg vsΨ bsΨ
  with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od) =
    slEq
  , ∧-intro (fcB-live Ψ sched st fc)
             (setNode-fnCap Ψ nid (merge-st k true) (EvalSt.nodes st) refl
               (fcB-nodes Ψ sched st fc))
  , rg , vsΨ , bsΨ
... | just (scan-st _)       = slEq , fc , rg , vsΨ , bsΨ
... | just (take-st _)       = slEq , fc , rg , vsΨ , bsΨ
... | just (switch-st _ _)   = slEq , fc , rg , vsΨ , bsΨ
... | just (concat-st _ _ _) = slEq , fc , rg , vsΨ , bsΨ
... | just (exhaust-st _ _)  = slEq , fc , rg , vsΨ , bsΨ
... | nothing                = slEq , fc , rg , vsΨ , bsΨ
thruWrap-Ψ sl Ψ concatᵒ nid true (vs , bs , sched , st) slEq fc rg vsΨ bsΨ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-fnCap Ψ nid (EvalSt.nodes st) (fcB-nodes Ψ sched st fc)
... | just (concat-st q act od) | qB =
    slEq
  , ∧-intro (fcB-live Ψ sched st fc)
             (setNode-fnCap Ψ nid (concat-st q act true) (EvalSt.nodes st) qB
               (fcB-nodes Ψ sched st fc))
  , rg , vsΨ , bsΨ
... | just (scan-st _)       | _ = slEq , fc , rg , vsΨ , bsΨ
... | just (take-st _)       | _ = slEq , fc , rg , vsΨ , bsΨ
... | just (merge-st _ _)    | _ = slEq , fc , rg , vsΨ , bsΨ
... | just (switch-st _ _)   | _ = slEq , fc , rg , vsΨ , bsΨ
... | just (exhaust-st _ _)  | _ = slEq , fc , rg , vsΨ , bsΨ
... | nothing                | _ = slEq , fc , rg , vsΨ , bsΨ
thruWrap-Ψ sl Ψ switchᵒ nid true (vs , bs , sched , st) slEq fc rg vsΨ bsΨ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
    slEq
  , ∧-intro (fcB-live Ψ sched st fc)
             (setNode-fnCap Ψ nid (switch-st cur true) (EvalSt.nodes st) refl
               (fcB-nodes Ψ sched st fc))
  , rg , vsΨ , bsΨ
... | just (scan-st _)       = slEq , fc , rg , vsΨ , bsΨ
... | just (take-st _)       = slEq , fc , rg , vsΨ , bsΨ
... | just (merge-st _ _)    = slEq , fc , rg , vsΨ , bsΨ
... | just (concat-st _ _ _) = slEq , fc , rg , vsΨ , bsΨ
... | just (exhaust-st _ _)  = slEq , fc , rg , vsΨ , bsΨ
... | nothing                = slEq , fc , rg , vsΨ , bsΨ
thruWrap-Ψ sl Ψ exhaustᵒ nid true (vs , bs , sched , st) slEq fc rg vsΨ bsΨ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act od) =
    slEq
  , ∧-intro (fcB-live Ψ sched st fc)
             (setNode-fnCap Ψ nid (exhaust-st act true) (EvalSt.nodes st) refl
               (fcB-nodes Ψ sched st fc))
  , rg , vsΨ , bsΨ
... | just (scan-st _)       = slEq , fc , rg , vsΨ , bsΨ
... | just (take-st _)       = slEq , fc , rg , vsΨ , bsΨ
... | just (merge-st _ _)    = slEq , fc , rg , vsΨ , bsΨ
... | just (concat-st _ _ _) = slEq , fc , rg , vsΨ , bsΨ
... | just (switch-st _ _)   = slEq , fc , rg , vsΨ , bsΨ
... | nothing                = slEq , fc , rg , vsΨ , bsΨ

wet-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (nid : NodeId)
  (path′ : Path Γ u t) (vals : List (Val Γ (obs u)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (thru-outer op nid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (stepFrame sf id now (thru-outer op nid) path′ vals fin sched st)
wet-thru c sl Ψ J sf id now op nid path′ vals fin sched st ok pb vb rg =
  let wk = thruWalk-Ψ sl Ψ sf op nid path′ id now vals sched st
             (proj₁ (proj₁ ok))
             (proj₂ ok)
             (regP?-Ψ c Ψ J (EvalSt.registry st) rg)
             (proj₂ (∧-true _ _ vb))
             (proj₂ (∧-true _ _ pb))
      r  = thruWalk sf op nid path′ id now vals sched st
      wr = thruWrap-Ψ sl Ψ op nid fin r
             (proj₁ wk)
             (proj₁ (proj₂ wk))
             (proj₁ (proj₂ (proj₂ wk)))
             (proj₁ (proj₂ (proj₂ (proj₂ wk))))
             (proj₂ (proj₂ (proj₂ (proj₂ wk))))
  in proj₁ wr
   , proj₁ (proj₂ wr)
   , proj₁ (proj₂ (proj₂ (proj₂ wr)))
   , proj₁ (proj₂ (proj₂ wr))
   , proj₂ (proj₂ (proj₂ (proj₂ wr)))

------------------------------------------------------------------
-- § 2.5  THE DISPATCHER — one clause per frame constructor, so the
-- assembly below never case-splits and the five leaves stay separable.
wet-face : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  {s u} (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (f ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  WetFace sl Ψ (stepFrame sf id now f path′ vals fin sched st)
wet-face c sl Ψ J sf id now (map-f fn) path′ vals fin sched st ok pb vb rg =
  wet-map c sl Ψ J sf id now fn path′ vals fin sched st ok pb vb rg
wet-face c sl Ψ J sf id now (scan-f fn nid) path′ vals fin sched st ok pb vb rg =
  wet-scan c sl Ψ J sf id now fn nid path′ vals fin sched st ok pb vb rg
wet-face c sl Ψ J sf id now (take-f nid) path′ vals fin sched st ok pb vb rg =
  wet-take c sl Ψ J sf id now nid path′ vals fin sched st ok pb vb rg
wet-face c sl Ψ J sf id now (from-inner op a i) path′ vals fin sched st ok pb vb rg =
  wet-inner c sl Ψ J sf id now op a i path′ vals fin sched st ok pb vb rg
wet-face c sl Ψ J sf id now (thru-outer op nid) path′ vals fin sched st ok pb vb rg =
  wet-thru c sl Ψ J sf id now op nid path′ vals fin sched st ok pb vb rg

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
-- § 5b  THE FRAME FACE, ASSEMBLED — ex-postulate, now a definition.
--
-- Six obligations, FIVE of them off `stepFrame-face`'s single call:
-- the level bound, `capsOK?`, `valsCaps?` and the events caps half
-- verbatim, and `regP? (pathSz? …)` via `capsOK?-regs` on that same
-- `capsOK?`.  The Σ's mixed conjuncts recombine caps and Ψ halves
-- pointwise — `regP?-∧` for the registry, `∧-intro` for values and
-- events.  All the Ψ content comes from `wet-face`, which is Ψ-pure
-- since the FrameFace move (§ 2 header).
------------------------------------------------------------------

stepFrame-burst-face : SiCFace → IfcFace →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
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
stepFrame-burst-face siC ifc c sl Ψ d 2≤S 1≤R slC slSz J sf id now f path′ vals fin sched st
                     ok pb vb rg hD =
    j′
  , proj₁ (proj₂ FC)
  , ((proj₁ WF , wCaps) , proj₁ (proj₂ WF))
  , ∧-intro capsVals (proj₁ (proj₂ (proj₂ WF)))
  , regP?-∧ (pathSz? (Caps.cSize (frameStep (J + j′) c))) (pathBΨ? Ψ)
      (EvalSt.registry t′)
      (capsOK?-regs (frameStep (J + j′) c) s′ t′ wCaps)
      (proj₁ (proj₂ (proj₂ (proj₂ WF))))
  , ∧-intro capsEvs (proj₂ (proj₂ (proj₂ (proj₂ WF))))
  where
  r  = stepFrame sf id now f path′ vals fin sched st
  s′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
  t′ = proj₂ (proj₂ (proj₂ (proj₂ r)))

  FC = stepFrame-face siC ifc c d J sl sf id now f path′ vals fin sched st
         2≤S 1≤R (proj₁ (proj₁ ok)) slC (proj₂ (proj₁ ok))
         (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (f ↠ path′))
                        (pathBΨ? Ψ (f ↠ path′)) pb))
         (proj₁ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb))
         slSz hD

  j′       = proj₁ FC
  wCaps    = proj₁ (proj₂ (proj₂ FC))
  capsVals = proj₁ (proj₂ (proj₂ (proj₂ FC)))
  capsEvs  = proj₂ (proj₂ (proj₂ (proj₂ FC)))

  WF : WetFace sl Ψ r
  WF = wet-face c sl Ψ J sf id now f path′ vals fin sched st ok pb vb rg

------------------------------------------------------------------
-- § 6  THE INSTANTIATION — every closure fact a real proof.
------------------------------------------------------------------

module BurstWalk
  {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (siC : SiCFace)
  (ifc : IfcFace)
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
    -- GAS-BLIND FOR NOW: the two-flavour ledger carries no fuel
    -- content.  The nodry (third) flavour is what will spend this
    -- hook — GOK becomes `sf ≡ budgetAt e sl id` when it lands
    ; GOK       = λ _ _ → ⊤
    ; g-mint    = λ _ _ _ _ _ → tt
    ; e-nil     = λ _ → refl
    ; e-close   = λ _ _ → refl
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
    ; sf-step   = λ J sf id now f path′ vals fin sched st ok pb vb rg _ hD →
                    stepFrame-burst-face siC ifc {e = e} c sl Ψ d 2≤S 1≤R slC slSz
                      J sf id now f path′ vals fin sched st ok pb vb rg hD
    }

  module V = Walk {e = e} S W R d 2≤S burstH

------------------------------------------------------------------
-- § 7  THE PAYOFF — the walk/cascade burst content, at Ŝ, with no Dm.
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

cascadeGo-burst-dry : SiCFace → IfcFace →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
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
cascadeGo-burst-dry siC ifc {n = n} {e = e} id a chains sched st
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

  module BW = BurstWalk {e = e} siC ifc c sl Ψ d 2≤S 1≤R slC slSz

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

------------------------------------------------------------------
-- § 8  THE ANCHOR — the cascade's dry half, and nothing else.
--
-- THE MIRROR CENSUS (2026-08-12), which reshaped tier 0.  The old
-- anchor (`cascadeGo-wet-core`, .Wet/Part6, DELETED — RECOVERY: git
-- show 9b48235 restores it) concluded hasDry × INV?-landing in one
-- postulate.  The census read it against the proven caps apparatus and
-- found the two conjuncts in OPPOSITE states:
--
--   · THE INV? HALF WAS ALREADY PROVEN, TWICE.  Externally,
--     `cascade-wet-via-caps` (.Caps-Bridge) lands INV? Ψ′ Ŝ at the
--     cascade's output from caps-tick + fn-tick + the B1/B2 bridges,
--     never reading the old core.  Internally, the Walk's `Res.good`
--     (.Delivery-Walk) threads slotsEq × capsOK? (frameStep J c) ×
--     fnCapBounded? Ψ × regP? through every intermediate cascadeGo
--     state — § 7 projects only `Res.burst` and discards it.  So the
--     old core's INV? conjunct asked for what the repo already had,
--     and its only consumer (dry-tick-core's first hypothesis, whose
--     own conclusion is dry-only) never needed to ask.
--   · THE DRY HALF IS STRUCTURALLY UNMIRRORABLE.  The caps axis is
--     gas-blind end to end: capsOK?, the Walk, cascadeGo-caps carry
--     no fuel content, so no caps output can feed hasDry.  This
--     conjunct is the anchor, and it is all of it.
--
-- THE POSTULATE CANNOT BE PROBED (receipt inherited 2026-08-11 from
-- the old core, unchanged by the split): the abstract Gas family
-- blocks computation, so no probe reaches the region where the caps
-- hypotheses matter; probed rows covered root-path chains only.
-- Symbolic-or-nothing — do not spend a session probing it.
--
-- PROBED 2026-08-13, DEMAND SIDE ONLY (Demand-Probe): the can't-probe
-- ruling covers the SUPPLY (the opaque seeded budget); the demand is
-- measurable by injecting `gasPad h g0` into subscribeE, and it came
-- back ADDITIVE on every probed shape — h* = k+1 for scan-under-*All
-- (all four operators identical), 2k+1 for double-wrap per step, n
-- per μ layer, 1 per first sharedConnect, 0 for deferᵉ.  Peels happen
-- ONLY at subscribeInner / sharedConnect / μ.  Covered region:
-- subscribe-time bursts.  NOT covered: the delivery path (cascadeGo
-- takes no Gas parameter, its gas is minted internally), which is
-- this postulate's own region — so this receipt AIMS the route's
-- step (2) and moves NO risk class.
--
-- THE ROUTE (this is where the grind goes next):
--   (1) EXTEND THE TWO-FLAVOUR LEDGER TO THREE.  hasDry rides the
--       walk's own burst ledger: Bb/Eb gain a nodry conjunct.  Every
--       ledger law is mechanical — hasDry-append (.Measures:145),
--       hasDry [] = false definitionally, and b-deliv/b-handoff append
--       only value events, exhausted closes and handoffs, none of
--       which is `close _ dried` (dryEvent computes to false on each).
--   (2) THE CONTENT LANDS IN THE FRAME FACE.  A dried close enters the
--       stream only from stepFrame's interior subscribes, so the
--       residue after (1) is stepFrame-burst-face's dry conjunct —
--       whose from-inner case IS `subscribeE-demand` (.Anchor-Dry, its
--       own header says whichever is discharged first absorbs the
--       other).  The gas is not free-floating: chainStep mints
--       `budgetAt e sl id` (Rx/Evaluator:1598), so the dry question is
--       seeded-budget-covers-delivery-demand — the class already
--       proven once at the root (caps-fuel-root), with the supply fact
--       Dm ≤ Ŝ proven in .Anchor-Dry.
--
-- Class FALSITY until evidence reaches the *All interiors — the risky
-- region is a from-inner subscribe mid-delivery, exactly where no
-- probe reaches.  Consumer: dry-tick-core (.Caps-Bridge), which owns
-- every hypothesis below (the caps-tick chain for the caps facts, INV?
-- projections for the Ψ facts, cascade-depth-capsH for the depth).
------------------------------------------------------------------

postulate
  cascadeGo-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
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
    hasDry (proj₁ (cascadeGo a id chains sched st)) ≡ false
