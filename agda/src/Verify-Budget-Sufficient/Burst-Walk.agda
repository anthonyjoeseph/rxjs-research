------------------------------------------------------------------
-- BURST-WALK: the THREE-flavour burst ledger over the Delivery-Walk —
-- the walk/cascade burst content landed at Ŝ with no tower constant,
-- and (2026-08-13) the cascade's DRY half off the same run: the third
-- flavour is `nodry`, gas-conditioned through the walk's GOK hook, and
-- `cascadeGo-nodry` — the ex-anchor — is now a projection of `cascadeGo-burst-nodry`.  The
-- anchor's risk lives in ONE per-frame face, `stepFrame-nodry` (its own header carries the census).
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
-- carries the conjunction; `Res.burst` returns both flavours; `burstB?-halves`
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
-- WHAT REPLACED WHAT.  `cascadeGo-burst-dry` replaces BOTH
-- `chainStep-demand` and `foldPath-demand` (ex-.Anchor-Dry, deleted) and
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
-- THE FRAME FACE IS NOT A POSTULATE.  `stepFrame-burst-face` is
-- an ASSEMBLY over the PROVEN `stepFrame-face` (.Caps-Face:4678) plus
-- five per-frame WET leaves (`wet-face`) plus the DRY face
-- (`stepFrame-nodry`).  Four of
-- its conjuncts come off that one call — the level bound and `capsOK?`
-- verbatim, `valsCaps?` verbatim, and `regP? (pathSz? …)` via
-- `capsOK?-regs` on that same `capsOK?`.  ALL THREE STATE-LOCAL WET
-- LEAVES ARE PROVEN — the map, take and scan leaves
-- — leaving `wet-inner` and `wet-thru`, the two *All edges, which
-- carry the wet content (same family as `subscribeInner-demand`,
-- .Anchor-Dry), and `stepFrame-nodry`, which carries the dry.
--
-- Also home to frameBΨ?/pathBΨ?/regsBΨ?, RELOCATED from .Caps-Bridge
-- (they were defined there, downstream of this module's consumers).
------------------------------------------------------------------
module Verify-Budget-Sufficient.Burst-Walk where

open import Data.Bool    using (Bool; true; false; T; if_then_else_; _∧_; _∨_; not)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ; ≤⇒≤ᵇ; ≤ᵇ⇒≤; m≤m+n; m≤n+m; m≤n⊔m)
open import Data.List    using (List; []; _∷_; _++_; map; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Unit    using (⊤; tt)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Nullary using (yes; no)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim using (Gas; gs; g0; Id; Tick; Source; InstEvent;
                           value; init; close; handoff; complete;
                           CloseReason; cut; cutPending; exhausted; dried;
                           gasPad; gasTower;
                           InstEmit; _at_from_as_; EmitKind; delivery)
open import Rx.Exp  using (Ty; Ctx; Closed; Val; obs; Fn; applyFn; _×ᵗ_; _≟ᵗ_; sizeᵉ; syncSizeᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; Slots; Arrival; RegId; Chain; Path; Frame;
         _↠_; root; share-sink;
         map-f; scan-f; take-f; from-inner; thru-outer; Stream;
         stepFrame; cascadeGo; dropSource; shareLatch; shareFinish; slotsSize;
         hasDry; dryEvent; budgetAt; capsHgo; capsBase;
         arrTy; arrVal; fLvlD; opIterD; regAt; subscribeInner; subscribeE;
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
  using (depthFrame; depthCascade; depthInner; depthFin; depthE)

open import Verify-Budget-Sufficient.Caps-Nest using (nest)

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; walkOK; walkOK-finish; slotsCaps?;
         valCaps?; valsCaps?; eventCaps?; burstCaps?;
         eventsCaps?-widen; burstCaps?-widen; valsCaps?-lvl; valsCaps?-parts;
         pathSz?-len; pathSz?-tail; pathSz?-widen;
         capsOK?-count; capsOK?-delivered; capsOK?-regs; shareLatch-caps;
         frameStep-mono-j; frameStep-0; stepFrame-face; frameBud)

open import Verify-Budget-Sufficient.Wet
  using (burstB?; eventB?; valB?; sizeCapAt; ΨAt;
         fnCapBounded?; fcB-live; fcB-nodes; sweepLive-fnCap;
         fnCapᵛ; fnCapᵉ; caseWᵗ; fnCapᵗ; applyFn-fnCap; pathLen; T-to; T⇒≡true;
         fnCapLive; fnCapNode; setNode-fnCap; scanVals-fnCap;
         hasDry-append; ∨-false;
         INV?; dBound; regsLen?; hopR; unconn; pathB?; _hasAtLeast_;
         slotsFnCap)
open import Verify-Budget-Sufficient.Walk-Level
  using (WalkLevel; subscribeE-walk-level; capsOK⇒regsLen; regsLen?-mono)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Frame-Width using (dWᵉ; dWᵛ; pWᵛ; outWᵛ)

------------------------------------------------------------------
-- THE Ψ LEDGER — the fnCap halves of valB?/eventB?/burstB? and
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
-- THE THREE-FLAVOUR LEDGERS, named once so the face postulate and
-- the Walk-Hyps instantiation are definitionally the same predicates.
--
-- THE THIRD FLAVOUR (the anchor ruling, `cascadeGo-nodry`'s header): the event
-- and stream ledgers carry `nodry` beside the caps and Ψ halves.  It
-- spends the hook the walk always had for it (GOK/g-mint,
-- .Delivery-Walk's GOK/g-mint hook): nodry is GAS-CONDITIONED — `subscribeInner g0`
-- emits a dried close, so no gas-blind ledger can carry it — and the
-- walk's one minted gas (`chainStep`'s `budgetAt e sl id`) is exactly
-- what GOK pins.  The flavour is level-INDEPENDENT (dryness does not
-- mention J), so every widen law passes it through untouched; it rides
-- the same J only because the ledger is one Bool.
------------------------------------------------------------------

-- VbB sits OUTSIDE the t-anonymous-module: it never mentions t, and an
-- unmentioned module implicit is an unsolvable meta at every use site
VbB : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → ℕ → ℕ → ∀ {s} → List (Val Γ s) → Bool
VbB c sl Ψ J vs = valsCaps? (frameStep J c) sl vs ∧ valsΨ? Ψ vs

module _ {n} {Γ : Ctx n} {t : Ty} where

  PbB : Caps → ℕ → ℕ → ∀ {u} → Path Γ u t → Bool
  PbB c Ψ J p = pathSz? (Caps.cSize (frameStep J c)) p ∧ pathBΨ? Ψ p

  EbB : Caps → Slots Γ → ℕ → ℕ → List (InstEvent (Val Γ t)) → Bool
  EbB c sl Ψ J es =
    all (eventCaps? (frameStep J c) sl) es ∧ eventsΨ? Ψ es
      ∧ not (any dryEvent es)

  BbB : Caps → Slots Γ → ℕ → ℕ → Stream Γ t → Bool
  BbB c sl Ψ J str =
    burstCaps? (frameStep J c) sl str ∧ burstΨ? Ψ str
      ∧ not (hasDry str)

-- dry-freeness of event lists composes over ++ (the stream version is
-- .Measures' hasDry-append; this is its one-emit mirror)
any-dry-++ : ∀ {A : Set} (xs ys : List (InstEvent A)) →
  any dryEvent xs ≡ false → any dryEvent ys ≡ false →
  any dryEvent (xs ++ ys) ≡ false
any-dry-++ []       ys h₁ h₂ = h₂
any-dry-++ (x ∷ xs) ys h₁ h₂
  with ∨-false (dryEvent x) _ h₁
... | e₁ , h₁′ rewrite e₁ = any-dry-++ xs ys h₁′ h₂

-- `not x ≡ true` and `x ≡ false`, in both directions: the ledger
-- carries the ∧-composable form, the dry lemmas speak the other
not-out : ∀ {x : Bool} → not x ≡ true → x ≡ false
not-out {false} _ = refl

not-in : ∀ {x : Bool} → x ≡ false → not x ≡ true
not-in refl = refl

-- THE SEVERING CLOSE IS NEVER DRY.  `cutThrough` (Rx/Evaluator:246) is
-- the only event source shared by take's cut and switch's kill, and
-- every close it mints carries `cut` or `cutPending` — the two REASONS
-- an operator ends a chain.  `dried` is minted in exactly one place
-- (`subscribeInner g0`, Evaluator:1006) and this is not it.  So both
-- severing paths are dry-free UNCONDITIONALLY: no gas hypothesis, no
-- caps, no level.  Consequence for `stepFrame-nodry`: of `stepFrame`'s five frames,
-- take-f needs nothing beyond this lemma, and thru-outer's switchᵒ
-- branch sheds its `closes` half here.
close-severs-nodry : ∀ {A : Set} (src : Source) (b : Bool) →
  dryEvent {A} (close src (if b then cut else cutPending)) ≡ false
close-severs-nodry src true  = refl
close-severs-nodry src false = refl

-- the head of a cutThrough step is emitted under an `if`; both arms
-- keep the list dry-free, so the guard never needs to be inspected
nodry-if : ∀ {A : Set} (b : Bool) (ev : InstEvent A) (es : List (InstEvent A)) →
  dryEvent ev ≡ false → any dryEvent es ≡ false →
  any dryEvent (if b then es else (ev ∷ es)) ≡ false
nodry-if true  ev es he hs = hs
nodry-if false ev es he hs rewrite he = hs

cutThrough-nodry : ∀ {n} {Γ : Ctx n} {t}
  (nid : NodeId) (dl : List RegId) (wm : RegId) (dy : List Source)
  (rs : List (RegId × Source × Chain Γ t)) →
  any dryEvent (proj₁ (proj₂ (cutThrough nid dl wm dy rs))) ≡ false
cutThrough-nodry nid dl wm dy []                   = refl
cutThrough-nodry nid dl wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c)
     | cutThrough nid dl wm dy r | cutThrough-nodry nid dl wm dy r
... | false | _                    | ih = ih
... | true  | kept , closes , rids | ih =
      nodry-if (any (_≡ᵇ rid) dl ∧ memberSource src dy)
               (close src (if any (_≡ᵇ rid) dl ∨ (wm ≤ᵇ rid) then cut else cutPending))
               closes
               (close-severs-nodry src (any (_≡ᵇ rid) dl ∨ (wm ≤ᵇ rid)))
               ih

OKB : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Caps → Slots Γ → ℕ → ℕ → Sched Γ → EvalSt e → Set
OKB c sl Ψ J sched st =
  walkOK c sl J sched st × (fnCapBounded? Ψ sched st ≡ true)

------------------------------------------------------------------
-- ONE FRAME PRESERVES BOTH FLAVOURS — no longer one postulate.
--
-- 2026-08-10: `stepFrame-burst-face` was a MONOLITH; it is now a REAL
-- ASSEMBLY (`stepFrame-burst-face`) over the already-proven caps face plus five per-frame
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
-- WHAT IS LEFT is the WET face of one frame (`WetFace`): five
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

-- THE siC HYPOTHESIS (SiCFace), named once: `stepFrame-face`'s own first
-- argument.  It is a PARAMETER rather than an import because the
-- supplier (`subscribeInner-caps`, Subscribe-Face:951, PROVEN) lives in
-- the most expensive module in the tree (timings:
-- typecheck-performance-numbers.md) and importing it here would cost
-- this module its fast loop.  Caps-Bridge, which imports both, applies it.
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

-- THE ifc HYPOTHESIS (IfcFace), named once: `stepFrame-face`'s second
-- argument.  It is a PARAMETER rather than an import because the
-- supplier (`innerFinish-caps`, Subscribe-Face:1760, PROVEN) lives in
-- the most expensive module in the tree (timings:
-- typecheck-performance-numbers.md) and importing it here would cost
-- this module its fast loop.  Caps-Bridge, which imports both, applies it.
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

-- THE WET FACE (WetFace) — exactly what `stepFrame-face` does NOT say.
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

-- THE OBLIGATIONS STILL OPEN.  The three STATE-LOCAL frames are
-- proven — map-f, take-f, scan-f — and the
-- from-inner edge is now a REAL DEFINITION all the way down to ONE
-- postulate: `wet-inner` proves the two inert paths,
-- `wet-innerFinish` proves merge/switch/exhaust/mismatch and
-- reduces concat+yes through the PROVEN `concatDrain-Ψ` walk to
-- `subscribeInner-Ψ` below — the Ψ face of the one function all three
-- *All-edge postulates bottom out in (`wet-thru` and
-- `subscribeInner-demand` (.Anchor-Dry) are the other two).
--
-- Ψ-PURE SINCE 2026-08-10 (the FrameFace move, `FrameFace`'s header): no level
-- index, no caps receipts.  What remains says only that a subscribe
-- PRESERVES the Ψ ledger — the same invariant `INV?`'s Ψ half claims
-- for whole subscribes (subscribeE-wet, tier 2) — so its proof is the
-- Ψ mirror of Subscribe-Face's proven caps clique, with the gas edge
-- into `subscribeE` as the one real recursion.
--
-- CALL-SITE ARGUMENTS THESE ABSORB: none — every index is pinned by
-- WetFace above.

-- subscribeE-Ψ — THE PENDING POSTULATE.
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

-- SPLIT LEMMAS — helpers for subscribeInner-Ψ's gs clause.
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

-- subscribeInner-Ψ — NOW A REAL DEFINITION.
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

-- THE MAP LEAF — a REAL PROOF.  `stepFrame` on a map-f touches
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
-- THE TAKE LEAF — also a REAL PROOF.  `takeDispatch` keeps a
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
-- THE SCAN LEAF — also a REAL PROOF, cribbed from
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
-- THE FROM-INNER LEAF — an assembly over ONE postulate.
--
-- `innerReact` (Evaluator:1233) passes its payloads through UNTOUCHED
-- on two of its three paths: the not-finished path (`fin = false`), and
-- the ABSORBED path (`fin = true`, but some registration under this
-- inner instance is still live, so the completion is swallowed).  Only
-- the completion moves state.  Same move as `stepFrame-burst-face`'s split, one level
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
-- THE COMPLETION PATH — a REAL DEFINITION down to
-- `subscribeInner-Ψ`.  Mirrors the caps side's proven
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
-- `wet-inner`, which is this definition's one consumer
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
-- THE THRU-OUTER LEAF.  `stepFrame (thru-outer op nid) =
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
-- THE DISPATCHER (wet-face) — one clause per frame constructor, so the
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
-- THE Ψ-STATE FACTS the walk's OK closure needs — all REAL.
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
-- RECOMBINATION (burstB?-halves) — the two flavours ARE `burstB? (cSize c′) Ψ`,
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
-- THE LEDGER GLUE (regP?-∧ / chP?-∧) — pointwise conjunctions over the registry and
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
-- THE DRY FACE OF ONE FRAME (stepFrame-nodry) — WHERE THE ANCHOR'S RISK NOW LIVES
-- (2026-08-13; the ruling is `cascadeGo-nodry`'s header).
--
-- One frame of one delivery, run on the WALK'S OWN MINTED GAS, emits
-- no dried close.  This is the anchor postulate (`cascadeGo-nodry`,
-- `cascadeGo-nodry`) with everything transport-shaped stripped off: the walk carries
-- dryness through appends and widens mechanically (`EbB`/`BbB`'s third
-- flavour), so the entire dry content of the cascade concentrates in
-- this one per-frame face.
--
-- THE GAS HYPOTHESIS IS THE POINT.  `sf ≡ budgetAt e sl id` — the one
-- gas `chainStep` mints (Rx/Evaluator:1598), carried to the frame by
-- the walk's GOK/g-mint hook (.Delivery-Walk, built for exactly this).
-- Without it the statement is FALSE: `subscribeInner g0` emits a
-- dried close and the depth premise does not exclude g0 (depth
-- measures nesting demand, not supply).
--
-- THE GRIND ROUTE, per frame constructor:
--   · map-f / take-f / scan-f — event inspection: these frames emit
--     no events of their own (the map/take/scan leaves' proofs enumerate the outputs);
--     their nodry halves are refl-shaped.
--   · from-inner / thru-outer (the risky region, and the reason the
--     anchor was FALSITY class) — the interior `subscribeE`, consumed
--     through the COLLAPSED WALK FACE (`subscribeE-walk-level`,
--     .Walk-Level), whose hasDry conjunct is `hasDry ≡ false` and whose
--     hypotheses are LEVEL-indexed at an arbitrary (c , j) — i.e.
--     stated to be satisfiable MID-DELIVERY, which the retired outer
--     face (fixed at capsAt e sl id / id-entry B) was not.  At the
--     frame's own J, the walk supplies: capsOK? (frameStep J c) and
--     fnCapBounded? Ψ from OKB; the path facts from PbB; the value
--     size from VbB.  The two pieces to manufacture, each named the
--     moment the grind reaches it:
--       (i) INV? Ψ (cSize (frameStep J c)) mid-delivery — assembled
--           conjunct-by-conjunct from capsOK? + fnCapBounded? + the
--           regP? ledger, the SAME move as cascade-wet-via-caps' INV? recombination
--           (.Caps-Bridge) makes one stratum up.  Needs
--           cReg (frameStep J c) ≤ cSize (frameStep J c) — B2's
--           frameStep analogue — for the registry-length conjunct.
--           ARITHMETIC CHECKED TRUE 2026-08-13 (hand derivation, not
--           yet machine): with F j := cSize (frameStep j c), R ≤ S,
--           2 ≤ S, induct on j: F 0 = S ≥ R; F (suc j) = S + 2S·F j
--           (frameStep-size-suc) ≥ S·F j + S·F j ≥ F j + R·S, and
--           R·(1+(1+j)·S) = R·(1+jS) + RS ≤ F j + RS.  Uses only
--           R ≤ S ≤ F j (iterSize-infl) — no new machinery needed.
--      (ii) the fuel: `budgetAt e sl id hasAtLeast suc G` for a demand
--           G measured at Ŝ := sizeCapAt e sl (suc id) — the
--           general-id crib of `caps-fuel-root` (.Wet/Part6, PROVEN,
--           id = 0).  SHAPE CHECKED 2026-08-13: `budgetAt e sl id`
--           unfolds to gasPad (2^(sz·suc id·suc id)) (gasTower
--           (3 + capsHgo m (suc id))) — the EXACT gas
--           `budget-hasAtLeast sz m id` (.Measures, PROVEN, general
--           id) is stated at — and the demand side's chain
--           (dBound-bound → prod≤3pow → tower-3 → capsAt-tower) is
--           general in id throughout; only the 6≤V and size-fits
--           facts change instantiation.  The inner value's size fits
--           under Ŝ by the walk's own landing arithmetic (lvl-fits +
--           capsAt-suc-full, `cascadeGo-burst-nodry`'s payoff arithmetic).
--
-- CLASS: FALSITY, inherited from the anchor — this face IS the
-- anchor's risky region (a from-inner subscribe mid-delivery), now
-- with a named engine instead of an unnamed gap.  A failure here that
-- is not a walk-level failure means the walk cannot supply (i) or
-- (ii), which would be a finding about the ledger, not this face.
-- CANNOT BE PROBED, same receipt as the anchor: the gas family is
-- abstract, and `budgetAt` is a tower the checker will not normalise.
--
-- ═══ THE FIVE-FRAME CENSUS, 2026-08-13 — three frames are now REAL ═══
--
-- `stepFrame-nodry` is no longer a monolith: it is an assembly over the
-- frame constructors, and the risk does NOT spread evenly across them.
-- Reading `stepFrame` (Rx/Evaluator:1252-1275) and everything it calls:
--
--   map-f    — events are literally `[]`.                    PROVEN, refl
--   scan-f   — every `dispatch` arm emits `[]`.              PROVEN, refl
--   take-f   — `takeDispatch`: `[]`, or `cutThrough`'s
--              closes, and CUTTHROUGH NEVER MINTS `dried`
--              (`cutThrough-nodry` — every close it
--              makes is `cut`/`cutPending`).                 PROVEN
--   from-inner — `innerReact` → `innerFinish`, whose only
--              emitting arm is concatᵒ's `concatDrain`.      postulated
--   thru-outer — `thruWrap`/`thruWalk`/`thruConsume`, whose
--              events are `switchKill`'s closes (cutThrough
--              again, free) plus `subscribeInner`'s.         postulated
--
-- ═══ THE CONSOLIDATION THAT FALLS OUT, and it is the finding ═══
--
-- Chase the two postulated frames to their leaves and they MEET:
-- `concatDrain` (Evaluator:1195) emits nothing of its own — its `bs`
-- is `subscribeInner`'s, appended down the queue.  `switchKill` is
-- cutThrough.  So after the three proven frames, EVERY remaining
-- dried-close risk in the whole cascade is `subscribeInner`, whose two
-- clauses are:
--   · `g0`      — emits `close drySource dried` (Evaluator:1006).
--                 THE one dry mint in the evaluator.  Excluded by the
--                 gas hypothesis: `budgetAt` is a `gasPad` of a
--                 `gasTower`, never `g0`.
--   · `gs fuel` — `subscribeE fuel …`, i.e. `subscribeE-walk-level`'s
--                 hasDry conjunct, at `fuel` — and the walk face asks for
--                 `g hasAtLeast suc G`, an INEQUALITY, not a pin to
--                 `budgetAt`, so the `gs`-peel goes straight through.
--                 Checked 2026-08-13; had the walk pinned its gas the
--                 descent would not have typed.
--
-- ═══ THE LOOP QUESTION, RULED 2026-08-13 ═══
--
-- The two remaining frames are NOT one-step: `concatDrain` and
-- `thruWalk` LOOP, calling `subscribeInner` at a state that has
-- already moved.  So the leaf's hypotheses (capsOK? and friends, all
-- state-dependent) must be RE-ESTABLISHED per iteration — which is
-- what the caps route's Σ-witness does and what a bare `≡ false`
-- conclusion cannot.  The gas hypothesis is the one part that threads
-- for FREE: `fuel` is passed unchanged by every one of innerReact,
-- innerFinish, concatDrain, thruWalk, thruConsume and thruWrap
-- (checked 2026-08-13), so the `g0` exclusion never has to be re-won.
--
-- TWO ROUTES WERE ON THE TABLE.  (A) take the already-proven caps
-- faces (siC/ifc) as extra parameters and re-establish `capsOK?` at
-- the moved state from their Σ-witness, mirroring what `stepFrame-burst-face` already
-- does one level up.  (B) widen SiCFace/IfcFace's own conclusions
-- with a nodry conjunct, so the re-establishment comes for free.
--
-- RULED: (A).  (B) is tidier to read and strictly worse to build —
-- its suppliers (`subscribeInner-caps`, `innerFinish-caps`) are
-- PROVEN inside Subscribe-Face, so widening their conclusions
-- re-grinds finished work in the most expensive module in the repo
-- (timings: typecheck-performance-numbers.md), and buys no strength that threading the same witness does not.
-- (A) also has a working precedent in this file rather than a
-- hypothetical one.
--
-- WHAT THAT MAKES THE TWO FRAMES: transport over ONE leaf, named
-- below as `SiNodry` and postulated once.  The `-core` pair keeps
-- that structural rather than prose — each frame is a real definition
-- applying its core to the single leaf, so `subscribeInner-nodry` has
-- a consumer from the minute it is stated and the census above is
-- checkable by grep instead of by reading this header.
------------------------------------------------------------------

-- THE ONE LEAF.  Everything dry in the cascade reduces to this, and
-- its own two clauses are the g0 mint (excluded by `gk`) and
-- `subscribeE fuel …` (= `subscribeE-walk-level`'s hasDry conjunct).
SiNodry : Set
SiNodry = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  -- the Ψ-side twin of the line above; see subscribeE-inner-nodry-inv's
  -- header for why it is threaded (INV?'s slotsFnCap conjunct)
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner g op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling (2026-08-13): the walk face's pins force
  -- the honest instantiation Ŝ := sizeCapAt e sl (suc id), and this is
  -- the c-to-entry anchoring the caller owns (c is free here; the
  -- caller knows it is capsAt-rooted).  The face's budget at this
  -- call's arguments stays under the next instant's size cap.
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) J) c)
    ≤ sizeCapAt e sl (suc id) →
  g ≡ budgetAt e sl id →
  any dryEvent (proj₁ (proj₂ (proj₂
    (subscribeInner g op allNid κ id now o sched st))))
    ≡ false

-- THE MINTED BUDGET IS NEVER EMPTY, and this is what excludes the
-- evaluator's ONE dry mint.  `budgetAt` unfolds to
-- `gasPad (2 ^ N) (gasTower H)`, and `2 ^ N` is positive whatever N is,
-- so the gas the machine mints always carries a `gs` head.  Hence
-- `subscribeInner g0` — the sole site that emits `close _ dried`
-- (Rx/Evaluator:1006) — is UNREACHABLE under the gas hypothesis, as a
-- theorem rather than as an appeal to the tower's size.
2^-pos : ∀ (m : ℕ) → Σ ℕ (λ k → 2 ^ m ≡ suc k)
2^-pos zero    = 0 , refl
2^-pos (suc m) with 2^-pos m
... | k , eq rewrite eq = k + suc (k + 0) , refl

budgetAt-gs : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id) →
  Σ Gas (λ g′ → budgetAt e sl id ≡ gs g′)
budgetAt-gs e sl id
  with 2^-pos ((sizeᵉ e + slotsSize sl) * suc id * suc id)
... | k , eq rewrite eq =
      gasPad k (gasTower (3 + capsHgo (capsBase e sl) (suc id))) , refl

-- THE BURST SPLIT KEEPS EVERY CLOSE VERBATIM.  `splitEvents` rebuilds
-- the bookkeeping list constructor for constructor — `close s r` goes
-- through with its reason untouched — so a dry-free burst splits into a
-- dry-free event list.  Proven, not assumed: this is the whole gap
-- between the walk face's `hasDry` conjunct and what `subscribeInner`
-- actually returns.
splitEvents-nodry : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (es : List (InstEvent (Val Γ u))) → any dryEvent es ≡ false →
  any (dryEvent {A}) (proj₁ (proj₂ (splitEvents {A = A} es))) ≡ false
splitEvents-nodry []                h = refl
splitEvents-nodry (value v   ∷ es)  h = splitEvents-nodry es h
splitEvents-nodry (init s    ∷ es)  h = splitEvents-nodry es h
splitEvents-nodry (handoff s ∷ es)  h = splitEvents-nodry es h
splitEvents-nodry (complete  ∷ es)  h = splitEvents-nodry es h
-- the reason is CASE-SPLIT rather than rewritten: the hypothesis lives
-- at `Val Γ u` and the goal at `A`, so `dryEvent`'s implicit differs on
-- the two sides and a rewrite cannot bridge them.  Split, and both
-- sides compute; the `dried` arm is absurd, which is the real content
splitEvents-nodry (close s cut        ∷ es) h = splitEvents-nodry es h
splitEvents-nodry (close s cutPending ∷ es) h = splitEvents-nodry es h
splitEvents-nodry (close s exhausted  ∷ es) h = splitEvents-nodry es h
splitEvents-nodry (close s dried      ∷ es) ()

splitBurst-nodry : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (str : Stream Γ u) → hasDry str ≡ false →
  any (dryEvent {A}) (proj₁ (proj₂ (splitBurst {A = A} str))) ≡ false
splitBurst-nodry []         h = refl
splitBurst-nodry (em ∷ ems) h
  with ∨-false (any dryEvent (InstEmit.events em)) (hasDry ems) h
... | hd , tl =
      any-dry-++ (proj₁ (proj₂ (splitEvents (InstEmit.events em))))
                 (proj₁ (proj₂ (splitBurst ems)))
                 (splitEvents-nodry (InstEmit.events em) hd)
                 (splitBurst-nodry ems tl)

-- EX-RESIDUE, PROVEN 2026-08-13.  It was postulated on the grounds
-- that `outWᵛ` sits outside this module's import scope — a missing
-- import, not a mathematical obstacle, and the wrong reason for a
-- postulate.  `dWᵛ` at an `obs` type IS `dWᵉ` (Rx/Frame-Width:411,
-- definitional) and `valCaps?` already carries
-- `pWᵛ n sl (obs u) o ≤ᵇ cWid` with `pWᵛ = outWᵛ ⊔ dWᵛ`, so the bound
-- is ⊔'s right injection.
--
-- WHAT ACTUALLY BLOCKED IT, recorded because the error message points
-- somewhere else: `valsCaps?` is NOT just `all valCaps?` — it carries
-- a second conjunct bounding the LIST LENGTH by `suc (cWid c)`
-- (Caps-Face/Part5:809).  A hand-peel that assumes the `all` shape
-- fails with a mismatch reported against `sizeᵉ o ≤ᵇ …`, which reads
-- like an `∧`-association problem and is not one.  `valsCaps?-parts`
-- is the lemma that splits it; use it rather than peeling by hand.
inner-dWO : ∀ {n} {Γ : Ctx n} {u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (o : Val Γ (obs u)) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  dWᵉ n sl o ≤ Caps.cWid (frameStep J c)
inner-dWO {n = n} {u = u} c sl Ψ J o vb =
  ≤-trans (m≤n⊔m (outWᵛ n sl (obs u) o) (dWᵉ n sl o))
          (≤ᵇ⇒≤ (pWᵛ n sl (obs u) o) W (T-to wOK))
  where
  B = Caps.cSize (frameStep J c)
  W = Caps.cWid (frameStep J c)

  vcs : valsCaps? (frameStep J c) sl (o ∷ []) ≡ true
  vcs = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ []))
                      (valsΨ? Ψ (o ∷ [])) vb)

  allv : all (valCaps? (frameStep J c) sl (obs u)) (o ∷ []) ≡ true
  allv = proj₁ (valsCaps?-parts (frameStep J c) sl (o ∷ []) vcs)

  vc : ((sizeᵉ o ≤ᵇ B) ∧ (pWᵛ n sl (obs u) o ≤ᵇ W)) ≡ true
  vc = proj₁ (∧-true ((sizeᵉ o ≤ᵇ B) ∧ (pWᵛ n sl (obs u) o ≤ᵇ W)) true allv)

  wOK : (pWᵛ n sl (obs u) o ≤ᵇ W) ≡ true
  wOK = proj₂ (∧-true (sizeᵉ o ≤ᵇ B) (pWᵛ n sl (obs u) o ≤ᵇ W) vc)

-- Residue postulates for subscribeE-inner-nodry-core.
-- Each names one manufacturing obligation; all seven are consumed by
-- the assembly below.
postulate
  -- Path-size predicate for the extended path from-inner ↠ κ.
  -- frameSz? B (from-inner ...) = true; pathSz? B κ from pb; the gap
  -- is suc (pathLen κ) ≤ B, supplied as the pLen argument.
  subscribeE-inner-nodry-pSz : ∀ {n} {Γ : Ctx n} {t u}
    (c : Caps) (Ψ J : ℕ) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ u t) →
    PbB c Ψ J κ ≡ true →
    suc (suc (pathLen κ)) ≤ Caps.cSize (frameStep J c) →
    pathSz? (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ κ) ≡ true
  -- Path-length bound for the extended path:
  -- suc (pathLen (from-inner … ↠ κ)) = suc (suc (pathLen κ)).
  --
  -- ⚠ SHAPE RISK, FOUND ON REVIEW 2026-08-13 — NOT PROVABLE FROM THE
  -- HYPOTHESES AS STATED, and it matches the known anti-pattern
  -- ("a conclusion needing information that appears in NONE of its
  -- hypotheses", CLAUDE.md).  `pathSz?` (Caps-Face/Part1:307) is
  -- `true` outright on `root` and `share-sink`, and on a cons it
  -- yields the bound for the TAIL:
  --     pathSz? B (f ↠ p) = frameSz? B f ∧ (suc (pathLen p) ≤ᵇ B) ∧ …
  -- so `PbB c Ψ J κ` delivers exactly `suc (pathLen κ) ≤ B`.  The walk
  -- face, applied at `from-inner … ↠ κ`, wants `suc (suc (pathLen κ))
  -- ≤ B`.  ONE UNIT SHORT, and neither OKB (a state predicate) nor the
  -- depth premise (unrelated to B) closes the gap.
  --
  -- This is NOT known false — the caps may well have the slack — it is
  -- UNDERDETERMINED, so the fix is a signature change, not a grind.
  -- The rule that applies is "prefer a free hypothesis to a carried
  -- postulate": thread `suc (suc (pathLen κ)) ≤ cSize (frameStep J c)`
  -- inward from whoever owns the path.  BEWARE: it is NOT free one
  -- level up either — `stepFrame-nodry` holds PbB at `f ↠ path′`, the
  -- very same path, which again gives only `suc (pathLen path′) ≤ B`.
  -- So the slack has to come from further out, and finding where is
  -- the obligation.  Do not grind this postulate; restate the chain.
  subscribeE-inner-nodry-pLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (Ψ J dep : ℕ)
    (κ : Path Γ u t) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e)
    (fuel : Gas) (op : AllOp) (allNid : NodeId) (id : Id) (now : Tick) →
    OKB {e = e} c sl Ψ J sched st →
    PbB c Ψ J κ ≡ true →
    depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
    suc (suc (pathLen κ)) ≤ Caps.cSize (frameStep J c)
  -- Depth bound for the inner subscribeE call.
  -- depthE fuel o (from-inner ... ↠ κ) ... ≤ depthInner (gs fuel) ... ≤ dep.
  subscribeE-inner-nodry-depth : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (Ψ J dep : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
    depthE fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
           (record sched { nextNode = suc (Sched.nextNode sched) }) st ≤ dep
  -- INV? at the inner frame's level, assembled from OKB + regP? ledger
  -- + the two SLOT bounds.  Conjunct by conjunct: stBounded? and
  -- regsSz? are capsOK?'s own; fnCapBounded? is OKB's second conjunct;
  -- regsB? recombines capsOK?'s regsSz? with regP?'s pathBΨ? half
  -- (regsB?-of-parts, .Caps-Bridge — DOWNSTREAM of this module, so the
  -- proof either relocates it or inlines all-zip); registry-count is
  -- frameStep-reg≤size (.Caps-Bridge:151, PROVEN); and the two slot
  -- conjuncts are the added hypotheses.
  --
  -- ⚠ SHAPE DEFECT FOUND AND REPAIRED 2026-08-13 — the SAME anti-pattern
  -- as `-pLen` above ("a conclusion needing information that appears in
  -- NONE of its hypotheses"), caught by reading the definitions rather
  -- than by a failed grind.  INV?'s last two conjuncts are
  -- `slotsSize (Sched.slots sched) ≤ᵇ B` and `slotsFnCap … ≤ᵇ Ψ`, and
  -- the ORIGINAL hypothesis list could reach NEITHER: OKB is
  -- `walkOK × fnCapBounded?`, `walkOK` is `slots-eq × capsOK?`, and
  -- capsOK? bounds live/nodes/registry/widths — it never bounds the
  -- SLOT STORE's size or fn-weight, and fnCapBounded? reads only
  -- live/nodes.  `PbB`/`VbB` are about the path and the value.  So the
  -- statement was UNDERDETERMINED, not hard.
  --
  -- The repair is the sanctioned one ("prefer a free hypothesis to a
  -- carried postulate"), and it is nearly free because it MIRRORS a
  -- hypothesis already threaded at every level of this stack:
  -- `slotsSize sl ≤ cSize c` was present all the way down (so that
  -- conjunct was always reachable and only the transport was unstated);
  -- its Ψ-side twin `slotsFnCap sl ≤ Ψ` was simply missing, and is now
  -- threaded beside it through -core, subscribeE-inner-nodry and
  -- SiNodry.  At the true instantiation Ψ := ΨAt e sl is
  -- `fnCapᵉ e + slotsFnCap sl`, so the new hypothesis is `m≤n+m` — the
  -- same way `caps-fuel-root` (.Wet/Part6) already discharges it.
  --
  -- CLASS: this row was carried as FALSITY and is neither false nor
  -- merely hard — it was SHAPE.  With the hypotheses threaded it is
  -- DIFFICULTY: every remaining conjunct has a named proven source.
  subscribeE-inner-nodry-inv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sched : Sched Γ) (st : EvalSt e) →
    slotsSize sl ≤ Caps.cSize c →
    slotsFnCap sl ≤ Ψ →
    OKB {e = e} c sl Ψ J sched st →
    regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
    INV? Ψ (Caps.cSize (frameStep J c)) sched st ≡ true
  -- pathB? for the extended path.
  -- frameB? B Ψ (from-inner ...) = true; pathB? B Ψ κ from PbB.
  subscribeE-inner-nodry-pBO : ∀ {n} {Γ : Ctx n} {t u}
    (c : Caps) (Ψ J : ℕ) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ u t) →
    PbB c Ψ J κ ≡ true →
    pathB? (Caps.cSize (frameStep J c)) Ψ (from-inner op allNid inst ↠ κ) ≡ true
  -- Gas bound at the inner call: fuel hasAtLeast suc G.
  -- Follows from gk (gs fuel ≡ budgetAt e sl id) via budget-hasAtLeast
  -- and dBound monotonicity; the gs-peel is why this descends here.
  -- RESTATED 2026-08-13 at the RESET caps Ŝ := sizeCapAt e sl (suc id):
  -- the walk face's reset-anchor pins reject the old level-cap
  -- instantiation (frameStep J c cannot ceiling a walk that climbs
  -- past J), and the reset caps are where budget-hasAtLeast actually
  -- lives — budgetAt e sl id is minted from e's entry measures, so
  -- this form is the MORE provable one.
  subscribeE-inner-nodry-fuel : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (fuel : Gas)
    (op : AllOp) (allNid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
    (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    nest o sl (EvalSt.connectedShares st) ≤ bud →
    depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
    gs fuel ≡ budgetAt e sl id →
    fuel hasAtLeast suc (dBound (sizeCapAt e sl (suc id))
                                (hopR (sizeCapAt e sl (suc id)))
                                (unconn sl (EvalSt.connectedShares st))
                                (hopDᵉ (sizeCapAt e sl (suc id)) o)
                                (syncSizeᵉ o))

-- THE ASSEMBLY.  Applies the walk face at the inner frame's (c , J),
-- manufacturing the walk face's hypotheses from the existing context.
-- The hasDry conjunct (conjunct 8 of the 9-conjunct Σ, 0-indexed) is
-- extracted by the p2…p9 projection chain, exactly as in
-- subscribeE-wet-core.  The ℓ degeneracy bites: dBound degenerates at
-- zero hops/shares; fix is ℓ = B + (suc (pathLen κ) + G) (mirrors the
-- B + (pathLen κ + G) fix in subscribeE-wet-core).
subscribeE-inner-nodry-core : WalkLevel → ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling; see SiNodry
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) J) c)
    ≤ sizeCapAt e sl (suc id) →
  gs fuel ≡ budgetAt e sl id →
  hasDry (proj₁ (subscribeE fuel o
           (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
           (record sched { nextNode = suc (Sched.nextNode sched) }) st))
    ≡ false
subscribeE-inner-nodry-core wl {n} {Γ} {t} {e} {u}
    c sl Ψ dep bud 2≤S 1≤R slC slSz slFc
    J fuel op allNid κ id now o sched st ok pb vb rg nB hD cl gk =
  dry
  where
  inst   = Sched.nextNode sched
  sched' = record sched { nextNode = suc inst }
  B      = Caps.cSize (frameStep J c)
  -- the demand at the RESET caps (the pins' Ŝ), not the level cap:
  -- the level cap cannot ceiling the climb, and cl anchors it
  Ŝr     = sizeCapAt e sl (suc id)
  L̂      = opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) J
  G      = dBound Ŝr (hopR Ŝr) (unconn sl (EvalSt.connectedShares st))
                  (hopDᵉ Ŝr o) (syncSizeᵉ o)
  ℓ      = B + (suc (pathLen κ) + G)

  -- slots unchanged by nextNode bump (definitional)
  slEq : Sched.slots sched' ≡ sl
  slEq = proj₁ (proj₁ ok)

  -- capsOK? definitionally ignores nextNode
  cOK : capsOK? (frameStep J c) sched' st ≡ true
  cOK = proj₂ (proj₁ ok)

  -- size of o: VbB → valsCaps? → all → valCaps? → sizeᵛ (obs u) o ≤ B
  vcaps : valsCaps? (frameStep J c) sl (o ∷ []) ≡ true
  vcaps = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ [])) (valsΨ? Ψ (o ∷ [])) vb)
  vcall : all (valCaps? (frameStep J c) sl (obs u)) (o ∷ []) ≡ true
  vcall = proj₁ (∧-true _ (length (o ∷ []) ≤ᵇ suc (Caps.cWid (frameStep J c))) vcaps)
  vc : valCaps? (frameStep J c) sl (obs u) o ≡ true
  vc = proj₁ (∧-true (valCaps? (frameStep J c) sl (obs u) o) _ vcall)
  szO : sizeᵉ o ≤ B
  szO = ≤ᵇ⇒≤ (sizeᵉ o) B (T-to (proj₁ (∧-true _ _ vc)))

  -- fnCap of o: VbB → valsΨ? → valΨ? → fnCapᵛ (obs u) o ≤ Ψ
  vΨ : valsΨ? Ψ (o ∷ []) ≡ true
  vΨ = proj₂ (∧-true (valsCaps? (frameStep J c) sl (o ∷ [])) (valsΨ? Ψ (o ∷ [])) vb)
  vΨ-hd : valΨ? Ψ (obs u) o ≡ true
  vΨ-hd = proj₁ (∧-true (valΨ? Ψ (obs u) o) _ vΨ)
  fnO : fnCapᵉ o ≤ Ψ
  fnO = ≤ᵇ⇒≤ (fnCapᵉ o) Ψ (T-to vΨ-hd)

  -- path-length bound for from-inner ↠ κ (residue)
  pLen' = subscribeE-inner-nodry-pLen c sl Ψ J dep κ o sched st fuel op allNid id now ok pb hD

  -- regsLen? ℓ via capsOK⇒regsLen + regsLen?-mono
  regsO : regsLen? ℓ (EvalSt.registry st) ≡ true
  regsO = regsLen?-mono B ℓ (EvalSt.registry st) (m≤m+n B _)
            (capsOK⇒regsLen (frameStep J c) sched st (proj₂ (proj₁ ok)))

  W = wl o c Ψ Ŝr Ŝr (hopR Ŝr) G ℓ L̂ dep bud (suc (sizeᵉ o)) J
         fuel (from-inner op allNid inst ↠ κ) id now sl sched' st
         2≤S 1≤R slEq slC slSz cOK szO
         (inner-dWO c sl Ψ J o vb)
         (subscribeE-inner-nodry-pSz c Ψ J op allNid inst κ pb pLen')
         pLen' nB ≤-refl
         (subscribeE-inner-nodry-depth c sl Ψ J dep fuel op allNid κ id now o sched st ok hD)
         (subscribeE-inner-nodry-inv c sl Ψ J sched st slSz slFc ok rg)
         fnO
         (subscribeE-inner-nodry-pBO c Ψ J op allNid inst κ pb)
         -- the reset-anchor pins: floor from the entry lemma, F/R̂ by
         -- construction, ceiling from the caller's cl, budget ≤-refl
         (2≤capsAt-size e sl (suc id)) refl refl cl ≤-refl
         ≤-refl
         (subscribeE-inner-nodry-fuel c sl Ψ dep bud J fuel op allNid κ id now o sched st
                                      ok nB hD gk)
         (m≤n+m (suc (pathLen κ) + G) B)
         regsO

  j′  = proj₁ W
  p2  = proj₂ W
  p3  = proj₂ p2
  p4  = proj₂ p3
  p5  = proj₂ p4
  p6  = proj₂ p5
  p7  = proj₂ p6
  p8  = proj₂ p7
  p9  = proj₂ p8
  dry = proj₁ p9

subscribeE-inner-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling; see SiNodry
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) J) c)
    ≤ sizeCapAt e sl (suc id) →
  gs fuel ≡ budgetAt e sl id →
  hasDry (proj₁ (subscribeE fuel o
           (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
           (record sched { nextNode = suc (Sched.nextNode sched) }) st))
    ≡ false
subscribeE-inner-nodry = subscribeE-inner-nodry-core subscribeE-walk-level

-- EX-POSTULATE.  Two clauses, and the dry one is now impossible by
-- construction rather than by hypothesis.
subscribeInner-nodry : SiNodry
subscribeInner-nodry {e = e} c sl Ψ dep bud 2≤S 1≤R slC slSz slFc J g op allNid
                     κ id now o sched st ok pb vb rg nB hD cl gk
  with budgetAt-gs e sl id
... | g′ , eq
      rewrite trans gk eq =
      splitBurst-nodry
        (proj₁ (subscribeE g′ o
                 (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
                 (record sched { nextNode = suc (Sched.nextNode sched) }) st))
        (subscribeE-inner-nodry c sl Ψ dep bud 2≤S 1≤R slC slSz slFc J g′ op allNid
           κ id now o sched st ok pb vb rg nB hD cl (sym eq))

postulate
  -- from-inner: `innerReact` absorbs or finishes; `innerFinish`'s only
  -- emitting arm is concatᵒ's `concatDrain`, whose events are
  -- `subscribeInner`'s, looped over the queue.  The loop is the whole
  -- obligation: re-establish the leaf's state-dependent hypotheses
  -- after each queue element, per the (A) ruling above.
  --
  -- PARKED 2026-08-13 (tier-0 focus moved to the walk face's hasDry /
  -- regsLen? conjuncts).  RESUMPTION PLAN, from the wind-down census:
  -- every arm except concatᵒ + `just (concat-st q true od)` + yes refl
  -- emits `[]`.  That arm is `concatDrain`, whose queue invariant is
  -- `all (obsCaps? (frameStep j c) sl) q ≡ true` — exactly what
  -- capsOK?'s node conjunct gives for the concat-st node, and exactly
  -- the invariant `concatDrain-caps` (Subscribe-Face:1674) already
  -- threads; crib its shape with the caps conjuncts swapped for
  -- `any dryEvent ≡ false` via the SiNodry leaf.
  --
  -- ⚠ NEW OBLIGATION 2026-08-13, UNMEASURED: the SiNodry leaf now
  -- carries the reset-anchor ceiling (`cSize (frameStep (opIterD …) c)
  -- ≤ sizeCapAt e sl (suc id)`), so this loop must PAY it per element,
  -- at its own c and the element's own nest/size — a postulated
  -- consumer absorbs a hypothesis silently, so nothing has checked the
  -- loop can.  Via opIterD-dominated the payment needs the element's
  -- nest/ops bounds under cSize c, dep under capsH, and the J-shifted
  -- budget under the J = 0 one (the sadd/mono tower).  The payer
  -- anchors are the dry-tick chain's own (caps-tick, cascade-depth-
  -- capsH) — plausible, NOT verified.  Same note on thruOuter below.
  innerReact-nodry-core : SiNodry →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
    2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    ∀ (J : ℕ) {s} (sf : Gas) (id : Id) (now : Tick)
    (op : AllOp) (allNid inst : NodeId)
    (path′ : Path Γ s t) (vals : List (Val Γ s))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    PbB c Ψ J (from-inner op allNid inst ↠ path′) ≡ true →
    VbB c sl Ψ J vals ≡ true →
    regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
    sf ≡ budgetAt e sl id →
    depthFrame sf id now (from-inner op allNid inst) path′ vals fin sched st ≤ d →
    any dryEvent
        (proj₁ (proj₂ (stepFrame sf id now (from-inner op allNid inst)
                                 path′ vals fin sched st)))
      ≡ false

  -- thru-outer: `thruWrap` passes events through untouched; `thruWalk`
  -- loops `thruConsume`, whose events are `switchKill`'s (cutThrough,
  -- free) plus `subscribeInner`'s.  Same loop obligation as above.
  --
  -- PARKED 2026-08-13, same wind-down census.  RESUMPTION PLAN: the
  -- body reduces to `thruWalk`'s events (thruWrap passes bs through in
  -- every arm); the induction is `thruWalk-caps` (Subscribe-Face:1593)
  -- with per-arm `thruConsume` handling cribbed from `thruConsume-caps`
  -- (:1377).  One gap the census surfaced: SiCFace is subscribeInner's
  -- face, not thruConsume's — re-establishing capsOK? after a
  -- thruConsume arm additionally needs `capsOK?-setNode` /
  -- `capsOK?-mergeBump` / `switchKill-caps` added to the .Caps-Face
  -- import block (switchKill-caps sits at Caps-Face/Part4:1619,
  -- exported through the Part5→…→Caps-Face chain).
  --
  -- ⚠ NEW OBLIGATION 2026-08-13: owes the SiNodry ceiling per element,
  -- exactly as innerReact-nodry-core above — see that note.
  thruOuter-nodry-core : SiNodry →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
    2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    ∀ (J : ℕ) {u} (sf : Gas) (id : Id) (now : Tick)
    (op : AllOp) (nid : NodeId)
    (path′ : Path Γ u t) (vals : List (Val Γ (obs u)))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    PbB c Ψ J (thru-outer op nid ↠ path′) ≡ true →
    VbB c sl Ψ J vals ≡ true →
    regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
    sf ≡ budgetAt e sl id →
    depthFrame sf id now (thru-outer op nid) path′ vals fin sched st ≤ d →
    any dryEvent
        (proj₁ (proj₂ (stepFrame sf id now (thru-outer op nid)
                                 path′ vals fin sched st)))
      ≡ false

-- take's dispatch: the non-cut arm emits nothing, the cutting arm
-- emits cutThrough's closes.  Unconditional — no gas, no caps, no level
takeDispatch-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  any dryEvent (proj₁ (proj₂ (takeDispatch {t = t} nid vals fin sched st ns)))
    ≡ false
takeDispatch-nodry nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = cutThrough-nodry nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                               (EvalSt.dying st) (EvalSt.registry st)
... | false = refl
takeDispatch-nodry nid vals fin sched st nothing                  = refl
takeDispatch-nodry nid vals fin sched st (just (scan-st _))       = refl
takeDispatch-nodry nid vals fin sched st (just (merge-st _ _))    = refl
takeDispatch-nodry nid vals fin sched st (just (concat-st _ _ _)) = refl
takeDispatch-nodry nid vals fin sched st (just (switch-st _ _))   = refl
takeDispatch-nodry nid vals fin sched st (just (exhaust-st _ _))  = refl

stepFrame-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
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
  sf ≡ budgetAt e sl id →
  depthFrame sf id now f path′ vals fin sched st ≤ d →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))
    ≡ false

-- MAP: the frame emits nothing at all
stepFrame-nodry c sl Ψ d 2≤S 1≤R slC slSz J sf id now
                (map-f fn) path′ vals fin sched st _ _ _ _ _ _ = refl

-- SCAN: every arm of the node-state dispatch emits `[]`
stepFrame-nodry c sl Ψ d 2≤S 1≤R slC slSz J {u = u} sf id now
                (scan-f fn nid) path′ vals fin sched st _ _ _ _ _ _
  with lookupNode nid (EvalSt.nodes st)
... | nothing                  = refl
... | just (take-st _)         = refl
... | just (merge-st _ _)      = refl
... | just (concat-st _ _ _)   = refl
... | just (switch-st _ _)     = refl
... | just (exhaust-st _ _)    = refl
... | just (scan-st {w} acc) with w ≟ᵗ u
...   | yes refl = refl
...   | no  _    = refl

-- TAKE: the one severing frame, and it is free (cutThrough-nodry)
stepFrame-nodry c sl Ψ d 2≤S 1≤R slC slSz J sf id now
                (take-f nid) path′ vals fin sched st _ _ _ _ _ _ =
  takeDispatch-nodry nid vals fin sched st (lookupNode nid (EvalSt.nodes st))

-- the two *All edges: delegated whole, hypotheses passed verbatim
stepFrame-nodry c sl Ψ d 2≤S 1≤R slC slSz J sf id now
                (from-inner op allNid inst) path′ vals fin sched st
                ok pb vb rg gk hD =
  innerReact-nodry-core subscribeInner-nodry
                   c sl Ψ d 2≤S 1≤R slC slSz J sf id now op allNid inst
                   path′ vals fin sched st ok pb vb rg gk hD

stepFrame-nodry c sl Ψ d 2≤S 1≤R slC slSz J sf id now
                (thru-outer op nid) path′ vals fin sched st
                ok pb vb rg gk hD =
  thruOuter-nodry-core subscribeInner-nodry
                  c sl Ψ d 2≤S 1≤R slC slSz J sf id now op nid
                  path′ vals fin sched st ok pb vb rg gk hD

------------------------------------------------------------------
-- THE FRAME FACE, ASSEMBLED (stepFrame-burst-face) — ex-postulate, now a definition.
--
-- Six obligations, FIVE of them off `stepFrame-face`'s single call:
-- the level bound, `capsOK?`, `valsCaps?` and the events caps half
-- verbatim, and `regP? (pathSz? …)` via `capsOK?-regs` on that same
-- `capsOK?`.  The Σ's mixed conjuncts recombine caps and Ψ halves
-- pointwise — `regP?-∧` for the registry, `∧-intro` for values and
-- events.  All the Ψ content comes from `wet-face`, which is Ψ-pure
-- since the FrameFace move (`FrameFace`'s header); the nodry third
-- comes from `stepFrame-nodry`, fed by the new gas hypothesis.
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
  sf ≡ budgetAt e sl id →
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
                     ok pb vb rg gk hD =
    j′
  , proj₁ (proj₂ FC)
  , ((proj₁ WF , wCaps) , proj₁ (proj₂ WF))
  , ∧-intro capsVals (proj₁ (proj₂ (proj₂ WF)))
  , regP?-∧ (pathSz? (Caps.cSize (frameStep (J + j′) c))) (pathBΨ? Ψ)
      (EvalSt.registry t′)
      (capsOK?-regs (frameStep (J + j′) c) s′ t′ wCaps)
      (proj₁ (proj₂ (proj₂ (proj₂ WF))))
  , ∧-intro capsEvs
      (∧-intro (proj₂ (proj₂ (proj₂ (proj₂ WF))))
               (not-in (stepFrame-nodry c sl Ψ d 2≤S 1≤R slC slSz
                          J sf id now f path′ vals fin sched st
                          ok pb vb rg gk hD)))
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
-- THE INSTANTIATION — every closure fact a real proof.
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
  ebC J es h = proj₁ (∧-true (all (eventCaps? (frameStep J c) sl) es)
                             (eventsΨ? Ψ es ∧ not (any dryEvent es)) h)

  ebΨ : ∀ (J : ℕ) (es : List (InstEvent (Val Γ t))) → EbB c sl Ψ J es ≡ true →
        eventsΨ? Ψ es ≡ true
  ebΨ J es h = proj₁ (∧-true (eventsΨ? Ψ es) (not (any dryEvent es))
                 (proj₂ (∧-true (all (eventCaps? (frameStep J c) sl) es)
                                (eventsΨ? Ψ es ∧ not (any dryEvent es)) h)))

  ebD : ∀ (J : ℕ) (es : List (InstEvent (Val Γ t))) → EbB c sl Ψ J es ≡ true →
        not (any dryEvent es) ≡ true
  ebD J es h = proj₂ (∧-true (eventsΨ? Ψ es) (not (any dryEvent es))
                 (proj₂ (∧-true (all (eventCaps? (frameStep J c) sl) es)
                                (eventsΨ? Ψ es ∧ not (any dryEvent es)) h)))

  bbC : ∀ (J : ℕ) (str : Stream Γ t) → BbB c sl Ψ J str ≡ true →
        burstCaps? (frameStep J c) sl str ≡ true
  bbC J str h = proj₁ (∧-true (burstCaps? (frameStep J c) sl str)
                              (burstΨ? Ψ str ∧ not (hasDry str)) h)

  bbΨ : ∀ (J : ℕ) (str : Stream Γ t) → BbB c sl Ψ J str ≡ true →
        burstΨ? Ψ str ≡ true
  bbΨ J str h = proj₁ (∧-true (burstΨ? Ψ str) (not (hasDry str))
                 (proj₂ (∧-true (burstCaps? (frameStep J c) sl str)
                                (burstΨ? Ψ str ∧ not (hasDry str)) h)))

  bbD : ∀ (J : ℕ) (str : Stream Γ t) → BbB c sl Ψ J str ≡ true →
        not (hasDry str) ≡ true
  bbD J str h = proj₂ (∧-true (burstΨ? Ψ str) (not (hasDry str))
                 (proj₂ (∧-true (burstCaps? (frameStep J c) sl str)
                                (burstΨ? Ψ str ∧ not (hasDry str)) h)))

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

  -- the nodry mirrors: a mapped value and an optional complete carry
  -- no dried close by construction
  mv-nodry : ∀ (vs : List (Val Γ t)) →
    any dryEvent (map value vs) ≡ false
  mv-nodry []       = refl
  mv-nodry (v ∷ vs) = mv-nodry vs

  ft-nodry : ∀ (fin : Bool) →
    any (dryEvent {Val Γ t}) (if fin then complete ∷ [] else []) ≡ false
  ft-nodry true  = refl
  ft-nodry false = refl

  -- one delivery emit is dry-free exactly when its event list is:
  -- hasDry (em ∷ []) = any dryEvent es ∨ false, and the ∨ collapses
  -- once the left side is known false
  nodry-one : ∀ (es : List (InstEvent (Val Γ t))) (id : Id) (src : Source)
    (k : EmitKind) →
    any dryEvent es ≡ false →
    not (hasDry ((es at id from src as k) ∷ [])) ≡ true
  nodry-one es id src k h =
    subst (λ x → not (x ∨ false) ≡ true) (sym h) refl

  burstH : Walk-Hyps e S W R d
  burstH = record
    { OK        = OKB {e = e} c sl Ψ
    ; Pb        = PbB c Ψ
    ; Vb        = VbB c sl Ψ
    ; Eb        = EbB c sl Ψ
    ; Bb        = BbB c sl Ψ
    -- THE GAS HOOK, SPENT (2026-08-13, the anchor ruling, `cascadeGo-nodry`'s header): the
    -- nodry flavour is gas-conditioned, so GOK pins the frame gas to
    -- the one gas the walk mints.  g-mint is the walk's own slotsEq
    ; GOK       = λ sf id → sf ≡ budgetAt e sl id
    ; g-mint    = λ J id sched st ok →
                    cong (λ s → budgetAt e s id) (proj₁ (proj₁ ok))
    ; e-nil     = λ _ → refl
    ; e-close   = λ _ _ → refl
    ; e-app     = λ J es₁ es₂ h₁ h₂ →
                    ∧-intro (all-++-intro _ es₁ es₂ (ebC J es₁ h₁) (ebC J es₂ h₂))
                    (∧-intro (all-++-intro _ es₁ es₂ (ebΨ J es₁ h₁) (ebΨ J es₂ h₂))
                             (not-in (any-dry-++ es₁ es₂
                                        (not-out (ebD J es₁ h₁))
                                        (not-out (ebD J es₂ h₂)))))
    ; e-widen   = λ {J} {J′} le es h →
                    ∧-intro (eventsCaps?-widen sl es (frameStep-mono-j c 2≤S le)
                              (ebC J es h))
                            (∧-intro (ebΨ J es h) (ebD J es h))
    ; b-nil     = λ _ → refl
    ; b-app     = λ J s₁ s₂ h₁ h₂ →
                    ∧-intro (all-++-intro _ s₁ s₂ (bbC J s₁ h₁) (bbC J s₂ h₂))
                    (∧-intro (all-++-intro _ s₁ s₂ (bbΨ J s₁ h₁) (bbΨ J s₂ h₂))
                             (not-in (hasDry-append s₁ s₂
                                        (not-out (bbD J s₁ h₁))
                                        (not-out (bbD J s₂ h₂)))))
    ; b-widen   = λ {J} {J′} le str h →
                    ∧-intro (burstCaps?-widen sl str (frameStep-mono-j c 2≤S le)
                              (bbC J str h))
                            (∧-intro (bbΨ J str h) (bbD J str h))
    ; b-deliv   = λ J id src evs vals fin hE hV →
                    ∧-intro
                      (∧-intro (all-++-intro _ evs _ (ebC J evs hE)
                                 (all-++-intro _ (map value vals) _
                                   (mv-caps (frameStep J c) vals
                                     (vsC-all (frameStep J c) vals (vbC J vals hV)))
                                   (ft-caps (frameStep J c) fin)))
                               refl)
                      (∧-intro
                        (∧-intro (all-++-intro _ evs _ (ebΨ J evs hE)
                                   (all-++-intro _ (map value vals) _
                                     (mv-Ψ vals (vbΨ J vals hV))
                                     (ft-Ψ fin)))
                                 refl)
                        (nodry-one
                          (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
                          id src delivery
                          (any-dry-++ evs
                            (map value vals ++ (if fin then complete ∷ [] else []))
                            (not-out (ebD J evs hE))
                            (any-dry-++ (map value vals)
                              (if fin then complete ∷ [] else [])
                              (mv-nodry vals) (ft-nodry fin)))))
    ; b-handoff = λ J id src evs i hE →
                    ∧-intro
                      (∧-intro (all-++-intro _ evs _ (ebC J evs hE) refl) refl)
                      (∧-intro
                        (∧-intro (all-++-intro _ evs _ (ebΨ J evs hE) refl) refl)
                        (nodry-one (evs ++ handoff (toℕ i) ∷ []) id src delivery
                          (any-dry-++ evs (handoff (toℕ i) ∷ [])
                            (not-out (ebD J evs hE)) refl)))
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
    ; sf-step   = λ J sf id now f path′ vals fin sched st ok pb vb rg gk hD →
                    stepFrame-burst-face siC ifc {e = e} c sl Ψ d 2≤S 1≤R slC slSz
                      J sf id now f path′ vals fin sched st ok pb vb rg gk hD
    }

  module V = Walk {e = e} S W R d 2≤S burstH

------------------------------------------------------------------
-- THE PAYOFF (cascadeGo-burst-nodry) — the walk/cascade burst content, at Ŝ, with no Dm,
-- AND the cascade's dry half, off the SAME run (2026-08-13).
--
-- The level arithmetic is `cascadeGo-caps`'s own (Caps-Face:4901),
-- cribbed term for term: Res.cnt through dWalkᶜ-mono and cDel-body,
-- Res.hi through lvls-mono and sizeCount-body.  Then capsAt-suc-full
-- lands the widened caps half on capsAt (suc id) — whose cSize IS
-- sizeCapAt e sl (suc id) — and `burstB?-halves` recombines with the constant Ψ
-- half.  The nodry half projects straight off the third flavour at
-- the landing level — dryness is level-independent, so it needs no
-- widening at all.  The consumer (dry-tick-core's telescope,
-- .Caps-Bridge) owns every hypothesis: caps facts from the caps-tick
-- chain, Ψ facts by projection from INV? (valB-fc, regsB?,
-- pathBΨ?-of), the depth from cascade-depth-capsH.
------------------------------------------------------------------

cascadeGo-burst-nodry : SiCFace → IfcFace →
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
  (burstB? (sizeCapAt e sl (suc id)) Ψ
           (proj₁ (cascadeGo a id chains sched st)) ≡ true)
  × (hasDry (proj₁ (cascadeGo a id chains sched st)) ≡ false)
cascadeGo-burst-nodry siC ifc {n = n} {e = e} id a chains sched st
                      slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD =
  burstB?-halves (capsAt e sl (suc id)) sl Ψ (proj₁ cg)
    (subst (λ x → burstCaps? x sl (proj₁ cg) ≡ true)
           (sym (capsAt-suc-full e sl id))
           (burstCaps?-widen sl (proj₁ cg)
              (frameStep-mono-j c 2≤S lvl-fits)
              (BW.bbC (BW.V.Res.lvl GO) (proj₁ cg) (BW.V.Res.burst GO))))
    (BW.bbΨ (BW.V.Res.lvl GO) (proj₁ cg) (BW.V.Res.burst GO))
  , not-out (BW.bbD (BW.V.Res.lvl GO) (proj₁ cg) (BW.V.Res.burst GO))
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
-- THE EX-ANCHOR (cascadeGo-nodry) — the cascade's dry half, now TWO PROJECTIONS of
-- the `cascadeGo-burst-nodry` run (2026-08-13; postulate → definition).
--
-- THE RULING THAT DISCHARGED IT: the dry half rides the walk as a
-- THIRD, GAS-CONDITIONED ledger flavour (`EbB`/`BbB`), spending the GOK/g-mint
-- hook the walk was built with (.Delivery-Walk).  Every transport
-- law proved mechanical exactly as the route predicted — appends by
-- `hasDry-append`/`any-dry-++`, seeds and deliveries by computation
-- (`dryEvent` is false on value/init/close-exhausted/handoff/complete),
-- widens for free (dryness is level-independent).  What remains is the
-- per-frame face, `stepFrame-nodry`, where the WHOLE of the
-- anchor's former risk now lives — one named postulate whose from-inner
-- case consumes the COLLAPSED walk face (`subscribeE-walk-level`,
-- .Walk-Level), the statement built to be satisfiable mid-delivery.
--
-- WHAT THIS MOVE BUYS, in risk-ledger terms: `cascadeGo-nodry` and
-- `subscribeE-wet-core` used to be two independent FALSITY rows.  Both
-- now bottom out in `subscribeE-walk-level` (the wet core by
-- instantiation, the anchor through `subscribeInner-nodry`), so the
-- tier-0 risk CONSOLIDATES onto one statement — plus `stepFrame-nodry`'s two named
-- manufacture obligations, (i) mid-delivery INV? and (ii) the
-- general-id fuel, each a crib of a proven sibling.
--
-- History (mirror census 2026-08-12, demand-side probe 2026-08-13,
-- the can't-probe receipt): superseded by this discharge; recover the
-- full text from the parent of the landing commit if the route ever
-- needs re-litigating.  The can't-probe receipt SURVIVES on `stepFrame-nodry`'s header,
-- restated there.
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
cascadeGo-burst-dry siC ifc id a chains sched st
                    slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD =
  proj₁ (cascadeGo-burst-nodry siC ifc id a chains sched st
           slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD)

cascadeGo-nodry : SiCFace → IfcFace →
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
  hasDry (proj₁ (cascadeGo a id chains sched st)) ≡ false
cascadeGo-nodry siC ifc id a chains sched st
                slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD =
  proj₂ (cascadeGo-burst-nodry siC ifc id a chains sched st
           slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD)
