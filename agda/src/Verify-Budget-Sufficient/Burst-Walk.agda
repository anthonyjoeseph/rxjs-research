------------------------------------------------------------------
-- BURST-WALK: the THREE-flavour burst ledger over the Delivery-Walk —
-- the walk/cascade burst content landed at Ŝ with no tower constant,
-- and (2026-08-13) the cascade's DRY half off the same run: the third
-- flavour is `nodry`, gas-conditioned through the walk's GOK hook, and
-- `cascadeGo-nodry` — the ex-anchor — is now a projection of `cascadeGo-burst-nodry`.  The
-- anchor's risk lives in ONE per-frame face, `stepFrame-nodry` (its own header carries the census).
--
-- Landed from Caps-Burst-Walk-Probe (DELETED; git history) (2026-08-10), which
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
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; s≤s; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ; ≤⇒≤ᵇ; ≤ᵇ⇒≤; m≤m+n; m≤n+m; m≤n⊔m;
         m≤m⊔n; n≤1+n)
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
                           gasPad; gasTower; towerℕ;
                           InstEmit; _at_from_as_; EmitKind; delivery)
open import Rx.Exp  using (Ty; Ctx; Closed; Val; obs; Fn; applyFn; _×ᵗ_; _≟ᵗ_; sizeᵉ; syncSizeᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; Slots; Arrival; RegId; Chain; Path; Frame;
         _↠_; root; share-sink;
         map-f; scan-f; take-f; from-inner; thru-outer; Stream;
         stepFrame; cascadeGo; dropSource; shareLatch; shareFinish; slotsSize;
         hasDry; dryEvent; budgetAt; capsHgo; capsBase;
         arrTy; arrVal; fLvlD; opIterD; regAt; subscribeInner; subscribeE;
         splitBurst; splitEvents; sLvlD; sIterD; sIterD-suc; sizeAt;
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
         ∧-intro; ∧-true; all-++-intro;
         opIterD-infl; capsAt-base-size; 6≤capsAt-size; tower-3; capsAt-tower)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthCascade; depthInner; depthFin; depthE; depthDrain)

open import Verify-Budget-Sufficient.Caps-Nest using (nest)

-- THE LEVEL DESCENTS, spent by the thru walk's ceiling channel.  The wet
-- walk face already threads an abstract ceiling level and converts it to
-- each callee's budget with these; the nodry face now does the same, which
-- is what took the per-element ceiling off an unstated fLvlD inequality.
open import Verify-Budget-Sufficient.Caps-Chain using (walk-desc; inner-desc)
open import Verify-Budget-Sufficient.Caps using (sIterD-mono)

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; walkOK; walkOK-finish; slotsCaps?;
         valCaps?; valsCaps?; eventCaps?; burstCaps?;
         eventsCaps?-widen; burstCaps?-widen; valsCaps?-lvl; valsCaps?-parts;
         pathSz?-len; pathSz?-tail; pathSz?-widen;
         capsOK?-count; capsOK?-delivered; capsOK?-regs; shareLatch-caps;
         frameStep-mono-j; frameStep-0; stepFrame-face; frameBud;
         -- the inner-at-suc-J kit, cribbed from subscribeInner-caps
         frameStep-chain-suc; pathSz?-⊑; capsOK?-mono;
         -- the size half of the recombination lemmas below
         frameSz?; regsSz?;
         -- the node ring: capsOK? bounds every stored node, and the lookup
         -- projects that bound onto the one node a clause is looking at
         NodeCaps; lookupNode-caps; capsOK?-nodeSz; capsOK?-nodeWid;
         boundedNode; widNode)

open import Verify-Budget-Sufficient.Wet
  using (burstB?; eventB?; valB?; sizeCapAt; ΨAt;
         B2-cReg≤cSize;
         fnCapBounded?; fcB-live; fcB-nodes; sweepLive-fnCap;
         fnCapᵛ; fnCapᵉ; caseWᵗ; fnCapᵗ; applyFn-fnCap; pathLen; T-to; T⇒≡true;
         fnCapLive; fnCapNode; setNode-fnCap; scanVals-fnCap;
         hasDry-append; ∨-false; ≤ᵇ-widen;
         INV?; INV?-widen; dBound; regsLen?; hopR; unconn; pathB?; pathB?-widen;
         frameB?; regsB?; all-zip;
         _hasAtLeast_;
         slotsFnCap;
         dBound-bound; prod≤3pow; unconn≤slots; syncSize≤sizeᵉ; slotHop-cap;
         hasAtLeast-pad-plus; hasAtLeast-tower; hasAtLeast-mono)
open import Verify-Budget-Sufficient.Walk-Level
  using (WalkLevel; subscribeE-walk-level; capsOK⇒regsLen; regsLen?-mono;
         any-dry-++; splitEvents-nodry; splitBurst-nodry;
         switchKill-closes-nodry; thruWrap-pass)
open import Verify-Budget-Sufficient.Psi-Split
open import Rx.Frame-Width using (pWᵉ)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Frame-Width using (dWᵉ; dWᵛ; pWᵛ; outWᵛ)


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

-- any-dry-++ MOVED DOWN to .Walk-Level (2026-08-14), with the whole
-- dry trio: the ground subscribeInner-walk consumes it there, and this
-- module sits above .Walk-Level.  Imported back below.

-- VbB's HEAD AND TAIL PROJECTIONS.  `thruConsume-nodry-vb` in the block below
-- is the head projection stated again at one instantiation (`Val Γ (obs u)` IS
-- `Closed Γ s`, per Rx/Exp's definition of `Val`).  Both are `all` over a cons
-- and nothing more, so they are proven here once and the callers spend them —
-- which is what the concat side does: one receipt minted per node lookup
-- (`concatNode-vb`), then projected down the drain's recursion.
--
-- The length conjunct is why these are lemmas rather than `refl`: `valsCaps?`
-- carries `length vs ≤ᵇ suc (cWid c)` beside the per-element `all`, so the
-- head needs `1 ≤ᵇ suc _` and the tail needs the bound to survive dropping a
-- cons.  Both hold, and neither is definitional in the list.
VbB-head : ∀ {n} {Γ : Ctx n} {s}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (o : Val Γ s) (os : List (Val Γ s)) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  VbB c sl Ψ J (o ∷ []) ≡ true
VbB-head {s = s} c sl Ψ J o os h
  with ∧-true (valsCaps? (frameStep J c) sl (o ∷ os)) (valsΨ? Ψ (o ∷ os)) h
... | hc , hΨ
  with ∧-true (all (valCaps? (frameStep J c) sl s) (o ∷ os))
              (length (o ∷ os) ≤ᵇ suc (Caps.cWid (frameStep J c))) hc
... | hall , _ =
  -- ∧-true's Bool arguments are EXPLICIT, per this module's standing note:
  -- `all` over a cons reduces to a conjunction Agda cannot recover from the
  -- equation alone, so underscores here leave one unsolved meta per projection.
  ∧-intro
    (∧-intro
      (∧-intro (proj₁ (∧-true (valCaps? (frameStep J c) sl s o)
                              (all (valCaps? (frameStep J c) sl s) os) hall))
               refl)
      refl)
    (∧-intro (proj₁ (∧-true (valΨ? Ψ s o) (all (valΨ? Ψ s) os) hΨ)) refl)

VbB-tail : ∀ {n} {Γ : Ctx n} {s}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (o : Val Γ s) (os : List (Val Γ s)) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  VbB c sl Ψ J os ≡ true
VbB-tail {s = s} c sl Ψ J o os h
  with ∧-true (valsCaps? (frameStep J c) sl (o ∷ os)) (valsΨ? Ψ (o ∷ os)) h
... | hc , hΨ
  with ∧-true (all (valCaps? (frameStep J c) sl s) (o ∷ os))
              (length (o ∷ os) ≤ᵇ suc (Caps.cWid (frameStep J c))) hc
... | hall , hlen =
  -- The length conjunct drops a cons, so it goes through ≤ rather than
  -- ≤ᵇ-widen: the widen's B is `cWid C` only AFTER `suc … ≤ᵇ suc …` reduces,
  -- and Agda will not run that reduction backwards to solve for B.
  ∧-intro
    (∧-intro (proj₂ (∧-true (valCaps? (frameStep J c) sl s o)
                            (all (valCaps? (frameStep J c) sl s) os) hall))
             (T⇒≡true (length os ≤ᵇ suc (Caps.cWid (frameStep J c)))
               (≤⇒≤ᵇ (≤-trans (n≤1+n (length os))
                              (≤ᵇ⇒≤ (length (o ∷ os))
                                    (suc (Caps.cWid (frameStep J c)))
                                    (T-to hlen))))))
    (proj₂ (∧-true (valΨ? Ψ s o) (all (valΨ? Ψ s) os) hΨ))

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
-- Landed from SubscribeInner-Psi-Probe (DELETED; git history).  Pattern mirrors
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
  Caps.cReg c ≤ Caps.cSize c →
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
  -- THE PATH-LENGTH HYPOTHESIS, IN THE CAPS FACE'S OWN SHAPE (2026-08-15).
  -- This is `lC` verbatim from subscribeE-caps / subscribeInner-caps, and
  -- that is the point: WalkStmt's hypotheses ARE the caps face's, so the wet
  -- inner call has no business asking for a different one.
  --
  -- It previously asked for `suc (suc (pathLen κ))` at level J — one unit
  -- more than any caller could produce.  The unit had nowhere to come from
  -- because the wet core was subscribing the inner at level J while the
  -- PROVEN twin `subscribeInner-caps` (.Subscribe-Face) subscribes at
  -- `suc j`: "the inner is subscribed under one more frame, at the same
  -- instant, and at ONE MORE j".  Extending a path without paying the frame
  -- is what made the bound unreachable; paying it makes `frameStep-chain-suc`
  -- deliver the extra unit exactly where the walk face wants it.
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner g op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling (2026-08-13): the walk face's pins force
  -- the honest instantiation Ŝ := sizeCapAt e sl (suc id), and this is
  -- the c-to-entry anchoring the caller owns (c is free here; the
  -- caller knows it is capsAt-rooted).  The face's budget at this
  -- call's arguments stays under the next instant's size cap.
  -- AT suc J, matching the level the inner is now subscribed at (see the
  -- path-length hypothesis above).  L̂ is opIterD's value at the level the
  -- walk face is actually applied at, so bumping the call bumps this too.
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) (suc J)) c)
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

-- THE SAME FACT WITH THE PAD COUNT KEPT (2026-08-15).  budgetAt-gs
-- existentially quantifies the GAS, which is all its own consumers need —
-- but a caller that wants a hasAtLeast bound needs the ℕ pad, since
-- hasAtLeast-pad-plus is indexed by it.  The body above already computes
-- that number and then discards it behind `Σ Gas`, so the strengthening is
-- free: same `with`, return the ℕ instead of the gas built from it.
--
-- This exists because subscribeE-inner-nodry-fuel was written against
-- budgetAt-gs as though its witness were the pad count.  It is not, and the
-- mismatch does not surface as a missing hypothesis — it surfaces as
-- `Gas !=< ℕ` deep inside an arithmetic chain, which is why the assembly
-- read as complete until a real check ran.
budgetAt-gs-pad : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id) →
  Σ ℕ (λ k → budgetAt e sl id
               ≡ gs (gasPad k (gasTower (3 + capsHgo (capsBase e sl) (suc id)))))
budgetAt-gs-pad e sl id
  with 2^-pos ((sizeᵉ e + slotsSize sl) * suc id * suc id)
... | k , eq rewrite eq = k , refl

-- splitEvents-nodry / splitBurst-nodry MOVED DOWN to .Walk-Level
-- (2026-08-14), with any-dry-++: the ground subscribeInner-walk
-- consumes the split there.  Imported back through the module import.

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
-- subscribeE-inner-nodry-pSz and -pLen are BOTH GONE (2026-08-15), and they
-- fell to the same one-line change: the inner call now subscribes at `suc J`,
-- matching the PROVEN twin subscribeInner-caps.
--   · -pLen was an identity returning a bound nothing could supply.  With the
--     level bump, `frameStep-chain-suc` DERIVES it from the caps face's own lC.
--   · -pSz manufactured pathSz? at the extended path.  It existed only because
--     at level J its length conjunct was unreachable; at suc J the core builds
--     it inline as `pC′`, exactly as subscribeInner-caps builds its own.
-- The lesson is worth more than the two rows: a postulate whose hypotheses
-- cannot supply its conclusion is often not a hard lemma but a MISPLACED CALL,
-- and the proven twin is where to look for the placement.
--   RECOVERY: git show 4a76fff restores the identity form and the analysis
--   that led here, if the level bump ever has to be undone.

postulate
  -- INV? at the inner frame's level, assembled from OKB + regP? ledger
  -- + the two SLOT bounds.  Conjunct by conjunct: stBounded? and
  -- regsSz? are capsOK?'s own; fnCapBounded? is OKB's second conjunct;
  -- regsB? recombines capsOK?'s regsSz? with regP?'s pathBΨ? half
  -- (regsB?-of-parts — RELOCATED INTO THIS MODULE 2026-08-20, above,
  -- beside the Ψ predicates it consumes; it previously sat in
  -- .Caps-Bridge, downstream, and that placement was this row's only
  -- blocker.  Nothing had to move DOWN and no all-zip inlining is
  -- needed: .Caps-Bridge was downstream of all three ingredient
  -- families, so the lemmas were simply left behind when the Ψ
  -- predicates themselves were relocated here on 2026-08-10);
  -- registry-count is
  -- frameStep-reg≤size (.Caps, PROVEN — the citation here read
  -- ".Caps-Bridge:151" and that line is unrelated comment text); and the two slot
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
  -- merely hard — it was SHAPE.  With the hypotheses threaded it was
  -- DIFFICULTY, blocked on the placement above rather than on
  -- mathematics; with that relocated it is GRINDABLE.  Every conjunct
  -- now has a named source IN SCOPE — the recombination lemma above,
  -- PROVEN frameStep-reg≤size (.Caps-Bridge:151), capsOK?'s own two,
  -- OKB's second, and the two threaded slot hypotheses — so what is
  -- left is assembling six conjuncts, with nothing to decide.
  subscribeE-inner-nodry-inv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sched : Sched Γ) (st : EvalSt e) →
    slotsSize sl ≤ Caps.cSize c →
    slotsFnCap sl ≤ Ψ →
    OKB {e = e} c sl Ψ J sched st →
    regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
    INV? Ψ (Caps.cSize (frameStep J c)) sched st ≡ true
  -- pathB? for the extended path — GRINDABLE, and it is THREE LINES:
  --   ∧-intro refl (pathB?-of-parts κ (proj₁ (∧-true _ _ pb))
  --                                   (proj₂ (∧-true _ _ pb)))
  -- `frameB? B Ψ (from-inner _ _ _) = true` gives the head by `refl`, and
  -- `pathB?-of-parts` — PROVEN, IN THIS MODULE above the block since the
  -- 2026-08-20 relocation — recombines PbB's pathSz? and pathBΨ? halves
  -- into pathB?.  It was previously in .Caps-Bridge, downstream, which is
  -- why this row's route used to elide the recombination step and read as
  -- vaguer than it is.  `pathB?` carries no length conjunct, which is what
  -- keeps it cheap.
-- pathB? FOR THE EXTENDED PATH — a real body since 2026-08-20, and it is
-- three lines.  `frameB? B Ψ (from-inner _ _ _) = true` (.Measures) gives the
-- head by `refl`, and `pathB?-of-parts` — PROVEN above in this module since
-- the relocation that moved it out of downstream .Caps-Bridge — recombines
-- PbB's `pathSz?` and `pathBΨ?` halves into the real `pathB?` that INV?
-- reads.  `pathB?` carries no length conjunct, which is what keeps it cheap.
--
-- ∧-true's Bool arguments are EXPLICIT here on purpose: `PbB` reduces to a
-- conjunction Agda cannot recover from the equation alone, the same reason
-- the from-inner strip in .Caps-Bridge spells them out.
subscribeE-inner-nodry-pBO : ∀ {n} {Γ : Ctx n} {t u}
  (c : Caps) (Ψ J : ℕ) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ u t) →
  PbB c Ψ J κ ≡ true →
  pathB? (Caps.cSize (frameStep J c)) Ψ (from-inner op allNid inst ↠ κ) ≡ true
subscribeE-inner-nodry-pBO c Ψ J op allNid inst κ pb =
  ∧-intro refl
    (pathB?-of-parts κ
      (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb))
      (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)))

-- Gas bound at the inner call: fuel hasAtLeast suc G.
-- ASSEMBLED 2026-08-14: follows from gk via budgetAt-gs (gs-peel) and the
-- demand chain dBound-bound → prod≤3pow → tower-3 → m≤n+m.  sizeᵉ o ≤ Ŝr
-- hypothesis added (was missing; derives at call site from szO via
-- frameStep-mono-j + opIterD-infl + the caller's cl ceiling).
-- RESTATED 2026-08-13 at the RESET caps Ŝ := sizeCapAt e sl (suc id):
-- the walk face's reset-anchor pins reject the old level-cap
-- instantiation (frameStep J c cannot ceiling a walk that climbs
-- past J), and the reset caps are where budget-hasAtLeast actually
-- lives — budgetAt e sl id is minted from e's entry measures, so
-- this form is the MORE provable one.
-- SEALED 2026-08-15.  This was a POSTULATE the wet spine consumed as an
-- axiom; discharging it makes the body transparent to Verify-Well-Formed,
-- which is the exact transition that OOMed the first full build after
-- wet-landing-lift's discharge tonight (`Killed: 9` in VWF/Part13; a fourth
-- instance of the trap, figures in typecheck-performance-numbers.md).  No
-- consumer needs more than the type.  private-impl + abstract-alias rather
-- than a plain `abstract` block, because the body has a with-abstraction
-- and untyped where-bindings, both of which `abstract` rejects.
-- The type is NAMED rather than written twice: private-impl + abstract-alias
-- needs the signature at both sites, and duplicating a type this size made
-- Agda elaborate it twice.  Measured on the Walk-Level twin the same night,
-- that cost more memory than the seal saved.  Same idiom as SiNodry above.
InnerNodryFuel : Set
InnerNodryFuel = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (fuel : Gas)
  (op : AllOp) (allNid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  gs fuel ≡ budgetAt e sl id →
  sizeᵉ o ≤ sizeCapAt e sl (suc id) →
  fuel hasAtLeast suc (dBound (sizeCapAt e sl (suc id))
                              (hopR (sizeCapAt e sl (suc id)))
                              (unconn sl (EvalSt.connectedShares st))
                              (hopDᵉ (sizeCapAt e sl (suc id)) (slotHop (sizeCapAt e sl (suc id)) sl) o)
                              (syncSizeᵉ o))

private
  subscribeE-inner-nodry-fuel-go : InnerNodryFuel
  subscribeE-inner-nodry-fuel-go {e = e} c sl Ψ dep bud J fuel op allNid κ id now o sched st
      ok nB hD gk sz≤Ŝr
    with budgetAt-gs-pad e sl id
  ... | k , eq =
    hasAtLeast-mono demand fuelH
    where
    Ŝr      = sizeCapAt e sl (suc id)
    H       = 3 + capsHgo (capsBase e sl) (suc id)
    U       = unconn sl (EvalSt.connectedShares st)
    6≤V     : 6 ≤ Ŝr
    -- 6≤capsAt-size is the ONE lemma in this family whose CONCLUSION
    -- already carries the suc (`6 ≤ cSize (capsAt e sl (suc id))`), unlike
    -- 2≤capsAt-size / capsAt-base-size / capsAt-tower, which conclude at
    -- the id they are given.  Passing `suc id` here lands a level too high
    -- and the mismatch surfaces as an iterSize term, not as an index error.
    6≤V     = 6≤capsAt-size e sl id
    slots≤V : slotsSize sl ≤ Ŝr
    slots≤V = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl (suc id))
    U≤V     : U ≤ Ŝr
    U≤V     = ≤-trans (unconn≤slots sl (EvalSt.connectedShares st)) slots≤V
    s≤V     : syncSizeᵉ o ≤ Ŝr
    s≤V     = ≤-trans (syncSize≤sizeᵉ o) sz≤Ŝr
    r≤R     : hopDᵉ Ŝr (slotHop Ŝr sl) o ≤ hopR Ŝr
    r≤R     = slotHop-cap Ŝr sl (2≤capsAt-size e sl (suc id)) slots≤V o sz≤Ŝr
    gs-inj  : ∀ {a b : Gas} → gs a ≡ gs b → a ≡ b
    gs-inj refl = refl
    fuelIs  : fuel ≡ gasPad k (gasTower H)
    fuelIs  = gs-inj (trans gk eq)
    -- PARENTHESISED ON PURPOSE: _hasAtLeast_ binds tighter than _+_, so
    -- `g hasAtLeast k + towerℕ H` parses as `(g hasAtLeast k) + towerℕ H`
    -- — a Set added to a ℕ, reported as "ℕ should be a sort" rather than
    -- as a precedence problem.
    fuelH   : fuel hasAtLeast (k + towerℕ H)
    fuelH   = subst (λ g → g hasAtLeast (k + towerℕ H)) (sym fuelIs)
                    (hasAtLeast-pad-plus k (hasAtLeast-tower H))
    D       = dBound Ŝr (hopR Ŝr) U (hopDᵉ Ŝr (slotHop Ŝr sl) o) (syncSizeᵉ o)
    demand  : suc D ≤ k + towerℕ H
    demand  =
      ≤-trans (s≤s (dBound-bound s≤V r≤R))
      (≤-trans (prod≤3pow Ŝr U 6≤V U≤V)
      (≤-trans (tower-3 (capsH e sl (suc id)) Ŝr (proj₁ (capsAt-tower e sl (suc id))))
               (m≤n+m (towerℕ H) k)))


abstract
  subscribeE-inner-nodry-fuel : InnerNodryFuel
  subscribeE-inner-nodry-fuel = subscribeE-inner-nodry-fuel-go

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
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling; see SiNodry
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) (suc J)) c)
    ≤ sizeCapAt e sl (suc id) →
  gs fuel ≡ budgetAt e sl id →
  hasDry (proj₁ (subscribeE fuel o
           (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
           (record sched { nextNode = suc (Sched.nextNode sched) }) st))
    ≡ false
subscribeE-inner-nodry-core wl {n} {Γ} {t} {e} {u}
    c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
    J fuel op allNid κ id now o sched st ok pb sspLen vb rg nB hD cl gk =
  dry
  where
  inst   = Sched.nextNode sched
  sched' = record sched { nextNode = suc inst }
  B      = Caps.cSize (frameStep J c)
  -- the demand at the RESET caps (the pins' Ŝ), not the level cap:
  -- the level cap cannot ceiling the climb, and cl anchors it
  Ŝr     = sizeCapAt e sl (suc id)
  L̂      = opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) (suc J)
  G      = dBound Ŝr (hopR Ŝr) (unconn sl (EvalSt.connectedShares st))
                  (hopDᵉ Ŝr (slotHop Ŝr sl) o) (syncSizeᵉ o)
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

  -- sizeᵉ o ≤ Ŝr: from szO (sizeᵉ o ≤ B) via the monotone J ≤ L̂ step
  sz≤Ŝr : sizeᵉ o ≤ Ŝr
  -- J ≤ opIterD … (suc J): one step up to suc J, then opIterD's own
  -- inflation at that level.  The cl ceiling now anchors at suc J, so the
  -- old `opIterD-infl … J` no longer meets it.
  sz≤Ŝr = ≤-trans szO
            (≤-trans (proj₁ (frameStep-mono-j c 2≤S
                               (≤-trans (n≤1+n J)
                                        (opIterD-infl (Caps.cSize c) (Caps.cWid c)
                                                      dep bud (suc (sizeᵉ o)) (suc J)))))
                     cl)

  -- THE PATH-LENGTH BOUND, DERIVED (2026-08-15) — cribbed from
  -- subscribeInner-caps, which pays the same unit the same way: extend the
  -- path by a frame, subscribe at one more j, and the chain bound carries.
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n J)
  B′     = Caps.cSize (frameStep (suc J) c)
  -- every caps-indexed hypothesis the walk face wants must move up with the
  -- level, exactly as subscribeInner-caps widens its own
  cOK′   : capsOK? (frameStep (suc J) c) sched' st ≡ true
  cOK′   = capsOK?-mono (frameStep J c) (frameStep (suc J) c) sched' st step⊑ cOK

  -- pathSz? AT THE EXTENDED PATH, BUILT rather than postulated.  This is
  -- subscribeInner-caps' `pC′` verbatim: the head frame is free (refl), the
  -- new length conjunct is the widened lC, and κ's own chain rides
  -- pathSz?-⊑ up the step.  Building it is what retires
  -- subscribeE-inner-nodry-pSz — the postulate existed only because the
  -- inner call sat at J, where the length conjunct was unreachable.
  pC     : pathSz? (Caps.cSize (frameStep J c)) κ ≡ true
  pC     = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                         (pathBΨ? Ψ κ) pb)
  pC′    : pathSz? B′ (from-inner op allNid inst ↠ κ) ≡ true
  pC′    = ∧-intro refl
             (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                        (≤⇒≤ᵇ (≤-trans sspLen (proj₁ step⊑))))
                      (pathSz?-⊑ κ step⊑ pC))
  pLen'  : suc (suc (pathLen κ)) ≤ B′
  pLen'  = frameStep-chain-suc c J (pathLen κ) 2≤S sspLen

  -- regsLen? ℓ via capsOK⇒regsLen + regsLen?-mono
  regsO : regsLen? ℓ (EvalSt.registry st) ≡ true
  regsO = regsLen?-mono B ℓ (EvalSt.registry st) (m≤m+n B _)
            (capsOK⇒regsLen (frameStep J c) sched st (proj₂ (proj₁ ok)))

  W = wl o c Ψ Ŝr Ŝr (hopR Ŝr) G ℓ L̂ dep bud (suc (sizeᵉ o)) (suc J)
         fuel (from-inner op allNid inst ↠ κ) id now sl sched' st
         2≤S 1≤R hCR slEq slC slSz cOK′ (≤-trans szO (proj₁ step⊑))
         (≤-trans (inner-dWO c sl Ψ J o vb) (proj₁ (proj₂ step⊑)))
         pC′
         pLen' nB ≤-refl
         hD
         (INV?-widen sched' st (proj₁ step⊑)
            (subscribeE-inner-nodry-inv c sl Ψ J sched st slSz slFc ok rg))
         fnO
         (pathB?-widen (from-inner op allNid inst ↠ κ) (proj₁ step⊑)
            (subscribeE-inner-nodry-pBO c Ψ J op allNid inst κ pb))
         -- the reset-anchor pins: floor from the entry lemma, F/R̂ by
         -- construction, ceiling from the caller's cl, budget ≤-refl
         (2≤capsAt-size e sl (suc id)) refl refl cl ≤-refl
         ≤-refl
         (subscribeE-inner-nodry-fuel c sl Ψ dep bud J fuel op allNid κ id now o sched st
                                      ok nB hD gk sz≤Ŝr)
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
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling; see SiNodry
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) (suc J)) c)
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
subscribeInner-nodry {e = e} c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc J g op allNid
                     κ id now o sched st ok pb sspLen vb rg nB hD cl gk
  with budgetAt-gs e sl id
... | g′ , eq
      rewrite trans gk eq =
      splitBurst-nodry
        (proj₁ (subscribeE g′ o
                 (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
                 (record sched { nextNode = suc (Sched.nextNode sched) }) st))
        (subscribeE-inner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc J g′ op allNid
           κ id now o sched st ok pb sspLen vb rg nB hD cl (sym eq))

-- THE CONCAT NODE'S STORED QUEUE IS VbB-BOUNDED, and this is a real body: the
-- leaves it stands on are all proven, so nothing here is postulated.  It is the
-- receipt `concatDrain-nodry` drains against, and the whole reason that drain is
-- allowed to take one: the queue it is handed is not an arbitrary list but the
-- `q` of a `concat-st` READ OUT OF THE NODE TABLE, which `capsOK?` bounds.
-- `innerReact-nodry` is the single site that performs the lookup, so the receipt
-- is minted there once and projected per element afterwards (`VbB-head` for the
-- element, `VbB-tail` for the recursive call).
--
-- ⚠ THIS REPLACES `concatDrain-nodry-vb`, WHICH WAS REFUTABLE AS WRITTEN.  That
-- statement concluded `VbB c sl Ψ J (o ∷ [])` for an ARBITRARY `o : Closed Γ s`
-- from a hypothesis mentioning only `sched` and `st`, so it quantified over
-- expressions far larger than `cSize c` — a conclusion needing information no
-- hypothesis carried.  Adding a premise is licensed here precisely because the
-- unconditional form is FALSE, and because the premise is a genuine
-- precondition of the operation rather than a convenience of today's call site.
-- Note also what the repair is NOT: `o ∈ q` does not work, since `q` is itself a
-- free parameter of the drain — that relates one unconstrained thing to another.
-- The link has to reach the STATE, which is what makes `allNid` and this
-- equation load-bearing.
--
-- THE CENSUS, one proven source per conjunct of `VbB`, and `capsOK?` reaches
-- `nodes` three times to supply them:
--
--   all (valCaps? …) q     ← boundedNode's `all` (the sizeᵉ half, via
--                             capsOK?-nodeSz) zipped with widNode's first
--                             conjunct (the pWᵉ half, via capsOK?-nodeWid).
--                             `valCaps? C sl (obs s) o` IS that conjunction.
--   length q ≤ᵇ suc (cWid C) ← widNode's SECOND conjunct, `length q ≤ᵇ cWid C`,
--                             widened by one.
--   all (valΨ? …) q        ← fnCapNode's `all`, via OKB's fnCapBounded?
--                             conjunct.  `fnCapᵛ (obs s) o` IS `fnCapᵉ o`.
--
-- ⚠ AND THE LENGTH CONJUNCT IS THE CORRECTION WORTH KEEPING.  Two successive
-- readings of `capsOK?` got this census wrong in opposite directions.  The
-- first found only widNode, concluded the size and fn-cap halves had no source,
-- and proposed a new FIELD on widNode cascading through every producer and
-- consumer of capsOK?.  The second found those two and concluded the LENGTH had
-- no source above it, guessing the bound would have to come from an arrival-
-- ledger induction over the pushes.  Both were false, and for the same reason:
-- the reading stopped early.  `widNode`'s concat clause COUNTS the queue
-- outright.  Read the whole record before concluding a conjunct is unreachable.
--
-- Sealed per the budget-sufficient-spine rule; the `with` on the slots equation
-- is why it is private-impl + abstract-alias rather than a plain block.
private
  concatNode-vb-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (allNid : NodeId)
    (q : List (Closed Γ s)) (act od : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    lookupNode allNid (EvalSt.nodes st) ≡ just (concat-st q act od) →
    VbB c sl Ψ J q ≡ true
  concatNode-vb-go {n = n} c sl Ψ J allNid q act od sched st ok eqN
    with proj₁ (proj₁ ok)
  ... | refl =
    let C   = frameStep J c
        cok = proj₂ (proj₁ ok)
        nc  = subst (NodeCaps C (Sched.slots sched)) eqN
                (lookupNode-caps C (Sched.slots sched) allNid (EvalSt.nodes st)
                   (capsOK?-nodeSz C sched st cok)
                   (capsOK?-nodeWid C sched st cok))
        nf  = subst (NodeΨ Ψ) eqN
                (lookupNode-fnCap Ψ allNid (EvalSt.nodes st)
                   (fcB-nodes Ψ sched st (proj₂ ok)))
        hwq = ∧-true (all (λ o → pWᵉ n (Sched.slots sched) o ≤ᵇ Caps.cWid C) q)
                     (length q ≤ᵇ Caps.cWid C) (proj₂ nc)
    in ∧-intro
         (∧-intro
            (all-zip (λ o → sizeᵉ o ≤ᵇ Caps.cSize C)
                     (λ o → pWᵉ n (Sched.slots sched) o ≤ᵇ Caps.cWid C)
                     _
                     (λ o hsz hwd → ∧-intro hsz hwd)
                     q (proj₁ nc) (proj₁ hwq))
            (≤ᵇ-widen (length q) (n≤1+n (Caps.cWid C)) (proj₂ hwq)))
         nf

abstract
  concatNode-vb : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (allNid : NodeId)
    (q : List (Closed Γ s)) (act od : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    lookupNode allNid (EvalSt.nodes st) ≡ just (concat-st q act od) →
    VbB c sl Ψ J q ≡ true
  concatNode-vb = concatNode-vb-go

-- ─────────────────────────────────────────────────────────────────
-- THE NODRY RESIDUE LEAVES.  `innerReact-nodry` / `thruOuter-nodry` are
-- real bodies that case-split the evaluator's dispatch and APPLY
-- `subscribeInner-nodry` at each arm calling `subscribeInner`; these are
-- what those bodies cannot pay.  Every one is a genuine open obligation
-- and none takes a proven lemma as an argument.
--
-- NOTE ON slFc: slotsFnCap sl ≤ Ψ is THREADED, not postulated.  It is a
-- static capsule invariant that OKB cannot reach — `walkOK` is
-- slots-eq × capsOK?, and capsOK? bounds live/nodes/registry/widths but
-- never the slot store's fn-weight; `fnCapBounded?` reads only
-- live/nodes.  So it rides beside its already-threaded size-side twin
-- `slotsSize sl ≤ cSize c`, all the way down through stepFrame-nodry,
-- innerReact-nodry/thruOuter-nodry and SiNodry, and is a PARAMETER of
-- module BurstWalk.  It costs nothing: at the true instantiation
-- Ψ := ΨAt e sl is `fnCapᵉ e + slotsFnCap sl`, so the whole chain is
-- discharged by `m≤n+m` at cascadeGo-burst-nodry — the same way
-- `caps-fuel-root` (.Wet/Part6) already discharges it.
--
-- NOTE ON ceiling, RESOLVED (2026-08-20): the per-element ceiling is no
-- longer paid from the frame's fused `fLvlD` by an unstated inequality.
-- The thru walk threads an ABSTRACT ceiling level L̂ — `CL`'s own idiom,
-- one flavour down — and converts it to each element's budget with the
-- PROVEN Caps-Chain descents `inner-desc` then `walk-desc`.  The bud then
-- sits in the SAME `k` position on both sides of every step, so the
-- tension the *-nestBud rows were stuck on (one conjunct wants bud large,
-- the other wants it small) leaves the level algebra entirely; what
-- survives is a nest bound with no ceiling coupled to it, and one
-- k-and-index fit at the frame boundary.
--
-- NOTE ON loop invariants: OKB/regP? after each subscribeInner step
-- are left as leaves.  These are the capsOK?-preservation obligations
-- that the caps face (.Subscribe-Face) already proves for its own
-- induction; the nodry face needs its own copy at the same indices.
--
-- NOTE ON nest: mList?-style nest bounds per element are not in
-- stepFrame-nodry's hypotheses.  Each leaf postulate takes the
-- minimum context needed.
postulate

  -- ── innerReact / concatDrain loop leaves ────────────────────────


  -- PINNED 2026-08-20, THEN REFUTED AND RESTATED THE SAME DAY.
  --
  -- THE PIN IS SOUND AND STAYS.  Before it the Σ's only conjunct was
  -- `all (nest … ≤ᵇ bud) q`, UPWARD-CLOSED in bud, so the max over a finite q
  -- discharged it for free — while the consumer needs bud SMALL, feeding the
  -- same bud to opIterD's `k` position where a bigger bud is a higher level and
  -- a harder ceiling.  The free witness was the one witness that could not be
  -- spent.  The ceiling conjunct demands the ceiling AT THAT SAME BUD, so
  -- enlarging the witness now costs something.  Pinning here RETIRED
  -- `concatDrain-nodry-cl`: with the witness arriving already knowing it fits,
  -- there is nothing left to transfer from an fLvlD-level bound.
  --
  -- REFUTED (2026-08-20) in the OKB-only form —
  -- `Refuted.Concat-Drain.concatDrain-nodry-nestBud-absurd`, and checked the
  -- decisive way: the postulate itself, applied to the witness, gave `⊥`.  The
  -- ceiling conjunct measures a cap derived from `c` against
  -- `sizeCapAt e sl (suc id)`, and OKB relates the two NOT AT ALL — it gets
  -- easier as `c` grows, while sizeCapAt reads only `e` and `sl` — so
  -- `cSize c = suc (sizeCapAt e sl 1)` kills it at every bud, whatever the
  -- queue holds.  Conjunct one was unreachable for its own reason: a free
  -- `Closed Γ s` list has no nest bound, which is the retired
  -- `concatDrain-nodry-vb`'s defect arriving one conjunct over.
  --
  -- SO THE TWO ADDED HYPOTHESES ARE A RESTATEMENT AND NOT A CONVENIENCE, one
  -- per conjunct: the fLvlD tie for the ceiling, `VbB` for the nest bound.
  -- `concatDrain-nodry` carried both and passed neither, which is exactly the
  -- reading "the call site happens to supply it" is not allowed to have — the
  -- licence here is the refutation, not the caller.
  --
  -- WHAT REMAINS IS THE ROW'S REAL CONTENT, and it is a tension rather than a
  -- grind: conjunct one wants bud LARGE enough for every element, conjunct two
  -- wants `opIterD S W dep bud (suc (sizeᵉ o)) (suc J) ≤ fLvlD S W dep J` and so
  -- wants it SMALL.  Whether one bud does both is open.  Two sub-facts are
  -- owed and neither exists in the tree: that opIterD/fLvlD inequality (the
  -- block header above calls it "stated as a separate leaf" — it is not, and
  -- `make find Q='fLvlD'` says so), and `nest` from `VbB`'s per-element size
  -- and width bounds.
  concatDrain-nodry-nestBud : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ dep J : ℕ) (id : Id) (allNid : NodeId)
    (q : List (Closed Γ s))
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    VbB c sl Ψ J q ≡ true →
    Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) dep J) c)
      ≤ sizeCapAt e sl (suc id) →
    Σ ℕ (λ bud →
           all (λ o → nest o sl (EvalSt.connectedShares st) ≤ᵇ bud) q ≡ true
         × all (λ o → Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c)
                                                     dep bud (suc (sizeᵉ o)) (suc J)) c)
                        ≤ᵇ sizeCapAt e sl (suc id)) q ≡ true)

  -- Loop invariant after one subscribeInner step in concatDrain.
  -- OKB + regP? are preserved (the caps face proves the caps side;
  -- the nodry face needs its own copy here).
  concatDrain-nodry-loop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sf : Gas)
    (allNid : NodeId) (κ : Path Γ s t)
    (id : Id) (now : Tick) (o : Closed Γ s)
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    OKB {e = e} c sl Ψ J sched₀ st₀ →
    regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
    let r      = subscribeInner sf concatᵒ allNid κ id now o sched₀ st₀
        sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
        st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
    in OKB {e = e} c sl Ψ J sched₁ st₁
       × regP? (PbB c Ψ J) (EvalSt.registry st₁) ≡ true

  -- Nest bound for remaining queue elements after one subscribeInner step.
  -- connectedShares can grow, so bud from state₀ may not bound state₁;
  -- this leaf asserts the invariant holds at the new state.
  concatDrain-nodry-nestRec : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J bud : ℕ) (sf : Gas)
    (allNid : NodeId) (κ : Path Γ s t)
    (id : Id) (now : Tick) (o : Closed Γ s) (q : List (Closed Γ s))
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    OKB {e = e} c sl Ψ J sched₀ st₀ →
    all (λ o′ → nest o′ sl (EvalSt.connectedShares st₀) ≤ᵇ bud) q ≡ true →
    let r      = subscribeInner sf concatᵒ allNid κ id now o sched₀ st₀
        st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
    in all (λ o′ → nest o′ sl (EvalSt.connectedShares st₁) ≤ᵇ bud) q ≡ true

  -- ── thruOuter / thruWalk / thruConsume loop leaves ───────────────

  -- Nest bound for the remaining walk elements after one thruConsume step —
  -- the exact twin of `concatDrain-nodry-nestRec` above, one operator over.
  -- connectedShares can grow, so a bud read at state₀ need not bound state₁.
  --
  -- IT REPLACES `thruConsume-nodry-nestBud` (REFUTED 2026-08-20,
  -- `Refuted.Concat-Drain.thruConsume-nodry-nestBud-absurd`).  That row bundled
  -- a nest bound and a CEILING into one Σ over one witness, and the ceiling
  -- conjunct compared a cap derived from `c` against `sizeCapAt e sl (suc id)`
  -- — two quantities OKB relates not at all, so `cSize c = suc (sizeCapAt e sl 1)`
  -- killed it at every bud.  The ceiling half is now a threaded level (see the
  -- note on ceiling above), which is what let the two halves come apart; the
  -- nest half is this, at a bud the CALLER owns.
  --
  -- THE ROUTE, and the arithmetic half of it is already spent: `nest-keeps`
  -- (.Caps-Nest) reduces this to share-ledger MEMBERSHIP monotonicity across
  -- the step — `nest` is antitone in the connected set, so a bound survives
  -- any ENLARGEMENT of it — and `subscribeE-connected-mono` (.Keeps-Ring) is
  -- that monotonicity for the subscribe underneath.  What is owed is the
  -- thruConsume-level version of that one membership fact.
  thruConsume-nodry-nestRec : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ J bud : ℕ) (sf : Gas)
    (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    OKB {e = e} c sl Ψ J sched₀ st₀ →
    all (λ o′ → nest o′ sl (EvalSt.connectedShares st₀) ≤ᵇ bud) os ≡ true →
    let st₁ = proj₂ (proj₂ (proj₂ (thruConsume sf op nid κ id now o sched₀ st₀)))
    in all (λ o′ → nest o′ sl (EvalSt.connectedShares st₁) ≤ᵇ bud) os ≡ true

  -- ONE ELEMENT'S SIZE, at the level `inner-desc` reads it.  `valsCaps?`
  -- carries a per-element `valCaps?`, whose size half bounds the element at
  -- `Caps.cSize (frameStep J c)`; `inner-desc` wants that bound one level up
  -- and in the `sizeᵉ` spelling the reset-anchor ceiling is stated in.  Both
  -- moves are size-cap arithmetic and NEITHER mentions bud — which is the
  -- point: it is what takes the ceiling descent off the bud entirely.
  thruWalk-nodry-elem-size : ∀ {n} {Γ : Ctx n} {u}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
    (o : Val Γ (obs u)) (os : List (Val Γ (obs u))) →
    2 ≤ Caps.cSize c →
    VbB c sl Ψ J (o ∷ os) ≡ true →
    suc (sizeᵉ o) ≤ suc (sizeAt (Caps.cSize c) (suc J))

  -- THE WALK'S BUD AND ITS ROOM, at the frame boundary — the one thing
  -- `thruOuter-nodry` cannot read off its own premises.  `frame-step`
  -- (.Caps-Chain) opens the frame's own `fLvlD` as an `sIterD` over
  -- `suc (widAt S W J)` payloads at `k = suc (sizeAt S (suc J))`, so the room
  -- conjunct is that k-and-index fit and `walk-index` meets the index on
  -- `valsCaps?`'s length bound.  What is NOT arithmetic is the nest bound,
  -- and that is why this is a Σ and not a pin: both conjuncts pull on the
  -- SAME bud — large enough for every element, small enough for the frame's
  -- k — and neither is upward-closed, so no free witness discharges it.
  --
  -- THE DEPTH PREMISE IS CARRIED because the conclusion needs it: at
  -- `dep = 0` the frame has no nesting allowance at all, and a payload walk
  -- that subscribes cannot fit under `fLvlD S W 0 J`.  `depthFrame` is what
  -- excludes that, so it is a hypothesis rather than a hoped-for side
  -- condition — the shape CLAUDE.md's "conclusion needs information no
  -- hypothesis carries" rule asks for.
  --
  -- THE NEST CONJUNCT'S ROUTE IS KNOWN, AND IT IS STATE-FREE:
  -- `refresh-supplies-nest-strict` (.Caps-Nest § 3) bounds `nest o sl cs` by
  -- `sizeAt S (suc j)` at EVERY share ledger `cs`, out of `sizeᵉ o ≤ sizeAt S j`
  -- and `slotsSize sl ≤ S` — and the frame holds both (`valsCaps?`'s
  -- per-element size half, and the threaded `slSz`).  So the witness is
  -- `bud := sizeAt S (suc J)`, and at that pin the ROOM conjunct's own k fit
  -- is `≤-refl` against `frame-step`'s `suc (sizeAt S (suc j))`.
  --
  -- WHAT IS NOT ASSEMBLED IS THE ROOM CONJUNCT'S SHAPE.  `frame-step`
  -- (.Caps-Chain) converts a `J + j₁ ≤ sIterD …` RECEIPT into a
  -- `J + j₁ ≤ fLvlD S W (suc d) J` one; this row wants the DESCENT form, a
  -- bound on the sIterD value itself, which the descents section does not
  -- yet carry for the frame boundary.  That missing descent is the whole
  -- residue, and it is pure D-tower arithmetic.
  thruOuter-nodry-bud : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ dep J : ℕ) (sf : Gas)
    (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    OKB {e = e} c sl Ψ J sched st →
    VbB c sl Ψ J vals ≡ true →
    depthFrame sf id now (thru-outer op nid) κ vals fin sched st ≤ dep →
    Σ ℕ (λ bud →
           all (λ o → nest o sl (EvalSt.connectedShares st) ≤ᵇ bud) vals ≡ true
         × (sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) J
              ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep J))

  -- Loop invariant after one thruConsume step: OKB + regP? at the level
  -- the step LANDS at, with that level reported.
  --
  -- ⚠ REFUTED IN THE SAME-LEVEL FORM (2026-08-20) — `Refuted.Thru-Loop`,
  -- and the witness computes: `capsOK?` on the post-state evaluates to
  -- `false` while the conclusion demanded `true`.
  --
  -- WHY.  Concat's park clause is a pure GROWTH step: with the node's
  -- inner already active, `thruConsume` appends the element to the node's
  -- queue and emits nothing — which is exactly why the nodry conclusion
  -- is `refl` there, and why nothing else in this block notices.  And
  -- `capsOK?`'s width conjunct bounds that queue's LENGTH
  -- (`widNode`'s `length q ≤ᵇ W`).  A queue sitting AT the cap is one
  -- park from breaching it, and the refuted telescope said nothing about
  -- the queue at all: CLAUDE.md's first almost-always-wrong shape.
  --
  -- IT WAS NOT A ZERO-CAP ARTIFACT: the refutation's caps are read off the
  -- value (cSize 3, cWid 2, both pinned by `refl`), every other conjunct
  -- held with margin, and the only tight one was the length.  Threading
  -- `vb : VbB c sl Ψ J vals` would NOT have repaired it either: VbB bounds
  -- each element, never the queue's length.
  --
  -- THE REPAIR IS A REPORTED LEVEL, NOT A HYPOTHESIS — conditioning on the
  -- queue would be the "call site happens to supply it" trade, since the
  -- walk's SECOND element cannot supply it: the FIRST is what filled the
  -- queue.  So the step reports the level it lands at, and the walk above
  -- re-reads its ledgers there.
  --
  -- AND THE REPORTED CEILING IS `sLvlD`, NOT `fIterD`.  The first reading of
  -- this defect took `pushThru-walk` for the mirror and so wrote the walk's
  -- index as `fIterD` over `length str` — one whole FRAME per payload, which
  -- is the wrong granularity and does not fit under the frame's own charge
  -- (`fLvlD` is inflationary, so k frames cannot sit inside one).  The
  -- mirror is `stepThru-walk`, which measures THIS traversal — a value list
  -- inside one frame — against `sIterD S W dep (suc bud) (length vals) j`,
  -- one `sLvlD` per payload.  Diffing the two mirrors' ARGUMENTS is what
  -- separated them; their statements read alike.
  --
  -- IT WAS CLASSED GRINDABLE on the grounds that it is pure preservation,
  -- hypothesis P at state₀ and conclusion P at state₁.  That reading is
  -- the trap: preservation is only cheap when the step cannot grow the
  -- thing preserved, and this step exists to grow it.  Shape-checking a
  -- statement against `hypothesis ⇒ conclusion` says nothing about the
  -- STEP in between.
  thruConsume-nodry-loop : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (sf : Gas)
    (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    OKB {e = e} c sl Ψ J sched₀ st₀ →
    regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
    let r      = thruConsume sf op nid κ id now o sched₀ st₀
        sched₁ = proj₁ (proj₂ (proj₂ r))
        st₁    = proj₂ (proj₂ (proj₂ r))
    in Σ ℕ (λ j′ →
            OKB {e = e} c sl Ψ (J + j′) sched₁ st₁
          × regP? (PbB c Ψ (J + j′)) (EvalSt.registry st₁) ≡ true
          × (J + j′ ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc J)))

  -- ── thruWalk recursion leaves ────────────────────

  thruWalk-nodry-dep : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ dep J : ℕ) (sf : Gas)
    (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    OKB {e = e} c sl Ψ J sched₀ st₀ →
    depthFrame sf id now (thru-outer op nid) κ (o ∷ os) false sched₀ st₀ ≤ dep →
    let r      = thruConsume sf op nid κ id now o sched₀ st₀
        sched₁ = proj₁ (proj₂ (proj₂ r))
        st₁    = proj₂ (proj₂ (proj₂ r))
    in depthFrame sf id now (thru-outer op nid) κ os false sched₁ st₁ ≤ dep

  -- ── switch arm leaves ─────────────────────────────────────────────

  -- OKB + regP? after switchKill; needed by the switch arm's subscribeInner-nodry call.
  -- The nest bound across a switchKill.  The switch arm reads its nest
  -- budget at the PRE-kill state and spends it at the POST-kill one, and
  -- `switchKill` touches the share ledger, so the two are different
  -- readings of `connectedShares`.  Level-free and caps-free: the whole
  -- claim is that killing a subscription does not raise anyone's nesting.
  -- Same route as `thruConsume-nodry-nestRec` below: `nest-keeps` plus one
  -- membership fact about this step's share ledger.
  switchKill-nest : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
    (sl : Slots Γ) (bud : ℕ) (cur : Maybe NodeId) (o : Val Γ (obs u))
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    nest o sl (EvalSt.connectedShares st₀) ≤ bud →
    nest o sl (EvalSt.connectedShares
                 (proj₂ (proj₂ (switchKill cur sched₀ st₀)))) ≤ bud

  switchKill-context : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
    (cur : Maybe NodeId)
    (sched₀ : Sched Γ) (st₀ : EvalSt e) →
    OKB {e = e} c sl Ψ J sched₀ st₀ →
    regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
    let sched₁ = proj₁ (proj₂ (switchKill cur sched₀ st₀))
        st₁    = proj₂ (proj₂ (switchKill cur sched₀ st₀))
    in OKB {e = e} c sl Ψ J sched₁ st₁
       × regP? (PbB c Ψ J) (EvalSt.registry st₁) ≡ true

------------------------------------------------------------------
-- concatDrain-nodry — structural recursion over the concat queue.
-- Applies subscribeInner-nodry at each element (THE FIT TEST).
--
-- slFc is taken as a direct parameter, threaded from module BurstWalk.
concatDrain-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ dep : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  -- THE QUEUE'S RECEIPT, minted once by `concatNode-vb` at the node lookup in
  -- `innerReact-nodry` and projected per element here.  A genuine
  -- precondition and not a convenience of the call site: the unconditional
  -- per-element form (the retired `concatDrain-nodry-vb`) is refutable,
  -- because nothing ties a free `Closed Γ s` to this state.
  VbB c sl Ψ J q ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) dep J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthDrain sf allNid κ id now q sched st ≤ dep →
  any dryEvent (proj₁ (proj₂ (concatDrain sf allNid κ id now q sched st))) ≡ false

concatDrain-nodry c sl Ψ dep 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                  [] sched st _ _ _ _ _ _ _ _ = refl

concatDrain-nodry c sl Ψ dep 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                  (o ∷ q) sched₀ st₀ ok pb sspLen vbq rg gk cl hD
  with concatDrain-nodry-nestBud c sl Ψ dep J id allNid (o ∷ q) sched₀ st₀ ok vbq cl
... | bud , nestQ , clQ
  -- Scrutinise only `done` (4th component).  This preserves
  -- `proj₁ (proj₂ (proj₂ (subscribeInner ...)))` (3rd component) in the goal
  -- so that subscribeInner-nodry's return type matches directly.
  with proj₁ (proj₂ (proj₂ (proj₂ (subscribeInner sf concatᵒ allNid κ id now o sched₀ st₀))))
... | false =
  -- done=false: concatDrain returns the element's events; goal = subscribeInner-nodry's type
  subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
    J sf concatᵒ allNid κ id now o sched₀ st₀
    ok pb sspLen
    (VbB-head c sl Ψ J o q vbq)
    rg
    (≤ᵇ⇒≤ (nest o sl (EvalSt.connectedShares st₀)) bud
      (T-to (proj₁ (∧-true _ _ nestQ))))
    (≤-trans (m≤m⊔n _ _) hD)
    (≤ᵇ⇒≤ (Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c)
                                          dep bud (suc (sizeᵉ o)) (suc J)) c))
           _
           (T-to (proj₁ (∧-true _ _ clQ))))
    gk
... | true =
  -- done=true: concatDrain appends element events ++ tail events
  let sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (subscribeInner sf concatᵒ allNid κ id now o sched₀ st₀)))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (subscribeInner sf concatᵒ allNid κ id now o sched₀ st₀)))))
      bs     = proj₁ (proj₂ (proj₂ (subscribeInner sf concatᵒ allNid κ id now o sched₀ st₀)))
      h-head = subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
                 J sf concatᵒ allNid κ id now o sched₀ st₀
                 ok pb sspLen
                 (VbB-head c sl Ψ J o q vbq)
                 rg
                 (≤ᵇ⇒≤ (nest o sl (EvalSt.connectedShares st₀)) bud
                   (T-to (proj₁ (∧-true _ _ nestQ))))
                 (≤-trans (m≤m⊔n _ _) hD)
                 (≤ᵇ⇒≤ (Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c)
                                                       dep bud (suc (sizeᵉ o)) (suc J)) c))
                        _
                        (T-to (proj₁ (∧-true _ _ clQ))))
                 gk
      loop   = concatDrain-nodry-loop c sl Ψ J sf allNid κ id now o sched₀ st₀ ok rg
      ok₁    = proj₁ loop
      rg₁    = proj₂ loop
      nestQ′ = concatDrain-nodry-nestRec c sl Ψ J bud sf allNid κ id now o q sched₀ st₀
                 ok (proj₂ (∧-true _ _ nestQ))
      h-tail = concatDrain-nodry c sl Ψ dep 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                 q sched₁ st₁ ok₁ pb sspLen (VbB-tail c sl Ψ J o q vbq) rg₁ gk cl
                 (≤-trans (m≤n⊔m _ _) hD)
  in any-dry-++ bs _ h-head h-tail

------------------------------------------------------------------
-- thruConsume-nodry — per-element nodry proof for one thruConsume step.
-- Applies subscribeInner-nodry in each arm that calls subscribeInner.
thruConsume-nodry : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (os : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthFrame sf id now (thru-outer op nid) κ (o ∷ os) false sched st ≤ dep →
  -- THE CEILING, at an ABSTRACT LEVEL.  The walk cannot hand every element
  -- the frame's own `fLvlD`: that level is one whole frame's climb, and
  -- `fLvlD` being inflationary, k of them do not fit inside one.  So the
  -- ceiling arrives at a level L̂ the walk owns, and this element's own
  -- operator sweep is placed under it.
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) (suc J) ≤ L̂ →
  any dryEvent (proj₁ (proj₂ (thruConsume sf op nid κ id now o sched st))) ≡ false

-- helper: apply subscribeInner-nodry for one thruConsume call.
--
-- The depth premise (`depthFrame … ≤ dep`) and the size-cap premise are
-- DELIBERATELY ABSENT: the body derives both element-level facts from
-- `ok` via thruConsume-nodry-dep / -nestBud, so neither was ever an
-- ingredient.  Carrying them was not merely redundant — `depthFrame`
-- unfolds through `thruConsume`, so in the concat/exhaust arms (whose
-- clauses sit under a `with` on `lookupNode`) the premise's type is
-- stated against the ABSTRACTED scrutinee while the caller's `hD` is
-- stated against the unabstracted one, and the two are compared at
-- `Sched Γ` and differ.  Dropping the dead premises removes the
-- comparison entirely.  This STRENGTHENS the helper (fewer hypotheses).
thruConsume-nodry-apply : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (os : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthInner sf op nid κ id now o sched st ≤ dep →
  -- THE CEILING, threaded rather than conjured, and now at an abstract
  -- level: the *-nestBud form that manufactured a bud AND a ceiling out of
  -- `ok` alone was refutable in both halves (Refuted.Concat-Drain), so both
  -- arrive from the caller and the level descent does the rest.
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) (suc J) ≤ L̂ →
  any dryEvent (proj₁ (proj₂ (proj₂ (subscribeInner sf op nid κ id now o sched st)))) ≡ false
thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now o os sched st ok pb sspLen vb rg gk hD-elem nBst clL̂ dsc =
  subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
    J sf op nid κ id now o sched st
    ok pb sspLen (VbB-head c sl Ψ J o os vb) rg nBst hD-elem
    (≤-trans (proj₁ (frameStep-mono-j c 2≤S dsc)) clL̂) gk

-- MERGE: one subscribeInner call, events = bs
thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) (≤-trans (n≤1+n _) hD)) nBst clL̂ dsc

-- CONCAT: dispatch on node state
-- The scrutinee and the clause ORDER both mirror Rx.Evaluator's own
-- `with w ≟ᵗ u` exactly.  Writing `w ≟ᵗ _` here does not abstract the
-- goal's occurrence (the metavariable is not syntactically the
-- evaluator's `u`), leaving the with-function stuck and `refl` red.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st)
-- concat active=true + type match: parks the element, emits []
... | just (concat-st {w} q true od) with w ≟ᵗ u
...   | yes refl = refl
...   | no _    = refl
-- concat active=false: subscribes, emits bs.  The `{u = u}` binder is
-- repeated on every full-LHS clause of this with-block: the nested
-- `with` above forces the repeats, and an LHS that omits it does not
-- line up with the first clause, leaving the goal's `thruConsume`
-- stuck on its own `lookupNode` with-scrutinee.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (concat-st q false od) =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) (≤-trans (n≤1+n _) hD)) nBst clL̂ dsc
-- other node shapes: thruConsume's own catch-all emits [].  These are
-- enumerated rather than written `| _`, because a VARIABLE scrutinee
-- leaves the evaluator's with-function stuck — its catch-all only fires
-- once Agda knows the shape is none of the concat cases.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | nothing = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (scan-st _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (take-st _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (merge-st _ _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (switch-st _ _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf concatᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (exhaust-st _ _) = refl

-- SWITCH: switchKill (closes only, nodry by switchKill-closes-nodry)
--         + subscribeInner (bs, nodry by SiNodry), combined by any-dry-++
thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf switchᵒ nid κ id now o os sched₀ st₀ ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st₀)
-- NO `with subscribeInner …` here.  Scrutinising the tuple rebinds its
-- third component as a FRESH variable `bs`, which no longer unifies with
-- the `proj₁ (proj₂ (proj₂ (subscribeInner …)))` that both the goal and
-- `subscribeInner-nodry`'s conclusion mention.  Leaving the projection
-- standing keeps the two syntactically equal, and `any-dry-++`'s second
-- argument is then inferred from `h-bs`.
... | just (switch-st cur od) =
  let sched₁    = proj₁ (proj₂ (switchKill cur sched₀ st₀))
      st₁        = proj₂ (proj₂ (switchKill cur sched₀ st₀))
      h-closes   = switchKill-closes-nodry cur sched₀ st₀
      ctx₁       = switchKill-context c sl Ψ J cur sched₀ st₀ ok rg
      ok₁        = proj₁ ctx₁
      rg₁        = proj₂ ctx₁
      -- VbB is state-independent (valsCaps? ∧ valsΨ? depend only on vals and caps)
      vb-elem    = VbB-head c sl Ψ J o os vb
      -- the nest bound arrives at st₀ and is spent at st₁; the CEILING is
      -- state-free, so only the nest half needs carrying across the kill
      nB         = switchKill-nest sl bud cur o sched₀ st₀ nBst
      cl-elem    = ≤-trans (proj₁ (frameStep-mono-j c 2≤S dsc)) clL̂
      -- depthConsume switchᵒ routes through depthConsumeS, which on a
      -- switch-st node IS depthInner at the POST-switchKill state — exactly
      -- sched₁/st₁ above.  So the same ⊔/suc projection serves here.
      hD-elem    = ≤-trans (m≤m⊔n _ _) (≤-trans (n≤1+n _) hD)
      h-bs       = subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
                     J sf switchᵒ nid κ id now o sched₁ st₁
                     ok₁ pb sspLen vb-elem rg₁ nB hD-elem cl-elem gk
  in any-dry-++ (proj₁ (switchKill cur sched₀ st₀)) _ h-closes h-bs
... | nothing = refl
... | just (scan-st _) = refl
... | just (take-st _) = refl
... | just (merge-st _ _) = refl
... | just (concat-st _ _ _) = refl
... | just (exhaust-st _ _) = refl

-- EXHAUST active=true: drops the payload, emits []
thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf exhaustᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = refl
-- EXHAUST active=false: subscribes, emits bs
... | just (exhaust-st false od) =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf exhaustᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) (≤-trans (n≤1+n _) hD)) nBst clL̂ dsc
... | nothing = refl
... | just (scan-st _) = refl
... | just (take-st _) = refl
... | just (merge-st _ _) = refl
... | just (concat-st _ _ _) = refl
... | just (switch-st _ _) = refl

------------------------------------------------------------------
-- thruWalk-nodry — structural recursion over vals.
thruWalk-nodry : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthFrame sf id now (thru-outer op nid) κ vals false sched st ≤ dep →
  -- THE WALK'S CEILING CHANNEL.  `sIterD … (length vals) J` is the level
  -- this traversal climbs to — one `sLvlD` per payload, which is what
  -- `stepThru-walk` (.Walk-Level) already measures the same `thruWalk`
  -- against — and L̂ is any level that covers it.
  all (λ o → nest o sl (EvalSt.connectedShares st) ≤ᵇ bud) vals ≡ true →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) J ≤ L̂ →
  any dryEvent (proj₁ (proj₂ (thruWalk sf op nid κ id now vals sched st))) ≡ false

thruWalk-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now
               [] sched st _ _ _ _ _ _ _ _ _ _ = refl

-- The head's outputs are LET-BOUND PROJECTIONS, never `with`-scrutinised.
-- Abstracting the tuple rebinds `sched₁`/`st₁` as fresh variables, but the
-- types of everything introduced afterwards (`ok₁`, `rg₁` from
-- thruConsume-nodry-loop) still mention `proj… (thruConsume …)` — a fresh
-- instance the abstraction never touched — so the recursive call's OKB
-- argument is compared at `Sched Γ` against a variable and fails.
thruWalk-nodry {e = e} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now
               (o ∷ os) sched₀ st₀ ok pb sspLen vb rg gk hD nst clL̂ dsc =
  let step   = thruConsume sf op nid κ id now o sched₀ st₀
      bs     = proj₁ (proj₂ step)
      sched₁ = proj₁ (proj₂ (proj₂ step))
      st₁    = proj₂ (proj₂ (proj₂ step))
      S      = Caps.cSize c
      W      = Caps.cWid  c
      -- the nest ledger, split at the head.  `∧-true`'s two Bool sides are
      -- given EXPLICITLY: `all` on a cons reduces to a conjunction whose
      -- sides the unifier will not recover from the equation alone.
      nstH   = proj₁ (∧-true (nest o sl (EvalSt.connectedShares st₀) ≤ᵇ bud)
                             (all (λ o′ → nest o′ sl (EvalSt.connectedShares st₀) ≤ᵇ bud) os)
                             nst)
      nstT   = proj₂ (∧-true (nest o sl (EvalSt.connectedShares st₀) ≤ᵇ bud)
                             (all (λ o′ → nest o′ sl (EvalSt.connectedShares st₀) ≤ᵇ bud) os)
                             nst)
      nBst   = ≤ᵇ⇒≤ (nest o sl (EvalSt.connectedShares st₀)) bud (T-to nstH)
      -- THE HEAD'S CEILING, by the two proven descents: this element's
      -- operator sweep sits inside the walk's own step (`inner-desc`, on
      -- the element's SIZE and not on bud), and that step inside the walk
      -- (`walk-desc`).  Neither move mentions the ceiling, which is what
      -- decoupled the bud from it.
      dsc₀   = ≤-trans (inner-desc S W dep bud J (sizeᵉ o) 2≤S
                          (thruWalk-nodry-elem-size c sl Ψ J o os 2≤S vb))
                       (≤-trans (walk-desc S W dep (suc bud) (length os) J) dsc)
      h-head = thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now o os
                 sched₀ st₀ ok pb sspLen vb rg gk hD nBst clL̂ dsc₀
      loop   = thruConsume-nodry-loop c sl Ψ dep bud J sf op nid κ id now o sched₀ st₀ ok rg
      j₁     = proj₁ loop
      ok₁    = proj₁ (proj₂ loop)
      rg₁    = proj₁ (proj₂ (proj₂ loop))
      hj₁    = proj₂ (proj₂ (proj₂ loop))
      -- every OTHER ledger is read again at the level the step landed at,
      -- and every one of them WIDENS upward; the ceiling is the only
      -- conjunct that gets harder, and `dsc₁` is where it is paid
      le₁    = m≤m+n J j₁
      mono₁  = frameStep-mono-j c 2≤S le₁
      pb₁    = ∧-intro (pathSz?-widen κ (proj₁ mono₁)
                          (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                         (pathBΨ? Ψ κ) pb)))
                       (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                      (pathBΨ? Ψ κ) pb))
      sspL₁  = ≤-trans sspLen (proj₁ mono₁)
      -- {e} is a PHANTOM on VbB-tail: VbB does not mention e, so nothing
      -- in the explicit arguments or the conclusion can solve it.
      vbT    = VbB-tail c sl Ψ J o os vb
      vb₁    = ∧-intro (valsCaps?-lvl _ _ sl os mono₁
                          (proj₁ (∧-true (valsCaps? (frameStep J c) sl os)
                                         (valsΨ? Ψ os) vbT)))
                       (proj₂ (∧-true (valsCaps? (frameStep J c) sl os)
                                      (valsΨ? Ψ os) vbT))
      nst₁   = thruConsume-nodry-nestRec c sl Ψ J bud sf op nid κ id now o os sched₀ st₀ ok nstT
      hD₁    = thruWalk-nodry-dep c sl Ψ dep J sf op nid κ id now o os sched₀ st₀ ok hD
      dsc₁   = ≤-trans (sIterD-mono (length os) (length os) dep dep (suc bud) (suc bud)
                          2≤S ≤-refl ≤-refl hj₁ ≤-refl ≤-refl ≤-refl)
                       (≤-trans (≤-reflexive (sym (sIterD-suc S W dep (suc bud) (length os) J)))
                                dsc)
      h-tail = thruWalk-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc (J + j₁) sf op nid κ id now
                 os sched₁ st₁ ok₁ pb₁ sspL₁ vb₁ rg₁ gk hD₁ nst₁ clL̂ dsc₁
  -- the tail's event list is NAMED rather than left as `_`: with the head's
  -- outputs let-bound (see above) there is no with-pattern to fix it.
  in any-dry-++ bs (proj₁ (proj₂ (thruWalk sf op nid κ id now os sched₁ st₁)))
                h-head h-tail

------------------------------------------------------------------
-- innerReact-nodry — from-inner frame; real body applying concatDrain-nodry.
-- All arms except concatᵒ + (just (concat-st q act od)) + yes refl emit [].
innerReact-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {s} (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId)
  (path′ : Path Γ s t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (from-inner op allNid inst ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now (from-inner op allNid inst) path′ vals fin sched st ≤ d →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now (from-inner op allNid inst)
                               path′ vals fin sched st)))
    ≡ false

-- switch's innerFinish arm, lifted OUT of innerReact-nodry.  Agda cannot
-- return to an outer `with` level with `...` once a nested `with` has been
-- opened, so innerReact-nodry is allowed exactly ONE nested `with` (concat's
-- `w ≟ᵗ s`) and it must be the LAST clause.  switch's `c₀ ≡ᵇ inst` test lives
-- here instead; both of its branches emit [].
innerFinish-switch-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (allNid inst c₀ : NodeId) (path′ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s)) (od : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  any dryEvent
      (proj₁ (proj₂ (innerFinish sf switchᵒ allNid inst path′ id now vals sched st
                                 (just (switch-st (just c₀) od)))))
    ≡ false
innerFinish-switch-nodry sf allNid inst c₀ path′ id now vals od sched st
  with c₀ ≡ᵇ inst
... | true  = refl
... | false = refl

-- fin = false: innerReact emits []
innerReact-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J {s} sf id now op allNid inst path′ vals fin sched st
                 ok pb vb rg gk cl hD
  with fin
... | false = refl
-- fin = true, alive-through check passes: emits []
... | true  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
...   | true  = refl
-- fin = true, alive-through fails: dispatch to innerFinish
-- The node shapes are ENUMERATED for every op rather than closed with
-- `| _`.  innerFinish's own catch-all clause only fires once Agda can
-- rule out its four specific (op, node) clauses, which a variable
-- scrutinee never does — it stays stuck and `refl` is red.
-- `in eqN` CAPTURES THE LOOKUP EQUATION, which is what `concatNode-vb` needs
-- in the concat arm below and what a plain `with` discards.  It costs no
-- clause changes anywhere in this 30-arm block: `in` NAMES the proof, it does
-- not add a pattern position — nor a `with` nesting level, which this
-- function has no room for (see the note above).
...   | false with op | lookupNode allNid (EvalSt.nodes st) in eqN
-- MERGE: innerFinish emits []
...     | mergeᵒ  | just (merge-st k od)          = refl
...     | mergeᵒ  | nothing                       = refl
...     | mergeᵒ  | just (scan-st _)              = refl
...     | mergeᵒ  | just (take-st _)              = refl
...     | mergeᵒ  | just (concat-st _ _ _)        = refl
...     | mergeᵒ  | just (switch-st _ _)          = refl
...     | mergeᵒ  | just (exhaust-st _ _)         = refl
-- CONCAT: every arm EXCEPT the type-matching one emits []
...     | concatᵒ | nothing                       = refl
...     | concatᵒ | just (scan-st _)              = refl
...     | concatᵒ | just (take-st _)              = refl
...     | concatᵒ | just (merge-st _ _)           = refl
...     | concatᵒ | just (switch-st _ _)          = refl
...     | concatᵒ | just (exhaust-st _ _)         = refl
-- SWITCH: innerFinish emits []
...     | switchᵒ | just (switch-st (just c₀) od) =
            innerFinish-switch-nodry sf allNid inst c₀ path′ id now vals od sched st
...     | switchᵒ | just (switch-st nothing od)   = refl
...     | switchᵒ | nothing                       = refl
...     | switchᵒ | just (scan-st _)              = refl
...     | switchᵒ | just (take-st _)              = refl
...     | switchᵒ | just (merge-st _ _)           = refl
...     | switchᵒ | just (concat-st _ _ _)        = refl
...     | switchᵒ | just (exhaust-st _ _)         = refl
-- EXHAUST: innerFinish emits []
...     | exhaustᵒ | just (exhaust-st act od)     = refl
...     | exhaustᵒ | nothing                      = refl
...     | exhaustᵒ | just (scan-st _)             = refl
...     | exhaustᵒ | just (take-st _)             = refl
...     | exhaustᵒ | just (merge-st _ _)          = refl
...     | exhaustᵒ | just (concat-st _ _ _)       = refl
...     | exhaustᵒ | just (switch-st _ _)         = refl
-- CONCAT, type-matching: THE ONLY arm that calls concatDrain →
-- subscribeInner, and so the only one where subscribeInner-nodry is
-- APPLIED.  It opens the function's single nested `with` and therefore
-- must be the LAST clause — nothing may follow it.
...     | concatᵒ | just (concat-st {w} q act od) with w ≟ᵗ s
...       | no _    = refl
...       | yes refl =
              let -- Strip the from-inner frame from pb to get PbB for path′.
                  -- ∧-true's Bool arguments are EXPLICIT: PbB reduces to a
                  -- conjunction Agda cannot recover from the equation alone.
                  pb-sz   = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ path′))
                                          (pathBΨ? Ψ (from-inner op allNid inst ↠ path′)) pb)
                  pb-bΨ   = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ path′))
                                          (pathBΨ? Ψ (from-inner op allNid inst ↠ path′)) pb)
                  -- frameBΨ? Ψ (from-inner _ _ _) = true, so
                  -- pathBΨ? Ψ (from-inner … ↠ path′) reduces DEFINITIONALLY
                  -- to pathBΨ? Ψ path′ — pb-bΨ is already the tail fact and
                  -- needs no ∧-true (which only reintroduced an ambiguous
                  -- `{s}` on the bare frame).
                  pb′     = ∧-intro
                              (pathSz?-tail (Caps.cSize (frameStep J c)) (from-inner op allNid inst) path′ pb-sz)
                              pb-bΨ
                  sspLen  = pathSz?-len (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ path′) pb-sz
              in concatDrain-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf allNid path′ id now
                   q sched st ok pb′ sspLen
                   (concatNode-vb c sl Ψ J allNid q act od sched st ok eqN)
                   rg gk cl
                   -- hD reduces HERE and only here: the `with` above
                   -- scrutinises `lookupNode allNid (nodes st)` and `w ≟ᵗ s`,
                   -- so depthFrame → depthReact → depthFin → depthFinC has
                   -- unfolded to `suc (depthDrain … q …) ≤ d`.  One n≤1+n
                   -- spends the frame's own arc and hands the drain its fold.
                   (≤-trans (n≤1+n _) hD)

------------------------------------------------------------------
-- thruOuter-nodry — thru-outer frame; uses thruWrap-pass + thruWalk-nodry.
thruOuter-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {u} (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (nid : NodeId)
  (path′ : Path Γ u t) (vals : List (Val Γ (obs u)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (thru-outer op nid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now (thru-outer op nid) path′ vals fin sched st ≤ d →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now (thru-outer op nid)
                               path′ vals fin sched st)))
    ≡ false

thruOuter-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now op nid path′ vals fin sched st ok pb vb rg gk cl hD =
  let TW    = thruWalk sf op nid path′ id now vals sched st
      eq    = proj₁ (thruWrap-pass op nid fin TW)
      -- strip thru-outer frame from pb.  ∧-true's two Bool arguments are
      -- given EXPLICITLY: PbB reduces to a conjunction whose sides Agda
      -- cannot recover from the equation alone, so `∧-true _ _` leaves
      -- unsolved metas here.
      pb-sz   = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (thru-outer op nid ↠ path′))
                              (pathBΨ? Ψ (thru-outer op nid ↠ path′)) pb)
      pb-bΨ   = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (thru-outer op nid ↠ path′))
                              (pathBΨ? Ψ (thru-outer op nid ↠ path′)) pb)
      -- frameBΨ? Ψ (thru-outer _ _) = true, so pb-bΨ is already
      -- pathBΨ? Ψ path′ ≡ true definitionally.
      pb′     = ∧-intro
                  (pathSz?-tail (Caps.cSize (frameStep J c)) (thru-outer op nid) path′ pb-sz)
                  pb-bΨ
      sspLen  = pathSz?-len (Caps.cSize (frameStep J c)) (thru-outer op nid ↠ path′) pb-sz
      -- THE WALK'S BUD AND ITS ROOM.  The frame holds its ceiling at its own
      -- `fLvlD`, which is the level the walk is instantiated at; what it
      -- cannot read off its premises is a bud that bounds every element's
      -- nesting AND leaves the walk's `sIterD` inside that same `fLvlD`.
      bud , nst , room =
        thruOuter-nodry-bud c sl Ψ d J sf op nid path′ id now vals fin sched st 2≤S ok vb hD
  in subst (λ x → any dryEvent x ≡ false) (sym eq)
           (thruWalk-nodry c sl Ψ d bud (fLvlD (Caps.cSize c) (Caps.cWid c) d J)
              2≤S 1≤R hCR slC slSz slFc J sf op nid path′ id now vals sched st
              ok pb′ sspLen vb rg gk hD nst cl room)

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
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {s u} (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (f ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  -- the fused per-frame ceiling, delivered by the walk's CL channel
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now f path′ vals fin sched st ≤ d →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))
    ≡ false

-- MAP: the frame emits nothing at all
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (map-f fn) path′ vals fin sched st _ _ _ _ _ _ _ = refl

-- SCAN: every arm of the node-state dispatch emits `[]`
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J {u = u} sf id now
                (scan-f fn nid) path′ vals fin sched st _ _ _ _ _ _ _
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
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (take-f nid) path′ vals fin sched st _ _ _ _ _ _ _ =
  takeDispatch-nodry nid vals fin sched st (lookupNode nid (EvalSt.nodes st))

-- the two *All edges: real definitions, subscribeInner-nodry is APPLIED inside
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (from-inner op allNid inst) path′ vals fin sched st
                ok pb vb rg gk cl hD =
  innerReact-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now op allNid inst
                   path′ vals fin sched st ok pb vb rg gk cl hD

stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (thru-outer op nid) path′ vals fin sched st
                ok pb vb rg gk cl hD =
  thruOuter-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now op nid
                  path′ vals fin sched st ok pb vb rg gk cl hD

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
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {s u} (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (f ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now f path′ vals fin sched st ≤ d →
  let r  = stepFrame sf id now f path′ vals fin sched st
      s′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
      t′ = proj₂ (proj₂ (proj₂ (proj₂ r)))
  in Σ ℕ λ j′ → (J + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) d J)
    × OKB {e = e} c sl Ψ (J + j′) s′ t′
    × (VbB c sl Ψ (J + j′) (proj₁ r) ≡ true)
    × (regP? (PbB c Ψ (J + j′)) (EvalSt.registry t′) ≡ true)
    × (EbB c sl Ψ (J + j′) (proj₁ (proj₂ r)) ≡ true)
stepFrame-burst-face siC ifc c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now f path′ vals fin sched st
                     ok pb vb rg gk cl hD =
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
               (not-in (stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc
                          J sf id now f path′ vals fin sched st
                          ok pb vb rg gk cl hD)))
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
  (hCR : Caps.cReg c ≤ Caps.cSize c)
  (slC : slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true)
  (slSz : slotsSize sl ≤ Caps.cSize c)
  (slFc : slotsFnCap sl ≤ Ψ)
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
    -- THE CEILING CHANNEL, HONEST: the fused per-frame ceiling the
    -- SiNodry leaf prices new registrations against.  Downward closed
    -- because frameStep is monotone in its level index
    ; CL        = λ L id′ → Caps.cSize (frameStep L c) ≤ sizeCapAt e sl (suc id′)
    ; cl-anti   = λ id′ le h → ≤-trans (proj₁ (frameStep-mono-j c 2≤S le)) h
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
    ; sf-step   = λ J sf id now f path′ vals fin sched st ok pb vb rg gk cl hD →
                    stepFrame-burst-face siC ifc {e = e} c sl Ψ d 2≤S 1≤R hCR slC slSz slFc
                      J sf id now f path′ vals fin sched st ok pb vb rg gk cl hD
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
  -- FREE at the true instantiation: Ψ = ΨAt e sl = fnCapᵉ e + slotsFnCap sl.
  slFc : slotsFnCap sl ≤ Ψ
  slFc = m≤n+m (slotsFnCap sl) (fnCapᵉ e)
  cg  = cascadeGo a id chains sched st

  module BW = BurstWalk {e = e} siC ifc c sl Ψ d 2≤S 1≤R (B2-cReg≤cSize e sl id) slC slSz slFc

  inv0 : capsOK? (frameStep 0 c) sched st ≡ true
  inv0 = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv

  -- THE ENTRY FUNDING for the walk's ceiling premise: the walk's whole
  -- delivery-counted level cap Λ fits under `sizeCount c d` (the cnt-cdel
  -- arithmetic below, read off the CAP rather than the run), and at
  -- `sizeCount c d` the ceiling is `capsAt-suc-full` verbatim — the next
  -- instant's caps ARE the current caps stepped by the full budget
  walk≤cdel = ≤-trans (dWalkᶜ-mono n (Caps.cSize c) (length chains)
                         (regAt (Caps.cSize c) (Caps.cReg c) 0)
                         2≤S ≤-refl ≤-refl ≤-refl n≤S ≤-refl
                         (≤-trans lenB (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))))
                      (≤-reflexive (sym (cDel-body c d)))

  hC = ≤-trans (proj₁ (frameStep-mono-j c 2≤S
                  (≤-trans (lvls-mono _ (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl walk≤cdel)
                           (≤-reflexive (sym (sizeCount-body c d))))))
               (≤-reflexive (sym (cong Caps.cSize (capsAt-suc-full e sl id))))

  GO = BW.V.cascadeGo-go 0 a id chains sched st
         ( ((refl , inv0) , hFC)
         , regP?-∧ (pathSz? (Caps.cSize (frameStep 0 c))) (pathBΨ? Ψ)
             (EvalSt.registry st) (capsOK?-regs c sched st inv) rΨ )
         (chP?-∧ (pathSz? (Caps.cSize (frameStep 0 c))) (pathBΨ? Ψ) chains pS pΨ)
         (∧-intro (∧-intro (∧-intro vC refl) refl) (∧-intro vΨ refl))
         hC hD

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

-- (DELETED 2026-08-18) `cascadeGo-burst-dry` sat here — `proj₁` of
-- `cascadeGo-burst-nodry`, exactly as `cascadeGo-nodry` below is `proj₂`.
-- Its only consumer was `dry-tick-core`'s argument list, and that list is
-- wrong about itself: the dry half concludes `hasDry`, and a `burstB?`
-- bound cannot be an ingredient of it.  Recreating
-- it is one line against `cascadeGo-burst-nodry`, so nothing is lost but the
-- typing; RECOVERY: git show fa9692d:agda/src/Verify-Budget-Sufficient/Burst-Walk.agda

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
