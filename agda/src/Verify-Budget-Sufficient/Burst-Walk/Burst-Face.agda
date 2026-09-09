------------------------------------------------------------------
-- BURST-FACE: the frame face and the cascade payoff, assembled.
-- Hoisted out of `.Burst-Walk`, whose blocks are all acyclic and so are
-- checked in ONE pass with nothing stubbed — every body in that file
-- was paid for whenever any of it was.  This region is the half the
-- walk's chain index made expensive, being the only one that APPLIES
-- the walk generic, and it took a single-figure count of names with it,
-- so the cut costs an import list and returns both halves to the dev
-- loop.


-- Landed from `git show 050c69a^:agda/probe/Caps-Burst-Walk-Probe.agda`, which
-- was v2 of the route: v1's two bridging postulates were BOTH
-- mis-stated (one concluded fnCap facts from hypotheses carrying no
-- fnCap information; one lacked the plen/gas guards that keep its
-- arithmetic true), and v0 — demand ledgers CONSTANT in the walk
-- level — was MACHINE-REFUTED (the probe is deleted at
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

-- THE DESIGN, in one paragraph.  `valB? B Ψ`'s two conjuncts have
-- OPPOSITE characters: the SIZE half grows per frame and must ride
-- the walk's caps level (`valsCaps? (frameStep J c) sl`), while the
-- FNCAP half is frame-invariant ("Ψ never grows — caseW is
-- substitution-invariant", .Measures) and rides CONSTANT.  The walk
-- carries the conjunction; `Res.burst` returns both flavours; `burstB?-halves`
-- recombines them pointwise into `burstB? (cSize c′) Ψ` — a real
-- proof.  Stating the receipt at the CASCADE level (walk entered at
-- J = 0) makes the landing-level bound the exact arithmetic
-- `cascadeGo-caps` (.Caps-Face) already proves, cribbed term for
-- term; then `capsAt-suc-full` (.Caps, refl) lands the widened
-- caps half on `capsAt e sl (suc id)`, whose cSize IS the dry target
-- Ŝ = sizeCapAt e sl (suc id).  Dm = (2·B + 12) · towerℕ (suc sz)
-- appears NOWHERE — the anchor's content is no longer a second,
-- measured-not-proven numeric model, but the same "landing level fits
-- sizeCount" obligation the caps machinery exists to prove.

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

-- THE FRAME FACE IS NOT A POSTULATE.  `stepFrame-burst-face` is
-- an ASSEMBLY over the PROVEN `stepFrame-face` (.Caps-Face) plus
-- five per-frame WET leaves (`wet-face`) plus the DRY face
-- (`stepFrame-nodry`).  Four of
-- its conjuncts come off that one call — the level bound and `capsOK?`
-- verbatim, `valsCaps?` verbatim, and `regP? (pathSz? …)` via
-- `capsOK?-regs` on that same `capsOK?`.  EVERY LEAF IS PROVEN —
-- the three state-local wet leaves (map, take, scan), `wet-inner` and
-- `wet-thru` (the two *All edges, same family as `subscribeInner-demand`,
-- ex-.Anchor-Dry), and `stepFrame-nodry`, which carries the dry.

-- RECOVERY: `git log --diff-filter=D -- agda/src/Verify-Budget-Sufficient/Demand-Probe.agda`
--  restores 1857 lines / 194 refl rows of GAS-DEMAND measurement — the minimal
--  gasPad h* at which each canonical program stops drying.  Deleted because its
--  target `cascadeGo-nodry` is discharged; wanted back only if a restatement
--  reopens gas SUFFICIENCY, which `subscribeE-Ψ` is not (that is fnCap/Ψ
--  preservation, and the probe says nothing about it).
------------------------------------------------------------------
module Verify-Budget-Sufficient.Burst-Walk.Burst-Face where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ; m≤n+m)
open import Data.List    using (List; []; _∷_; _++_; map; length)
open import Data.Bool.ListAction using (all; any)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Fin     using (toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; value; handoff; complete; _at_from_as_; EmitKind; delivery)
open import Rx.Exp  using (Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; Arrival; RegId; Path; Frame; _↠_; Stream; stepFrame; cascadeGo; hasDry;
  dryEvent; budgetAt; arrTy; arrVal; fLvlD; regAt; shareAdmit; shareLatch; foldPath; chainStep)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk
  using (Walk-Hyps; module Walk; regP?; chP?; chP?-const)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Measures using
  (all-++-intro; burstB?; fnCapBounded?; fnCapᵉ; hasDry-append; slotsFnCap; ΨAt; ∧-true)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthCascade)


-- THE SHARE-LEDGER RING.  `nest` is antitone in the connected set, so a
-- nest bound survives any step that only ENLARGES that set — and the ring
-- proves exactly that, per evaluator step, as a `KeepsC` record.  This is
-- what the walk's two nest-preservation obligations spend.

-- THE LEVEL DESCENTS, spent by the thru walk's ceiling channel.  The wet
-- walk face already threads an abstract ceiling level and converts it to
-- each callee's budget with these; the nodry face now does the same, which
-- is what took the per-element ceiling off an unstated fLvlD inequality.
open import Verify-Budget-Sufficient.Caps using (1≤capsAt-reg; 2≤capsAt-size; B2-cReg≤cSize; Caps; capsAt; capsAt-suc-full; capsH; cDel;
  cDel-body; dWalkᶜ-mono; frameStep; frameStep-0; frameStep-mono-j; lvls-mono; sizeCount;
  sizeCount-body)

-- THE CAPS FACE'S OWN thruConsume STEP, PROVEN.  It carries the level the
-- step lands at and the caps invariant there; the nodry walk's loop
-- invariant is that plus the Ψ half, which this module proves itself.

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; capsOK?; eventCaps?; frameStrat?; pathFloor; pathOrd?; pathPark?; pathSz?;
  pathSz?-widen;
  pathStrat?; slotsCaps?; valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-delivered; capsOK?-regOrd; capsOK?-regPark; capsOK?-regs;
  pathPark-delivered; pathSz?-len; pathSz?-tail; registry-entStrat;
  shareLatch-caps; valsCaps?; valsCaps?-lvl; valsStrat?; walkOK-finish)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (SiCType; IfcType)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (burstCaps?-widen; eventsCaps?-widen)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Frame-Face using
  (stepFrame-face)

open import Verify-Budget-Sufficient.Wet.Part6 using
  (sizeCapAt)
open import Verify-Budget-Sufficient.Burst-Walk.Predicates using
  (BbB; EbB; OKB; PbB; VbB)
open import Verify-Budget-Sufficient.Walk-Level.Parts using
  (any-dry-++)
open import Verify-Budget-Sufficient.Psi-Split using
  (burstB?-halves; burstΨ?; chP?-∧; chP?-projˡ; chP?-projʳ; eventsΨ?; frameBΨ?; pathBΨ?;
  regP?-∧; regP?-projˡ;
  regsBΨ?; regStrat?-paths; valsΨ?; valΨ?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves using
  (chainStep-ord; chainStep-park; foldPath-ord; foldPath-park; shareAdmit-ord; shareAdmit-park;
  shareAdmit-strat; stepFrame-valsStrat)
open import Decide using (not-in; not-out; ∧-intro; ∧-trueˡ; ∧-trueʳ)
open import Verify-Budget-Sufficient.Burst-Walk.Leaves using
  (WetFace; wet-face)
open import Verify-Budget-Sufficient.Burst-Walk using
  (fnCapB-latch; fnCapB-finish; stepFrame-nodry)

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

stepFrame-burst-face : SiCType → IfcType →
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
  -- THE ENTRY READING, WHICH THIS FACE ONLY FORWARDS.  Nothing in the
  -- burst content reads a stratification; the two premises are here
  -- because `stepFrame-face` mints a registration and the mint's side
  -- condition is stated against the frame's own path and payload
  pathStrat? (f ↠ path′) ≡ true →
  valsStrat? (pathFloor (f ↠ path′)) vals ≡ true →
  -- AND THE CHAIN'S OWN TWO READINGS, forwarded for the same reason and
  -- to both halves: the caps face spends them at the mint, the nodry
  -- face at the drain
  pathOrd? (Sched.nextNode sched) (f ↠ path′) ≡ true →
  pathPark? (f ↠ path′) st ≡ true →
  let r  = stepFrame sf id now f path′ vals fin sched st
      s′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
      t′ = proj₂ (proj₂ (proj₂ (proj₂ r)))
  in Σ ℕ λ j′ → (J + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) d J)
    × OKB {e = e} c sl Ψ (J + j′) s′ t′
    × (VbB c sl Ψ (J + j′) (proj₁ r) ≡ true)
    × (regP? (PbB c Ψ (J + j′)) (EvalSt.registry t′) ≡ true)
    × (EbB c sl Ψ (J + j′) (proj₁ (proj₂ r)) ≡ true)
stepFrame-burst-face siC ifc c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now f path′ vals fin sched st
                     ok pb vb rg gk cl hD hps hvs stO stK =
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
                          ok pb vb rg gk cl hD hps hvs stO stK)))
  where
  r  = stepFrame sf id now f path′ vals fin sched st
  s′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
  t′ = proj₂ (proj₂ (proj₂ (proj₂ r)))

  FC = stepFrame-face siC ifc c d J sl sf id now f path′ vals fin sched st
         2≤S 1≤R (proj₁ (proj₁ ok)) slC (proj₂ (proj₁ ok))
         (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (f ↠ path′))
                        (pathBΨ? Ψ (f ↠ path′)) pb))
         (proj₁ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb))
         slSz hD hps hvs stO stK

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
  (siC : SiCType)
  (ifc : IfcType)
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

  -- AND THE STRAT HALF NEEDS ITS OWN, FOR A SHARPER REASON THAN THE
  -- REST OF THIS SHELF.  The others name their sides because the
  -- unifier will not invert a function application; this one is
  -- ambiguous even once it does.  At a CONS the right factor
  -- `pathStrat? (f ↠ p)` REDUCES to a conjunction of its own, so the
  -- ledger's outer ∧ and the reading's inner one are the same symbol
  -- and nothing says where the split falls -- the left side is left
  -- blocked and reports many minutes downstream, at the importer.  The
  -- projection is stated over a path VARIABLE, where the reading is
  -- neutral and the split is forced, and applied at the cons.
  pbS : ∀ (J : ℕ) {u} (p : Path Γ u t) →
        (PbB c Ψ J p ∧ pathStrat? p) ≡ true → pathStrat? p ≡ true
  pbS J p h = proj₂ (∧-true (PbB c Ψ J p) (pathStrat? p) h)

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
    -- THE ENTRY READING, CONJOINED AT THE INSTANTIATION RATHER THAN IN
    -- `PbB`.  Only this walk owes the registration mint's side
    -- condition, so the stratification half rides here and every other
    -- consumer of the burst predicates is left reading what it always did
    ; Pb        = λ J p → PbB c Ψ J p ∧ pathStrat? p
    -- `VbB` IS PATH-BLIND -- it bounds a payload's size and function
    -- caps, neither of which depends on the chain the payload is
    -- travelling -- but the reading beside it is not, and that asymmetry
    -- is the point: the floor is what MOVES at the fan, and nowhere else
    ; Vb        = λ p J vs → VbB c sl Ψ J vs ∧ valsStrat? (pathFloor p) vs
    ; Eb        = EbB c sl Ψ
    ; Bb        = BbB c sl Ψ
    -- THE GAS HOOK, SPENT (the anchor ruling, `cascadeGo-nodry`'s header): the
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
    -- AND THE ENVELOPE DROPS THE READING, WHICH IS NOT A LOSS.  `Bb` is
    -- the burst ledger and carries no floor, so the payload's reading has
    -- no conjunct to land in here; it is spent where the floor MOVES,
    -- which is the fan, and re-earned per frame at the step
    ; b-deliv   = λ J id src evs vals fin hE hV →
                    ∧-intro
                      (∧-intro (all-++-intro _ evs _ (ebC J evs hE)
                                 (all-++-intro _ (map value vals) _
                                   (mv-caps (frameStep J c) vals
                                     (vsC-all (frameStep J c) vals
                                       (vbC J vals (∧-trueˡ hV))))
                                   (ft-caps (frameStep J c) fin)))
                               refl)
                      (∧-intro
                        (∧-intro (all-++-intro _ evs _ (ebΨ J evs hE)
                                   (all-++-intro _ (map value vals) _
                                     (mv-Ψ vals (vbΨ J vals (∧-trueˡ hV)))
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
    ; p-len     = λ J p h →
                    pathSz?-len (Caps.cSize (frameStep J c)) p (pbC J p (∧-trueˡ h))
    ; p-tail    = λ J f p h →
                    ∧-intro
                      (∧-intro (pathSz?-tail (Caps.cSize (frameStep J c)) f p
                                 (pbC J (f ↠ p) (∧-trueˡ h)))
                               (proj₂ (∧-true (frameBΨ? Ψ f) (pathBΨ? Ψ p)
                                 (pbΨ J (f ↠ p) (∧-trueˡ h)))))
                      -- the tail's reading is the frame's own conjunct
                      -- dropped: `pathStrat?` of a push is the frame read
                      -- at the TERMINAL's floor, and that floor is what
                      -- the tail already carries
                      (proj₂ (∧-true (frameStrat? (pathFloor p) f) (pathStrat? p)
                                (pbS J (f ↠ p) h)))
    ; p-widen   = λ {J} {J′} le p h →
                    ∧-intro
                      (∧-intro (pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le))
                                 (pbC J p (∧-trueˡ h)))
                               (pbΨ J p (∧-trueˡ h)))
                      (∧-trueʳ h)
    ; v-widen   = λ {J} {J′} le _ vs h →
                    ∧-intro
                      (∧-intro (valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le)
                                 (vbC J vs (∧-trueˡ h)))
                               (vbΨ J vs (∧-trueˡ h)))
                      (∧-trueʳ h)
    -- THE ONE PLACE THE READING MOVES.  The size and Ψ halves are
    -- constant across the admitted chains and go through unchanged; the
    -- floor half is re-earned per chain out of the registry's own
    -- stratification, which is exactly the conjunct `capsOK?` carries
    ; v-fan     = λ J i vs sched st ok h →
                    chP?-∧ (λ _ → VbB c sl Ψ J vs)
                           (λ κ → valsStrat? (pathFloor κ) vs)
                           (shareAdmit i (EvalSt.registry st))
                      (chP?-const (VbB c sl Ψ J vs)
                         (shareAdmit i (EvalSt.registry st)) (∧-trueˡ h))
                      (proj₂ (shareAdmit-strat i vs st
                                (registry-entStrat (frameStep J c) sched st
                                  (proj₂ (proj₁ ok)))
                                (∧-trueʳ h)))
    -- THE CHAIN'S TWO ENTRY READINGS, CARRIED AS ONE LEDGER, exactly as
    -- the caps face carries them.  The burst face itself reads bursts and
    -- levels and inspects neither the scheduler's counter nor the store's
    -- parks -- but its FRAME STEP now does, because the nodry cascade it
    -- drives spends both at the mint, so the ledger cannot be the constant
    -- `true` any more.  Every transport below is the caps face's, term for
    -- term: the readings are properties of the scheduler and the store,
    -- and the two faces walk the same scheduler and the same store
    ; Ob        = λ sched st p → pathOrd? (Sched.nextNode sched) p ∧ pathPark? p st
    ; o-cons    = λ rid sched st p h →
                    ∧-intro (∧-trueˡ h) (pathPark-delivered p rid st (∧-trueʳ h))
    ; o-fan     = λ J i fin sched st ok →
                    chP?-∧ (λ {u} p → pathOrd? (Sched.nextNode sched) p)
                           (λ {u} p → pathPark? p (shareLatch i fin st))
                           (shareAdmit i (EvalSt.registry st))
                      (shareAdmit-ord i sched st
                         (capsOK?-regOrd (frameStep J c) sched st (proj₂ (proj₁ ok))))
                      (shareAdmit-park i fin st
                         (capsOK?-regPark (frameStep J c) sched st (proj₂ (proj₁ ok))))
    ; o-fold    = λ sf gas id now envSrc p vals evs fin sched st ps h →
                    chP?-∧ (λ {u} κ → pathOrd?
                              (Sched.nextNode
                                (proj₁ (proj₂ (foldPath sf gas id now envSrc p vals
                                                 evs fin sched st)))) κ)
                           (λ {u} κ → pathPark? κ
                              (proj₂ (proj₂ (foldPath sf gas id now envSrc p vals
                                               evs fin sched st))))
                           ps
                      (foldPath-ord sf gas id now envSrc p vals evs fin sched st ps
                         (chP?-projˡ (λ {u} κ → pathOrd? (Sched.nextNode sched) κ)
                                     (λ {u} κ → pathPark? κ st) ps h))
                      (foldPath-park sf gas id now envSrc p vals evs fin sched st ps
                         (chP?-projʳ (λ {u} κ → pathOrd? (Sched.nextNode sched) κ)
                                     (λ {u} κ → pathPark? κ st) ps h))
    ; o-chain   = λ id a p sched st chains h →
                    chP?-∧ (λ {u} κ → pathOrd?
                              (Sched.nextNode
                                (proj₁ (proj₂ (chainStep id a p sched st)))) κ)
                           (λ {u} κ → pathPark? κ
                              (proj₂ (proj₂ (chainStep id a p sched st))))
                           chains
                      (chainStep-ord id a p sched st chains
                         (chP?-projˡ (λ {u} κ → pathOrd? (Sched.nextNode sched) κ)
                                     (λ {u} κ → pathPark? κ st) chains h))
                      (chainStep-park id a p sched st chains
                         (chP?-projʳ (λ {u} κ → pathOrd? (Sched.nextNode sched) κ)
                                     (λ {u} κ → pathPark? κ st) chains h))
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
    -- THE STEP, WITH THE READING SPENT AND RE-EARNED.  The face itself
    -- reads nothing stratified, so its own ledgers are the burst ones
    -- and the two halves are split off here: the registry ledger by
    -- projection, the path and payload readings forwarded whole.  What
    -- comes back carries no reading at all, so both are rebuilt --  the
    -- payload's out of the frame's discarded conjunct, the registry's
    -- out of the `capsOK?` the step lands at
    ; sf-step   = λ J sf id now f path′ vals fin sched st ok pb vb rg gk cl hD hOb →
                    let hOb2 = ∧-true (pathOrd? (Sched.nextNode sched) (f ↠ path′))
                                      (pathPark? (f ↠ path′) st) hOb
                        hS = pbS J (f ↠ path′) pb
                        hF = proj₁ (∧-true (frameStrat? (pathFloor path′) f)
                                           (pathStrat? path′) hS)
                        hV = ∧-trueʳ vb
                        BF = stepFrame-burst-face siC ifc {e = e} c sl Ψ d 2≤S 1≤R hCR
                               slC slSz slFc J sf id now f path′ vals fin sched st ok
                               (∧-trueˡ pb) (∧-trueˡ vb)
                               (regP?-projˡ (PbB c Ψ J) (λ {u} p → pathStrat? p)
                                 (EvalSt.registry st) rg)
                               gk cl hD hS hV (proj₁ hOb2) (proj₂ hOb2)
                        r  = stepFrame sf id now f path′ vals fin sched st
                        t′ = proj₂ (proj₂ (proj₂ (proj₂ r)))
                        s′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
                        ok′ = proj₁ (proj₂ (proj₂ BF)) in
                    proj₁ BF
                    , proj₁ (proj₂ BF)
                    , ok′
                    , ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ BF))))
                        (stepFrame-valsStrat sf id now f path′ vals fin sched st hF hV)
                    , regP?-∧ (PbB c Ψ (J + proj₁ BF)) (λ {u} p → pathStrat? p)
                        (EvalSt.registry t′)
                        (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ BF)))))
                        (regStrat?-paths (EvalSt.registry t′)
                          (registry-entStrat (frameStep (J + proj₁ BF) c) s′ t′
                            (proj₂ (proj₁ ok′))))
                    , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ BF))))
                    , refl
    }

  module V = Walk {e = e} S W R d 2≤S burstH

------------------------------------------------------------------
-- THE PAYOFF (cascadeGo-burst-nodry) — the walk/cascade burst content, at Ŝ, with no Dm,
-- AND the cascade's dry half, off the SAME run.
--
-- The level arithmetic is `cascadeGo-caps`'s own (.Caps-Face),
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

cascadeGo-burst-nodry : SiCType → IfcType →
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
  -- THE ENTRY READING, PER CHAIN.  The walk's ledgers now carry a
  -- stratification half beside the size and Ψ ones, so the cascade's
  -- own entry point owes both: every chain the arrival is dispatched
  -- along is stratified, and the payload sits below that chain's floor.
  -- The payload half is path-INDEXED, which is what lets the reading
  -- move at the fan and nowhere else
  chP? (λ {u} p → pathStrat? p) chains ≡ true →
  chP? (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains ≡ true →
  -- AND THE CHAIN'S TWO ENTRY READINGS, WHICH THE WALK CARRIES AND
  -- NOTHING HERE DERIVES.  The order half reads the scheduler's counter
  -- and the park half the store; the burst content implies neither, so
  -- both are owed by whoever produced the chains -- for the cascade,
  -- the registry filter one call up
  chP? (λ {u} p → pathOrd? (Sched.nextNode sched) p ∧ pathPark? p st)
       chains ≡ true →
  (burstB? (sizeCapAt e sl (suc id)) Ψ
           (proj₁ (cascadeGo a id chains sched st)) ≡ true)
  × (hasDry (proj₁ (cascadeGo a id chains sched st)) ≡ false)
cascadeGo-burst-nodry siC ifc {n = n} {e = e} id a chains sched st
                      slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD hpS hvS hOb =
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
         , regP?-∧ (PbB c Ψ 0) (λ {u} p → pathStrat? p) (EvalSt.registry st)
             (regP?-∧ (pathSz? (Caps.cSize (frameStep 0 c))) (pathBΨ? Ψ)
                (EvalSt.registry st) (capsOK?-regs c sched st inv) rΨ)
             (regStrat?-paths (EvalSt.registry st)
                (registry-entStrat c sched st inv)) )
         (chP?-∧ (PbB c Ψ 0) (λ {u} p → pathStrat? p) chains
            (chP?-∧ (pathSz? (Caps.cSize (frameStep 0 c))) (pathBΨ? Ψ) chains pS pΨ)
            hpS)
         (chP?-∧ (λ _ → VbB c sl Ψ 0 (arrVal a ∷ []))
                 (λ κ → valsStrat? (pathFloor κ) (arrVal a ∷ [])) chains
            (chP?-const (VbB c sl Ψ 0 (arrVal a ∷ [])) chains
               (∧-intro (∧-intro (∧-intro vC refl) refl) (∧-intro vΨ refl)))
            hvS)
         hC hD hOb

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
-- the `cascadeGo-burst-nodry` run (postulate → definition).
--
-- THE RULING THAT DISCHARGED IT: the dry half rides the walk as a
-- THIRD, GAS-CONDITIONED ledger flavour (`EbB`/`BbB`), spending the GOK/g-mint
-- hook the walk was built with (.Delivery-Walk).  Every transport
-- law proved mechanical exactly as the route predicted — appends by
-- `hasDry-append`/`any-dry-++`, seeds and deliveries by computation
-- (`dryEvent` is false on value/init/close-exhausted/handoff/complete),
-- widens for free (dryness is level-independent).  What remained was the
-- per-frame face, `stepFrame-nodry`, where the WHOLE of the anchor's former
-- risk lived — a real definition now, whose from-inner case consumes the
-- COLLAPSED walk face (`subscribeE-walk-level`, .Walk-Level), the statement
-- built to be satisfiable mid-delivery.  That was the last of it: the anchor
-- chain holds no postulate.
--
-- WHAT THIS MOVE BUYS, in risk-ledger terms: `cascadeGo-nodry` and
-- `subscribeE-wet-core` used to be two independent FALSITY rows.  Both
-- now bottom out in `subscribeE-walk-level` (the wet core by
-- instantiation, the anchor through `subscribeInner-nodry`), so the
-- anchor risk CONSOLIDATED onto one statement — plus `stepFrame-nodry`'s two
-- named manufacture obligations, (i) mid-delivery INV? and (ii) the
-- general-id fuel, each a crib of a proven sibling, and each since paid.
------------------------------------------------------------------

-- (DELETED) `cascadeGo-burst-dry` sat here — `proj₁` of
-- `cascadeGo-burst-nodry`, exactly as `cascadeGo-nodry` below is `proj₂`.
-- Its only consumer was `dry-tick-core`'s argument list, and that list is
-- wrong about itself: the dry half concludes `hasDry`, and a `burstB?`
-- bound cannot be an ingredient of it.  Recreating
-- it is one line against `cascadeGo-burst-nodry`, so nothing is lost but the
-- typing; RECOVERY: git show fa9692d:agda/src/Verify-Budget-Sufficient/Burst-Walk.agda

cascadeGo-nodry : SiCType → IfcType →
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
  chP? (λ {u} p → pathStrat? p) chains ≡ true →
  chP? (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains ≡ true →
  chP? (λ {u} p → pathOrd? (Sched.nextNode sched) p ∧ pathPark? p st)
       chains ≡ true →
  hasDry (proj₁ (cascadeGo a id chains sched st)) ≡ false
cascadeGo-nodry siC ifc id a chains sched st
                slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD hpS hvS hOb =
  proj₂ (cascadeGo-burst-nodry siC ifc id a chains sched st
           slC slSz inv hFC vC vΨ pS pΨ rΨ n≤S lenB hD hpS hvS hOb)
