------------------------------------------------------------------
-- BURST-WALK: the THREE-flavour burst ledger over the Delivery-Walk —
-- the walk/cascade burst content landed at Ŝ with no tower constant,
-- and the cascade's DRY half off the same run: the third
-- flavour is `nodry`, gas-conditioned through the walk's GOK hook, and
-- `cascadeGo-nodry` — the ex-anchor — is now a projection of `cascadeGo-burst-nodry`.
-- THE ANCHOR CHAIN IS DISCHARGED: `stepFrame-nodry`, which carried the last of
-- its risk, is a real definition, and this module's only live postulate is
-- `subscribeE-Ψ`.

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

-- Also home to frameBΨ?/pathBΨ?/regsBΨ?, RELOCATED from .Caps-Bridge
-- (they were defined there, downstream of this module's consumers).
------------------------------------------------------------------

-- RECOVERY: `git log --diff-filter=D -- agda/src/Verify-Budget-Sufficient/Demand-Probe.agda`
--  restores 1857 lines / 194 refl rows of GAS-DEMAND measurement — the minimal
--  gasPad h* at which each canonical program stops drying.  Deleted because its
--  target `cascadeGo-nodry` is discharged; wanted back only if a restatement
--  reopens gas SUFFICIENCY, which `subscribeE-Ψ` is not (that is fnCap/Ψ
--  preservation, and the probe says nothing about it).
module Verify-Budget-Sufficient.Burst-Walk where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; s≤s; z≤n; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ; ≤⇒≤ᵇ; ≤ᵇ⇒≤; m≤m+n; m≤n+m; m≤n⊔m;
         m≤m⊔n; n≤1+n; ≤-pred)
open import Data.List    using (List; []; _∷_; _++_; map; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Nullary using (yes; no)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim using (Gas; gs; g0; Id; Tick; Source; InstEvent; value; close; handoff; complete; cut; cutPending;
  gasPad; gasTower; towerℕ; InstEmit; _at_from_as_; EmitKind; delivery)
open import Rx.Exp  using (Ctx; Closed; Val; obs; Fn; _×ᵗ_; _≟ᵗ_; sizeᵉ; syncSizeᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; Arrival; RegId; Chain; Path; Frame; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; Stream; stepFrame; cascadeGo; dropSource; shareLatch; shareFinish; hasDry;
  dryEvent; budgetAt; capsHgo; capsBase; arrTy; arrVal; fLvlD; opIterD; regAt; subscribeInner;
  subscribeE; splitBurst; splitEvents; sLvlD; sIterD; sIterD-suc; sizeAt; fLvlD-suc; widAt;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeId; NodeState; takeDispatch; takeVals;
  cutThrough; lookupNode; pathHasNode; memberSource; scanVals; innerFinish; mergeAllDrain;
  aliveThroughᶠ; mergeAllBump; switchKill; thruConsume; thruWalk; thruWrap; scan-st; take-st;
  hasRoom; mergeAll-st; switch-st; exhaust-st)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk
  using (Walk-Hyps; module Walk; regP?)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; all-++-intro; all-zip; burstB?; caseWᵗ; dBound; dBound-bound; fcB-live;
  fcB-nodes; fnCapBounded?; fnCapNode; fnCapᵉ; fnCapᵗ; hasAtLeast-mono; hasAtLeast-pad-plus;
  hasAtLeast-tower; hasDry-append; hopR; INV?; pathB?; pathB?-widen; pathLen; prod≤3pow;
  regsLen?; slotHop-cap; slotsFnCap; syncSize≤sizeᵉ; takeVals-all; unconn; unconn≤slots; ΨAt;
  ∧-true)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthWalk; depthConsume; depthCascade; depthInner; depthFin; depthDrain)

open import Verify-Budget-Sufficient.Caps-Nest using (nest; nest-keeps)

-- THE SHARE-LEDGER RING.  `nest` is antitone in the connected set, so a
-- nest bound survives any step that only ENLARGES that set — and the ring
-- proves exactly that, per evaluator step, as a `KeepsC` record.  This is
-- what the walk's two nest-preservation obligations spend.
open import Verify-Budget-Sufficient.Keeps-Ring
  using (KeepsC; thruConsume-keeps; switchKill-keeps; subscribeInner-keeps)

-- THE LEVEL DESCENTS, spent by the thru walk's ceiling channel.  The wet
-- walk face already threads an abstract ceiling level and converts it to
-- each callee's budget with these; the nodry face now does the same, which
-- is what took the per-element ceiling off an unstated fLvlD inequality.
open import Verify-Budget-Sufficient.Caps-Chain using (walk-desc; inner-desc)
open import Verify-Budget-Sufficient.Caps using (sIterD-mono; sizeAt-mono;
                                                 1≤capsAt-reg; 2≤capsAt-size;
                                                 6≤capsAt-size; B2-cReg≤cSize;
                                                 Caps; capsAt;
                                                 capsAt-base-size;
                                                 capsAt-suc-full; capsAt-tower;
                                                 capsH; cDel; cDel-body;
                                                 dWalkᶜ-mono; frameStep;
                                                 frameStep-0; frameStep-mono-j;
                                                 frameStep-reg≤size; lvls-mono;
                                                 opIterD-infl; sizeCount;
                                                 sizeCount-body; tower-3)

-- THE CAPS FACE'S OWN thruConsume STEP, PROVEN.  It carries the level the
-- step lands at and the caps invariant there; the nodry walk's loop
-- invariant is that plus the Ψ half, which this module proves itself.
open import Verify-Budget-Sufficient.Subscribe-Face
  using (thruConsume-caps; subscribeInner-caps)

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; capsOK?; capsOK?-mono; eventCaps?; pathSz?; pathSz?-widen; regsSz?; slotsCaps?;
  valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-delivered; capsOK?-nodeSz; capsOK?-nodeWid; capsOK?-parts;
  capsOK?-regs; frameBud; lookupNode-caps; mList?; mList?-head; mList?-keeps; mList?-tail;
  NodeCaps; pathSz?-len; pathSz?-tail; shareLatch-caps; switchKill-caps; valsCaps?;
  valsCaps?-lvl; valsCaps→mList-strict; walkOK-finish)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (burstCaps?-widen; eventsCaps?-widen; frameStep-chain-suc; pathSz?-⊑;
   valCaps?-size)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (cSize≤frameStep; valsCaps?-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part7 using
  (stepFrame-face)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (valsLen; valsOf)

open import Verify-Budget-Sufficient.Wet.Part6 using
  (sizeCapAt)
open import Verify-Budget-Sufficient.Wet.Part1 using
  (INV?-widen; scanVals-fnCap; setNode-fnCap; sweepLive-fnCap)
open import Verify-Budget-Sufficient.Burst-Walk.Predicates using
  (BbB; EbB; OKB; PbB; VbB)
open import Verify-Budget-Sufficient.Walk-Level
  using (subscribeE-walk-level; capsOK⇒regsLen; regsLen?-mono)
open import Verify-Budget-Sufficient.Walk-Level.Statement using
  (WalkLevel)
open import Verify-Budget-Sufficient.Walk-Level.Parts using
  (any-dry-++; map-Ψ; splitBurst-nodry; switchKill-closes-nodry; thruWrap-pass)
open import Verify-Budget-Sufficient.Psi-Split using
  (allΨ-of; allΨ-to; burstB?-halves; burstΨ?; chP?-∧; eventsΨ?; frameBΨ?;
   INV?-of-parts; lookupNode-fnCap; NodeΨ; pathB?-of-parts; pathBΨ?; regP?-∧;
   regsB?-of-parts; regsBΨ?; splitEvents-bk-Ψ; splitEvents-vals-Ψ; valsΨ?;
   valΨ?)
open import Rx.Frame-Width using (pWᵉ; dWᵉ; outWᵛ; pWᵛ)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Frame-Width using (dWᵉ; pWᵛ; outWᵛ; pWᵉ)
open import Decide using (T-to; T⇒≡true; not-in; not-out; ∧-intro; ≤ᵇ-widen)


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

-- any-dry-++ MOVED DOWN to .Walk-Level, with the whole
-- dry trio: the ground subscribeInner-walk consumes it there, and this
-- module sits above .Walk-Level.  Imported back below.

-- VbB's HEAD AND TAIL PROJECTIONS.  `thruConsume-nodry-vb` in the block below
-- is the head projection stated again at one instantiation (`Val Γ (obs u)` IS
-- `Closed Γ s`, per Rx/Exp's definition of `Val`).  Both are `all` over a cons
-- and nothing more, so they are proven here once and the callers spend them —
-- which is what the mergeAll side does: one receipt minted per node lookup
-- (`mergeAllNode-vb`), then projected down the drain's recursion.
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

-- ONE ELEMENT'S SIZE, at the level `inner-desc` reads it.  Spent by both
-- payload walks — the thru walk over a value list and the mergeAll drain over
-- a queue — which is why it is named for neither.  `valsCaps?`
-- carries a per-element `valCaps?`, whose size half bounds the element at
-- `Caps.cSize (frameStep J c)` — which IS `sizeAt (cSize c) J`; `inner-desc`
-- wants that bound one level up, and one level up is a RAISE.  It mentions
-- no bud, which is the point: it is what takes the ceiling descent off the
-- bud entirely.
nodry-elem-size : ∀ {n} {Γ : Ctx n} {u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (o : Val Γ (obs u)) (os : List (Val Γ (obs u))) →
  2 ≤ Caps.cSize c →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  suc (sizeᵉ o) ≤ suc (sizeAt (Caps.cSize c) (suc J))
nodry-elem-size {u = u} c sl Ψ J o os 2≤S vb =
  s≤s (≤-trans
        (≤ᵇ⇒≤ (sizeᵉ o) (Caps.cSize (frameStep J c))
          (T-to (valCaps?-size (frameStep J c) sl (obs u) o
                  (proj₁ (∧-true (valCaps? (frameStep J c) sl (obs u) o)
                                 (all (valCaps? (frameStep J c) sl (obs u)) os)
                                 (valsOf (frameStep J c) sl (o ∷ os)
                                   (proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ os))
                                                  (valsΨ? Ψ (o ∷ os)) vb))))))))
        (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl (n≤1+n J)))

-- THE TWO NEST PRESERVATIONS, and both are the share ring read once.
-- `nest` is antitone in the connected set, so a bound survives a step that
-- only enlarges it; `thruConsume-keeps` / `switchKill-keeps` are that
-- enlargement, per step, and `mList?-keeps` / `nest-keeps` do the rest.
thruConsume-nodry-nestRec : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (sl : Slots Γ) (bud : ℕ) (sf : Gas)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  mList? bud sl (EvalSt.connectedShares st₀) os ≡ true →
  let st₁ = proj₂ (proj₂ (proj₂ (thruConsume sf op nid κ id now o sched₀ st₀)))
  in mList? bud sl (EvalSt.connectedShares st₁) os ≡ true
thruConsume-nodry-nestRec sl bud sf op nid κ id now o os sched₀ st₀ h =
  mList?-keeps bud sl (EvalSt.connectedShares st₀)
    (EvalSt.connectedShares
      (proj₂ (proj₂ (proj₂ (thruConsume sf op nid κ id now o sched₀ st₀)))))
    os (KeepsC.connMono (thruConsume-keeps sf op nid κ id now o sched₀ st₀)) h

switchKill-nest : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (sl : Slots Γ) (bud : ℕ) (cur : Maybe NodeId) (o : Val Γ (obs u))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  nest o sl (EvalSt.connectedShares st₀) ≤ bud →
  nest o sl (EvalSt.connectedShares
               (proj₂ (proj₂ (switchKill {t = t} {e = e} cur sched₀ st₀)))) ≤ bud
switchKill-nest {t = t} {e = e} sl bud cur o sched₀ st₀ h =
  nest-keeps o sl (EvalSt.connectedShares st₀)
    (EvalSt.connectedShares (proj₂ (proj₂ (switchKill {t = t} {e = e} cur sched₀ st₀))))
    bud (KeepsC.connMono (switchKill-keeps cur sched₀ st₀)) h

-- THE WALK'S DEPTH, DOWN ONE ELEMENT.  `depthWalk` on a cons is the
-- element's own charge ⊔ the tail's, so the tail's is under the whole —
-- and the tail is read at exactly the state `thruWalk` recurses from.
thruWalk-nodry-dep : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (dep : ℕ) (sf : Gas)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  depthWalk sf op nid κ id now (o ∷ os) sched₀ st₀ ≤ dep →
  let r      = thruConsume sf op nid κ id now o sched₀ st₀
      sched₁ = proj₁ (proj₂ (proj₂ r))
      st₁    = proj₂ (proj₂ (proj₂ r))
  in depthWalk sf op nid κ id now os sched₁ st₁ ≤ dep
thruWalk-nodry-dep dep sf op nid κ id now o os sched₀ st₀ h =
  ≤-trans (m≤n⊔m _ _) h

-- ONE FRAME'S ALLOWANCE, OPENED FOR THE TRAVERSAL INSIDE IT.  `fLvlD S W
-- (suc d) j` unfolds to exactly an `sIterD` at `d`, over `suc (widAt S W j)`
-- payloads, at `k = suc (sizeAt S (suc j))`, starting from `fLvl S W j` --
-- so a traversal that fits those two counts fits inside the frame, and the
-- `k` slot is `≤-refl` whenever the bud is pinned to the frame's own refresh.
-- Both frame boundaries that open a payload traversal spend this: the
-- thru-outer frame over a value list, and the from-inner frame over a
-- mergeAll queue.
--
-- THE FUEL IS TAKEN AS `pred d`, NOT BY SPLITTING `d`, and that is what
-- makes it usable at both.  A frame charges itself one level before opening
-- the traversal, so `1 ≤ d` is free at every such call site; matching on THAT
-- rather than on `d` keeps a caller with a thirty-arm clause tree from
-- having to split all of it just to name `d′`.
frame-room : ∀ (S W d m j : ℕ) → 2 ≤ S → 1 ≤ d →
  m ≤ suc (widAt S W j) →
  sIterD S W (pred d) (suc (sizeAt S (suc j))) m j ≤ fLvlD S W d j
frame-room S W zero     m j 2≤S ()      hm
frame-room S W (suc d′) m j 2≤S (s≤s _) hm =
  ≤-trans (sIterD-mono m (suc (widAt S W j)) d′ d′
             (suc (sizeAt S (suc j))) (suc (sizeAt S (suc j)))
             2≤S ≤-refl ≤-refl (m≤m+n j _) ≤-refl ≤-refl hm)
          (≤-reflexive (sym (fLvlD-suc S W d′ j)))

-- THE FRAME'S OWN ARC, SPENT.  A frame clause that opens a traversal charges
-- itself first, so the hypothesis in hand is `suc <inner> ≤ d`; this reads the
-- inner charge back out at `pred d`, again without splitting `d` at the
-- caller.  Matching `s≤s` is what forces the fuel to be a successor, so the
-- two lemmas agree on `pred d` by construction rather than by convention.
fuel-pred : ∀ {m d : ℕ} → suc m ≤ d → m ≤ pred d
fuel-pred (s≤s h) = h

-- `not x ≡ true` and `x ≡ false`, in both directions: the ledger
-- carries the ∧-composable form, the dry lemmas speak the other

-- THE SEVERING CLOSE IS NEVER DRY.  `cutThrough` (Rx.Evaluator) is
-- the only event source shared by take's cut and switch's kill, and
-- every close it mints carries `cut` or `cutPending` — the two REASONS
-- an operator ends a chain.  `dried` is minted in exactly one place
-- (`subscribeInner g0`, Rx.Evaluator) and this is not it.  So both
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

------------------------------------------------------------------
-- ONE FRAME PRESERVES BOTH FLAVOURS — no longer one postulate.
--
-- `stepFrame-burst-face` is a REAL ASSEMBLY over the already-proven
-- caps face plus five per-frame WET leaves, of which the three
-- STATE-LOCAL ones are proven here and the two *All edges remain.
--
-- WHAT THE CAPS SIDE ALREADY GIVES.  `stepFrame-face` (.Caps-Face)
-- picks a j′ and reports the level bound, `capsOK?`, `valsCaps?` and
-- the emitted-events caps half, all at J+j′.  One more conjunct falls
-- straight out of that `capsOK?`: `regP? (pathSz? …)` IS
-- `capsOK?-regs`.  So five of the assembly's six obligations are
-- discharged by machinery that exists.
--
-- WHAT IS LEFT is the WET face of one frame (`WetFace`): five
-- Ψ-only conjuncts, all frame-invariant — no level index anywhere.
--
-- THE EVENTS CAPS HALF MOVED TO `FrameFace`.  It sat here
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
-- supplier (`subscribeInner-caps`, .Subscribe-Face, PROVEN) lives in
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
-- supplier (`innerFinish-caps`, .Subscribe-Face, PROVEN) lives in
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)

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
-- reduces mergeAll+yes through the PROVEN `mergeAllDrain-Ψ` walk to
-- `subscribeInner-Ψ` below — the Ψ face of the one function all three
-- *All-edge postulates bottom out in (`wet-thru` and
-- `subscribeInner-demand` (.Anchor-Dry) are the other two).
--
-- Ψ-PURE (the FrameFace move, `FrameFace`'s header): no level
-- index, no caps receipts.  What remains says only that a subscribe
-- PRESERVES the Ψ ledger — the same invariant `INV?`'s Ψ half claims
-- for whole subscribes (subscribeE-wet, tier 2) — so its proof is the
-- Ψ mirror of Subscribe-Face's proven caps clique, with the gas edge
-- into `subscribeE` as the one real recursion.
--
-- CALL-SITE ARGUMENTS THESE ABSORB: none — every index is pinned by
-- WetFace above.

-- THE Ψ RECEIPT A SUBSCRIBE FRAME HANDS BACK.  Ψ = fnCapᵉ e +
-- slotsFnCap sl is set once at init and the slots never move
-- (nextNode/live/ordinals never write that field), so the bound is a
-- statement about what the frame ADDS.  `fnCapBounded?` reads only
-- .live and .nodes; every new live entry has fnCap ≤ Ψ (a cold value
-- comes from a slot, and a `deferᵉ` body IS the b whose fnCapᵉ b ≤ Ψ),
-- and the new nodes are take-st/scan-st/… which are ≤ Ψ outright.
-- `regP?` grows only through `register`, at a path derived from κ, so
-- `pathBΨ? Ψ κ ≡ true` covers each new entry; `burstΨ?`'s base cases
-- emit init/close/complete, Ψ-bounded by definition, and map/scan go
-- through `applyFn-fnCap`.  The cost is that the induction covers every
-- clause, not that any one of them is undecided.
--
-- TWIN: the same clique at the caps measure is proven -- `subscribeE-caps`
--   over `subscribeInner-Ψ`'s descent, clause for clause, and the *All
--   family recurses through the inner exactly as it does there.
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

-- SPLIT LEMMAS — helpers for subscribeInner-Ψ's gs clause, over the
-- WHOLE burst.  Their per-emit halves moved DOWN to .Psi-Split, beside
-- the predicate and the other three flavours of the same reassembly,
-- when the level walk's map push face turned out to need them too —
-- same reason the dry trio moved out of this module before them.
-- Pattern mirrors splitBurst-vals-caps / splitBurst-bk-caps: pass xs to
-- all-++-intro explicitly so Agda unifies directly with the
-- splitBurst (em ∷ ems) → proj₁/proj₂ reduction.
private
  splitBurst-vals-Ψ : ∀ {n} {Γ : Ctx n} {u} {A : Set} (Ψ : ℕ)
    (burst : Stream Γ u) →
    burstΨ? Ψ burst ≡ true →
    valsΨ? Ψ (proj₁ (splitBurst {A = A} burst)) ≡ true
  splitBurst-vals-Ψ Ψ [] _ = refl
  splitBurst-vals-Ψ {u = u} {A = A} Ψ (em ∷ ems) h =
    all-++-intro _ (proj₁ (splitEvents {A = A} (InstEmit.events em))) _
      (splitEvents-vals-Ψ {A = A} Ψ (InstEmit.events em) (proj₁ (∧-true _ _ h)))
      (splitBurst-vals-Ψ {A = A} Ψ ems (proj₂ (∧-true _ _ h)))

  splitBurst-eventsΨ : ∀ {n} {Γ : Ctx n} {u t} (Ψ : ℕ) (burst : Stream Γ u) →
    eventsΨ? {u = t} Ψ (proj₁ (proj₂ (splitBurst {A = Val Γ t} burst))) ≡ true
  splitBurst-eventsΨ Ψ [] = refl
  splitBurst-eventsΨ {Γ = Γ} {t = t} Ψ (em ∷ ems) =
    all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ t} (InstEmit.events em)))) _
      (splitEvents-bk-Ψ {t = t} Ψ (InstEmit.events em))
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
-- straight through; the sixth is `applyFn-fnCap` (.Wet) pointwise
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

-- AND BACK.  `PbB` is a size half and a Ψ half, `regsSz?` IS `regP?` of the
-- size half, so the ledger recombines entrywise.  Spent where the two halves
-- are re-established by DIFFERENT faces — caps proves the size side at the
-- new level, this module's Ψ pass proves the other — and neither hands back
-- the conjunction.
regP?-of-parts : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (Ψ J : ℕ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? (Caps.cSize (frameStep J c)) rs ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) rs ≡ true →
  regP? (PbB c Ψ J) rs ≡ true
regP?-of-parts c Ψ J []       hs hΨ = refl
regP?-of-parts c Ψ J (r ∷ rs) hs hΨ =
  ∧-intro (∧-intro (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κᵣ)
                                  (regsSz? (Caps.cSize (frameStep J c)) rs) hs))
                   (proj₁ (∧-true (pathBΨ? Ψ κᵣ)
                                  (regP? (λ {v} p → pathBΨ? Ψ p) rs) hΨ)))
          (regP?-of-parts c Ψ J rs
             (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κᵣ)
                            (regsSz? (Caps.cSize (frameStep J c)) rs) hs))
             (proj₂ (∧-true (pathBΨ? Ψ κᵣ)
                            (regP? (λ {v} p → pathBΨ? Ψ p) rs) hΨ)))
  where
  κᵣ = proj₂ (proj₂ (proj₂ r))

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
-- The induction itself lives once in .Measures as `takeVals-all`; this
-- name stays because its call sites read it
takeVals-Ψ : ∀ {n} {Γ : Ctx n} {s} (Ψ k : ℕ) (vals : List (Val Γ s)) →
  valsΨ? Ψ vals ≡ true →
  valsΨ? Ψ (proj₁ (takeVals k vals)) ≡ true
takeVals-Ψ {s = s} Ψ k vals h = takeVals-all (valΨ? Ψ s) k vals h

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
  go (just (mergeAll-st _ _ _ _))    = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go (just (switch-st _ _))   = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go (just (exhaust-st _ _))  = wet-nil {u = s} c sl Ψ J fin sched st ok rg
  go nothing                  = wet-nil {u = s} c sl Ψ J fin sched st ok rg

------------------------------------------------------------------
-- THE SCAN LEAF — also a REAL PROOF, cribbed from
-- `stepFrame-scan-wet` (.Wet/Part1), the same clause proven against the
-- capᴱ ledger.  The one difference that matters: the caps half is NOT
-- re-derived (the assembly already holds it), so this needs only the
-- fnCap half of the node lookup — `lookupNode-fnCap` rather than the
-- two-sided `lookupNode-B`, whose `boundedNode` premise nothing at this
-- level can pay.

-- (`NodeΨ` / `lookupNode-fnCap` and the All ↔ all Ψ bridges all moved
-- DOWN to .Psi-Split, with the predicate — the level walk's scan push
-- needs the node lookup too and sits BELOW this module; imported back
-- through the wholesale open above)

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
... | just (mergeAll-st _ _ _ _)    | _ = wet-nil {u = u} c sl Ψ J fin sched st ok rg
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
-- `innerReact` (Rx.Evaluator) passes its payloads through UNTOUCHED
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
-- decomposition (`innerFinish-caps` over `mergeAllDrain-caps` over
-- `subscribeInner-caps`, Subscribe-Face): switch/exhaust rewrite
-- one node field on which `fnCapNode` is `true` outright, every
-- mismatched read is the evaluator's catch-all pass, and mergeAll+yes
-- is the drain.

-- the drain walk: one `subscribeInner-Ψ` receipt per queued inner,
-- threading the Ψ state invariant; the residue queue is a suffix of
-- the input, so its bound rides along rather than being re-derived.
-- AN INNER THAT STAYS OPEN NO LONGER STOPS THE WALK — it spends a
-- lane, and the walk stops on the LIMIT instead, so the recursion is
-- over the queue in both arms and the residue is whatever the gate
-- shut on
mergeAllDrain-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (allNid : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  all (λ o → fnCapᵉ o ≤ᵇ Ψ) q ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = mergeAllDrain g allNid κ id now lim act q sched st
      sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
      st′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
   × (all (λ o → fnCapᵉ o ≤ᵇ Ψ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
mergeAllDrain-Ψ sl Ψ g allNid κ id now lim act [] sched st slEq fc rg qB pB =
  slEq , fc , rg , refl , refl , refl
mergeAllDrain-Ψ sl Ψ g allNid κ id now lim act (o ∷ q) sched st slEq fc rg qB pB
  with hasRoom lim act
-- the gate is shut: nothing runs, and the residue is the input
... | false = slEq , fc , rg , refl , refl , qB
... | true
  with subscribeInner g mergeAllᵒ allNid κ id now o sched st
     | subscribeInner-Ψ sl Ψ g mergeAllᵒ allNid κ id now o sched st slEq fc rg
         (proj₁ (∧-true (fnCapᵉ o ≤ᵇ Ψ) (all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) q) qB)) pB
...   | (inst , vs , bs , done , sched₁ , st₁) | (slEq₁ , fc₁ , rg₁ , vsΨ , bsΨ)
  with mergeAllDrain g allNid κ id now lim (if done then act else suc act) q sched₁ st₁
     | mergeAllDrain-Ψ sl Ψ g allNid κ id now lim (if done then act else suc act)
         q sched₁ st₁ slEq₁ fc₁ rg₁
         (proj₂ (∧-true (fnCapᵉ o ≤ᵇ Ψ) (all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) q) qB)) pB
...     | (vs′ , bs′ , act′ , q′ , sched₂ , st₂) | (slEq₂ , fc₂ , rg₂ , vsΨ′ , bsΨ′ , qB′) =
      slEq₂ , fc₂ , rg₂
    , all-++-intro _ vs vs′ vsΨ vsΨ′
    , all-++-intro _ bs bs′ bsΨ bsΨ′
    , qB′

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

-- FLATTEN: the drain — the one clause with real content.  THE
-- UNBOUNDED LIMIT IS NOT A CLAUSE OF ITS OWN: it parks nothing, so its
-- queue is empty and the drain is the counter decrement the merge face
-- used to state separately
wet-innerFinish {s = s} c sl Ψ J sf id now mergeAllᵒ allNid instNid path′ vals sched st ok pb vb rg
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
... | just (switch-st _ _)   | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (exhaust-st _ _)  | _ = wet-pass c sl Ψ J vals false sched st ok
                                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                                    (valsΨ? Ψ vals) vb)) rg
... | just (mergeAll-st {w} lim act q od) | nb with w ≟ᵗ s
...   | no _     = wet-pass c sl Ψ J vals false sched st ok
                     (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals)
                                    (valsΨ? Ψ vals) vb)) rg
...   | yes refl =
        proj₁ D
      , ∧-intro (fcB-live Ψ sched′ st′ (proj₁ (proj₂ D)))
                (setNode-fnCap Ψ allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′)
                  q′B (fcB-nodes Ψ sched′ st′ (proj₁ (proj₂ D))))
      , all-++-intro _ vals (proj₁ dr)
          (proj₂ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb))
          (proj₁ (proj₂ (proj₂ (proj₂ D))))
      , proj₁ (proj₂ (proj₂ D))
      , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ D))))
    where
    D = mergeAllDrain-Ψ sl Ψ sf allNid path′ id now lim (pred act) q sched st
          (proj₁ (proj₁ ok)) (proj₂ ok)
          (regP?-Ψ c Ψ J (EvalSt.registry st) rg)
          nb
          (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c))
                           (from-inner mergeAllᵒ allNid instNid ↠ path′))
                         (pathBΨ? Ψ (from-inner mergeAllᵒ allNid instNid ↠ path′)) pb))
    dr     = mergeAllDrain sf allNid path′ id now lim (pred act) q sched st
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
... | just (mergeAll-st _ _ _ _) = wet-pass c sl Ψ J vals false sched st ok
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
... | just (mergeAll-st _ _ _ _) = wet-pass c sl Ψ J vals false sched st ok
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
-- mergeAllBump-fnCap, switchKill-Ψ, mergeAllConsume-Ψ, thruConsume-Ψ,
-- thruWalk-Ψ, thruWrap-Ψ, then the assembly `wet-thru`.

-- the bump moves the counter and leaves the queue, so the node written
-- carries the bound the node read carried — which the lookup hands
-- over, and is no longer `refl` now that one constructor holds both
mergeAllBump-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (nid : NodeId) (done : Bool)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) (mergeAllBump nid done nodes) ≡ true
mergeAllBump-fnCap Ψ nid done nodes h
  with lookupNode nid nodes | lookupNode-fnCap Ψ nid nodes h
... | just (mergeAll-st lim k q od) | qB =
    setNode-fnCap Ψ nid (mergeAll-st lim (if done then k else suc k) q od) nodes qB h
... | just (scan-st _)       | _ = h
... | just (take-st _)       | _ = h
... | just (switch-st _ _)   | _ = h
... | just (exhaust-st _ _)  | _ = h
... | nothing                | _ = h

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

mergeAllConsume-Ψ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (Ψ : ℕ) (g : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  fnCapBounded? Ψ sched st ≡ true →
  regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st) ≡ true →
  valΨ? Ψ (obs u) o ≡ true →
  pathBΨ? Ψ κ ≡ true →
  let r      = thruConsume g mergeAllᵒ nid κ id now o sched st
      sched′ = proj₁ (proj₂ (proj₂ r))
      st′    = proj₂ (proj₂ (proj₂ r))
  in (Sched.slots sched′ ≡ sl)
   × (fnCapBounded? Ψ sched′ st′ ≡ true)
   × (regP? (λ {v} p → pathBΨ? Ψ p) (EvalSt.registry st′) ≡ true)
   × (valsΨ? Ψ (proj₁ r) ≡ true)
   × (eventsΨ? Ψ (proj₁ (proj₂ r)) ≡ true)
mergeAllConsume-Ψ {u = u} sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-fnCap Ψ nid (EvalSt.nodes st) (fcB-nodes Ψ sched st fc)
... | just (mergeAll-st {w} lim act q od) | qB with w ≟ᵗ u
...   | no _     = slEq , fc , rg , refl , refl
...   | yes refl with hasRoom lim act
-- a lane is free: subscribe, and the bump leaves the queue alone
...     | true =
    slEq₁
    , ∧-intro (fcB-live Ψ sched₁ st₁ fc₁)
               (mergeAllBump-fnCap Ψ nid done (EvalSt.nodes st₁)
                  (fcB-nodes Ψ sched₁ st₁ fc₁))
    , rg₁ , vsΨ , bsΨ
    where
    R      = subscribeInner g mergeAllᵒ nid κ id now o sched st
    sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
    st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
    done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
    SI     = subscribeInner-Ψ sl Ψ g mergeAllᵒ nid κ id now o sched st slEq fc rg oΨ pΨ
    slEq₁  = proj₁ SI
    fc₁    = proj₁ (proj₂ SI)
    rg₁    = proj₁ (proj₂ (proj₂ SI))
    vsΨ    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
    bsΨ    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
-- the gate is shut: the payload joins the queue, and its own bound is
-- the one conjunct the append needs
...     | false =
    slEq
    , ∧-intro (fcB-live Ψ sched st fc)
               (setNode-fnCap Ψ nid (mergeAll-st lim act (q ++ o ∷ []) od)
                  (EvalSt.nodes st)
                  (all-++-intro _ q (o ∷ []) qB (∧-intro oΨ refl))
                  (fcB-nodes Ψ sched st fc))
    , rg , refl , refl
mergeAllConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | nothing                | _ = slEq , fc , rg , refl , refl
mergeAllConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (scan-st _)       | _ = slEq , fc , rg , refl , refl
mergeAllConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (take-st _)       | _ = slEq , fc , rg , refl , refl
mergeAllConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
    | just (switch-st _ _)   | _ = slEq , fc , rg , refl , refl
mergeAllConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
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
thruConsume-Ψ sl Ψ g mergeAllᵒ nid κ id now o sched st slEq fc rg oΨ pΨ =
  mergeAllConsume-Ψ sl Ψ g nid κ id now o sched st slEq fc rg oΨ pΨ
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
... | just (mergeAll-st _ _ _ _)    = slEq , fc , rg , refl , refl
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
... | just (mergeAll-st _ _ _ _)        = slEq , fc , rg , refl , refl
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
thruWrap-Ψ sl Ψ mergeAllᵒ nid true (vs , bs , sched , st) slEq fc rg vsΨ bsΨ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-fnCap Ψ nid (EvalSt.nodes st) (fcB-nodes Ψ sched st fc)
... | just (mergeAll-st lim act q od) | qB =
    slEq
  , ∧-intro (fcB-live Ψ sched st fc)
             (setNode-fnCap Ψ nid (mergeAll-st lim act q true) (EvalSt.nodes st) qB
               (fcB-nodes Ψ sched st fc))
  , rg , vsΨ , bsΨ
... | just (scan-st _)       | _ = slEq , fc , rg , vsΨ , bsΨ
... | just (take-st _)       | _ = slEq , fc , rg , vsΨ , bsΨ
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
... | just (mergeAll-st _ _ _ _)    = slEq , fc , rg , vsΨ , bsΨ
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
... | just (mergeAll-st _ _ _ _)    = slEq , fc , rg , vsΨ , bsΨ
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
-- (.Wet) is exactly the live half, and nodes ride through.
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
-- THE DRY FACE OF ONE FRAME (stepFrame-nodry) — WHERE THE ANCHOR'S RISK USED TO
-- LIVE, and it is now a real definition (the ruling is `cascadeGo-nodry`'s header).

-- One frame of one delivery, run on the WALK'S OWN MINTED GAS, emits
-- no dried close.  This is the ex-anchor (`cascadeGo-nodry`)
-- with everything transport-shaped stripped off: the walk carries
-- dryness through appends and widens mechanically (`EbB`/`BbB`'s third
-- flavour), so the entire dry content of the cascade concentrates in
-- this one per-frame face.

-- THE GAS HYPOTHESIS IS THE POINT.  `sf ≡ budgetAt e sl id` — the one
-- gas `chainStep` mints (Rx.Evaluator), carried to the frame by
-- the walk's GOK/g-mint hook (.Delivery-Walk, built for exactly this).
-- Without it the statement is FALSE: `subscribeInner g0` emits a
-- dried close and the depth premise does not exclude g0 (depth
-- measures nesting demand, not supply).

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
--           ARITHMETIC CHECKED TRUE (hand derivation, not
--           yet machine): with F j := cSize (frameStep j c), R ≤ S,
--           2 ≤ S, induct on j: F 0 = S ≥ R; F (suc j) = S + 2S·F j
--           (frameStep-size-suc) ≥ S·F j + S·F j ≥ F j + R·S, and
--           R·(1+(1+j)·S) = R·(1+jS) + RS ≤ F j + RS.  Uses only
--           R ≤ S ≤ F j (iterSize-infl) — no new machinery needed.
--      (ii) the fuel: `budgetAt e sl id hasAtLeast suc G` for a demand
--           G measured at Ŝ := sizeCapAt e sl (suc id) — the
--           general-id crib of `caps-fuel-root` (.Wet/Part6, PROVEN,
--           id = 0).  SHAPE CHECKED: `budgetAt e sl id`
--           unfolds to gasPad (2^(sz·suc id·suc id)) (gasTower
--           (3 + capsHgo m (suc id))) — the EXACT gas
--           `budget-hasAtLeast sz m id` (.Measures, PROVEN, general
--           id) is stated at — and the demand side's chain
--           (dBound-bound → prod≤3pow → tower-3 → capsAt-tower) is
--           general in id throughout; only the 6≤V and size-fits
--           facts change instantiation.  The inner value's size fits
--           under Ŝ by the walk's own landing arithmetic (lvl-fits +
--           capsAt-suc-full, `cascadeGo-burst-nodry`'s payoff arithmetic).

-- THIS FACE WAS THE ANCHOR'S RISKY REGION (a from-inner subscribe
-- mid-delivery), carried as FALSITY until it was ground.  The receipt
-- that still matters: it CANNOT BE PROBED, same as the anchor — the gas
-- family is abstract and `budgetAt` is a tower the checker will not
-- normalise — so the discharge is a proof, and never could have been a probe.
--
-- ═══ THE FIVE-FRAME CENSUS — ALL FIVE ARE NOW REAL ═══

-- `stepFrame-nodry` is an assembly over the frame constructors, and the risk
-- did NOT spread evenly across them.  The census is kept because it is what
-- located the consolidation below; the column says where each frame's dryness
-- CAME FROM, not what is still owed:
--
--   map-f    — events are literally `[]`.                    PROVEN, refl
--   scan-f   — every `dispatch` arm emits `[]`.              PROVEN, refl
--   take-f   — `takeDispatch`: `[]`, or `cutThrough`'s
--              closes, and CUTTHROUGH NEVER MINTS `dried`
--              (`cutThrough-nodry` — every close it
--              makes is `cut`/`cutPending`).                 PROVEN
--   from-inner — `innerReact` → `innerFinish`, whose only
--              emitting arm is mergeAllᵒ's `mergeAllDrain`.     via SiNodry
--   thru-outer — `thruWrap`/`thruWalk`/`thruConsume`, whose
--              events are `switchKill`'s closes (cutThrough
--              again, free) plus `subscribeInner`'s.         via SiNodry
--
-- ═══ THE CONSOLIDATION THAT FALLS OUT, and it is the finding ═══

-- Chase those two frames to their leaves and they MEET:
-- `mergeAllDrain` (Rx.Evaluator) emits nothing of its own — its `bs`
-- is `subscribeInner`'s, appended down the queue.  `switchKill` is
-- cutThrough.  So after the three proven frames, EVERY remaining
-- dried-close risk in the whole cascade is `subscribeInner`, whose two
-- clauses are:
--   · `g0`      — emits `close drySource dried` (Rx.Evaluator).
--                 THE one dry mint in the evaluator.  Excluded by the
--                 gas hypothesis: `budgetAt` is a `gasPad` of a
--                 `gasTower`, never `g0`.
--   · `gs fuel` — `subscribeE fuel …`, i.e. `subscribeE-walk-level`'s
--                 hasDry conjunct, at `fuel` — and the walk face asks for
--                 `g hasAtLeast suc G`, an INEQUALITY, not a pin to
--                 `budgetAt`, so the `gs`-peel goes straight through.
--                 Checked; had the walk pinned its gas the
--                 descent would not have typed.
--
-- ═══ THE LOOP QUESTION, RULED ═══

-- The two remaining frames are NOT one-step: `mergeAllDrain` and
-- `thruWalk` LOOP, calling `subscribeInner` at a state that has
-- already moved.  So the leaf's hypotheses (capsOK? and friends, all
-- state-dependent) must be RE-ESTABLISHED per iteration — which is
-- what the caps route's Σ-witness does and what a bare `≡ false`
-- conclusion cannot.  The gas hypothesis is the one part that threads
-- for FREE: `fuel` is passed unchanged by every one of innerReact,
-- innerFinish, mergeAllDrain, thruWalk, thruConsume and thruWrap
-- (checked), so the `g0` exclusion never has to be re-won.

-- TWO ROUTES WERE ON THE TABLE.  (A) take the already-proven caps
-- faces (siC/ifc) as extra parameters and re-establish `capsOK?` at
-- the moved state from their Σ-witness, mirroring what `stepFrame-burst-face` already
-- does one level up.  (B) widen SiCFace/IfcFace's own conclusions
-- with a nodry conjunct, so the re-establishment comes for free.

-- RULED: (A).  (B) is tidier to read and strictly worse to build —
-- its suppliers (`subscribeInner-caps`, `innerFinish-caps`) are
-- PROVEN inside Subscribe-Face, so widening their conclusions
-- re-grinds finished work in the most expensive module in the repo
-- (timings: typecheck-performance-numbers.md), and buys no strength that threading the same witness does not.
-- (A) also has a working precedent in this file rather than a
-- hypothetical one.

-- WHAT THAT MAKES THE TWO FRAMES: transport over ONE leaf, named
-- below as `SiNodry` and — at the time of the ruling — postulated once,
-- since PROVEN as `subscribeInner-nodry`.  The `-core` pair keeps
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
  -- THE PATH-LENGTH HYPOTHESIS, IN THE CAPS FACE'S OWN SHAPE.
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
  -- the reset-anchor ceiling: the walk face's pins force
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
-- (Rx.Evaluator) — is UNREACHABLE under the gas hypothesis, as a
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

-- THE SAME FACT WITH THE PAD COUNT KEPT.  budgetAt-gs
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
-- , with any-dry-++: the ground subscribeInner-walk
-- consumes the split there.  Imported back through the module import.

-- EX-RESIDUE, PROVEN.  It was postulated on the grounds
-- that `outWᵛ` sits outside this module's import scope — a missing
-- import, not a mathematical obstacle, and the wrong reason for a
-- postulate.  `dWᵛ` at an `obs` type IS `dWᵉ` (Rx.Frame-Width,
-- definitional) and `valCaps?` already carries
-- `pWᵛ n sl (obs u) o ≤ᵇ cWid` with `pWᵛ = outWᵛ ⊔ dWᵛ`, so the bound
-- is ⊔'s right injection.
--
-- WHAT ACTUALLY BLOCKED IT, recorded because the error message points
-- somewhere else: `valsCaps?` is NOT just `all valCaps?` — it carries
-- a second conjunct bounding the LIST LENGTH by `suc (cWid c)`
-- (Caps-Face/.Part5).  A hand-peel that assumes the `all` shape
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
-- subscribeE-inner-nodry-pSz and -pLen are BOTH GONE, and they
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

-- INV? AT THE INNER FRAME'S LEVEL, assembled from OKB + the regP? ledger
-- + the two slot bounds + the ladder's registration/size side condition.
-- Conjunct by conjunct: stBounded? is capsOK?'s own first; fnCapBounded?
-- is OKB's second; the registry CARDINALITY is capsOK?'s last conjunct
-- carried across `cReg ≤ cSize` at the level the conclusion is stated at;
-- regsB? recombines capsOK?'s regsSz? with regP?'s pathBΨ? half
-- (`regsB?-of-parts` — in .Psi-Split, beside the Ψ predicates it consumes;
-- it previously sat in .Caps-Bridge, downstream, and that placement was
-- this row's only blocker.  Nothing had to move DOWN and no all-zip
-- inlining is needed: .Caps-Bridge was downstream of all three ingredient
-- families, so the lemmas were simply left behind when the Ψ predicates
-- themselves were relocated); and the two slot conjuncts are hypotheses,
-- transported across walkOK's `Sched.slots sched ≡ sl`.

-- ⚠ SHAPE DEFECT FOUND AND REPAIRED — the SAME anti-pattern as `-pLen`
-- above ("a conclusion needing information that appears in NONE of its
-- hypotheses"), caught by reading the definitions rather than by a failed
-- grind.  INV?'s last two conjuncts are `slotsSize (Sched.slots sched) ≤ᵇ
-- B` and `slotsFnCap … ≤ᵇ Ψ`, and the ORIGINAL hypothesis list could reach
-- NEITHER: OKB is `walkOK × fnCapBounded?`, `walkOK` is
-- `slots-eq × capsOK?`, and capsOK? bounds live/nodes/registry/widths — it
-- never bounds the SLOT STORE's size or fn-weight, and fnCapBounded? reads
-- only live/nodes.  `PbB`/`VbB` are about the path and the value.  So the
-- statement was UNDERDETERMINED, not hard.

-- The repair MIRRORS a hypothesis already threaded at every level of this
-- stack: `slotsSize sl ≤ cSize c` was present all the way down (so that
-- conjunct was always reachable and only the transport was unstated); its
-- Ψ-side twin `slotsFnCap sl ≤ Ψ` was simply missing, and is now threaded
-- beside it through -core, subscribeE-inner-nodry and SiNodry.  At the true
-- instantiation Ψ := ΨAt e sl is `fnCapᵉ e + slotsFnCap sl`, so the new
-- hypothesis is `m≤n+m` — the same way `caps-fuel-root` (.Wet/Part6)
-- already discharges it.

-- ⚠ AND THE SAME DEFECT AGAIN, ONE CONJUNCT OVER — REFUTED,
-- machine-checked: `inner-nodry-inv-regLen-absurd` (agda/evidence/refuted,
-- Refuted.Inner-Nodry).  INV?'s THIRD conjunct is the registry CARDINALITY
-- against the SIZE cap, and the only hypothesis mentioning that length is
-- capsOK?'s last, which bounds it against the REGISTRATION cap.  The two
-- caps dimensions are independent, so a caps with `cReg > cSize` satisfies
-- every hypothesis and breaks the conclusion — the witness holds four root
-- chains under cReg 4 and cSize 3, with every other conjunct clear by a
-- margin.

-- THE LESSON, and it is why the row was misclassified: this row was called
-- GRINDABLE on the grounds that "every conjunct has a named source IN
-- SCOPE", and `frameStep-reg≤size` was one of the names.  A lemma being
-- PROVEN and in scope says NOTHING about its own hypotheses being
-- available where it is applied — that lemma needs `1 ≤ cSize c` and
-- `cReg c ≤ cSize c`, neither of which the statement carried.  So the
-- premise is now stated at the level the conclusion is stated at, where
-- the consumer discharges it from its own `2≤S` and `hCR`.

-- AND THE SLOT PREMISE IS RE-INDEXED RATHER THAN CONDITIONED.  It reads
-- `slotsSize sl ≤ Caps.cSize (frameStep J c)`, which is the WEAKER
-- hypothesis and therefore the STRONGER statement: the inflation transport
-- belongs at the call site, which owns the `2≤S` that `cSize≤frameStep`
-- needs.  No hypothesis was added for it.
subscribeE-inner-nodry-inv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  slotsSize sl ≤ Caps.cSize (frameStep J c) →
  slotsFnCap sl ≤ Ψ →
  Caps.cReg (frameStep J c) ≤ Caps.cSize (frameStep J c) →
  OKB {e = e} c sl Ψ J sched st →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  INV? Ψ (Caps.cSize (frameStep J c)) sched st ≡ true
subscribeE-inner-nodry-inv c sl Ψ J sched st slSz slFc rgSz ((slEq , cOK) , fcb) rp
  with capsOK?-parts (frameStep J c) sched st cOK
... | stB , rgSzP , _ , _ , rLen , _ =
  INV?-of-parts Ψ (Caps.cSize (frameStep J c)) sched st stB fcb
    (T⇒≡true (length (EvalSt.registry st) ≤ᵇ Caps.cSize (frameStep J c))
      (≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (length (EvalSt.registry st))
                            (Caps.cReg (frameStep J c)) (T-to rLen))
                     rgSz)))
    (regsB?-of-parts (EvalSt.registry st) rgSzP
      (regP?-Ψ c Ψ J (EvalSt.registry st) rp))
    (subst (λ x → (slotsSize x ≤ᵇ Caps.cSize (frameStep J c)) ≡ true) (sym slEq)
      (T⇒≡true (slotsSize sl ≤ᵇ Caps.cSize (frameStep J c)) (≤⇒≤ᵇ slSz)))
    (subst (λ x → (slotsFnCap x ≤ᵇ Ψ) ≡ true) (sym slEq)
      (T⇒≡true (slotsFnCap sl ≤ᵇ Ψ) (≤⇒≤ᵇ slFc)))

-- pathB? FOR THE EXTENDED PATH — a real body, and it is
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
-- THE ROUTE: gk via budgetAt-gs (gs-peel) and the demand chain
-- dBound-bound → prod≤3pow → tower-3 → m≤n+m.  The `sizeᵉ o ≤ Ŝr`
-- hypothesis derives at the call site from szO via frameStep-mono-j +
-- opIterD-infl + the caller's cl ceiling.
--
-- IT IS STATED AT THE RESET CAPS Ŝ := sizeCapAt e sl (suc id), not at a
-- level cap: the walk face's reset-anchor pins reject the level-cap
-- instantiation (frameStep J c cannot ceiling a walk that climbs past J),
-- and the reset caps are where budget-hasAtLeast lives — budgetAt e sl id
-- is minted from e's entry measures, so this form is the MORE provable one.
--
-- SEALED, AND THE SEAL MAY NOT COME OFF.  A transparent body here reaches
-- Verify-Well-Formed, which is the exact transition that OOMs a full build
-- (`Killed: 9` in VWF/Part13; the trap's instances are in
-- typecheck-performance-numbers.md).  No consumer needs more than the type.  private-impl + abstract-alias rather
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

  -- THE PATH-LENGTH BOUND, DERIVED — cribbed from
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
            (subscribeE-inner-nodry-inv c sl Ψ J sched st
               (≤-trans slSz (cSize≤frameStep c J 2≤S)) slFc
               (frameStep-reg≤size c J (≤-trans (s≤s z≤n) 2≤S) hCR)
               ok rg))
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
-- receipt `mergeAllDrain-nodry` drains against, and the whole reason that drain is
-- allowed to take one: the queue it is handed is not an arbitrary list but the
-- `q` of a `mergeAll-st` READ OUT OF THE NODE TABLE, which `capsOK?` bounds.
-- `innerReact-nodry` is the single site that performs the lookup, so the receipt
-- is minted there once and projected per element afterwards (`VbB-head` for the
-- element, `VbB-tail` for the recursive call).
--
-- ⚠ THIS REPLACES `mergeAllDrain-nodry-vb`, WHICH WAS REFUTABLE AS WRITTEN.  That
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
-- the reading stopped early.  `widNode`'s mergeAll clause COUNTS the queue
-- outright.  Read the whole record before concluding a conjunct is unreachable.
--
-- Sealed per the budget-sufficient-spine rule; the `with` on the slots equation
-- is why it is private-impl + abstract-alias rather than a plain block.
private
  mergeAllNode-vb-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (allNid : NodeId)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    VbB c sl Ψ J q ≡ true
  mergeAllNode-vb-go {n = n} c sl Ψ J allNid lim act q od sched st ok eqN
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
  mergeAllNode-vb : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (allNid : NodeId)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    VbB c sl Ψ J q ≡ true
  mergeAllNode-vb = mergeAllNode-vb-go

-- ─────────────────────────────────────────────────────────────────
-- THE NODRY RESIDUE, NOW EMPTY.  `innerReact-nodry` / `thruOuter-nodry` are
-- real bodies that case-split the evaluator's dispatch and APPLY
-- `subscribeInner-nodry` at each arm calling `subscribeInner`; what those
-- bodies could not pay used to be postulated here.  Nothing is: the one
-- surviving member is `switchKill-context`, a real body, and the four NOTEs
-- below are what it and its neighbours THREAD rather than assert.

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

-- NOTE ON ceiling, RESOLVED: the per-element ceiling is no
-- longer paid from the frame's fused `fLvlD` by an unstated inequality.
-- The thru walk threads an ABSTRACT ceiling level L̂ — `CL`'s own idiom,
-- one flavour down — and converts it to each element's budget with the
-- PROVEN Caps-Chain descents `inner-desc` then `walk-desc`.  The bud then
-- sits in the SAME `k` position on both sides of every step, so the
-- tension the *-nestBud rows were stuck on (one conjunct wants bud large,
-- the other wants it small) leaves the level algebra entirely; what
-- survives is a nest bound with no ceiling coupled to it, and one
-- k-and-index fit at the frame boundary.

-- NOTE ON loop invariants, RESOLVED: OKB/regP? after a
-- subscribeInner / thruConsume step are no longer leaves.  Each is the caps
-- face's own step (.Subscribe-Face) tensored with this module's Ψ face, with
-- `capsOK?-regs` and `regP?-of-parts` recombining the registry halves at the
-- level the step reports — so the level the walk re-reads its ledgers at is
-- CARRIED rather than asserted, which is what the refuted same-level form
-- (Refuted.Thru-Loop) got wrong.
-- OKB + regP? after switchKill; needed by the switch arm's
-- subscribeInner-nodry call.  A REAL BODY, and the whole of it is a
-- three-way split of the conjunction along the faces that already own the
-- pieces — nothing about `switchKill` is re-derived here.

-- WHY THIS ONE IS AT THE SAME LEVEL, where the thru side's same-level form
-- is REFUTED (Refuted.Thru-Loop): `switchKill` only ever DROPS.  It filters
-- the registry through `cutThrough`, sweeps `live` against the survivors and
-- grows `cancelled` — and `capsOK?` reads none of the last.  `thruConsume`'s
-- the mergeAll park GROWS a node's queue, which is what `capsOK?`'s width conjunct
-- bounds, so there a post-state need not satisfy the invariant at the level
-- its pre-state did.  Dropping cannot break an upper bound; appending can.

-- THE SPLIT.  `walkOK` is slots-eq × `capsOK?`, and the Ψ half is
-- `fnCapBounded?`, so the three pieces land on three faces:

--   Sched.slots ≡ sl    ← switchKill-Ψ's first conjunct (the record update
--                          touches `live`, never `slots`, so this is the
--                          hypothesis itself — but read it off the face that
--                          states it, not off record eta)
--   capsOK?             ← switchKill-caps (.Caps-Face/Part4), at frameStep J c
--   fnCapBounded?       ← switchKill-Ψ's second conjunct
--
-- and the registry ledger recombines entrywise: `regP?-Ψ` peels the Ψ half of
-- `PbB` to feed switchKill-Ψ, which hands the Ψ half back at the new state,
-- while the SIZE half comes out of the new `capsOK?` by `capsOK?-regs` —
-- `regsSz?` IS `regP?` of that half.  `regP?-of-parts` glues them.  Neither
-- face hands back the conjunction, which is why the peel-and-glue pair exists.
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
switchKill-context c sl Ψ J cur sched₀ st₀ ((slEq , cOK) , fcb) rp =
  ((proj₁ Ψr , cOK₁) , proj₁ (proj₂ Ψr))
  , regP?-of-parts c Ψ J (EvalSt.registry st₁)
      (capsOK?-regs (frameStep J c) sched₁ st₁ cOK₁)
      (proj₁ (proj₂ (proj₂ Ψr)))
  where
  sched₁ = proj₁ (proj₂ (switchKill cur sched₀ st₀))
  st₁    = proj₂ (proj₂ (switchKill cur sched₀ st₀))
  cOK₁   = switchKill-caps (frameStep J c) cur sched₀ st₀ cOK
  Ψr     = switchKill-Ψ sl Ψ cur sched₀ st₀ slEq fcb
             (regP?-Ψ c Ψ J (EvalSt.registry st₀) rp)

-- THE DRAIN'S LOOP INVARIANT, at the level the step LANDS at.  Exact twin of
-- `thruConsume-nodry-loop`: the caps half is the caps face's own
-- `subscribeInner-caps`, the Ψ half is this module's `subscribeInner-Ψ`, and
-- the registry's two halves are recombined by `capsOK?-regs` (the size half,
-- read at the NEW level out of the invariant the step reports) and
-- `regP?-of-parts`.
--
-- THE LEVEL IS REPORTED AND NOT ASSUMED, for the reason the thru side's
-- same-level form was refuted (Refuted.Thru-Loop): the park clause GROWS
-- the node's queue, and `capsOK?`'s width conjunct bounds that queue's length,
-- so a step's post-state need not satisfy the invariant at the level its
-- pre-state did.  `subscribeInner-caps` reports STRICTLY (`suc (j + j′) ≤ …`);
-- one `n≤1+n` relaxes it to the form the drain's own descent consumes.
mergeAllDrain-nodry-loop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (sf : Gas)
  (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (q : List (Closed Γ s))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  OKB {e = e} c sl Ψ J sched₀ st₀ →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ q) ≡ true →
  nest o sl (EvalSt.connectedShares st₀) ≤ bud →
  depthInner sf mergeAllᵒ allNid κ id now o sched₀ st₀ ≤ dep →
  regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
  let r      = subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  in Σ ℕ (λ j′ →
          OKB {e = e} c sl Ψ (J + j′) sched₁ st₁
        × regP? (PbB c Ψ (J + j′)) (EvalSt.registry st₁) ≡ true
        × (J + j′ ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc J)))
mergeAllDrain-nodry-loop {s = s} c sl Ψ dep bud J sf allNid κ id now o q sched₀ st₀
                       2≤S 1≤R slC slSz ok pb sspLen vb nst hD rg =
  j′
  , ((slEq₁ , inv₁) , fc₁)
  , regP?-of-parts c Ψ (J + j′) (EvalSt.registry st₁)
      (capsOK?-regs (frameStep (J + j′) c) sched₁ st₁ inv₁) rg₁
  , ≤-trans (n≤1+n (J + j′)) lvl
  where
  slEq  = proj₁ (proj₁ ok) ; inv = proj₂ (proj₁ ok) ; fc = proj₂ ok
  pb-sz = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  pb-bΨ = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  vb-c  = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ q)) (valsΨ? Ψ (o ∷ q)) vb)
  vb-Ψ  = proj₂ (∧-true (valsCaps? (frameStep J c) sl (o ∷ q)) (valsΨ? Ψ (o ∷ q)) vb)
  oC    = proj₁ (∧-true (valCaps? (frameStep J c) sl (obs s) o)
                        (all (valCaps? (frameStep J c) sl (obs s)) q)
                        (valsOf (frameStep J c) sl (o ∷ q) vb-c))
  oΨ    = proj₁ (∧-true (valΨ? Ψ (obs s) o) (all (valΨ? Ψ (obs s)) q) vb-Ψ)
  SI    = subscribeInner-caps c dep bud J sf mergeAllᵒ allNid κ id now o sl sched₀ st₀
            2≤S 1≤R slEq slC slSz inv oC pb-sz sspLen nst hD
  j′ = proj₁ SI ; inv₁ = proj₁ (proj₂ SI)
  lvl = proj₂ (proj₂ (proj₂ (proj₂ SI)))
  SΨ    = subscribeInner-Ψ sl Ψ sf mergeAllᵒ allNid κ id now o sched₀ st₀
            slEq fc (regP?-Ψ c Ψ J (EvalSt.registry st₀) rg) oΨ pb-bΨ
  slEq₁ = proj₁ SΨ ; fc₁ = proj₁ (proj₂ SΨ) ; rg₁ = proj₁ (proj₂ (proj₂ SΨ))
  r = subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))

-- THE REMAINING QUEUE'S NEST LEDGER, ACROSS ONE STEP.  `nest` is antitone in
-- the connected set and `subscribeInner` only ever enlarges it, which is
-- exactly what the share-ledger ring proves per step; `mList?-keeps` lifts it
-- over the whole queue.  Nothing about the step's own element is needed.
mergeAllDrain-nodry-nestRec : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (bud : ℕ) (sf : Gas)
  (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (q : List (Closed Γ s))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  mList? bud sl (EvalSt.connectedShares st₀) q ≡ true →
  let st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂
              (subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀)))))
  in mList? bud sl (EvalSt.connectedShares st₁) q ≡ true
mergeAllDrain-nodry-nestRec sl bud sf allNid κ id now o q sched₀ st₀ h =
  mList?-keeps bud sl (EvalSt.connectedShares st₀)
    (EvalSt.connectedShares
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀)))))))
    q (KeepsC.connMono (subscribeInner-keeps sf mergeAllᵒ allNid κ id now o sched₀ st₀)) h

------------------------------------------------------------------
-- mergeAllDrain-nodry — structural recursion over the mergeAll queue.
-- Applies subscribeInner-nodry at each element (THE FIT TEST).
--
-- slFc is taken as a direct parameter, threaded from module BurstWalk.
mergeAllDrain-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  -- THE QUEUE'S RECEIPT, minted once by `mergeAllNode-vb` at the node lookup in
  -- `innerReact-nodry` and projected per element here.  A genuine
  -- precondition and not a convenience of the call site: the unconditional
  -- per-element form (the retired `mergeAllDrain-nodry-vb`, git history) is
  -- refutable,
  -- because nothing ties a free `Closed Γ s` to this state.
  VbB c sl Ψ J q ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthDrain sf allNid κ id now q sched st ≤ dep →
  -- THE DRAIN'S THREE CHANNELS, and all three arrive from the caller — which
  -- is a RESTATEMENT and not a convenience.  The bud-and-ceiling pair used to
  -- be manufactured out of `ok` alone by `mergeAllDrain-nodry-nestBud`, and both
  -- of its conjuncts are refutable that way
  -- (`Refuted.MergeAll-Drain.mergeAllDrain-nodry-nestBud-absurd`): a free
  -- `Closed Γ s` has no nest bound, and OKB relates a `c`-derived cap to
  -- `sizeCapAt e sl` not at all.  What the refutation also showed is that the
  -- two must be DECOUPLED — one conjunct wanted the bud large, the other small
  -- — so the ceiling is now an abstract level L̂ and the bud rides beside it,
  -- meeting only through the proven Caps-Chain descents.
  --
  -- `sIterD … (length q) J` is the level this drain climbs to, one `sLvlD` per
  -- queue element, which is exactly what the caps face's `mergeAllDrain-caps`
  -- (.Subscribe-Face) already measures the same drain against.
  mList? bud sl (EvalSt.connectedShares st) q ≡ true →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length q) J ≤ L̂ →
  any dryEvent (proj₁ (proj₂ (mergeAllDrain sf allNid κ id now lim act q sched st))) ≡ false

mergeAllDrain-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                  lim act [] sched st _ _ _ _ _ _ _ _ _ _ = refl

mergeAllDrain-nodry {e = e} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                  lim act (o ∷ q) sched₀ st₀ ok pb sspLen vbq rg gk hD nst clL̂ dsc
  -- THE ONLY SCRUTINY IS THE GATE.  An inner that stays open no longer
  -- ends the walk — it spends a lane — so `done` never branches the
  -- drain, and is read only as the counter the tail is called at
  with hasRoom lim act
-- the gate is shut: the drain emits nothing at all
... | false = refl
--
-- The head's outputs are LET-BOUND PROJECTIONS, never `with`-scrutinised —
-- the same reason as `thruWalk-nodry`'s cons arm: abstracting the tuple
-- rebinds `sched₁`/`st₁` as fresh variables while `ok₁`/`rg₁` keep mentioning
-- a `proj… (subscribeInner …)` the abstraction never touched.
... | true =
  let step   = subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀
      bs     = proj₁ (proj₂ (proj₂ step))
      done   = proj₁ (proj₂ (proj₂ (proj₂ step)))
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ step))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ step))))
      S      = Caps.cSize c
      W      = Caps.cWid  c
      -- the nest ledger, split at the head by the ring's own projections
      nBst   = mList?-head bud sl (EvalSt.connectedShares st₀) o q nst
      nstT   = mList?-tail bud sl (EvalSt.connectedShares st₀) o q nst
      -- THE HEAD'S CEILING, by the two proven descents: this element's inner
      -- subscribe sits inside the drain's own step (`inner-desc`, on the
      -- element's SIZE and not on bud), and that step inside the drain
      -- (`walk-desc`).  Neither move mentions the ceiling, which is what
      -- decoupled the bud from it.
      dsc₀   = ≤-trans (inner-desc S W dep bud J (sizeᵉ o) 2≤S
                          (nodry-elem-size c sl Ψ J o q 2≤S vbq))
                       (≤-trans (walk-desc S W dep (suc bud) (length q) J) dsc)
      hDo    = ≤-trans (m≤m⊔n _ _) hD
      h-head = subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
                 J sf mergeAllᵒ allNid κ id now o sched₀ st₀
                 ok pb sspLen (VbB-head c sl Ψ J o q vbq) rg nBst hDo
                 (≤-trans (proj₁ (frameStep-mono-j c 2≤S dsc₀)) clL̂) gk
      loop   = mergeAllDrain-nodry-loop c sl Ψ dep bud J sf allNid κ id now o q sched₀ st₀
                 2≤S 1≤R slC slSz ok pb sspLen vbq nBst hDo rg
      j₁     = proj₁ loop
      ok₁    = proj₁ (proj₂ loop)
      rg₁    = proj₁ (proj₂ (proj₂ loop))
      hj₁    = proj₂ (proj₂ (proj₂ loop))
      -- every OTHER ledger is read again at the level the step landed at, and
      -- every one of them WIDENS upward; the ceiling is the only conjunct that
      -- gets harder, and `dsc₁` is where it is paid
      le₁    = m≤m+n J j₁
      mono₁  = frameStep-mono-j c 2≤S le₁
      pb₁    = ∧-intro (pathSz?-widen κ (proj₁ mono₁)
                          (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                         (pathBΨ? Ψ κ) pb)))
                       (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                      (pathBΨ? Ψ κ) pb))
      sspL₁  = ≤-trans sspLen (proj₁ mono₁)
      vbT    = VbB-tail c sl Ψ J o q vbq
      vb₁    = ∧-intro (valsCaps?-lvl _ _ sl q mono₁
                          (proj₁ (∧-true (valsCaps? (frameStep J c) sl q)
                                         (valsΨ? Ψ q) vbT)))
                       (proj₂ (∧-true (valsCaps? (frameStep J c) sl q)
                                      (valsΨ? Ψ q) vbT))
      nst₁   = mergeAllDrain-nodry-nestRec sl bud sf allNid κ id now o q sched₀ st₀ nstT
      dsc₁   = ≤-trans (sIterD-mono (length q) (length q) dep dep (suc bud) (suc bud)
                          2≤S ≤-refl ≤-refl hj₁ ≤-refl ≤-refl ≤-refl)
                       (≤-trans (≤-reflexive (sym (sIterD-suc S W dep (suc bud) (length q) J)))
                                dsc)
      h-tail = mergeAllDrain-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc (J + j₁) sf
                 allNid κ id now lim (if done then act else suc act)
                 q sched₁ st₁ ok₁ pb₁ sspL₁ vb₁ rg₁ gk
                 (≤-trans (m≤n⊔m _ _) hD) nst₁ clL̂ dsc₁
  in any-dry-++ bs _ h-head h-tail

-- Loop invariant after one thruConsume step: OKB + regP? at the level
-- the step LANDS at, with that level reported.
--
--
-- WHY.  The park clause is a pure GROWTH step: with the node's lanes
-- all taken, `thruConsume` appends the element to the node's
-- queue and emits nothing — which is exactly why the nodry conclusion
-- is `refl` there, and why nothing else in this block notices.  And
-- `capsOK?`'s width conjunct bounds that queue's LENGTH
-- (`widNode`'s `length q ≤ᵇ W`).  A queue sitting AT the cap is one
-- park from breaching it, and the same-level telescope said nothing about
-- the queue at all: CLAUDE.md's first almost-always-wrong shape.
--
-- IT IS NOT A ZERO-CAP ARTIFACT: the witness's caps are read off the
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
--
-- ⚠ REFUTED IN THE SAME-LEVEL FORM — `Refuted.Thru-Loop`,
--   and the witness computes: `capsOK?` on the post-state evaluates to
--   `false` while the conclusion demanded `true`.

-- IT IS NO LONGER A POSTULATE.  `thruConsume-caps` (.Subscribe-Face) is this
-- step's caps face, PROVEN, and it already reports the landing level in the
-- `sLvlD` shape above; this module's own `thruConsume-Ψ` is the other half.
-- What the postulate was missing was not a proof but the hypotheses the
-- report actually needs: a level report cannot come out of OKB and regP?
-- alone, since neither mentions the element, the bud or the depth fuel it is
-- measured against.  Those arrive here, and the postulate goes away entirely
-- rather than trading tracked debt for a signature.
thruConsume-nodry-loop : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (sf : Gas)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  OKB {e = e} c sl Ψ J sched₀ st₀ →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  nest o sl (EvalSt.connectedShares st₀) ≤ bud →
  depthConsume sf op nid κ id now o sched₀ st₀ ≤ dep →
  regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
  let r      = thruConsume sf op nid κ id now o sched₀ st₀
      sched₁ = proj₁ (proj₂ (proj₂ r))
      st₁    = proj₂ (proj₂ (proj₂ r))
  in Σ ℕ (λ j′ →
          OKB {e = e} c sl Ψ (J + j′) sched₁ st₁
        × regP? (PbB c Ψ (J + j′)) (EvalSt.registry st₁) ≡ true
        × (J + j′ ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc J)))
thruConsume-nodry-loop {u = u} c sl Ψ dep bud J sf op nid κ id now o os sched₀ st₀
                       2≤S 1≤R slC slSz ok pb sspLen vb nst hD rg =
  j′
  , ((slEq₁ , inv₁) , fc₁)
  , regP?-of-parts c Ψ (J + j′) (EvalSt.registry st₁)
      (capsOK?-regs (frameStep (J + j′) c) sched₁ st₁ inv₁) rg₁
  , ≤-trans (n≤1+n (J + j′)) lvl
  where
  slEq  = proj₁ (proj₁ ok)
  inv   = proj₂ (proj₁ ok)
  fc    = proj₂ ok
  -- ∧-true's two Bool sides are given EXPLICITLY throughout, per this
  -- module's standing note: PbB, VbB and `all` on a cons all reduce to
  -- conjunctions the unifier will not recover from the equation alone.
  pb-sz = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  pb-bΨ = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  vb-c  = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ os))
                        (valsΨ? Ψ (o ∷ os)) vb)
  vb-Ψ  = proj₂ (∧-true (valsCaps? (frameStep J c) sl (o ∷ os))
                        (valsΨ? Ψ (o ∷ os)) vb)
  oC    = proj₁ (∧-true (valCaps? (frameStep J c) sl (obs u) o)
                        (all (valCaps? (frameStep J c) sl (obs u)) os)
                        (valsOf (frameStep J c) sl (o ∷ os) vb-c))
  oΨ    = proj₁ (∧-true (valΨ? Ψ (obs u) o) (all (valΨ? Ψ (obs u)) os) vb-Ψ)
  TC    = thruConsume-caps c dep bud J sf op nid κ id now o sl sched₀ st₀
            2≤S 1≤R slEq slC slSz inv oC pb-sz sspLen nst hD
  j′    = proj₁ TC
  inv₁  = proj₁ (proj₂ TC)
  lvl   = proj₂ (proj₂ (proj₂ (proj₂ TC)))
  TΨ    = thruConsume-Ψ sl Ψ sf op nid κ id now o sched₀ st₀
            slEq fc (regP?-Ψ c Ψ J (EvalSt.registry st₀) rg) oΨ pb-bΨ
  slEq₁ = proj₁ TΨ
  fc₁   = proj₁ (proj₂ TΨ)
  rg₁   = proj₁ (proj₂ (proj₂ TΨ))
  r      = thruConsume sf op nid κ id now o sched₀ st₀
  sched₁ = proj₁ (proj₂ (proj₂ r))
  st₁    = proj₂ (proj₂ (proj₂ r))

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
  -- THE WALK'S DEPTH, NOT THE FRAME'S.  `depthFrame`'s thru-outer clause is
  -- `suc (depthWalk …)` — the frame is the one arc of the cycle that re-reads
  -- the budget — so the walk and everything under it is stated one fuel
  -- below the frame, exactly as `fLvlD S W (suc d) J` unfolds to its payload
  -- walk at `d`.  `thruOuter-nodry` pays the `suc` once, where it is minted.
  depthWalk sf op nid κ id now (o ∷ os) sched st ≤ dep →
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
-- unfolds through `thruConsume`, so in the mergeAll/exhaust arms (whose
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
  -- `ok` alone was refutable in both halves (`Refuted.MergeAll-Drain`), so both
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

-- FLATTEN: dispatch on node state.
-- The scrutinee and the clause ORDER both mirror Rx.Evaluator's own
-- `with w ≟ᵗ u` exactly.  Writing `w ≟ᵗ _` here does not abstract the
-- goal's occurrence (the metavariable is not syntactically the
-- evaluator's `u`), leaving the with-function stuck and `refl` red.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _     = refl
...   | yes refl with hasRoom lim act
-- a lane is free: one subscribeInner call, events = bs
...     | true  =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) hD) nBst clL̂ dsc
-- the gate is shut: the element is parked and nothing is emitted
...     | false = refl
-- other node shapes: thruConsume's own catch-all emits [].  These are
-- enumerated rather than written `| _`, because a VARIABLE scrutinee
-- leaves the evaluator's with-function stuck — its catch-all only fires
-- once Agda knows the shape is none of the mergeAll cases.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | nothing = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (scan-st _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (take-st _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (switch-st _ _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
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
      hD-elem    = ≤-trans (m≤m⊔n _ _) hD
      h-bs       = subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
                     J sf switchᵒ nid κ id now o sched₁ st₁
                     ok₁ pb sspLen vb-elem rg₁ nB hD-elem cl-elem gk
  in any-dry-++ (proj₁ (switchKill cur sched₀ st₀)) _ h-closes h-bs
... | nothing = refl
... | just (scan-st _) = refl
... | just (take-st _) = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (exhaust-st _ _) = refl

-- EXHAUST active=true: drops the payload, emits []
thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf exhaustᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = refl
-- EXHAUST active=false: subscribes, emits bs
... | just (exhaust-st false od) =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf exhaustᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) hD) nBst clL̂ dsc
... | nothing = refl
... | just (scan-st _) = refl
... | just (take-st _) = refl
... | just (mergeAll-st _ _ _ _) = refl
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
  depthWalk sf op nid κ id now vals sched st ≤ dep →
  -- THE WALK'S CEILING CHANNEL.  `sIterD … (length vals) J` is the level
  -- this traversal climbs to — one `sLvlD` per payload, which is what
  -- `stepThru-walk` (.Walk-Level) already measures the same `thruWalk`
  -- against — and L̂ is any level that covers it.
  mList? bud sl (EvalSt.connectedShares st) vals ≡ true →
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
      -- the nest ledger, split at the head by the ring's own projections
      nBst   = mList?-head bud sl (EvalSt.connectedShares st₀) o os nst
      nstT   = mList?-tail bud sl (EvalSt.connectedShares st₀) o os nst
      -- THE HEAD'S CEILING, by the two proven descents: this element's
      -- operator sweep sits inside the walk's own step (`inner-desc`, on
      -- the element's SIZE and not on bud), and that step inside the walk
      -- (`walk-desc`).  Neither move mentions the ceiling, which is what
      -- decoupled the bud from it.
      dsc₀   = ≤-trans (inner-desc S W dep bud J (sizeᵉ o) 2≤S
                          (nodry-elem-size c sl Ψ J o os 2≤S vb))
                       (≤-trans (walk-desc S W dep (suc bud) (length os) J) dsc)
      h-head = thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now o os
                 sched₀ st₀ ok pb sspLen vb rg gk hD nBst clL̂ dsc₀
      loop   = thruConsume-nodry-loop c sl Ψ dep bud J sf op nid κ id now o os sched₀ st₀
                 2≤S 1≤R slC slSz ok pb sspLen vb nBst (≤-trans (m≤m⊔n _ _) hD) rg
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
      nst₁   = thruConsume-nodry-nestRec sl bud sf op nid κ id now o os sched₀ st₀ nstT
      hD₁    = thruWalk-nodry-dep dep sf op nid κ id now o os sched₀ st₀ hD
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
-- innerReact-nodry — from-inner frame; real body applying mergeAllDrain-nodry.
-- All arms except mergeAllᵒ + (just (mergeAll-st lim act q od)) + yes refl
-- emit [].
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
-- opened, so innerReact-nodry is allowed exactly ONE nested `with` (mergeAll's
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
-- `in eqN` CAPTURES THE LOOKUP EQUATION, which is what `mergeAllNode-vb` needs
-- in the mergeAll arm below and what a plain `with` discards.  It costs no
-- clause changes anywhere in this 30-arm block: `in` NAMES the proof, it does
-- not add a pattern position — nor a `with` nesting level, which this
-- function has no room for (see the note above).
...   | false with op | lookupNode allNid (EvalSt.nodes st) in eqN
-- FLATTEN: every arm EXCEPT the type-matching one emits []
...     | mergeAllᵒ | nothing                      = refl
...     | mergeAllᵒ | just (scan-st _)             = refl
...     | mergeAllᵒ | just (take-st _)             = refl
...     | mergeAllᵒ | just (switch-st _ _)         = refl
...     | mergeAllᵒ | just (exhaust-st _ _)        = refl
-- SWITCH: innerFinish emits []
...     | switchᵒ | just (switch-st (just c₀) od) =
            innerFinish-switch-nodry sf allNid inst c₀ path′ id now vals od sched st
...     | switchᵒ | just (switch-st nothing od)   = refl
...     | switchᵒ | nothing                       = refl
...     | switchᵒ | just (scan-st _)              = refl
...     | switchᵒ | just (take-st _)              = refl
...     | switchᵒ | just (mergeAll-st _ _ _ _)           = refl
...     | switchᵒ | just (exhaust-st _ _)         = refl
-- EXHAUST: innerFinish emits []
...     | exhaustᵒ | just (exhaust-st act od)     = refl
...     | exhaustᵒ | nothing                      = refl
...     | exhaustᵒ | just (scan-st _)             = refl
...     | exhaustᵒ | just (take-st _)             = refl
...     | exhaustᵒ | just (mergeAll-st _ _ _ _)          = refl
...     | exhaustᵒ | just (switch-st _ _)         = refl
-- FLATTEN, type-matching: THE ONLY arm that calls mergeAllDrain →
-- subscribeInner, and so the only one where subscribeInner-nodry is
-- APPLIED.  It opens the function's single nested `with` and therefore
-- must be the LAST clause — nothing may follow it.
...     | mergeAllᵒ | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
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
                  S       = Caps.cSize c
                  W       = Caps.cWid  c
                  vbq     = mergeAllNode-vb c sl Ψ J allNid lim act q od sched st ok eqN
                  vbq-c   = proj₁ (∧-true (valsCaps? (frameStep J c) sl q)
                                          (valsΨ? Ψ q) vbq)
                  -- THE DRAIN'S BUD IS THE FRAME'S REFRESH, exactly as at the
                  -- thru-outer boundary: `valsCaps→mList-strict` bounds every
                  -- queued payload's nesting by `sizeAt S (suc J)` at EVERY
                  -- share ledger, out of the per-element size half and the
                  -- threaded `slotsSize sl ≤ S`.  At that pin the ROOM
                  -- conjunct is `fLvlD`'s own `k`, so `frame-room` closes it
                  -- on the queue's LENGTH alone.
                  nst     = valsCaps→mList-strict c J sl (EvalSt.connectedShares st) q
                              (≤-trans (s≤s z≤n) 2≤S) slSz
                              (valsOf (frameStep J c) sl q vbq-c)
              -- hD reduces HERE and only here: the `with` above scrutinises
              -- `lookupNode allNid (nodes st)` and `w ≟ᵗ s`, so
              -- depthFrame → depthReact → depthFin → depthFinC has unfolded to
              -- `suc (depthDrain … q …) ≤ d`.  THE FRAME'S OWN ARC IS THE FUEL
              -- THE DRAIN RUNS ONE BELOW: `fuel-pred` hands the drain `pred d`
              -- and `frame-room` opens `fLvlD S W d J` at that same `pred d`,
              -- which is the only depth pairing the two sides can agree on —
              -- `fLvlD S W (suc d′) J` IS an `sIterD` at `d′`.  Relaxing the
              -- `suc` away instead (the earlier `n≤1+n`) left the drain at the
              -- frame's own fuel and made the room conjunct unprovable.
              in mergeAllDrain-nodry c sl Ψ (pred d) (sizeAt S (suc J)) (fLvlD S W d J)
                   2≤S 1≤R hCR slC slSz slFc J sf allNid path′ id now
                   lim (pred act) q sched st ok pb′ sspLen vbq rg gk
                   (fuel-pred hD) nst cl
                   (frame-room S W d (length q) J 2≤S (≤-trans (s≤s z≤n) hD)
                      (valsLen (frameStep J c) sl q vbq-c))

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

-- THE DEPTH FUEL SPLITS HERE, and only here.  `depthFrame`'s thru-outer
-- clause is `suc (depthWalk …)`: a frame is the one arc of the cycle that
-- RE-READS the budget, which is the same fact as `fLvlD S W (suc d) J`
-- unfolding to its payload walk at `d`.  So at zero the clause is
-- unreachable — a walk that subscribes cannot fit under no fuel at all —
-- and at suc the walk runs one level lower, at the REFRESHED budget.  This
-- is `stepThru-walk`'s (.Walk-Level) own shape; the two faces split their
-- fuel at the same place because it is the evaluator that decides where.
thruOuter-nodry c sl Ψ zero 2≤S 1≤R hCR slC slSz slFc J sf id now op nid path′ vals fin sched st ok pb vb rg gk cl ()
thruOuter-nodry c sl Ψ (suc d′) 2≤S 1≤R hCR slC slSz slFc J sf id now op nid path′ vals fin sched st ok pb vb rg gk cl hD =
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
      S       = Caps.cSize c
      W       = Caps.cWid  c
      -- the value ledger's caps half, read once and spent twice below
      vb-c    = proj₁ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)
      -- THE WALK'S BUD IS THE FRAME'S REFRESH, and nothing here guesses it:
      -- `valsCaps→mList-strict` bounds every admitted payload's nesting by
      -- `sizeAt S (suc J)` at EVERY share ledger, out of the per-element size
      -- half and the threaded `slotsSize sl ≤ S`.  At that pin the ROOM
      -- conjunct is `fLvlD`'s own `k` — `suc (sizeAt S (suc J))` — so the fit
      -- is `≤-refl` in the k slot, and all that is left is the payload count
      -- against `suc (widAt S W J)` (the same `valsCaps?` receipt) and the
      -- index against `fLvl S W J` (inflationary).
      nst     = valsCaps→mList-strict c J sl (EvalSt.connectedShares st) vals
                  (≤-trans (s≤s z≤n) 2≤S) slSz (valsOf (frameStep J c) sl vals vb-c)
      room    = frame-room S W (suc d′) (length vals) J 2≤S (s≤s z≤n)
                  (valsLen (frameStep J c) sl vals vb-c)
  in subst (λ x → any dryEvent x ≡ false) (sym eq)
           (thruWalk-nodry c sl Ψ d′ (sizeAt S (suc J)) (fLvlD S W (suc d′) J)
              2≤S 1≤R hCR slC slSz slFc J sf op nid path′ id now vals sched st
              ok pb′ sspLen vb rg gk (≤-pred hD) nst cl room)

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
takeDispatch-nodry nid vals fin sched st (just (mergeAll-st _ _ _ _))    = refl
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
... | just (mergeAll-st _ _ _ _)      = refl
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
--
-- History (mirror census, demand-side probe,
-- the can't-probe receipt): superseded by this discharge; recover the
-- full text from the parent of the landing commit if the route ever
-- needs re-litigating.  The can't-probe receipt SURVIVES on `stepFrame-nodry`'s header,
-- restated there.
------------------------------------------------------------------

-- (DELETED) `cascadeGo-burst-dry` sat here — `proj₁` of
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
