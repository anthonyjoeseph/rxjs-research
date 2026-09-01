-- Verify-Budget-Sufficient.Caps-Face.Part7
-- thruOuter-face … reach-via-size-absurd
module Verify-Budget-Sufficient.Caps-Face.Part7 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _∸_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (m+[n∸m]≡n; *-assoc; *-identityˡ; ^-distribˡ-+-*; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤; *-cancelˡ-≤;
  ≤-trans; ≤-refl; ≤-reflexive; +-identityʳ; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; *-mono-≤;
  *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; +-assoc; ⊔-lub; m≤m⊔n; m≤n⊔m; +-mono-≤; ⊔-mono-≤;
  ⊔-identityʳ; m⊔n≤m+n; *-distribˡ-+; *-distribʳ-+; m≤m*n; ^-*-assoc; *-comm; +-suc; ≤-pred;
  ≤-total)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; map; foldr)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-map)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted;
  InstEvent)
open import Rx.Exp       using (_×ᵗ_; obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵛ; Fn; applyFn)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; ent-step; reached-room; room-step; room-descend; base; walk)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-def; nestFac-monoS; 1≤nestFac; nestU; nestU-mono; nestU-room)
open import Verify-Budget-Sufficient.Subscribe-Face using (subscribeInner-caps; innerFinish-caps; stepFrame-caps)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; valsFit-of-max)
open import Verify-Budget-Sufficient.Nest-Walk using
  (nestDᵛˢ; foldPath-nodes; nodesMax; burstsOK; capsWalkOK; dispatchCapsOK; frameClosOK; frameDrainOK;
  capsDrainOK;
  fac-hoist; one-pow; FaceOK; faceAt; shareCapsOK)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade; depthChain; depthFold; depthShareGo; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (pathSzSum-cap; deliverLen; deliverNestD; deliverNestF; 1≤deliverNestF; chainsLenSum;
  chainsDelLen; chainsDelNestD; chainsDelNestF; 1≤chainsDelNestF; chainsDelSzSum;
  chainsDelNestF≡; chainsDelLen-chains; chainsDelNestD-chains; chainsDelSzSum-chains;
  chainsNestF≤; shareAdmit-len; shareAdmit-sz; admSz?)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦF-cap)
open import Verify-Budget-Sufficient.Fan-Caps using
  (fanLen; fanSq; delSize; delSq; delSq-monoᶜ; delSize-cap; delSq-cap; delSize-def; delSq-def)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using
  (foldPath-nest-regs; PathΦHyp; DispatchΦHyp; FrameΦHyp; valsΦ?; valsSz?;
   stepFrame-nest-Φ; stepFrame-regsSz; stepFrame-sz; Φ-to-bound)
open import Verify-Budget-Sufficient.Nodes-Nest-Walk using (foldPath-nest-nodes)
open import Verify-Budget-Sufficient.Live-Nest-Walk using
  (foldPath-nest-live; PathLiveHyp; walk-LiveHyp-go)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; pathNestD; chainsNestF; chainsSzSum; pathNestF; 1≤pathNestF; 1≤chainsNestF;
  nest-telescope; nest-scale; pow-distrib-*; storeNestMax; nestCapAt; nestOK?; nestFacAt;
  nestFacAt-def; 1≤nestFacAt; nest-inflate; realWidAt; realWidAt-def; nestIncAt; nestIncAt-def;
  size≤nestIncAt; m≤m^burst; nestBurstAt; 1≤nestBurstAt; nestUnit; slotsNestSum; liveNest;
  nodeNest; regsNestMax; sightCeil; slotWrapSum; nestCapAt-0; nestCap-mono₀; nestOK?-latch; nestOK?-store;
  storeNestMax-lub; storeNest-slots≤; storeNest-live≤; storeNest-nodes≤; storeNest-regs≤)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; scanVals; RegId; Chain; scan-st; take-st; mergeAll-st;
  switch-st; exhaust-st; setNode; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f; take-f;
  from-inner; thru-outer; cascadeLatch; cascadeFinish; takeDispatch; arrSource; chainsOf;
  chainsGo; cascadeGo; Path; arrTy; stepFrame; subscribeInner; mergeAllᵒ; switchᵒ; exhaustᵒ;
  thruWalk; thruWrap; innerFinish; innerReact; aliveThroughᶠ; cascade; sameSource; regAt;
  share-sink; root; dCapᶜ; dWalkᶜ; fLvlD; lvls; iterL; sLvlD; chainStep; budgetAt; arrTick;
  shareAdmit; shareLatch; foldPath; iterSize)
open import Rx.Slots using (Slots; slotsSize)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Delivery-Walk using
  (shareFinish-len; module Walk; Walk-Hyps)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN; delivN-cons; delivN-split; foldPath-sink-N; shareGo-cons-N; shareGo-skip-N;
  chainStep-deliv; cascadeGo-deliv; ⊑ᵈ-trans)
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; 8≤capsAt-size; Caps; capsAt; capsAt-base-size; capsAt-suc-full;
  capsAt-⊑-suc; capsH; cDel; _⊑ᶜ_; cDel-body; dCapᶜ-mono; dWalkᶜ-mono; frameStep; frameStep-0;
  iterSize-infl;
  frameStep-mono-j; frameStep-reg-mono; iterL-infl; sucJ≤fLvlD; regAt-mono; iterL-mono;
  iterSize-mono-count; lvls-add; lvls-infl; lvls-mono; size≤sizeCount; sizeCount;
  sizeCount-body)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; reach-reset; ∧-true; all-impl; 2X≡X+X)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over.  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthInner; depthFrame; depthReact; depthFin; depthWalk; depthCascade)
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers

open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (innerFinish-mergeAll-face; innerFinish-face-keep; thruOuter-face-core)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsAt-round-size; capsOK?; capsOK?-mono; eventCaps?; frameSz?; n≤capsAt-size; pathSz?;
  pathSz?-widen; regsSz?; regsSz?-widen; slotsCaps?; valCaps?; widNode; nestClosOK?ᵛ;
  nestClosOK?ᵛ-widen)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (clos-lift; face-charge; face-charge1; face-vals; mapFrame-caps; scanFrame-caps;
   scanVals-len; stepFrame-face-zero; takeDispatch-len; valsCaps?-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (foldPath-slots; capsOK?-count; capsOK?-delivered; capsOK?-nodeSz; capsOK?-nodeWid;
  capsOK?-regs; capsOK?-setNode; dropSweep-caps; face-lift; frameBud; FrameFace;
  lookupNode-caps; pathSz?-len; pathSz?-tail; shareLatch-caps; slotsCaps?-capsAt;
  takeDispatch-caps; valsCaps?; valsCaps?-lvl; walkOK; walkOK-finish)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (frameStep-⊑-+; valCaps?-size; valCaps?-wid; valCaps?-widen)
open import Decide using (T-to; T⇒≡true; ∧-intro; ∧-trueʳ)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using
  (nestWalkAt; nestWalkAt-def; unit+size≤nestWalkAt; nestCap-inc-sight≤capsH;
   nestUnit≤size; iterSize≤walkFac; walkFac≤nestWalkAt)

thruOuter-face :
  -- subscribeInner-caps  (.Subscribe-Face)
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (d j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (vals : List (Val Γ (obs u))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  -- SPENDING ARC 1.  `depthFrame … (thru-outer op nid) … = suc (depthWalk …)`
  -- — the one hop of the mirror that is a `suc` rather than the identity,
  -- because a frame is the arc of the cycle that RE-READS the budget and
  -- `fLvlD S W (suc d) J` unfolds to its payload walk at `d`
  suc (depthWalk g op nid κ id now vals sched st) ≤ d →
  FrameFace c d j sl
    (thruWrap op nid fin (thruWalk g op nid κ id now vals sched st))
thruOuter-face siC =
  thruOuter-face-core
    siC
    reach-reset
    (λ {n} {Γ} {t} {e} → foldPath-sink-N {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → shareGo-skip-N {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → shareGo-cons-N {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → shareFinish-len {n} {Γ} {t} {e})

-- the *All FINISH, face side.  Two of the three ops are the keep
-- above under one node write; mergeAll's is the drain, now landed
innerFinish-face :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  depthFin g op allNid inst κ id now vals sched st
    (lookupNode allNid (EvalSt.nodes st)) ≤ d →
  FrameFace c d j sl (innerFinish g op allNid inst κ id now vals sched st
                        (lookupNode allNid (EvalSt.nodes st)))

-- FLATTEN: the queue drain, and the one clause of the whole *All face
-- that appends a burst it did not already have.  THE UNBOUNDED LIMIT
-- IS NO LONGER A CLAUSE OF ITS OWN: it parks nothing, so its queue is
-- empty and the drain degenerates to the counter decrement the merge
-- face used to state separately — one obligation now covers both, and
-- the bounded limit between them that neither old face could express
innerFinish-face ifc c d j g mergeAllᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC slSz hD =
  innerFinish-mergeAll-face ifc c d j g allNid inst κ id now vals sl sched st
    2≤S 1≤R slEq slC inv pC lC vC slSz hD

-- SWITCH: clear the current-inner slot if this was it
innerFinish-face _ c d j g switchᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC _ _
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (scan-st _)       = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (take-st _)       = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (mergeAll-st _ _ _ _)    = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (exhaust-st _ _)  = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (switch-st nothing od) = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (switch-st (just cur) od) with cur ≡ᵇ inst
...   | false = innerFinish-face-keep c d j sl vals false sched st inv vC
...   | true  =
  innerFinish-face-keep c d j sl vals od sched
    (record st { nodes = setNode allNid (switch-st nothing od) (EvalSt.nodes st) })
    (capsOK?-setNode (frameStep j c) allNid (switch-st nothing od)
       sched st refl refl refl inv)
    vC

-- EXHAUST: clear the busy flag
innerFinish-face _ c d j g exhaustᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC _ _
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (scan-st _)       = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (take-st _)       = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (mergeAll-st _ _ _ _)    = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (switch-st _ _)   = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (exhaust-st act od) =
  innerFinish-face-keep c d j sl vals od sched
    (record st { nodes = setNode allNid (exhaust-st false od) (EvalSt.nodes st) })
    (capsOK?-setNode (frameStep j c) allNid (exhaust-st false od)
       sched st refl refl refl inv)
    vC

-- and the from-inner FRAME: a fin that nothing absorbs finishes the
-- inner, everything else forwards the payload untouched
innerReact-face :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick)
  (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  depthReact g op allNid inst κ id now vals sched st fin ≤ d →
  FrameFace c d j sl (innerReact g op allNid inst κ id now vals sched st fin)
-- an absorbed fin finishes nothing: `depthReact … false = 0`
innerReact-face _ c d j g op allNid inst κ id now vals false sl sched st
                2≤S 1≤R slEq slC inv pC lC vC _ _ =
  innerFinish-face-keep c d j sl vals false sched st inv vC
-- `depthReact … true = depthFin … (lookupNode …)`, and the aliveThroughᶠ
-- test below is NOT a scrutinee of the depth mirror, so `hD` survives the
-- with-abstraction untouched and reaches `innerFinish-face` as-is
innerReact-face ifc c d j g op allNid inst κ id now vals true sl sched st
                2≤S 1≤R slEq slC inv pC lC vC slSz hD
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = innerFinish-face-keep c d j sl vals false sched st inv vC
... | false = innerFinish-face ifc c d j g op allNid inst κ id now vals sl sched st
                2≤S 1≤R slEq slC inv pC lC vC slSz hD

-- SCAN, its own top-level piece as in the companion: the nested `with`
-- on the stored accumulator's type cannot be elaborated inside a
-- clause of the general frame case.  The receipt is EXACT — the width
-- factor is valsCaps?'s own conjunct, the size factor frameSz?'s
stepFrame-face-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (d j : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) (scan-f fn nid) ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  FrameFace c d j sl (stepFrame g id now (scan-f fn nid) κ vals fin sched st)
stepFrame-face-scan {s = s} {u = u} c d j g id now fn nid κ vals fin sl sched st
                    2≤S slC slEq inv fS vC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing                | _ = stepFrame-face-zero c d j u sl fin sched st inv
... | just (take-st _)       | _ = stepFrame-face-zero c d j u sl fin sched st inv
... | just (mergeAll-st _ _ _ _)    | _ = stepFrame-face-zero c d j u sl fin sched st inv
... | just (switch-st _ _)   | _ = stepFrame-face-zero c d j u sl fin sched st inv
... | just (exhaust-st _ _)  | _ = stepFrame-face-zero c d j u sl fin sched st inv
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = stepFrame-face-zero c d j u sl fin sched st inv
...   | yes refl =
  j′ , face-lift c d j j′
           (face-charge c j (length vals) (sizeᵗ fn) (proj₂ VP)
              (≤ᵇ⇒≤ (sizeᵗ fn) (Caps.cSize (frameStep j c)) (T-to fS)))
     , capsOK?-setNode (frameStep (j + j′) c) nid
         (scan-st (proj₂ run)) sched st
         (valCaps?-size (frameStep (j + j′) c) sl _ (proj₂ run) (proj₂ (proj₂ SC)))
         refl
         (subst (λ x → widNode (Caps.cWid (frameStep (j + j′) c)) x
                         (scan-st (proj₂ run)) ≡ true)
                (sym slEq)
                (valCaps?-wid (frameStep (j + j′) c) sl _ (proj₂ run)
                   (proj₂ (proj₂ SC))))
         (capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
            (frameStep-⊑-+ c 2≤S j j′) inv)
     , face-vals c j j′ sl (proj₁ run) 2≤S (proj₁ (proj₂ SC))
         (≤-trans (≤-reflexive (scanVals-len fn ac vals)) (proj₂ VP))
     , refl
  where
  run = scanVals fn ac vals
  VP  = valsCaps?-parts (frameStep j c) sl vals vC
  SC  = scanFrame-caps c j sl fn ac vals 2≤S slC fS
          (∧-intro (proj₁ nb)
                   (subst (λ x → (pWᵛ _ x u ac ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                          slEq (proj₂ nb)))
          (proj₁ VP)
  j′  = proj₁ SC

stepFrame-face :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (d j : ℕ) (sl : Slots Γ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) (f ↠ κ) ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  -- H1 and H2, the two the from-inner chain cannot source locally: the
  -- slot store fits the size cap, and this frame's depth fits the walk's
  slotsSize sl ≤ Caps.cSize c →
  depthFrame g id now f κ vals fin sched st ≤ d →
  FrameFace c d j sl (stepFrame g id now f κ vals fin sched st)

-- MAP: nothing touches the state, the receipt is one fold per node of
-- the step function, and the output is the input mapped
-- map/scan/take subscribe nothing, so `depthFrame` is 0 on all three and
-- neither new hypothesis is reached
stepFrame-face _ _ {s = s} {u = u} c d j sl g id now (map-f fn) κ vals fin sched st
               2≤S 1≤R slEq slC inv pS vC _ _ =
  j′ , face-lift c d j j′
           (face-charge1 c j (sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to fS)))
     , capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
         (frameStep-⊑-+ c 2≤S j j′) inv
     , face-vals c j j′ sl (map (applyFn fn) vals) 2≤S (proj₂ MP)
         (≤-trans (≤-reflexive (length-map (applyFn fn) vals)) (proj₂ VP))
     , refl
  where
  B   = Caps.cSize (frameStep j c)
  fS  = proj₁ (∧-true (frameSz? B (map-f fn))
                      ((suc (pathLen κ) ≤ᵇ B) ∧ pathSz? B κ) pS)
  VP  = valsCaps?-parts (frameStep j c) sl vals vC
  MP  = mapFrame-caps c j sl fn vals 2≤S slC fS (proj₁ VP)
  j′  = proj₁ MP

stepFrame-face _ _ c d j sl g id now (scan-f fn nid) κ vals fin sched st
               2≤S 1≤R slEq slC inv pS vC _ _ =
  stepFrame-face-scan c d j g id now fn nid κ vals fin sl sched st
    2≤S slC slEq inv
    (proj₁ (∧-true (frameSz? (Caps.cSize (frameStep j c)) (scan-f fn nid))
                   ((suc (pathLen κ) ≤ᵇ Caps.cSize (frameStep j c))
                      ∧ pathSz? (Caps.cSize (frameStep j c)) κ) pS))
    vC

-- TAKE: a prefix and a cut, no folds — j′ = 0 either way
stepFrame-face _ _ {s = s} c d j sl g id now (take-f nid) κ vals fin sched st
               2≤S 1≤R slEq slC inv pS vC _ _ =
  0 , face-lift c d j 0 z≤n
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ (proj₂ (proj₂ TD))))
                     (proj₂ (proj₂ (proj₂ (proj₂ TD)))) ≡ true)
            (sym (+-identityʳ j)) (proj₁ TDc)
    , subst (λ x → valsCaps? (frameStep x c) sl (proj₁ TD) ≡ true)
            (sym (+-identityʳ j))
            (∧-intro (proj₁ (proj₂ TDc))
               (T⇒≡true _ (≤⇒≤ᵇ
                  (≤-trans (takeDispatch-len nid vals fin sched st
                              (lookupNode nid (EvalSt.nodes st)))
                           (proj₂ VP)))))
    , subst (λ x → all (eventCaps? (frameStep x c) sl) (proj₁ (proj₂ TD)) ≡ true)
            (sym (+-identityʳ j)) (proj₂ (proj₂ TDc))
  where
  TD  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  VP  = valsCaps?-parts (frameStep j c) sl vals vC
  TDc = takeDispatch-caps (frameStep j c) nid vals fin sl sched st
          (lookupNode nid (EvalSt.nodes st)) slEq inv (proj₁ VP)

-- FROM-INNER and THRU-OUTER: the two *All edges, delegated whole to
-- the two pieces above
-- `depthFrame … (from-inner …) … fin` IS `depthReact … fin`, so `hD`
-- passes through with no transport at all
stepFrame-face _ ifc c d j sl g id now (from-inner op allNid inst) κ vals fin sched st
               2≤S 1≤R slEq slC inv pS vC slSz hD =
  innerReact-face ifc c d j g op allNid inst κ id now vals fin sl sched st
    2≤S 1≤R slEq slC inv (proj₂ pS2)
    (≤ᵇ⇒≤ (suc (pathLen κ)) B (T-to (proj₁ pS2))) vC slSz hD
  where
  B   = Caps.cSize (frameStep j c)
  -- frameSz? is `true` on both *All frames, so naming the frame again
  -- here would only mint a metavariable the reduction then hides
  pS1 = ∧-true true ((suc (pathLen κ) ≤ᵇ B) ∧ pathSz? B κ) pS
  pS2 = ∧-true (suc (pathLen κ) ≤ᵇ B) (pathSz? B κ) (proj₂ pS1)

-- `depthFrame … (thru-outer …) … = suc (depthWalk …)` — SPENDING ARC 1,
-- the one hop where the mirror is not the identity but a `suc`
stepFrame-face siC _ c d j sl g id now (thru-outer op nid) κ vals fin sched st
               2≤S 1≤R slEq slC inv pS vC slSz hD =
  thruOuter-face siC c d j g op nid κ id now vals fin sl sched st
    2≤S 1≤R slEq slC inv (proj₂ pS2)
    (≤ᵇ⇒≤ (suc (pathLen κ)) B (T-to (proj₁ pS2))) vC slSz hD
  where
  B   = Caps.cSize (frameStep j c)
  pS1 = ∧-true true ((suc (pathLen κ) ≤ᵇ B) ∧ pathSz? B κ) pS
  pS2 = ∧-true (suc (pathLen κ) ≤ᵇ B) (pathSz? B κ) (proj₂ pS1)

walkH :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (c : Caps) (d : ℕ) (sl : Slots Γ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  Walk-Hyps e (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
walkH siC ifc c d sl 2≤S 1≤R slC slSz = record
  { OK        = walkOK c sl
  ; Pb        = λ J p → pathSz? (Caps.cSize (frameStep J c)) p
  ; Vb        = λ J vs → valsCaps? (frameStep J c) sl vs
  -- TRIVIAL BURST INSTANTIATION: Eb and Bb are always true, so every
  -- closure fact is refl and Res.burst is never projected by callers.
  -- GAS-BLIND: the caps axis carries no fuel content, so GOK is ⊤;
  -- CEILING-BLIND for the same reason, so CL is ⊤
  ; GOK       = λ _ _ → ⊤
  ; g-mint    = λ _ _ _ _ _ → tt
  ; CL        = λ _ _ → ⊤
  ; cl-anti   = λ _ _ _ → tt
  ; Eb        = λ _ _ → true
  ; Bb        = λ _ _ → true
  ; e-nil     = λ _ → refl
  ; e-close   = λ _ _ → refl
  ; e-app     = λ _ _ _ _ _ → refl
  ; e-widen   = λ _ _ _ → refl
  ; b-nil     = λ _ → refl
  ; b-app     = λ _ _ _ _ _ → refl
  ; b-widen   = λ _ _ _ → refl
  ; b-deliv   = λ _ _ _ _ _ _ _ _ → refl
  ; b-handoff = λ _ _ _ _ _ _ → refl
  ; p-len     = λ J p h → pathSz?-len (Caps.cSize (frameStep J c)) p h
  ; p-tail    = λ J f p h → pathSz?-tail (Caps.cSize (frameStep J c)) f p h
  ; p-widen   = λ le p h → pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le)) h
  ; v-widen   = λ le vs h → valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le) h
  ; ok-reg    = λ J sched st ok → capsOK?-count (frameStep J c) sched st (proj₂ ok)
  ; ok-cons   = λ J rid sched st ok →
                  proj₁ ok , capsOK?-delivered (frameStep J c) rid sched st (proj₂ ok)
  ; ok-latch  = λ J i fin sched st ok →
                  proj₁ ok , shareLatch-caps (frameStep J c) i fin sched st (proj₂ ok)
  ; ok-finish = λ J i fin out ok → walkOK-finish c sl J i fin out ok
  ; sf-step   = λ J sf id now f path′ vals fin sched st ok hP hV hL _ _ hD →
                  let r  = stepFrame sf id now f path′ vals fin sched st
                      FC = stepFrame-face siC ifc c d J sl sf id now f path′ vals fin sched st
                             2≤S 1≤R (proj₁ ok) slC (proj₂ ok) hP hV slSz hD in
                  proj₁ FC
                  , proj₁ (proj₂ FC)
                  , ( trans (KeepsC.slotsEq
                               (stepFrame-keeps sf id now f path′ vals fin sched st))
                            (proj₁ ok)
                    , proj₁ (proj₂ (proj₂ FC)) )
                  , proj₁ (proj₂ (proj₂ (proj₂ FC)))
                  , capsOK?-regs (frameStep (J + proj₁ FC) c)
                      (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))
                      (proj₁ (proj₂ (proj₂ FC)))
                  , refl
  }

-- and the bound itself: the walk at level 0, then three widenings — the
-- dispatch gas to cDel's index (n ≤ cSize), the walk length to the
-- registry cap (length chains ≤ cReg), and dCapᶜ's own unfolding, which
-- is what `cDel` abbreviates
cascadeGo-deliveries :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  -- the walk's two new obligations, sourced one level up at `caps-tick`
  slotsSize sl ≤ Caps.cSize c →
  depthCascade a id chains sched st ≤ d →
  delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
    ≤ cDel c d
cascadeGo-deliveries siC ifc {n = n} {e = e} c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD =
  ≤-trans (W.Res.cnt (W.cascadeGo-go 0 a id chains sched st
             ((slEq , invʲ) , capsOK?-regs c sched st inv)
             pS (∧-intro (∧-intro vC refl) refl) tt hD))
    (≤-trans (dWalkᶜ-mono n (Caps.cSize c) (length chains)
                (regAt (Caps.cSize c) (Caps.cReg c) 0)
                2≤S ≤-refl ≤-refl ≤-refl n≤S ≤-refl
                (≤-trans lenB (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))))
             (≤-reflexive (sym (cDel-body c d))))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH siC ifc c d sl 2≤S 1≤R slC slSz)

------------------------------------------------------------------
-- THE CHARGE, IN THE CURRENCY THE WALK ACTUALLY PROVES — and the
-- currency the caps recurrence now SPENDS, so the charge is a theorem.
--
-- `Res.hi` says the level a cascade lands at is at most `lvls S W 0 D`,
-- which ITERATES `dLvl` once per delivery, and `dLvl` in turn iterates
-- `fLvl` once per frame.  The product this replaces
-- (`D * cSize * suc (suc cWid * suc cSize)`, whose right-hand factor is
-- `fCharge S W 0`, ONE FRAME'S RECEIPT READ AT LEVEL 0) charges every
-- delivery's frames at the level the CASCADE entered at; the iteration
-- charges each at the level the one before it LEFT.  That is the same
-- distinction entry-charging was refuted on one stratum down
-- (machine-refuted: a frame's own output breaches
-- the cap it was charged at), which is why the walk was rebuilt around
-- levels in the first place — and why the count the recurrence spends
-- was rebuilt around them too.
--
-- NOTHING IS LOST BY THE MOVE.  The product is DOMINATED by the
-- iteration — a linearity step at J = 0 gives `D * chargeAt S W 0` under
-- `lvls S W 0 D`, and `chargeAt S W 0` IS `cSize * fCharge S W 0`
-- (measured by a probe module since DELETED) — so every Instant-Height row the
-- product cleared this clears, with the same margin or more, and no
-- measurement is re-run.  `sizeCount` (.Caps) is now this level, its
-- pooled twin `poolBody` (Rx.Evaluator) the same level with every field
-- pooled, and `blowup-tower`'s count axis is `lvls-mono` where it was a
-- product of monotonicities
------------------------------------------------------------------

cascadeGo-level :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  depthCascade a id chains sched st ≤ d →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j →
     (j ≤ lvls (Caps.cSize c) (Caps.cWid c) d 0
             (delivN st (proj₂ (proj₂ r))))
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-level siC ifc {e = e} c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS slSz hD =
  W.Res.lvl GO , W.Res.hi GO , proj₂ (proj₁ (W.Res.good GO))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH siC ifc c d sl 2≤S 1≤R slC slSz)
  GO = W.cascadeGo-go 0 a id chains sched st
         ((slEq , invʲ) , capsOK?-regs c sched st inv)
         pS (∧-intro (∧-intro vC refl) refl) tt hD

-- and the assembly declared above: the landing level with the delivery
-- count widened to its own recursion, which is `sizeCount` by definition
-- THE ASSEMBLY, ground: the level the walk lands at, with the delivery
-- count widened to its own recursion.  Both pieces are theorems, so
-- this one is (the body is at the end of the next section, where
-- cascadeGo-level is)
cascadeGo-caps :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  slotsSize sl ≤ Caps.cSize c →
  depthCascade a id chains sched st ≤ d →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j → (j ≤ sizeCount c d)
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-caps siC ifc c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD =
  proj₁ LV
    , ≤-trans (≤-trans (proj₁ (proj₂ LV))
                       (lvls-mono D (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl
                          (cascadeGo-deliveries siC ifc c d a id chains sl sched st
                             2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD)))
              (≤-reflexive (sym (sizeCount-body c d)))
    , proj₂ (proj₂ LV)
  where
  D  = delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
  LV = cascadeGo-level siC ifc c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS slSz hD

------------------------------------------------------------------
-- THE CASCADE BOOKENDS AND THE CHAIN SNAPSHOT, ground.  Nothing here
-- is a caps argument: latching resets per-cascade scratch capsOK? does
-- not read, finishing is the same drop-and-sweep the share's finish is,
-- and the snapshot is a filter of the registry.
------------------------------------------------------------------

-- the latch resets delivered/cancelled/regWatermark/dying and may add
-- to completedSources — none of the five conjuncts sees any of them
cascadeLatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (cascadeLatch a st) ≡ true
cascadeLatch-caps c a sched st h with Arrival.isLast a
... | true  = h
... | false = h

cascadeFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  let r = cascadeFinish a sched st
  in capsOK? c (proj₁ r) (proj₂ r) ≡ true
cascadeFinish-caps c a sched st h with Arrival.isLast a
... | false = h
... | true  = dropSweep-caps c (arrSource a) sched st h

-- the snapshot is chainsGo's filter: source matches and the chain's
-- element type is the arrival's.  Same shape as shareAdmit's
chainsGo-caps : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  all (λ rc → pathSz? B (proj₂ rc)) (chainsGo a rs) ≡ true
chainsGo-caps B a [] h = refl
chainsGo-caps B a ((rid , s , (u , p)) ∷ r) h
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = chainsGo-caps B a r (proj₂ (∧-true _ _ h))
... | true  | no  _    = chainsGo-caps B a r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (chainsGo-caps B a r (proj₂ (∧-true _ _ h)))

chainsOf-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (st : EvalSt e) →
  regsSz? B (EvalSt.registry st) ≡ true →
  all (λ rc → pathSz? B (proj₂ rc)) (chainsOf a st) ≡ true
chainsOf-caps B a st = chainsGo-caps B a (EvalSt.registry st)

chainsGo-length : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  length (chainsGo a rs) ≤ length rs
chainsGo-length a [] = z≤n
chainsGo-length a ((rid , s , (u , p)) ∷ r)
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = ≤-trans (chainsGo-length a r) (n≤1+n _)
... | true  | no  _    = ≤-trans (chainsGo-length a r) (n≤1+n _)
... | true  | yes refl = s≤s (chainsGo-length a r)

chainsOf-length : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  length (chainsOf a st) ≤ length (EvalSt.registry st)
chainsOf-length a st = chainsGo-length a (EvalSt.registry st)

-- THE SLOT STORE SURVIVES A CHAIN STEP, one call into `foldPath` and so
-- one composition of `foldPath-slots`.
chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st))) ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st


-- AND SURVIVES THE WHOLE CHAIN FOLD, by the obvious induction over the
-- list: the cancelled arm changes nothing and the live arm composes the
-- step above with the tail.  It is one of the four components the
-- store's nesting is a `⊔` of, and the only one that needs no width at
-- all -- the slot store is threaded through the fold untouched, so its
-- nesting is not merely bounded but EQUAL.
cascadeGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))) ≡ Sched.slots sched₀
cascadeGo-slots a id [] sched₀ st₀ = refl
cascadeGo-slots a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true = cascadeGo-slots a id chains sched₀ st₀
... | false =
      let (emits , sched₁ , st₁) =
            chainStep id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      in trans (cascadeGo-slots a id chains sched₁ st₁)
               (chainStep-slots id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }))


-- AND NO CONSTANT MULTIPLE OF THE SYNTACTIC CEILING CAN WORK, BECAUSE
-- THE DESCENT IS A PRODUCT AND EVERY NARROW TERM IS A SUM.  That is
-- the difference between a width factor that is merely safe and one
-- that is structural.  The two refutations below kill one narrow
-- reading each, and either could be read as an off-by-a-constant that
-- a larger constant would fix.  It is not one.  `Harness.Main`'s
-- SERIES X decomposes the crossing instant and drives its two axes
-- INDEPENDENTLY (measured-not-rechecked, so it discharges nothing):
-- over a grid of fold depth `w` against source length `k` the descent
-- is `w * (k + 4) + 1` throughout, so the slope down the source axis
-- IS the fold depth.  `nestSyn`, `chainsNestD` and `storeNestMax` each
-- move with `w` alone and with `k` not at all, so no multiple of them
-- tracks a term in `w * k` however large it is taken.  `realWidAt` is
-- the one term in this vocabulary that moves with BOTH axes, which is
-- what makes `realWidAt * nestSyn` a product rather than a generous
-- constant, and why the width form clears every row the narrow ones
-- cross on.

-- AND THE CHAIN COUNT AND THE REGISTRY ARE FLAT ACROSS THAT WHOLE
-- GRID, both reading ONE at every cell, which is what says where the
-- growth is NOT.  It is not a longer selection for the cascade to fold
-- over, and it is not registrations accumulating as the fold threads
-- its state -- the two readings the shape of the recursion invites,
-- since both folds in this family carry their tail at the state the
-- head left.  What is left is the bounded limit's drain, which is
-- where all three refutations in this face already pointed.  The
-- positive mechanism is not read off this grid and is not claimed
-- here.

-- THE PENDING-SOURCE COMPONENT, which is where this statement is
-- FALSE.  A live source carries the values an emit has queued but not
-- yet dispatched, so a walk can leave one holding a value nested deeper
-- than anything the store held before.  It does, and the constructor
-- that does it is `deferᵉ`: its subscribe clause mints a live source of
-- its own with `elemTy = obs u` and the deferred BODY as the pending
-- payload, so `liveNest` reads the body's full depth.
--
-- AND THE ARGUMENT THAT SAID OTHERWISE WAS STRUCTURAL, WHICH IS WHY IT
-- HELD FOR SO LONG.  A live minted at a SCRIPTED slot takes its element
-- type from that slot, and `Slot`'s scripted constructor carries an
-- `isData` side condition that is false at every observable type -- so
-- no slot-minted live can carry an observable, and every family the
-- harness drives reads this component as zero.  All of that is true.
-- It is not exhaustive: the slot is one of TWO mint sites, and the
-- other one never meets `isData`.
--
-- THE OBVIOUS REPAIR IS ALSO DEAD, and it is dead for a reason worth
-- carrying rather than rediscovering.  Charging the ARRIVAL's payload
-- cannot cover the new live, because the payload IS the `deferᵉ` term
-- and `nestDᵉ` is zero there by design -- a deferred body is not
-- entered synchronously, so the synchronous measure declines to look
-- inside it.  The measure's zero and the store's content therefore
-- disagree at exactly one constructor, and every quantity built over
-- `nestDᵉ` -- the unit, the syntactic ceiling -- inherits the blindness.
-- What a repair must find is a term that sees a deferred body, and
-- `sizeᵛ` is one: the sighted measure descends where the synchronous
-- one stops, so the charge is the arrival's SIZE rather than its
-- depth, taken once per chain the selection carries.  That currency
-- costs nothing above, because the caps already bound an arrival's
-- size -- it is `valCaps?`'s first conjunct, which the tick holds
-- already -- so the premise the restatement needs is discharged where
-- the cascade is entered and never reaches a caller.
--
-- AND THE FOLD ABOVE IT IS THREADED IN THE LIVE COMPONENT'S OWN
-- CURRENCY, not in the store's, because the store is the one thing the
-- induction cannot carry: a walk GROWS the node table, so an inductive
-- step landing at `storeNestMax` of the state it produced could never
-- be brought back to the state it started from.  What does thread is
-- the pair the live component can actually reach -- the lives already
-- there, and the slots, which `cascadeGo-slots` proves the fold leaves
-- untouched.  The statement the caller wants follows because both are
-- summands of the same `⊔`.
--
-- THE SHAPE THAT COULD WORK IS THE μ STEP'S, NOT THE FRAME'S.  A μ
-- already jumps the level by a quadratic without paying an operator per
-- level, because its measure is RE-MINTED at the stepped level's size
-- cap rather than decremented.  A frame's sibling of that step is what
-- this leaf is waiting on, and it leaves the drain's conjunct
-- arithmetic — which is what kept the ceiling out of the types.
--
-- REFUTED: `Refuted.Chain-Step-Live-Nest`, three against one at a body
--   three layers deep and five against one at five, so the gap is
--   unbounded in the body's depth and no constant repairs it.
-- PROBED: `Probed.Chain-Step-Live-Nest` re-runs that same adversarial
--   family against THIS conclusion rather than a numeral standing in
--   for it.  Covered: the deferred-body rows the old form died on --
--   grown 3 against a charge of 16, grown 5 against 24 -- so the two
--   sides now move together where they used to diverge, and each is
--   pinned separately so a repair moving either fails naming a number.
--   Also covered, and it is the reason the file is not two rows: the
--   right side carries NO store term, so a step minting a live out of
--   a PARKED value would exceed it with the arrival left shallow.  The
--   attack is armed -- a limited merge whose first inner is a `deferᵉ`
--   leaves the second genuinely pending, and the node reads depth 2
--   and 4 -- and the grown fold stays at zero, so the drain does not
--   run inside a step and the missing store term is not owed here.
--   And the tight direction on the path: `frameNestF` is one at every
--   frame but `map-f`/`scan-f`, so two merge frames give the step a
--   second mint site while leaving the charge exactly where the
--   one-frame rows left it -- grown 3 against 19, grown 5 against 27.
--   And a `map-f`, the only frame that both exceeds a factor of one
--   and hands the step a value the ARRIVAL never carried: a constant
--   deferred body two and four deep, against a shallow arrival, mints
--   at the body's depth and the factor pays for it.  The constant must
--   be DEFERRED or the row cannot fail -- a plain deep observable
--   finishes inside the step and the grown fold stays at zero.
--   NOT covered: a share sink, whose mint site no row here reaches.
postulate
  chainStep-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) →
    let r = chainStep id a path sched st
    in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
         ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
           ⊔ slotsNestSum (Sched.slots sched)
           ⊔ pathNestF path * sizeᵛ (arrTy a) (arrVal a)

cascadeGo-live-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  foldr (λ l acc → liveNest l ⊔ acc) 0
        (Sched.live (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched₀)
      ⊔ slotsNestSum (Sched.slots sched₀)
      ⊔ chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
cascadeGo-live-nest a id [] sched₀ st₀ = ≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _)
cascadeGo-live-nest a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true =
  ≤-trans (cascadeGo-live-nest a id chains sched₀ st₀)
          (⊔-lub (m≤m⊔n _ _) (≤-trans tailBump (m≤n⊔m _ _)))
  where
  V = sizeᵛ (arrTy a) (arrVal a)

  tailBump : chainsNestF chains * V ≤ pathNestF c * chainsNestF chains * V
  tailBump =
    *-monoˡ-≤ V (≤-trans (≤-reflexive (sym (*-identityˡ (chainsNestF chains))))
                         (*-monoˡ-≤ (chainsNestF chains) (1≤pathNestF c)))
... | false =
  ≤-trans (cascadeGo-live-nest a id chains sched₁ st₁)
          (⊔-lub (⊔-lub liveArm slotsArm)
                 (≤-trans tailBump (m≤n⊔m _ _)))
  where
  st₀′ = record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }
  step = chainStep id a c sched₀ st₀′
  sched₁ = proj₁ (proj₂ step)
  st₁    = proj₂ (proj₂ step)

  slotsEq : Sched.slots sched₁ ≡ Sched.slots sched₀
  slotsEq = chainStep-slots id a c sched₀ st₀′

  V = sizeᵛ (arrTy a) (arrVal a)

  -- one chain's factor sits under the whole selection's, the rest of
  -- the list contributing a factor of at least one
  headBump : pathNestF c * V ≤ pathNestF c * chainsNestF chains * V
  headBump =
    *-monoˡ-≤ V (≤-trans (≤-reflexive (sym (*-identityʳ (pathNestF c))))
                         (*-monoʳ-≤ (pathNestF c) (1≤chainsNestF chains)))

  tailBump : chainsNestF chains * V ≤ pathNestF c * chainsNestF chains * V
  tailBump =
    *-monoˡ-≤ V (≤-trans (≤-reflexive (sym (*-identityˡ (chainsNestF chains))))
                         (*-monoˡ-≤ (chainsNestF chains) (1≤pathNestF c)))

  liveArm = ≤-trans (chainStep-nest-live id a c sched₀ st₀′)
                    (⊔-lub (m≤m⊔n _ _) (≤-trans headBump (m≤n⊔m _ _)))

  slotsArm =
    ≤-trans (≤-reflexive (cong slotsNestSum slotsEq))
            (≤-trans (m≤n⊔m (foldr (λ l acc → liveNest l ⊔ acc) 0
                                   (Sched.live sched₀))
                            (slotsNestSum (Sched.slots sched₀)))
                     (m≤m⊔n _ _))

-- AND THE CALLER'S FORM IS THE SAME FACT READ AGAINST THE WHOLE `⊔`,
-- since the two terms the induction threads are both summands of it.
cascadeGo-nest-live-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
       ≤ storeNestMax sched st
         ⊔ chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
cascadeGo-nest-live-flat a nextId chains sched st =
  ≤-trans (cascadeGo-live-nest a nextId chains sched st)
          (⊔-lub (⊔-lub (into (m≤n⊔m (slotsNestSum (Sched.slots sched)) _))
                        (into (m≤m⊔n (slotsNestSum (Sched.slots sched)) _)))
                 (m≤n⊔m _ _))
  where
  into : ∀ {m} →
    m ≤ slotsNestSum (Sched.slots sched)
        ⊔ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched) →
    m ≤ storeNestMax sched st
        ⊔ chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
  into h = ≤-trans h (≤-trans (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _)) (m≤m⊔n _ _))

cascadeGo-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  chainsNestF chains ≤ nestFacAt e sl id →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
       ≤ nestFacAt e sl id * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest-live {e = e} sl id a nextId chains sched st _ _ _ _ hsz hcf =
  ≤-trans (cascadeGo-nest-live-flat a nextId chains sched st)
          (⊔-lub storeArm chainArm)
  where
  RHS : ℕ
  RHS = storeNestMax sched st + nestIncAt e sl id

  storeArm : storeNestMax sched st ≤ nestFacAt e sl id * RHS
  storeArm = ≤-trans (m≤m+n (storeNestMax sched st) (nestIncAt e sl id))
                     (nest-inflate (nestFacAt e sl id) RHS (1≤nestFacAt e sl id))

  -- the arrival's own size is what the live fold gains, and the
  -- selection's factor is what it gains it once per chain for
  chainArm : chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
               ≤ nestFacAt e sl id * RHS
  chainArm =
    *-mono-≤ hcf
             (≤-trans hsz (≤-trans (size≤nestIncAt e sl id)
                                   (m≤n+m (nestIncAt e sl id)
                                          (storeNestMax sched st))))

-- THE BURST BOUND AT THE INDICES A CHAIN STEP FIXES, so that the fold
-- below and the caps face above name the same hypothesis.
chainBurstOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (W : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainBurstOK {n = n} {e = e} W id a path sched st =
  burstsOK W (budgetAt e (Sched.slots sched) id) n id (arrTick a) path
           (arrVal a ∷ []) (Arrival.isLast a) sched st

-- AND THE SAME PACKAGING FOR THE CAPS THE `*All` FRAMES SPEND, so a
-- consumer states one hypothesis per walk rather than one per frame.
chainCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c ac : Caps) (sl : Slots Γ) (d Lv : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainCapsOK {n = n} {e = e} c ac sl d Lv id a path sched st =
  capsWalkOK c ac sl d Lv (budgetAt e (Sched.slots sched) id) n id (arrTick a) path
             (arrVal a ∷ []) (Arrival.isLast a) sched st

-- THE STORE'S ONE ACCUMULATING CORNER, AND WHAT PAYS FOR IT IS THE
-- SELECTION.  Within the node arm the store deepens at two sites, not
-- five: `switch` and `exhaust` cannot move it whatever they store, and
-- a bounded `mergeAll`'s queue cannot either -- the measure over it is
-- a MAX, parking adds the single observable that arrived, and the
-- drain returns a SUFFIX of the queue it was handed.  What is left is
-- a `scan`'s accumulator, which the fold over an instant's values
-- genuinely deepens, and the inners a drain SUBSCRIBES, which install
-- their own nodes.
--
-- SO THE QUANTITY TO CHARGE IS THE CHAIN THE WALK IS WALKING, and the
-- whole of the claim is ONE CHAIN'S STEP.  Both storing sites sit under
-- a single `chainStep`, and the fold visits each chain once, so the
-- walk-level statement is a plain induction over the list -- the skip
-- arm weakens by a chain, the step arm spends this leaf and
-- re-associates -- and everything a single chain does to the store,
-- however many inners it subscribes, is invisible to a MAX that moves
-- once.
--
-- AND THE CHARGE IS THE PATH'S OWN, NOT THE PROGRAM'S.  A `scan` frame
-- carries its accumulator function, and the node the step installs is
-- that function applied to what arrived -- so the two quantities a step
-- can deepen by are the PAYLOAD's nesting and the wraps the frames
-- below it add, which is exactly what `pathNestD` counts.  Charging a
-- syntactic ceiling on `e` instead reads as tighter and is not even
-- true: the path is a free argument, so it is under no obligation to be
-- one of `e`'s.  Tying the two together is the CONSUMER's business,
-- where the chain list comes from the registry and the payload from a
-- slot, and it is a different fact from this one.
--
-- DEAD ROUTE: charging per MINTED INSTANCE, the same statement with the
--   schedule's own node counter in place of the length.  The count is
--   quadratic in the chain axis -- 20, 33, 48, 65 as `progF`'s width
--   climbs -- while every width in this development is linear in it, so
--   the charge is crossed by construction rather than by a constant:
--   at eighteen copies the path width and the entry ceiling are both
--   past, at twenty-two `capsBase` is too, 713 against 690.  The
--   counting is what fails and not the currency, the parent's own
--   conclusion holding at the crossing shape.  Do not re-derive a
--   tighter width for a mint count.
-- DEAD ROUTE: the two max-shaped charges, `store ⊔ nestSyn` and
--   `store + nestSyn`, which drop the count entirely on the reading
--   that a MAX cannot move more than one level per instant.  Both are
--   false at the same shape, the nodes map reading 26 against a store
--   of 3 and a `nestSyn` of 6.  A walk deepens once per CHAIN, so the
--   count that survives is a count of chains and there is no
--   count-free form of this row.
-- REFUTED: `Refuted.Chain-Step-Nodes` kills the `nestSyn` form of this
--   very statement, eleven against nine, and the gap is unbounded in
--   the fold depth of a frame the program never mentions.
chainStep-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c → c ⊑ᶜ ac →
  chainBurstOK W id a path sched st →
  chainCapsOK c ac sl d Lv id a path sched st →
  depthChain id a path sched st ≤ d →
  pathSz? (Caps.cSize ac) path ≡ true →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  ⦃ _ : FaceOK c sl ⦄ →
  let r = chainStep id a path sched st in
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ nestFac (Caps.cSize c′) W ^ deliverLen n ac path
      * (deliverNestF n ac path ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + W * (nestDᵛ (arrTy a) (arrVal a) + deliverNestD n ac path
                   + suc (deliverLen n ac path) * nestU (delSq n c′) (nestUnit e sl)))))
chainStep-nodes {n = n} {e = e} c ac d W sl Lv id a path sched st hsl 1≤W 1≤S hac hb hc hdp hpz hlv =
  proj₁ FP ,
  proj₁ (proj₂ FP) ,
  ≤-trans (proj₂ (proj₂ FP))
    (*-monoʳ-≤ (nestFac (Caps.cSize c′) W ^ deliverLen n ac path)
    (*-monoʳ-≤ (deliverNestF n ac path ^ W)
      (≤-trans (+-monoˡ-≤ (W * (deliverNestD n ac path + U))
                          (≤-trans (⊔-mono-≤ (≤-refl {nodesMax st})
                                             (≤-reflexive (⊔-identityʳ V)))
                                   (m⊔n≤m+n (nodesMax st) V)))
      (≤-trans (≤-reflexive (+-assoc (nodesMax st) V (W * (deliverNestD n ac path + U))))
               (+-monoʳ-≤ (nodesMax st) spread)))))
  where
  FP = foldPath-nodes c ac d W sl Lv (budgetAt e (Sched.slots sched) id) n id
         (arrTick a) (arrSource a) path (arrVal a ∷ [])
         (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
         (Arrival.isLast a) sched st hsl 1≤W 1≤S hac hb hc hdp
         hpz hlv
  c′ = frameStep (proj₁ FP) c
  V = nestDᵛ (arrTy a) (arrVal a)
  U = suc (deliverLen n ac path) * nestU (delSq n c′) (nestUnit e sl)

  spread : V + W * (deliverNestD n ac path + U) ≤ W * (V + deliverNestD n ac path + U)
  spread =
    ≤-trans (+-monoˡ-≤ (W * (deliverNestD n ac path + U)) (nest-inflate W V 1≤W))
      (≤-trans (≤-reflexive (sym (*-distribˡ-+ W V (deliverNestD n ac path + U))))
               (≤-reflexive (cong (W *_) (sym (+-assoc V (deliverNestD n ac path) U)))))

-- AND OVER A CASCADE'S CHAIN LIST, mirroring `cascadeGo`: a cancelled
-- registration walks nothing and owes nothing, and a delivered one owes
-- its own walk and then the rest of the fold at the state it left.
chainsBurstOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (W : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) → Set
chainsBurstOK W a nextId []               sched st = ⊤
chainsBurstOK W a nextId ((rid , c) ∷ chains) sched st =
  if any (_≡ᵇ rid) (EvalSt.cancelled st)
  then chainsBurstOK W a nextId chains sched st
  else (chainBurstOK W nextId a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
        × chainsBurstOK W a nextId chains
            (proj₁ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st }))))
            (proj₂ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- AND THE CAPS THE SAME FOLD SPENDS, arm for arm with the burst
-- hypothesis above: a cancelled registration walks nothing, so it owes
-- nothing here either.
chainsCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cp ac : Caps) (sl : Slots Γ) (d Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) → Set
chainsCapsOK cp ac sl d Lv a nextId []               sched st = ⊤
chainsCapsOK cp ac sl d Lv a nextId ((rid , c) ∷ chains) sched st =
  if any (_≡ᵇ rid) (EvalSt.cancelled st)
  then chainsCapsOK cp ac sl d Lv a nextId chains sched st
  else (chainCapsOK cp ac sl d Lv nextId a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
        × Σ ℕ λ L′ →
          (Lv + L′ ≤ sizeCount cp d ⊔ Caps.cSize cp)
        × chainsCapsOK cp ac sl d (Lv + L′) a nextId chains
            (proj₁ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st }))))
            (proj₂ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st })))))

cascadeGo-nodes-chains : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cp ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize cp → cp ⊑ᶜ ac →
  chainsBurstOK W a nextId chains sched st →
  chainsCapsOK cp ac sl d Lv a nextId chains sched st →
  depthCascade a nextId chains sched st ≤ d →
  all (λ rc → pathSz? (Caps.cSize ac) (proj₂ rc)) chains ≡ true →
  Lv ≤ sizeCount cp d ⊔ Caps.cSize cp →
  ⦃ _ : FaceOK cp sl ⦄ →
  let r = cascadeGo a nextId chains sched st in
  Σ ℕ λ j →
  let cp′ = frameStep j cp in
  (j ≤ sizeCount cp d ⊔ Caps.cSize cp)
  × (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ nestFac (Caps.cSize cp′) W ^ chainsDelLen n ac chains
      * (chainsDelNestF n ac chains ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + length chains
                * (W * (nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n ac chains
                        + suc (chainsDelLen n ac chains) * nestU (delSq n cp′) (nestUnit e sl))))))
cascadeGo-nodes-chains cp ac d W sl Lv a nextId [] sched st hsl 1≤W 1≤S hac hb hc hdp hpz hlv =
  0 , z≤n ,
  ≤-trans (≤-trans (m≤m+n _ 0) (one-pow W _)) (≤-reflexive (sym (*-identityˡ _)))
cascadeGo-nodes-chains {n = n} {e = e} cp ac d W sl Lv a nextId ((rid , c) ∷ chains) sched st hsl 1≤W 1≤S hac hb hc hdp hpz hlv
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | hb | hc
... | true | hb′ | hc′ =
  proj₁ TL ,
  proj₁ (proj₂ TL) ,
  ≤-trans (proj₂ (proj₂ TL))
    (≤-trans (*-monoʳ-≤ (R ^ K)
      (≤-trans (*-monoʳ-≤ (G ^ W) (+-monoʳ-≤ M grow))
               (≤-trans (nest-scale (deliverNestF n ac c ^ W) (G ^ W)
                           (M + suc (length chains) * (W * (V + C′ + U)))
                           (1≤pow≤ (deliverNestF n ac c) W (1≤deliverNestF n ac c)))
                        (≤-reflexive
                          (cong (_* (M + suc (length chains) * (W * (V + C′ + U))))
                                (sym (pow-distrib-* W (deliverNestF n ac c) G)))))))
    (≤-trans (nest-scale (R ^ deliverLen n ac c) (R ^ K) Xc (1≤pow≤ R (deliverLen n ac c) 1≤R))
             (≤-reflexive (cong (_* Xc) (sym (^-distribˡ-+-* R (deliverLen n ac c) K))))))
  where
  TL = cascadeGo-nodes-chains cp ac d W sl Lv a nextId chains sched st hsl 1≤W 1≤S hac hb′ hc′
         (lub3-l (depthCascade a nextId chains sched st)
                 (depthChain nextId a c sched
                    (record st { delivered = rid ∷ EvalSt.delivered st }))
                 (depthCascade a nextId chains
                    (proj₁ (proj₂ (chainStep nextId a c sched
                       (record st { delivered = rid ∷ EvalSt.delivered st }))))
                    (proj₂ (proj₂ (chainStep nextId a c sched
                       (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
         (proj₂ (∧-true _ _ hpz)) hlv
  cp′ = frameStep (proj₁ TL) cp
  R  = nestFac (Caps.cSize cp′) W
  1≤R : 1 ≤ R
  1≤R = 1≤nestFac (Caps.cSize cp′) W
  K  = chainsDelLen n ac chains
  M  = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V  = nestDᵛ (arrTy a) (arrVal a)
  C  = chainsDelNestD n ac chains
  C′ = deliverNestD n ac c ⊔ C
  Uz = nestU (delSq n cp′) (nestUnit e sl)
  U  = suc (deliverLen n ac c + K) * Uz
  Uₜ = suc K * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (deliverLen n ac c)))
  G  = chainsDelNestF n ac chains
  Xc = (deliverNestF n ac c * G) ^ W * (M + suc (length chains) * (W * (V + C′ + U)))
  grow : length chains * (W * (V + C + Uₜ)) ≤ suc (length chains) * (W * (V + C′ + U))
  grow = *-mono-≤ (n≤1+n (length chains))
                  (*-monoʳ-≤ W
                    (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (deliverNestD n ac c) C)) Uₜ≤U))
... | false | hb′ | hc′ =
  jt ,
  ⊔-lub (proj₁ (proj₂ TAILr)) (proj₁ (proj₂ HEADr)) ,
  ≤-trans TAILw
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (*-monoʳ-≤ (G ^ W)
                        (+-monoˡ-≤ (length chains * (W * (V + C + Uₜ)))
                                   HEADw)))
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (fac-hoist (R ^ deliverLen n ac c) (G ^ W) A Z (1≤pow≤ R (deliverLen n ac c) 1≤R)))
          (≤-trans (≤-reflexive (sym (*-assoc (R ^ K) (R ^ deliverLen n ac c) Y)))
          (≤-trans (≤-reflexive
                      (cong (_* Y) (trans (*-comm (R ^ K) (R ^ deliverLen n ac c))
                                          (sym (^-distribˡ-+-* R (deliverLen n ac c) K)))))
                   (*-monoʳ-≤ (R ^ (deliverLen n ac c + K))
          (≤-trans (nest-telescope (deliverNestF n ac c ^ W) (G ^ W) M
                                   (W * (V + deliverNestD n ac c + Uc))
                                   (length chains * (W * (V + C + Uₜ)))
                                   (1≤pow≤ (deliverNestF n ac c) W (1≤deliverNestF n ac c)))
                   (≤-trans (≤-reflexive
                               (cong (_* (M + (W * (V + deliverNestD n ac c + Uc)
                                               + length chains * (W * (V + C + Uₜ)))))
                                     (sym (pow-distrib-* W (deliverNestF n ac c) G))))
                     (*-monoʳ-≤ ((deliverNestF n ac c * G) ^ W)
                       (+-monoʳ-≤ M
                         (+-mono-≤ (*-monoʳ-≤ W
                                     (+-mono-≤ (+-monoʳ-≤ V (m≤m⊔n (deliverNestD n ac c) C)) Uc≤U))
                                   (*-monoʳ-≤ (length chains)
                                     (*-monoʳ-≤ W
                                       (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (deliverNestD n ac c) C))
                                                 Uₜ≤U)))))))))))))
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  r₁  = chainStep nextId a c sched st′
  sd₁ = proj₁ (proj₂ r₁)
  st₁ = proj₂ (proj₂ r₁)

  -- THE CASCADE'S LEVEL IS THE JOIN OF THIS CHAIN'S AND THE REST'S,
  -- which is the path fold's rule one layer out: a chain walks its own
  -- descent and reports what that descent cost, and the fold cannot ask
  -- one chain to have paid for another's substitutions.
  HEADr = chainStep-nodes cp ac d W sl Lv nextId a c sched st′ hsl
            1≤W 1≤S hac (proj₁ hb′) (proj₁ hc′)
            (lub3-m (depthCascade a nextId chains sched st)
                    (depthChain nextId a c sched st′)
                    (depthCascade a nextId chains sd₁ st₁) hdp)
            (proj₁ (∧-true _ _ hpz)) hlv
  TAILr = cascadeGo-nodes-chains cp ac d W sl (Lv + proj₁ (proj₂ hc′)) a nextId chains sd₁ st₁
            (trans (chainStep-slots nextId a c sched st′) hsl) 1≤W 1≤S hac
            (proj₂ hb′) (proj₂ (proj₂ (proj₂ hc′)))
            (lub3-r (depthCascade a nextId chains sched st)
                    (depthChain nextId a c sched st′)
                    (depthCascade a nextId chains sd₁ st₁) hdp)
            (proj₂ (∧-true _ _ hpz)) (proj₁ (proj₂ (proj₂ hc′)))
  jt  = proj₁ TAILr ⊔ proj₁ HEADr
  cp′ = frameStep jt cp

  sizeₕ : Caps.cSize (frameStep (proj₁ HEADr) cp) ≤ Caps.cSize cp′
  sizeₕ = iterSize-mono-count (Caps.cSize cp) (Caps.cSize cp) 1≤S
            (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  regₕ : Caps.cReg (frameStep (proj₁ HEADr) cp) ≤ Caps.cReg cp′
  regₕ = frameStep-reg-mono cp (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  sizeₜ : Caps.cSize (frameStep (proj₁ TAILr) cp) ≤ Caps.cSize cp′
  sizeₜ = iterSize-mono-count (Caps.cSize cp) (Caps.cSize cp) 1≤S
            (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  regₜ : Caps.cReg (frameStep (proj₁ TAILr) cp) ≤ Caps.cReg cp′
  regₜ = frameStep-reg-mono cp (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  M   = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V   = nestDᵛ (arrTy a) (arrVal a)
  C   = chainsDelNestD n ac chains
  Uz  = nestU (delSq n cp′) (nestUnit e sl)
  G   = chainsDelNestF n ac chains
  R   = nestFac (Caps.cSize cp′) W
  1≤R : 1 ≤ R
  1≤R = 1≤nestFac (Caps.cSize cp′) W
  K   = chainsDelLen n ac chains

  HEADw = ≤-trans (proj₂ (proj₂ HEADr))
            (*-mono-≤ (^-monoˡ-≤ (deliverLen n ac c) (nestFac-monoS sizeₕ W))
              (*-monoʳ-≤ (deliverNestF n ac c ^ W)
                (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st′))
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a) + deliverNestD n ac c)
                      (*-monoʳ-≤ (suc (deliverLen n ac c))
                        (nestU-mono (delSq n (frameStep (proj₁ HEADr) cp))
                                    (delSq n cp′) (nestUnit e sl)
                          (delSq-monoᶜ n (frameStep (proj₁ HEADr) cp) cp′
                                       sizeₕ regₕ))))))))

  TAILw = ≤-trans (proj₂ (proj₂ TAILr))
            (*-mono-≤ (^-monoˡ-≤ K (nestFac-monoS sizeₜ W))
              (*-monoʳ-≤ (G ^ W)
                (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st₁))
                  (*-monoʳ-≤ (length chains)
                    (*-monoʳ-≤ W
                      (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a) + C)
                        (*-monoʳ-≤ (suc K)
                          (nestU-mono (delSq n (frameStep (proj₁ TAILr) cp))
                                      (delSq n cp′) (nestUnit e sl)
                            (delSq-monoᶜ n (frameStep (proj₁ TAILr) cp) cp′
                                         sizeₜ regₜ)))))))))
  U   = suc (deliverLen n ac c + K) * Uz
  Uₜ  = suc K * Uz
  Uc  = suc (deliverLen n ac c) * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (deliverLen n ac c)))
  Uc≤U : Uc ≤ U
  Uc≤U = *-monoˡ-≤ Uz (s≤s (m≤m+n (deliverLen n ac c) K))
  A   = deliverNestF n ac c ^ W * (M + W * (V + deliverNestD n ac c + Uc))
  Z   = length chains * (W * (V + C + Uₜ))
  Y   = G ^ W * (A + Z)

-- AND THE SELECTION IS WITHIN THE REAL WIDTH, WHICH IS NOW A TWO-LINE
-- READING RATHER THAN A FACE OF ITS OWN.  A cascade's chain list is a
-- filter of the registry, and the width IS the registry cap, so the
-- fact the row above needs is `capsOK?`'s own fifth conjunct composed
-- with the filter's length bound -- both already proven.
--
-- WHAT THAT REPLACED IS THE POINT.  The width used to be a quantity
-- this development invented, `capsBase` at the entry squaring itself
-- each instant, and bridging it to anything a walk spends took two
-- leaves that were ranked FALSITY and could not be instantiated.
-- Choosing the width to BE the thing that is bounded is what makes the
-- bridge disappear instead of being ground.
chains-count-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (capsAt e sl id) sched st ≡ true →
  length (chainsOf a st) ≤ realWidAt e sl id
chains-count-width {e = e} sl id a sched st hcaps =
  subst (length (chainsOf a st) ≤_) (sym (realWidAt-def e sl id))
        (≤-trans (chainsOf-length a st)
                 (capsOK?-count (capsAt e sl id) sched st hcaps))

-- THE NODE-STATE COMPONENT, WHICH IS WHERE THE WIDTH IS ACTUALLY SPENT.
-- A `scan` node stores its accumulator and a bounded `mergeAll` node
-- stores its parked queue, so the nodes map is the only part of the
-- store a delivery can DEEPEN rather than merely re-point.  Measured
-- across every family the harness drives, the slot store, the pending
-- sources and the registry read the same before the walk and after,
-- and every unit of the growth is here -- which is what makes the
-- other three arms of the parent's `⊔` cheap and this one primitive.
cascadeGo-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  length chains ≤ realWidAt e sl id →
  nestDᵛ (arrTy a) (arrVal a) + chainsNestD chains ≤ nestUnit e sl →
  chainsDelLen n (capsAt e sl (suc id)) chains
    ≤ realWidAt e sl id * delSize n (capsAt e sl (suc id)) →
  -- THE FACTOR IS READ AT THE NEXT INSTANT'S CAP, and that is where the
  -- walk's level dies.  A cascade reports the level its own descent
  -- reached, bounded by `sizeCount c (capsH e sl id)` -- which is
  -- exactly the count `capsAt-suc-full` steps by -- so every quantity
  -- the walk hands back sits under the successor cap and nothing
  -- existential survives into this conclusion.  Reading the premise one
  -- instant later is what buys that, and it costs nothing the caps face
  -- was not already paying: `sub-charge-capsOK-lift` (.Caps-Bridge)
  -- collapses its own level against the same cap by the same chain.
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl (suc id)) chains
    * chainsDelNestF n (capsAt e sl (suc id)) chains ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId chains sched st →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
       ≤ nestFacAt e sl id
         * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest-nodes {n = n} {e = e} sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls hfac hdep hburst hcw hpz =
  ≤-trans (≤-trans (≤-trans (proj₂ (proj₂ CH)) lift)
                   (≤-reflexive
                     (sym (*-assoc (nestFac (Caps.cSize (capsAt e sl (suc id)))
                                            (nestBurstAt e sl id)
                                     ^ chainsDelLen n (capsAt e sl (suc id)) chains)
                                   (chainsDelNestF n (capsAt e sl (suc id)) chains
                                     ^ nestBurstAt e sl id) _))))
    (*-mono-≤ hfac
      (+-mono-≤ nodes≤store
        (≤-trans (*-mono-≤ hcnt
                    (*-monoʳ-≤ (nestBurstAt e sl id)
                      (≤-trans (+-monoˡ-≤ (suc (chainsDelLen n (capsAt e sl (suc id)) chains) * UU)
                                          depth≤)
                               (*-monoˡ-≤ UU (s≤s (s≤s hls))))))
                 (≤-reflexive (sym (nestIncAt-def e sl id))))))
  where

  SS = delSq n (capsAt e sl (suc id))
  UU = nestU SS (nestUnit e sl)

  CH = cascadeGo-nodes-chains (capsAt e sl id) (capsAt e sl (suc id)) (capsH e sl id) (nestBurstAt e sl id)
         sl 0 a nextId chains sched st hsl (1≤nestBurstAt e sl id)
         (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)) (capsAt-⊑-suc e sl id)
         hburst hcw hdep
         (all-impl _ _
            (λ rc h → pathSz?-widen (proj₂ rc) (proj₁ (capsAt-⊑-suc e sl id)) h)
            chains hpz)
         z≤n
         ⦃ faceAt e sl id ⦄

  -- the level's own ceiling, and the whole of the collapse: the count
  -- the cascade reports is under the one the recurrence steps by, so
  -- the stepped cap is componentwise under the next instant's
  lift-⊑ : frameStep (proj₁ CH) (capsAt e sl id) ⊑ᶜ capsAt e sl (suc id)
  lift-⊑ = subst (λ x → frameStep (proj₁ CH) (capsAt e sl id) ⊑ᶜ x)
                 (sym (capsAt-suc-full e sl id))
                 (frameStep-mono-j (capsAt e sl id) (2≤capsAt-size e sl id)
                                   (≤-trans (proj₁ (proj₂ CH))
                                      (⊔-lub ≤-refl
                                         (size≤sizeCount (capsAt e sl id) (capsH e sl id)
                                            (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)))))

  lift = *-mono-≤ (^-monoˡ-≤ (chainsDelLen n (capsAt e sl (suc id)) chains)
                     (nestFac-monoS (proj₁ lift-⊑) (nestBurstAt e sl id)))
           (*-monoʳ-≤ (chainsDelNestF n (capsAt e sl (suc id)) chains ^ nestBurstAt e sl id)
             (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
               (*-monoʳ-≤ (length chains)
                 (*-monoʳ-≤ (nestBurstAt e sl id)
                   (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a)
                                + chainsDelNestD n (capsAt e sl (suc id)) chains)
                     (*-monoʳ-≤ (suc (chainsDelLen n (capsAt e sl (suc id)) chains))
                       (nestU-mono (delSq n (frameStep (proj₁ CH) (capsAt e sl id)))
                                   SS (nestUnit e sl)
                         (delSq-monoᶜ n (frameStep (proj₁ CH) (capsAt e sl id))
                                      (capsAt e sl (suc id))
                                      (proj₁ lift-⊑) (proj₂ (proj₂ lift-⊑))))))))))

  -- the walk charges its depth in the delivery currency and the
  -- selection bound is a path fact, so the fan allowance is what sits
  -- between them -- and the unit is priced at the delivery square
  -- precisely so it has room for one
  depth≤ : nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n (capsAt e sl (suc id)) chains ≤ UU
  depth≤ =
    ≤-trans (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a))
                       (chainsDelNestD-chains n (capsAt e sl (suc id)) chains))
      (≤-trans (≤-reflexive (sym (+-assoc (nestDᵛ (arrTy a) (arrVal a))
                                          (chainsNestD chains)
                                          (fanSq n (capsAt e sl (suc id))))))
        (≤-trans (+-monoˡ-≤ (fanSq n (capsAt e sl (suc id))) hchg)
                 (nestU-room SS (nestUnit e sl)
                             (fanSq n (capsAt e sl (suc id)))
                             (≤-trans (s≤s z≤n) ≤-refl)
                             (≤-trans (m≤n+m (fanSq n (capsAt e sl (suc id)))
                                             (Caps.cSize (capsAt e sl (suc id))
                                                * Caps.cSize (capsAt e sl (suc id))))
                                      (delSq-cap n (capsAt e sl (suc id))
                                                 (1≤capsAt-reg e sl (suc id)))))))


  nodes≤store : foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st) ≤ storeNestMax sched st
  nodes≤store = ≤-trans (m≤n⊔m (NA ⊔ NB) NC) (m≤m⊔n ((NA ⊔ NB) ⊔ NC) ND)
    where
    NA = slotsNestSum (Sched.slots sched)
    NB = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    NC = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
    ND = regsNestMax (EvalSt.registry st)

-- THE REGISTRY COMPONENT, whose paths only ever gain frames the path
-- measure does not charge.  A walk registers the inners a release
-- subscribes, and a registration's path extends the chain's own with a
-- `from-inner` frame, which is the one frame `pathNestD` charges zero
-- for -- so the deepest registered path after the walk is expected to
-- be one the walk already had in hand.  The measurement agrees at
-- every cell of every family the harness drives.  It is stated at the
-- parent's right-hand side rather than at the tighter bound that
-- reading suggests, because the tighter form needs the chain list to
-- come FROM the registry and this statement takes it free.
--
-- PROBED: `Probed.Cascade-Store-Components` pins this component by
--   `refl` beside the store the walk started from, over three families.
--   It reads ZERO on every one -- every registration the walk touched
--   is retired by the time the cascade ends -- while the node summand
--   in the same rows goes to four times the starting store.  So the
--   increment this row carries is not being spent HERE, and the growth
--   the wider statement pays for is the node table's.  Not covered, and
--   it is the only region that could move this component: a walk that
--   leaves a registration STANDING whose path is deeper than any the
--   store held, which is what the `nestUnit` factor of the increment
--   would have to pay for.  No family reaches it, so the reading is a
--   receipt about retirement rather than about the bound.
postulate
  cascadeGo-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    let r = cascadeGo a nextId chains sched st
    in regsNestMax (EvalSt.registry (proj₂ (proj₂ r)))
         ≤ storeNestMax sched st + nestIncAt e sl id

-- THE WALK'S STORE GROWTH, IN THE WIDTH CURRENCY, AND IT IS PRIMITIVE.
-- One arrival's chain walk leaves the store measure no deeper than it
-- found it plus one `nestSyn` per unit of REAL WIDTH.  The width factor
-- is the content rather than decoration over a narrower truth, and the
-- mechanism is one arc: mergeAll's DRAIN stores each released inner in
-- turn, and it is reached through a `from-inner` frame, which the path
-- measure charges nothing for -- so ONE delivery can store arbitrarily
-- many times, and no charge that counts what the run DID can bound it.
-- `realWidAt` is the one term in this vocabulary that moves with the
-- axis that drives the drain, which is why the width form clears the
-- rows the narrow ones cross on.
--
-- AND THE STORE MEASURE IS A `⊔` OF FOUR COMPONENTS, SO THE ROW SPLITS
-- FOUR WAYS RATHER THAN INDUCTING ONCE.  A least upper bound sits
-- below a target exactly when each of its arms does, so the walk's
-- slot store, its pending sources, its node states and its registry
-- can each be charged this same right-hand side independently.  The
-- slot arm needs no charge at all, the fold threading that store
-- untouched, and the split is worth taking because the three arms
-- that survive it are nowhere near equally hard.
cascadeGo-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  length chains ≤ realWidAt e sl id →
  nestDᵛ (arrTy a) (arrVal a) + chainsNestD chains ≤ nestUnit e sl →
  chainsDelLen n (capsAt e sl (suc id)) chains
    ≤ realWidAt e sl id * delSize n (capsAt e sl (suc id)) →
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl (suc id)) chains
    * chainsDelNestF n (capsAt e sl (suc id)) chains ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId chains sched st →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  let r = cascadeGo a nextId chains sched st
  in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
       ≤ nestFacAt e sl id
         * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest {n = n} {e = e} sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls hfac hsz hdep hburst hcw hpz =
  ⊔-lub (⊔-lub (⊔-lub SL LV) ND) RG
  where
  r   = cascadeGo a nextId chains sched st
  sd′ = proj₁ (proj₂ r)
  st′ = proj₂ (proj₂ r)

  RHS : ℕ
  RHS = storeNestMax sched st + nestIncAt e sl id

  up : RHS ≤ nestFacAt e sl id * RHS
  up = nest-inflate (nestFacAt e sl id) RHS (1≤nestFacAt e sl id)

  base≤ : storeNestMax sched st ≤ RHS
  base≤ = m≤m+n _ _

  SL : slotsNestSum (Sched.slots sd′) ≤ nestFacAt e sl id * RHS
  SL = ≤-trans (≤-reflexive (cong slotsNestSum (cascadeGo-slots a nextId chains sched st)))
               (≤-trans (≤-trans (≤-trans (m≤m⊔n _ _) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _))) base≤) up)

  -- ONE CHAIN'S FACTOR OUT OF THE SELECTION'S POWER.  The fanout
  -- premise bounds the whole product raised to the burst; the burst is
  -- a successor and every factor is at least one, so the bare product
  -- comes out of it.
  chF≤fac : chainsNestF chains ≤ nestFacAt e sl id
  chF≤fac =
    ≤-trans (chainsNestF≤ n (capsAt e sl (suc id)) chains)
      (≤-trans (m≤m^burst e sl id (chainsDelNestF n (capsAt e sl (suc id)) chains)
                          (1≤chainsDelNestF n (capsAt e sl (suc id)) chains))
               (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ _)))
                                 (*-monoˡ-≤ _ (1≤pow≤ (nestFac (Caps.cSize (capsAt e sl (suc id)))
                                                               (nestBurstAt e sl id))
                                                      (chainsDelLen n (capsAt e sl (suc id)) chains)
                                                      (1≤nestFac _ _))))
                        hfac))

  LV : foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sd′) ≤ nestFacAt e sl id * RHS
  LV = cascadeGo-nest-live sl id a nextId chains sched st hsl hcaps hnest hval hsz chF≤fac

  ND : foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st′)
         ≤ nestFacAt e sl id * RHS
  ND = cascadeGo-nest-nodes sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls
         hfac hdep hburst hcw hpz

  RG : regsNestMax (EvalSt.registry st′) ≤ nestFacAt e sl id * RHS
  RG = ≤-trans (cascadeGo-nest-regs sl id a nextId chains sched st hsl hcaps hnest hval) up

-- ONE ARRIVAL'S WHOLE CASCADE, IN THE WIDTH CURRENCY -- and the width
-- factor is the content, not decoration over a narrower truth.  A
-- delivery walks an already-registered chain, so the tempting reading
-- is that it deepens by one operator's worth, and that the cascade is
-- one such step per delivery or per chain.  Every version of that
-- reading is false, and the mechanism is one arc: mergeAll's DRAIN
-- spends a nesting level through `depthFinC`, and it is reached
-- through a `from-inner` frame, which `pathNestD` charges nothing for.
-- Every other level this family spends is paid by a path term --
-- `pathNestD` charges the `thru-outer` frame and only that frame -- so
-- the drain's levels have nothing to come out of but the constant, and
-- a program whose folds nest spends arbitrarily many of them on ONE
-- delivery.  The width factor is what pays for them, and it pays with
-- room to spare.  So this is a primitive statement, and no
-- decomposition that charges by the run is a route to it.
--
-- REFUTED: `Refuted.Cascade-Deliv-Depth`, the per-DELIVERY half, at
--   ONE chain, ONE delivery and no cancellation -- so neither the skip
--   branch nor the phantom tail's delivery count is what kills it.
--   Across the fold parameter the descent climbs six a layer against
--   the bound's three, ties at two and crosses at three.  The BOUNDED
--   limit is the ingredient every earlier family lacked: with nothing
--   parked there is no drain to reach, and the same witness under an
--   unbounded limit clears the bound comfortably.
-- REFUTED: `Refuted.Nest-Depth-One` kills the subscribe-side sibling
--   of the same narrow reading, descent 21 against 19, which is where
--   the arc above was first read off.
-- DEAD ROUTE: a plain structural induction on the chain list, with the
--   bound stated at the entry store.  The cons clause's THIRD arm reads
--   the tail at the state the head's `chainStep` left, and that state's
--   store is strictly deeper -- measured at three before the step and
--   twelve after it, on one chain and one delivery -- so the induction
--   hypothesis is being applied at a store the conclusion does not
--   mention.  Nothing about the arm can be repaired locally: the two
--   surviving arms close against the entry store and this one cannot,
--   whatever the head-arm leaf says.  What it needs is a generalisation
--   that THREADS the store growth as a budget, and the quantity it
--   would thread is `cascadeGo-nest`'s, the row above -- so that row is
--   a genuine prerequisite of this one rather than a sibling.
-- DEAD ROUTE: the head arm without a width term, `depthChain` under the
--   payload nesting plus the path's plus the store's.  It is attractive
--   because the drain's unpaid levels come out of what is STORED, which
--   is the one term that already accounts for them.  The grid refutes it
--   without a new probe: at a single chain the whole cascade IS its head
--   arm, and the descent moves with the source length while the payload
--   nesting, the path measure and the store are each flat in it.
-- DEAD ROUTE: charging per CHAIN instead.  That clause CLOSES, which
--   the per-delivery one does not -- both tails take the hypothesis at
--   `length chains`, and the head is the one chain by which `suc`
--   exceeds it -- but the leaf under it is a single delivery within
--   one `nestSyn`, and that charge is SMALLER than the per-delivery
--   one wherever a chain is skipped, so the same witness kills it a
--   fortiori.
--
-- RECOVERY: `git show f53fff4:agda/src/Verify-Budget-Sufficient/Caps-Face/Part7.agda`
--   restores the per-chain assembly and its four leaves -- the marked-state
--   helper, the chain-step store and caps-at-the-next-index transports, and
--   the registry count under the real width.  The chain-step transports are
--   about `chainStep` alone and survive the refutation of what consumed
--   them; the assembly does not.

-- AND THE SAME SELECTION AGAINST THE SYNTACTIC CEILING, which is the
-- fact that ties a walk's charge back to the program.  A registration's
-- path is a rootward walk through `e`'s own spine, and `pathNestD`
-- charges the `thru-outer` frame and only that frame -- one per *All
-- layer, which is exactly the `suc` `nestDᵉ` spends on the same layer --
-- so the deepest registered chain is within `nestDᵉ e`.  The PAYLOAD is
-- not in the registry at all: it came from a slot, so it is within that
-- slot's own nesting and hence within `slotsNestSum`.  Adding the two
-- lands inside `nestSyn`, which is their sum plus one.
--
-- IT IS STATED OVER THE SELECTION AND NOT OVER A FREE LIST, and that is
-- the whole content: a path nobody registered may carry a `scan` frame
-- whose function wraps deeper than the program it is being charged
-- against, so the free-list form of this bound does not survive.
--
-- REFUTED: `Refuted.Chain-Step-Nodes`, the free-path form, eleven
--   against nine and unbounded in the frame's fold depth.
-- PROBED: `Probed.Cascade-Chain-Count` reads this by `refl` on five
--   families AFTER the walk has run several instants, which is the only
--   half worth having: at the ENTRY arrival the registry holds nothing
--   but what the root subscribe put there and the reading comes back at
--   2 against a whole `nestSyn`, so a sweep of first instants cannot
--   fail.  Registrations deepen when a release SUBSCRIBES an inner, so
--   the chains that could cross this sit past the first cascade.  One
--   row drives the FOLD DEPTH, which is the axis that moves both sides
--   at once -- the wrap is in the scan's own function, so it lands in
--   `pathNestD` of every chain through that frame and in `nestDᵉ` of
--   the program together.  COVERED is the conclusion; the premises
--   compute nowhere.  NOT covered: `Γ₂`, and the vocabulary runs dry
--   after a handful of arrivals -- a row past the end announces itself,
--   reading its verdict false rather than passing quietly.
postulate
  arr-chains-nest-syn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) + chainsNestD (chainsOf a st) ≤ nestUnit e sl

-- THE FANOUT'S EXPONENT, AND IT IS A READING OF THE SIZE INVARIANT
-- RATHER THAN A NEW BET.  `capsOK?` carries `regsSz?` over the whole
-- registry, and `pathSz?` is two conjuncts per frame: the step
-- function's own size within the cap, and the path's LENGTH within the
-- same cap.  A path therefore charges at most cap-many frames of at
-- most cap-many units each, and a cascade's chain list is a selection
-- within the real width -- so the sum is the width times the cap
-- squared, with no appeal to what the run does.
--
-- IT IS STATED IN THE SIZE CURRENCY AND NOT THE FANOUT ONE, which is
-- what keeps it provable: the exponential is peeled off by
-- `chainsNestF≡` above the leaf, so nothing under here ever multiplies.
-- the selection inherits the registry's own size predicate, filter and
-- retag alike
chainsGo-sz : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  All (λ c → pathSz? B (proj₂ c) ≡ true) (chainsGo a rs)
chainsGo-sz B a [] h = []ᵃ
chainsGo-sz B a ((rid , src , (u , p)) ∷ rs) h
  with ∧-true (pathSz? B p) (all (λ en → pathSz? B (proj₂ (proj₂ (proj₂ en)))) rs) h
... | hp , hrs with sameSource (arrSource a) src | u ≟ᵗ arrTy a
... | false | _        = chainsGo-sz B a rs hrs
... | true  | no  _    = chainsGo-sz B a rs hrs
... | true  | yes refl = hp ∷ᵃ chainsGo-sz B a rs hrs

chainsSzSum-bound : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  All (λ c → pathSz? B (proj₂ c) ≡ true) cs →
  chainsSzSum cs ≤ length cs * (B * B)
chainsSzSum-bound B []       []ᵃ         = z≤n
chainsSzSum-bound B (c ∷ cs) (hc ∷ᵃ hcs) =
  +-mono-≤ (pathSzSum-cap B (proj₂ c) hc) (chainsSzSum-bound B cs hcs)

chainsLenSum-bound : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  All (λ c → pathSz? B (proj₂ c) ≡ true) cs →
  chainsLenSum cs ≤ length cs * B
chainsLenSum-bound B []       []ᵃ         = z≤n
chainsLenSum-bound B (c ∷ cs) (hc ∷ᵃ hcs) =
  +-mono-≤ (pathSz?-len B (proj₂ c) hc) (chainsLenSum-bound B cs hcs)

-- ONE FACTOR PER FRAME IS ONE FACTOR PER UNIT OF PATH LENGTH, so the
-- selection's total frame count is what the caps rider is raised to --
-- the length half of the size bound directly below, and bounded the
-- same way, by the width the registry admits times the length one
-- chain may reach.
arr-chains-len-sum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsDelLen n (capsAt e sl (suc id)) (chainsOf a st)
    ≤ realWidAt e sl id * delSize n (capsAt e sl (suc id))
arr-chains-len-sum {n = n} {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsDelLen-chains n C⁺ (chainsOf a st))
    (≤-trans (+-mono-≤ (≤-trans (chainsLenSum-bound B (chainsOf a st)
                                   (chainsGo-sz B a (EvalSt.registry st) regsz))
                                (*-mono-≤ wid B≤))
                       (*-monoˡ-≤ (fanLen n C⁺) wid))
             (≤-reflexive (trans (sym (*-distribˡ-+ (realWidAt e sl id)
                                        (Caps.cSize C⁺) (fanLen n C⁺)))
                                 (cong (realWidAt e sl id *_) (sym (delSize-def n C⁺))))))
  where
  C = capsAt e sl id
  C⁺ = capsAt e sl (suc id)
  B = Caps.cSize C
  B≤ = proj₁ (capsAt-⊑-suc e sl id)
  wid = chains-count-width sl id a sched st hcaps
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs C sched st hcaps

arr-chains-sz-sum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsDelSzSum n (capsAt e sl (suc id)) (chainsOf a st)
    ≤ realWidAt e sl id * delSq n (capsAt e sl (suc id))
arr-chains-sz-sum {n = n} {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsDelSzSum-chains n C⁺ (chainsOf a st))
    (≤-trans (+-mono-≤ (≤-trans (chainsSzSum-bound B (chainsOf a st)
                                   (chainsGo-sz B a (EvalSt.registry st) regsz))
                                (*-mono-≤ wid (*-mono-≤ B≤ B≤)))
                       (*-monoˡ-≤ (fanSq n C⁺) wid))
    (≤-trans (≤-reflexive (sym (*-distribˡ-+ (realWidAt e sl id)
                                 (Caps.cSize C⁺ * Caps.cSize C⁺) (fanSq n C⁺))))
             (*-monoʳ-≤ (realWidAt e sl id)
                        (delSq-cap n C⁺ (1≤capsAt-reg e sl (suc id))))))
  where
  C = capsAt e sl id
  C⁺ = capsAt e sl (suc id)
  B = Caps.cSize C
  B≤ = proj₁ (capsAt-⊑-suc e sl id)
  wid = chains-count-width sl id a sched st hcaps
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs C sched st hcaps

-- AND THE SAME SELECTION AGAINST THE FANOUT CEILING, which is the half
-- the additive reading got wrong.  A frame does not ADD its function's
-- charge to what it emits: a step function may name its payload twice,
-- so one `mapᵉ` can DOUBLE the nesting of the value coming out of it,
-- and a path composes those doublings while a cascade compounds one
-- path's worth per chain.  The factor is therefore a product, `2` per
-- unit of step-function syntax, and this says the product a registered
-- chain list can reach is within the instant's own fanout ceiling --
-- real width in the exponent, the size cap in the base.
--
-- REFUTED: `Refuted.Apply-Fn-Nest` kills the additive substitution
--   reading at one frame -- a payload named on both sides of a single
--   `mapᵉ` reads 2 against a charge of 0.  `Refuted.Step-Frame-Nest-Dup`
--   carries the same witness up to the frame the walk actually steps,
--   80 against 40, unbounded in the payload's own depth.
arr-chains-nest-fac : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl (suc id)) (chainsOf a st)
    * chainsDelNestF n (capsAt e sl (suc id)) (chainsOf a st) ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id
arr-chains-nest-fac {n = n} {e = e} sl id a sched st hsl hcaps hnest =
  ≤-trans (≤-reflexive
             (cong₂ _*_ (trans (cong (_^ L)
                                 (trans (nestFac-def B K)
                                   (trans (cong (_^ B) (^-*-assoc 2 B (suc K)))
                                          (^-*-assoc 2 (B * suc K) B))))
                               (^-*-assoc 2 (B * suc K * B) L))
                        (trans (cong (_^ K) (chainsDelNestF≡ n C (chainsOf a st)))
                               (^-*-assoc 2 S K))))
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (B * suc K * B * L) (S * K))))
      (≤-trans (^-monoʳ-≤ 2 expo)
               (≤-reflexive (sym (nestFacAt-def e sl id)))))
  where
  C = capsAt e sl (suc id)
  B = Caps.cSize C
  K = nestBurstAt e sl id
  L = chainsDelLen n C (chainsOf a st)
  S = chainsDelSzSum n C (chainsOf a st)
  D = delSize n C
  X = realWidAt e sl id * delSq n C
  Xʹ = suc D * X

  X≤Xʹ : X ≤ Xʹ
  X≤Xʹ = m≤m+n X (D * X)

  -- the length half lands on the fresh `suc`, the size half on the
  -- burst term the factor already had
  lenX : B * L ≤ X
  lenX =
    ≤-trans (*-mono-≤ (delSize-cap n C)
                      (arr-chains-len-sum sl id a sched st hsl hcaps))
            (≤-reflexive
              (trans (sym (*-assoc D (realWidAt e sl id) D))
                     (trans (cong (_* D) (*-comm D (realWidAt e sl id)))
                            (trans (*-assoc (realWidAt e sl id) D D)
                                   (cong (realWidAt e sl id *_) (sym (delSq-def n C)))))))

  szX : S * K ≤ K * Xʹ
  szX = ≤-trans (≤-reflexive (*-comm S K))
                (*-monoʳ-≤ K (≤-trans (arr-chains-sz-sum sl id a sched st hsl hcaps)
                                      X≤Xʹ))

  -- the subscribe half is now spent once per BURST VALUE at each frame,
  -- so the length term arrives with a `suc K` on it and the two halves
  -- together need the square the factor carries
  -- the flattened factor carries one power of the size cap per level
  -- of the term the descent walks, so the length half arrives with a
  -- second `B` on it and the ceiling gains the matching `suc B`
  lenX′ : B * suc K * B * L ≤ suc K * Xʹ
  lenX′ =
    ≤-trans (≤-reflexive
              (trans (*-assoc (B * suc K) B L)
                     (trans (cong (_* (B * L)) (*-comm B (suc K)))
                            (*-assoc (suc K) B (B * L)))))
            (*-monoʳ-≤ (suc K)
              (≤-trans (*-monoʳ-≤ B lenX)
                       (*-monoˡ-≤ X (≤-trans (delSize-cap n C) (n≤1+n D)))))

  sq : suc K + K ≤ suc K * suc K
  sq = +-monoʳ-≤ (suc K) (m≤m*n K (suc K))

  expo : B * suc K * B * L + S * K ≤ suc K * suc K * Xʹ
  expo =
    ≤-trans (+-mono-≤ lenX′ szX)
            (≤-trans (≤-reflexive (sym (*-distribʳ-+ Xʹ (suc K) K)))
                     (*-monoˡ-≤ Xʹ sq))

-- THE BURST BOUND A CASCADE'S WALKS RUN UNDER, and it is a caps fact
-- rather than a walk fact, which is why it is a leaf here and not a
-- clause up there.  A chain starts from ONE value -- the arrival's --
-- and only a `thru` frame can hand on more than it took, by however
-- many its inners emit; what caps that is the width, and the width cap
-- is `capsOK?`'s business.  So the walk takes the bound as a
-- hypothesis shaped like its own recursion and this is where the
-- hypothesis is met.
--
-- AND THE CAPS FACE ALREADY CARRIES THIS CONJUNCT, WHICH IS WHAT MAKES
-- A FLAT CAP THE RIGHT CURRENCY RATHER THAN A HOPEFUL ONE.  `valsCaps?`
-- is `all valCaps?` conjoined with exactly this length bound.  The
-- remaining distance is arithmetic and not a walk: every level a
-- cascade reaches is under `sizeCount`, so `frameStep-mono-j` puts its
-- width under `frameStep sizeCount`, which `capsAt-suc-full` says IS
-- the cap at the next instant -- which is the one this burst is read
-- from.  The grind is the induction that carries a flat bound where the
-- walk face carries a moving one, and it is a transcription rather than
-- a discovery.
--
-- TWIN: `thruWalk-walk` propagates this conjunct ACROSS THE FEARED HOP
--   and is proven -- taking it in at one level and handing it back at
--   another, with that level's growth bounded in the same tuple.
postulate
  arr-chains-bursts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    chainsBurstOK (nestBurstAt e sl id) a nextId (chainsOf a st) sched
      (cascadeLatch a st)

-- AND THE SAME SELECTION CARRIES THE CAPS, which is a preservation
-- statement and not a selection one: the predicate asserts the store
-- bound at every state the fold passes through, so what has to be shown
-- is that a walk which starts inside the caps stays inside them.  The
-- caps face already proves exactly that, frame by frame and with its own
-- level counter, so this is that receipt re-read at a flat cap rather
-- than a fresh induction.
--
-- AND "RE-READ AT A FLAT CAP" IS THE WHOLE OBLIGATION, NOT A FORMALITY.
-- The frame-wise receipt does not conclude at the cap it was handed:
-- `stepFrame-caps` returns a level `j'` and restates the invariant at
-- `frameStep (j + j')`, and composing a walk's levels is exactly what
-- `capsAt-suc-full` identifies with the cap at the NEXT instant.  So
-- the frame-wise route delivers the successor cap, and what is owed
-- here is that one instant's whole growth already fits inside the
-- single `frameBlowup` separating this instant's cap from the last --
-- an argument about the recurrence, not another induction over frames.
--
-- AND THE FOLD OVER THE CHAINS IS A BODY, so what is asserted is ONE
-- chain's walk and ONE chain's preservation rather than a selection's
-- worth of both.  The predicate recurses on the list -- a cancelled
-- registration walks nothing and weakens by a chain, a live one owes
-- its own walk and hands the rest the state its step produced -- so the
-- induction is the list's and nothing about it is undecided.  Splitting
-- here is what makes the two obligations greppable: the walk leaf is
-- the one the flat-cap rows measure, and the step leaf is the
-- preservation half those rows report as holding outright on two of the
-- three components.
--
-- AND THE SLOTS HALF IS ALREADY PROVEN, which is why the step leaf
-- carries only the caps: `chainStep-slots` says a step does not move
-- the vocabulary, so threading the equation costs nothing.
--
-- WHAT THE WALK LEAF STILL OWES, AND IT IS NOT THE WALK.  The drain's
-- predicate prices a PARKED inner twice over -- what it nests, and what
-- a level of the walk still has to spend -- and both are stated with
-- HEADROOM: three units above the nesting, and two above the size plus
-- one per level.  Those are the shapes the domination guard wants, and
-- they are the shapes the proven entry mirror takes as hypotheses too,
-- so the conjuncts are not suspect.  What has no source is the
-- headroom itself.
--
-- DEAD ROUTE: reading the headroom off the caps hypothesis cannot
--   work.  A mergeAll queue is store content, so the caps predicate
--   does bound every parked term -- but its store conjunct bounds one
--   by the cap EXACTLY, and the size currency the wet stack measures
--   with is that same projection by definition, so there is no second,
--   smaller number to spend the difference against.  The gap is a
--   constant two and the arithmetic cannot manufacture it; the
--   headroom has to be carried by whatever states the store bound, not
--   recovered downstream of it.

-- AND THE STEP LEAF IS NOT PRESERVATION IN GENERAL, WHICH NARROWS WHAT
-- ITS PROOF MAY REST ON.  Read either side of ONE step rather than a
-- whole cascade, the smallest cap the state fits rises by better than a
-- factor of two -- a drain SUBSCRIBES the inners it releases and the
-- step retires nothing, so what pays for the growth is the cascade's
-- FINISH, one level up and outside this statement.  So a step at an
-- arbitrary cap the pre-state satisfies does NOT return inside it, and
-- no arm-by-arm argument can conclude otherwise: the frame-wise receipt
-- lands at `frameStep (j + j')` and the caps ordering only ever widens.
--
-- WHAT IS LEFT IS THE INSTANT'S OWN SLACK, and it is the whole of the
-- remaining route.  `capsAt` is not an arbitrary cap: it is a
-- `frameBlowup` of the last instant's, so the statement can still be
-- true by that gap being wide enough to swallow one instant's whole
-- growth.  That is an argument about the recurrence -- the same one the
-- block above names -- and it is now the ONLY one available, which is
-- what the finding below buys.  The alternative is to give the predicate
-- the level its consumers already speak in, as the nodes face does.
--
-- AND THE WALK LEAF IS THE SAME STATEMENT, NOT A SIBLING OF IT.  The
-- walk predicate's `root` clause IS `capsOK?` at the state the walk
-- ends on, and a chain's walk ends exactly where its step does -- the
-- path fold and the walk recurse through the same `stepFrame`, and the
-- fold returns the scheduler and state untouched at `root`.  So on any
-- sink-free path the walk leaf IMPLIES the step leaf, the crossing
-- below is a crossing of both, and the two rows are one obligation
-- read at two granularities rather than two things to grind.

-- AND THE LEVEL IS NOW IN BOTH STATEMENTS, WHICH IS WHAT THE FINDING
-- BELOW BOUGHT.  Neither leaf asserts preservation any more: the
-- walk is asserted at `frameStep Lv`, the step is handed a state inside
-- `frameStep Lv` and REPORTS the increment that carries it, and the
-- predicate under them threads that level frame by frame and chain by
-- chain.  That is the discipline the frame receipt beside them has
-- always had, and the flat form is gone from the tree.
--
-- AND THE FLAT CEILING WAS AT THE WRONG GRANULARITY, WHICH IS WHY THE
-- STEP LEAF NOW REPORTS THE WALK'S OWN.  Asking one chain, from a level
-- whose only hypothesis is that it sits under the cascade's count, to
-- land under that same count is a conclusion needing what no hypothesis
-- carries: how much of the count is UNSPENT.  The level ladder climbs
-- one delivery-charge per delivery and never returns, so a chain
-- entered at the count itself must leave above it.  The bound is true
-- of a cascade and false of a chain read alone -- a cascade-level fact
-- stated per chain.
--
-- SO THE STEP LEAF IS STATED AT THE CEILING THE WALK ACTUALLY DELIVERS:
-- one charge per delivery, at THIS chain's base rather than at zero.
-- That is the proven cascade bound's own recurrence, so the fold carries
-- the whole remaining cascade's delivery count as its invariant and the
-- two ledger lines split it chain by chain; the conversion back to the
-- count is `lvls-add` and no longer a leaf.
--
-- AND THE LEVEL PREMISE ON THE WALK LEAF IS NOT A CONVENIENCE.  Without
-- it the statement is false at EVERY program and needs no state to kill:
-- the level is a free parameter, the only hypothesis mentioning it says
-- the state fits the cap AT that level and so gets WEAKER as it rises,
-- and the predicate produced asserts at every frame that the level is
-- under the cascade's count.  A level one above the count satisfies both
-- hypotheses and contradicts the conclusion.  So the bound is a property
-- of the CALL, and the delivery-counted form is the one a caller can
-- actually supply -- this chain's own charge, out of the fold's
-- invariant.
--
-- WHICH LEAVES THE PREDICATE'S OWN FLAT CONJUNCTS AS THE GRIND.  Its
-- frame clause and its share fold each demand a level bound against the
-- cascade's count, one per frame and one per admitted chain, and the
-- premise above is what pays for them: a chain is at most one delivery's
-- charge wide, so every intermediate level sits under the same ceiling.
--
-- REFUTED: `Refuted.Chain-Level-Unbounded` -- the level-free form of
--   THIS statement, at every program at once, by arithmetic rather than
--   by a row: a level one above the count satisfies both hypotheses and
--   breaks the conclusion.  `Refuted.Chain-Step-Flat` -- one step of one
--   chain, at a concrete cap the pre-state satisfies and the post-state
--   does not.  `Refuted.Frame-Step-Compose` -- the step does not
--   compose, so the level cannot be absorbed into the cap the machinery
--   re-enters at.
--
-- DEAD ROUTE: re-entering the frame receipt with its cap parameter
--   instantiated at the STEPPED cap, so that the level needs no
--   threading.  The step's width component iterates an exponential
--   whose base is its size component, and stepping raises the size, so
--   the second step runs at the raised base -- a tower storey per
--   level against a flat count that runs every iteration at the
--   original.  One level either side already overshoots by five orders
--   of magnitude.
--
-- TWIN: `stepFrame-caps` -- the same frame, proven, with exactly the
--   discipline owed here: invariant taken at the stepped cap, own
--   increment reported, conclusion restated at the sum.
--
-- RECOVERY: git show 1281567 restores `Probed.Chain-Walk-Level`, whose
--   `walkSpine` re-walks a path with the evaluator's own `stepFrame`
--   and reads a boolean conjunct at EVERY state the fold passes
--   through, rather than at the two ends a fit row can see.  That is
--   the instrument the three leaves below want: they are exactly the
--   conjuncts it could not pin, and the harness generalises to any of
--   them that is a boolean.
--
-- RECOVERY: git show c415649 restores `Probed.Chain-Caps-Flat`, whose
--   harness reads the SMALLEST FITTING CAP either side of a whole
--   cascade over three families, one component at a time -- the way to
--   find where a cascade's growth actually lands.

-- AND THE FRAME'S REGISTRATION CAP IS THE ROUND'S LEDGER AT ITS OWN
-- LEVEL, which is true by definition and stated anyway: read at a
-- CONCRETE caps both sides unfold the tower, and read at a variable
-- neither does.
frameStep-regAt : ∀ (c : Caps) (j : ℕ) →
  Caps.cReg (frameStep j c) ≡ regAt (Caps.cSize c) (Caps.cReg c) j
frameStep-regAt c j = refl

-- THE FLOOR IS ONE CONJUNCT AND ITS PARTS ARE READ OFF IT, because the
-- three facts the ladder's consumers ask for -- the constants, the slot
-- count, the gas -- are each a summand of the one sum that has to
-- survive a nesting.  Carrying them separately is what let a CONSTANT
-- floor be threaded past the sink head, where the nested round costs a
-- gas and the sum is the only form that pays for it.
-- AND A ROUND'S HEAD ONLY CLIMBS, so a level under the position is a
-- level under every entry of the round that starts there.
ent-infl : ∀ (c : Caps) (d J g i : ℕ) → J ≤ Ent c d J g i
ent-infl c d J g i =
  lvls-infl (Caps.cSize c) (Caps.cWid c) d J
    (dWalkᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g J i)

floor-parts : ∀ (X m gas g : ℕ) → X + m + gas ≤ g → (X ≤ g) × (m ≤ g) × (gas ≤ g)
floor-parts X m gas g h =
    ≤-trans (m≤m+n X m) (≤-trans (m≤m+n (X + m) gas) h)
  , ≤-trans (m≤n+m m X) (≤-trans (m≤m+n (X + m) gas) h)
  , ≤-trans (m≤n+m gas (X + m)) h

-- AND THE REGISTRY IS NOT HERE, WHICH IS THE POINT.  The sink is the
-- one head that prices a registered path, and it used to be handed
-- that pricing as two flat conjuncts carried unstepped past every
-- frame -- a base-cap `regsSz?` and a base-cap path receipt -- because
-- the nodes face read a path at the base cap and nothing stepped could
-- reach it.  It no longer does: the walk carries its own levelled path
-- receipt, so the sink's pricing may be read at the LEVEL, and at the
-- level it is a projection out of the `capsOK?` two conjuncts up.
--
-- SO WHAT WAS A PRESERVATION FAMILY IS NOW A PROJECTION.  Re-establishing
-- a BASE-cap registry pricing across a subscribe is not merely hard, it
-- is false -- a registration's path is built from the observable being
-- subscribed, a closed expression structurally unrelated to the program
-- the base cap was computed from -- and two of the leaves that claimed
-- it died at a witness.  Reading it at the frame's own cap asks
-- nothing of a subscribe at all, since the frame face already reports
-- the level it climbed to and `capsOK?` at that level already says what
-- the registry costs there.
--
-- REFUTED: `Refuted.Subscribe-Inner-Regs-Base` -- the base-cap form,
--   killed at a subscribed inner whose path outgrows any cap the outer
--   program fixes.

WalkHyps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
WalkHyps {n = n} {e = e} {u = u} sl id L sf gas nid now src p vals evs fin sched st =
  (Sched.slots sched ≡ sl)
  × (capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true)
  × (valsCaps? (frameStep L (capsAt e sl id)) sl vals ≡ true)
  × (all (nestClosOK?ᵛ (frameStep L (capsAt e sl id)) sl u) vals ≡ true)
  × (pathSz? (Caps.cSize (frameStep L (capsAt e sl id))) p ≡ true)
  × (depthFold sf gas nid now src p vals evs fin sched st ≤ capsH e sl id)
  × (Σ ℕ λ g → Σ ℕ λ P →
      (4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g)
      × (iterL (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id)
               (pathLen p) L
           ≤ P)
      × Reached (capsAt e sl id) (capsH e sl id) P g)

-- THE CLOSURE READING IS CARRIED BY THE WALK, NOT DERIVED AT THE
-- FRAME.  A `thru-outer` is handed an inner observable and owes its
-- size measured THROUGH the slot telescope, which is a strictly
-- stronger reading than the caps receipt beside it: `valCaps?` charges
-- the value's own syntax and nothing the slots it names expand to, and
-- the two come apart at the first shared definition.
--
-- AND IT CANNOT BE DERIVED FROM THAT RECEIPT, AT ANY CAP.  The
-- standing reading was that `capsAt`'s size is a tower and a tower
-- might simply dominate a telescope.  It cannot, and the tower's size
-- is not what decides it: the deficit is PER REFERENCE, so the value
-- the premise admits grows with the cap and carries the deficit up with
-- it.  A `map` spine whose every step is a template naming the slot
-- costs three of syntax and nine of closure per step, a fixed ratio at
-- every length, so at each cap one member of the family is admitted and
-- reads a closure above it.  So the reading is a HYPOTHESIS of the
-- walk, established where the values are admitted and preserved across
-- every frame that rebuilds them.
--
-- AND THE WIDTH CONJUNCT VERY NEARLY SUPPLIES IT, which is the half
-- worth keeping: references CAN be capped by `cWid`, since
-- `outWⱽ (ofᵉ ts)` is the list's length, so N references side by side
-- run out at the width.  The spine is where that gate is absent --
-- `outWⱽ` walks straight through a `mapᵉ` and every `dW` clause is a
-- join -- so the family sits at width one however many references it
-- names.  Width bounds how many references arrive TOGETHER; the closure
-- reading counts how many there are.
--
-- REFUTED: `Refuted.Nest-Clos-Cap-Free` -- the derivation, verbatim, at
--   `frameStep 0 (capsAt … 0)`: the spine family above, its length read
--   off the cap by a hand-rolled third, with `init-capsOK?` supplying
--   the state premise and `capsAt-base-size`/`capsAt-base-wid` the two
--   floors.  It is what closes the question `Refuted.Nest-Clos-Flat`
--   left standing.
-- REFUTED: `Refuted.Thru-Fit-Frame-Slot` -- the frame head WITHOUT a
--   resolved-size premise, at a telescope each of whose layers doubles
--   its predecessor: every term of the grant is pinned at its floor by
--   an arrival that merely NAMES the slot, so the deficit diverges
--   rather than crossing.  That is the argument for the premise existing
--   at all, and its `parent-premise-absurd` is the other half -- the
--   cap those rows are read at does not admit the telescope, so what
--   they kill is the premise-free form and not this one.
-- REFUTED: `Refuted.Nest-Clos-Flat` -- the same reading stated over an
--   ARBITRARY cap rather than `capsAt`'s.  The witness cap is the
--   value's own `sizeᵉ`, so the premise holds by construction at every
--   size the family reaches and raising the cap raises the admitted
--   value with it; three references to one slot read `4 6 8` of syntax
--   against `10 18 26` of closure.
-- REFUTED: `Refuted.Clos-Wrap-Sum` -- the subscribe-side ceiling's
--   traded sum, which is the one quantity in the tier that prices a
--   slot's own BODY rather than counting slots, and so the obvious thing
--   to transport here.  Both factors of `slotWrap` are
--   nesting-denominated and one is a bare `nestDᵉ`, so a slot whose
--   definition wears no `*All` head contributes nothing however large
--   its body is; a pure-`map` vocabulary reads the whole sum at zero
--   against a closure of ten, and the stratum SCALE cannot repair it.

-- THE FRAME-LOCAL LEAF, WHICH IS `⊤` AT FOUR OF THE FIVE HEADS AND SO
-- was never a statement about a walk at all.  Matching on the frame
-- says so in code: only a `thru-outer` carries an obligation, and what
-- it carries is the closure reading of the values it is about to
-- subscribe, one value at a time.
walk-frame-clos : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src (f ↠ p) vals evs fin sched st →
  frameClosOK (frameStep L (capsAt e sl id)) sl f vals
walk-frame-clos sl id L sf gas nid now src (map-f _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (scan-f _ _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (take-f _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (from-inner _ _ _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (thru-outer _ _) p vals evs fin sched st
  (_ , _ , _ , hcl , _) = hcl

-- WHAT THE REGISTRY IS PRICED AT, AND IT IS THE INSTANT'S EXIT CAP
-- rather than its entry one.  A registration's path is built from the
-- observable being subscribed, and a runtime observable is a CLOSED
-- EXPRESSION structurally unrelated to the program the entry cap was
-- computed from -- so an entry-cap pricing of the registry is not
-- preservable across a subscribe at all, at any enlargement of that
-- cap.  What IS big enough is the cap the recurrence's own step
-- reaches: `capsAt (suc id)` is `frameStep (sizeCount c d) c`, and the
-- walk's ceiling is that same count, so every level a subscribe can
-- climb to is componentwise under it.
--
-- AND AT THAT CAP THE FACT IS NOT A SEPARATE OBLIGATION, which is the
-- whole payoff.  `capsOK?` already carries `regsSz?` at whatever cap
-- it is read at, and the walk holds a levelled `capsOK?` at every
-- state it passes through -- so the registry's pricing is a
-- PROJECTION out of a receipt already in hand plus one widening, and
-- the frame-by-frame preservation family that used to thread it, two
-- of whose leaves were machine-refuted, is gone.  A subscribe's own
-- registrations are priced by the subscribe face, which reports the
-- level it climbed to; nothing here re-proves that.
RegsBase : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (st : EvalSt e) → Set
RegsBase {e = e} sl id st =
  regsSz? (Caps.cSize (capsAt e sl (suc id))) (EvalSt.registry st) ≡ true

-- THE PROJECTION, and it is the only route to a `RegsBase` there is.
-- Every level the walk reaches sits under the recurrence's step count
-- by its own ceiling, and `capsAt-suc-full` says the cap at that count
-- IS the exit cap -- so a levelled caps receipt widens into the
-- registry's pricing componentwise.
regs-exit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  L ≤ sizeCount (capsAt e sl id) (capsH e sl id) ⊔ Caps.cSize (capsAt e sl id) →
  capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
  RegsBase sl id st
regs-exit {e = e} sl id L sched st hL cok =
  regsSz?-widen (EvalSt.registry st) (proj₁ lift⊑)
    (capsOK?-regs (frameStep L (capsAt e sl id)) sched st cok)
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  lift⊑ : frameStep L c ⊑ᶜ capsAt e sl (suc id)
  lift⊑ = subst (λ x → frameStep L c ⊑ᶜ x) (sym (capsAt-suc-full e sl id))
            (frameStep-mono-j c 2≤S
              (≤-trans hL (⊔-lub ≤-refl
                 (size≤sizeCount c d 2≤S (1≤capsAt-reg e sl id)))))

-- WHAT ONE TURN OF THE RING CARRIES, and it is a ROUND package rather
-- than a flat one.  The ring is the walk's SECOND recursion -- over
-- admitted registrations instead of over a path -- so what has to
-- reproduce itself across a turn is everything a registered chain is
-- walked UNDER: the schedule's slots, the levelled caps receipt, the
-- arriving values' pricing, and the position the round has climbed
-- to.
--
-- THE POSITION IS WHAT A FLAT CEILING CANNOT REPLACE.  A level under
-- the count says nothing about how much of the count is unspent, so a
-- turn that advances the level has no ground to stand the next turn
-- on.  `Reached … J (suc g)` plus `Lv ≤ Ent … J g k` says instead that
-- the level is the `k`-th position of a round entered with `g` to
-- spend -- from which the ceiling is derivable and the NEXT position
-- is one `ent-step` away.  The path receipt is not here: each entry
-- brings its own, off the admitted list's `admSz?`.
--
-- TWIN: `arr-chains-caps-go` -- the cascade's fold over its chains,
--   carrying exactly this package over the same round.
RingState : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (gas Lv J g k : ℕ) (sched : Sched Γ) (st : EvalSt e) → Set
RingState {n = n} {Γ = Γ} {e = e} sl id i vals gas Lv J g k sched st =
  (Sched.slots sched ≡ sl)
  × (capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true)
  × (valsCaps? (frameStep Lv (capsAt e sl id)) sl vals ≡ true)
  × (all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (lookup Γ i)) vals ≡ true)
  × (4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g)
  × Reached (capsAt e sl id) (capsH e sl id) J (suc g)
  × (Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g k)

-- AND THE CEILING IS DERIVED FROM THE POSITION RATHER THAN CARRIED
-- BESIDE IT.  A position of the delivery walk inherits its room from
-- the base's one gas up -- which is `room-descend` -- and `room-step`
-- says the level that lands on IS the next position.  So the bound the
-- ring's Σ owes at every turn is two rewrites away from the package,
-- and carrying it as its own conjunct would oblige every producer to
-- supply a fact its other conjuncts imply.
ring-room : ∀ (c : Caps) (d g J k Lv : ℕ) → 2 ≤ Caps.cSize c →
  suc k ≤ regAt (Caps.cSize c) (Caps.cReg c) J →
  Reached c d J (suc g) →
  Lv ≤ Ent c d J g (suc k) →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c
ring-room c d g J k Lv 2≤S hi hR hLv =
  ≤-trans hLv
    (≤-trans (≤-reflexive (sym (room-step (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g J k)))
             (room-descend c d g J k 2≤S hi (reached-room c d J (suc g) 2≤S hR)))

-- THE STATE ONE TURN OF THE RING LEAVES BEHIND, named so the two leaves
-- and the recursion all read the same object.  A turn delivers into one
-- registration, and what the next turn sees is the schedule and the
-- store that delivery produced -- not the ones it started from, which is
-- the whole reason the ring cannot be a fold over a fixed state.
ringFold : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
  (p : Path Γ (lookup Γ i) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched Γ × EvalSt e
ringFold sf gas nid now i vals fin rid p sched st =
    proj₁ (proj₂ r)
  , proj₂ (proj₂ r)
  where
  r = foldPath sf gas nid now (Fin.toℕ i) p vals
        (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
        (record st { delivered = rid ∷ EvalSt.delivered st })

-- ONE TURN'S ADVANCE IS THE PATH FOLD, so the level it lands at is the
-- fold's own theorem and not a leaf.  `ringFold` IS `foldPath` at the
-- ring's gas over the entry's own source, the walk skeleton is
-- instantiated at exactly the caps hypotheses here, and its receipt
-- reports the three things the statement asks for: the level, that the
-- walk only climbed to it, and the state fact there.  The increment is
-- the difference, which is why the conclusion is stated at `Lv + L'`
-- and proven at the absolute level the walk names.
--
-- TWIN: `chainStep-caps` -- one chain's step of this same fold, with
--   the same discipline: invariant at the stepped cap, own increment
--   reported.
sink-step-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t) (Lv : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl vals ≡ true →
  depthFold sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≤ capsH e sl id →
  Σ ℕ λ L′ →
    (Lv + L′
       ≤ lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv
           (suc (delivN (record st { delivered = rid ∷ EvalSt.delivered st })
                        (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)))))
    × (capsOK? (frameStep (Lv + L′) (capsAt e sl id))
         (proj₁ (ringFold sf gas nid now i vals fin rid p sched st))
         (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)) ≡ true)
sink-step-caps {e = e} sl id sf gas nid now i vals fin rid p Lv sched st sleq cok hpz hvc hdp =
    W.Res.lvl FP ∸ Lv
  , subst (_≤ CEIL) (sym EQ) (≤-trans (W.Res.hi FP) STEP)
  , subst (λ x → capsOK? (frameStep x c)
                   (proj₁ (ringFold sf gas nid now i vals fin rid p sched st))
                   (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)) ≡ true)
          (sym EQ) (proj₂ (proj₁ (W.Res.good FP)))
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} S Wd (Caps.cReg c) d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) slSz)
  FP = W.foldPath-go Lv sf gas nid now (Fin.toℕ i) p vals
         (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched st′
         ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st′ cok)
         hpz hvc (W.eb-seed Lv (Fin.toℕ i) fin) tt tt hdp
  EQ : Lv + (W.Res.lvl FP ∸ Lv) ≡ W.Res.lvl FP
  EQ = m+[n∸m]≡n (W.Res.lo FP)
  D = delivN st′ (proj₂ (ringFold sf gas nid now i vals fin rid p sched st))
  CEIL = lvls S Wd d Lv (suc D)
  entry≤ : iterL S Wd d (pathLen p) Lv ≤ lvls S Wd d Lv 1
  entry≤ = iterL-mono (pathLen p) _ 2≤S ≤-refl ≤-refl ≤-refl
             (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) p hpz) (n≤1+n _))
  STEP : lvls S Wd d (iterL S Wd d (pathLen p) Lv) D ≤ CEIL
  STEP = ≤-trans (lvls-mono D D 2≤S ≤-refl ≤-refl entry≤ ≤-refl)
                 (≤-reflexive (sym (lvls-add S Wd d Lv 1 D)))

-- ONE TURN'S DELIVERIES AGAINST THE BUDGET READ AT ITS OWN POSITION,
-- which is what makes the advance land on the NEXT position rather than
-- merely somewhere higher.  The gas is the ring's own dispatch budget
-- and the round was entered with at least as much, which is the one
-- thing a level bound could never supply.
--
-- TWIN: `chain-deliv-cap` -- the same reading for a cascade's chain.
sink-deliv-cap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t) (Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  gas ≤ g →
  capsOK? (frameStep Lv (capsAt e sl id)) sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl vals ≡ true →
  depthFold sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≤ capsH e sl id →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g k →
  delivN (record st { delivered = rid ∷ EvalSt.delivered st })
         (proj₂ (ringFold sf gas nid now i vals fin rid p sched st))
    ≤ dCapᶜ (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
            (Caps.cReg (capsAt e sl id)) (capsH e sl id) g
            (Pos (capsAt e sl id) (capsH e sl id) J g k)
sink-deliv-cap {e = e} sl id sf gas nid now i vals fin rid p Lv J g k sched st
  sleq hgas cok hpz hvc hdp hLv =
  ≤-trans (W.Res.cnt FP)
          (dCapᶜ-mono {S} {S} {Wd} {Wd} {R} {R} {_} {_} {d} gas g
             2≤S ≤-refl ≤-refl ≤-refl hgas CLIMB)
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  R   = Caps.cReg c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} S Wd R d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) slSz)
  FP = W.foldPath-go Lv sf gas nid now (Fin.toℕ i) p vals
         (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched st′
         ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st′ cok)
         hpz hvc (W.eb-seed Lv (Fin.toℕ i) fin) tt tt hdp
  CLIMB : iterL S Wd d (pathLen p) Lv ≤ Pos c d J g k
  CLIMB = ≤-trans (iterL-mono (pathLen p) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) p hpz)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)

-- THE LADDER THE ENTRY'S WALK IS ENTERED WITH, and it is the round
-- package read one restart down.  A registered chain climbs at most
-- its own path length, `pathSz?` bounds that by one restart, and one
-- restart from the `k`-th position IS the position the round's `walk`
-- constructor reaches with a gas spent.  So what the entry needs is
-- what the ring already holds, at the level below.
sink-entry-ladder : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (p : Path Γ (lookup Γ i) t) (gas Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  RingState {t = t} sl id i vals gas Lv J g k sched st →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  suc k ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Σ ℕ λ g′ → Σ ℕ λ P →
    (4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g′)
    × (iterL (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
             (capsH e sl id) (pathLen p) Lv
         ≤ P)
    × Reached (capsAt e sl id) (capsH e sl id) P g′
sink-entry-ladder {e = e} sl id i vals p gas Lv J g k sched st
  (_ , _ , _ , _ , hfl , hR , hLv) hpzL hi =
  g , Pos c d J g k , hfl , CLIMB , walk J g k hi hR
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  CLIMB : iterL S W d (pathLen p) Lv ≤ Pos c d J g k
  CLIMB = ≤-trans (iterL-mono (pathLen p) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) p hpzL)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)

chain-walk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src p vals evs fin sched st →
  capsWalkOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now p vals fin sched st

-- ONE ADMITTED REGISTRATION'S OWN WALK, which is the first of the two
-- things the ring cannot do for itself.  The entry's path lives in the
-- REGISTRY rather than in the chain being charged, so its receipt is
-- not a sub-receipt of anything the ring holds -- but every hypothesis
-- the path induction wants of it is one the ring already carries.
-- Writing the body is what says so: the walk is entered at the ring's
-- level with the entry's own source, and the only place a `record`
-- update is visible is the `delivered` mark, which the caps receipt
-- survives and the registry does not see.
--
-- TWIN: `arr-chain-caps` -- the cascade's per-chain walk, entered from
--   its own round package by the same two rewrites.
sink-entry-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t) (Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  RingState {t = t} sl id i vals gas Lv J g k sched st →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  suc k ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  depthFold sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st })
    ≤ capsH e sl id →
  capsWalkOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv sf gas nid now
    p vals fin sched (record st { delivered = rid ∷ EvalSt.delivered st })
sink-entry-caps {e = e} sl id sf gas nid now i vals fin rid p Lv J g k sched st
  RS@(sleq , cok , hvc , hcl , _) hpz hi hdf =
  chain-walk-caps sl id Lv sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st })
    ( sleq
    , capsOK?-delivered (frameStep Lv c) rid sched st cok
    , hvc
    , hcl
    , hpz
    , hdf
    , sink-entry-ladder sl id i vals p gas Lv J g k sched st RS hpz hi )
  where
  c = capsAt e sl id

-- THE RING, AND IT IS THE RECURSION AND NOTHING ELSE.  A cancelled
-- registration is skipped at the position it was reached at; a live one
-- spends its own walk, reports its advance, and hands the tail the state
-- its delivery left one position further on.  Both of the depth
-- premise's tails come off the SAME `⊔`, because the measure reports the
-- tail at both states rather than choosing between them -- so neither
-- branch has to re-derive a depth bound, and the skip arm needs nothing
-- beyond the head of the admitted list's pricing being dropped.
sink-ring-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t)) (L₀ Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  RingState {t = t} sl id i vals gas Lv J g k sched st →
  admSz? (Caps.cSize (frameStep L₀ (capsAt e sl id))) ps ≡ true →
  L₀ ≤ Lv →
  k + length ps ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  depthShareGo sf gas nid now i vals fin ps sched st ≤ capsH e sl id →
  shareCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv sf gas nid now
    i vals fin ps sched st
sink-ring-go sl id sf gas nid now i vals fin [] L₀ Lv J g k sched st RS hadm hL₀ hlen hdp = tt
sink-ring-go {n = n} {e = e} sl id sf gas nid now i vals fin ((rid , p) ∷ ps) L₀ Lv J g k sched st
  RS hadm hL₀ hlen hdp
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true =
  sink-ring-go sl id sf gas nid now i vals fin ps L₀ Lv J g k sched st RS
    (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep L₀ (capsAt e sl id))) p)
                   (admSz? (Caps.cSize (frameStep L₀ (capsAt e sl id))) ps) hadm))
    hL₀
    (≤-trans (+-monoʳ-≤ k (n≤1+n (length ps))) hlen)
    (lub3-l (depthShareGo sf gas nid now i vals fin ps sched st)
            (depthFold sf gas nid now (Fin.toℕ i) p vals
              (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
              (record st { delivered = rid ∷ EvalSt.delivered st }))
            (depthShareGo sf gas nid now i vals fin ps
              (proj₁ (ringFold sf gas nid now i vals fin rid p sched st))
              (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)))
            hdp)
... | false =
    sink-entry-caps sl id sf gas nid now i vals fin rid p Lv J g k sched st RS hpzL HI
      (lub3-m DA DB DC hdp)
  , L′
  , ring-room c d g J k (Lv + L′) 2≤S HI hR (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
      (proj₂ RS₁))))))
  , sink-ring-go sl id sf gas nid now i vals fin ps L₀ (Lv + L′) J g (suc k) sched₁ st₁ RS₁
      (proj₂ (∧-true (pathSz? B₀ p) (admSz? B₀ ps) hadm))
      (≤-trans hL₀ (m≤m+n Lv L′))
      (subst (_≤ regAt (Caps.cSize c) (Caps.cReg c) J) (+-suc k (length ps)) hlen)
      (lub3-r DA DB DC hdp)
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  B₀  = Caps.cSize (frameStep L₀ c)
  hR  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ RS)))))
  HI : suc k ≤ regAt (Caps.cSize c) (Caps.cReg c) J
  HI = ≤-trans (subst (suc k ≤_) (sym (+-suc k (length ps)))
                      (s≤s (m≤m+n k (length ps))))
               hlen
  hpz = proj₁ (∧-true (pathSz? B₀ p) (admSz? B₀ ps) hadm)
  sched₁ = proj₁ (ringFold sf gas nid now i vals fin rid p sched st)
  st₁    = proj₂ (ringFold sf gas nid now i vals fin rid p sched st)
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  EVS = if fin then close (Fin.toℕ i) exhausted ∷ [] else []
  DA = depthShareGo sf gas nid now i vals fin ps sched st
  DB = depthFold sf gas nid now (Fin.toℕ i) p vals EVS fin sched st′
  DC = depthShareGo sf gas nid now i vals fin ps sched₁ st₁
  sleq = proj₁ RS
  cok  = proj₁ (proj₂ RS)
  hvc  = proj₁ (proj₂ (proj₂ RS))
  hcl  = proj₁ (proj₂ (proj₂ (proj₂ RS)))
  hfl  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ RS))))
  hgas = proj₂ (proj₂ (floor-parts (4 + (sizeᵉ e + slotsSize sl)) n gas g hfl))
  hLv  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ RS)))))
  hpzL = pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S hL₀)) hpz
  cok′ = capsOK?-delivered (frameStep Lv c) rid sched st cok
  ST  = sink-step-caps sl id sf gas nid now i vals fin rid p Lv sched st
          sleq cok′ hpzL hvc (lub3-m DA DB DC hdp)
  L′  = proj₁ ST
  D   = delivN st′ st₁
  STEP : lvls (Caps.cSize c) (Caps.cWid c) d Lv (suc D) ≤ Ent c d J g (suc k)
  STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLv ≤-refl)
                 (ent-step c d J g k D 2≤S
                    (sink-deliv-cap sl id sf gas nid now i vals fin rid p Lv J g k sched st
                       sleq hgas cok′ hpzL hvc (lub3-m DA DB DC hdp) hLv))
  RS₁ = trans (foldPath-slots sf gas nid now (Fin.toℕ i) p vals EVS fin sched st′) sleq
      , proj₂ (proj₂ ST)
      , valsCaps?-lvl (frameStep Lv c) (frameStep (Lv + L′) c) sl vals
          (frameStep-⊑-+ c 2≤S Lv L′) hvc
      , all-impl _ _
          (λ v h → nestClosOK?ᵛ-widen sl _ v (frameStep-⊑-+ c 2≤S Lv L′) h) vals hcl
      , hfl , hR
      , ≤-trans (proj₁ (proj₂ ST)) STEP

-- THE SINK'S RING RUNS IN A NESTED ROUND, and the walk's own round is
-- what it is nested in.  A ring is not a path: it advances one
-- REGISTRATION at a time, and what has to survive a turn is a position
-- within a round together with the gas that round was entered with.
-- The walk carries a reachable position and a level under it, and the
-- ring opens at position zero of that same round one gas down -- which
-- is the one thing the `walk` constructor charges for.
--
-- SO THE FLOOR IS DENOMINATED IN THE GAS, which is the only quantity
-- here that counts the nestings.  The depth mirror spends one at
-- exactly this head and nowhere else, and the caps face matches the
-- same `suc`, so a floor of the form `<constants> + gas <= g`
-- reproduces itself across a nesting for free: the nested round runs at
-- one less gas AND one less ledger, and the two decrements cancel.  A
-- CONSTANT floor survives one nesting and no more, which is the whole
-- reason the walk's floor carries its gas.
--
-- AND THE REST IS READ OFF THE LEVEL BOUND.  The ring's entry level is
-- the round's own head because the walk's level sits under the position
-- and a round's head only climbs; its admitted list fits one round's
-- ledger because the registry count is the frame cap at the walk's
-- level, which is that same ledger read below the position.
walk-sink-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps {t = t} sl id L sf gas nid now src (share-sink i) vals evs fin sched st →
  dispatchCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now i vals fin sched st
walk-sink-caps sl id L sf zero nid now src i vals evs fin sched st H = tt
walk-sink-caps sl id L sf (suc gas) nid now src i vals evs fin sched st
  (_ , _ , _ , _ , _ , _ , (zero , _ , () , _ , _))
walk-sink-caps {n = n} {Γ = Γ} {t = t} {e = e} sl id L sf (suc gas) nid now src i vals evs fin sched st
  (sleq , cok , hvc , hcl , _ , hdp , (suc g₀ , P , hfl , hlvP , hR)) =
    shareAdmit-sz i (Caps.cSize (capsAt e sl (suc id))) (EvalSt.registry st)
      (regs-exit sl id L sched st L≤TOP cok)
  , ≤-trans (shareAdmit-len i (EvalSt.registry st))
            (≤-trans (capsOK?-count (frameStep L c) sched st cok)
                     (subst (λ x → Caps.cReg (frameStep L c) ≤ Caps.cReg x)
                            (sym (capsAt-suc-full e sl id))
                            (frameStep-reg-mono c L≤)))
  , sink-ring-go sl id sf gas nid now i vals fin
      (shareAdmit i (EvalSt.registry st)) L L P g₀ 0 sched (shareLatch i fin st)
      ( sleq
      , shareLatch-caps (frameStep L c) i fin sched st cok
      , hvc
      , hcl
      , hfl₀ , hR , hL₀ )
      (shareAdmit-sz i (Caps.cSize (frameStep L c)) (EvalSt.registry st)
         (capsOK?-regs (frameStep L c) sched st cok))
      ≤-refl
      hlen₀
      hdp
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  hfl₀ : 4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g₀
  hfl₀ = ≤-pred (subst (_≤ suc g₀)
                   (+-suc (4 + (sizeᵉ e + slotsSize sl) + n) gas) hfl)
  L≤P : L ≤ P
  L≤P = ≤-trans (iterL-infl S W d (pathLen {Γ = Γ} {t = t} (share-sink i)) L) hlvP
  L≤TOP : L ≤ sizeCount c d ⊔ S
  L≤TOP = ≤-trans L≤P
            (≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d (suc g₀) P))
                     (reached-room c d P (suc g₀) 2≤S hR))
  hL₀ : L ≤ Ent c d P g₀ 0
  hL₀ = ≤-trans L≤P (ent-infl c d P g₀ 0)
  hlen₀ : 0 + length (shareAdmit i (EvalSt.registry st)) ≤ regAt S (Caps.cReg c) P
  hlen₀ = ≤-trans (shareAdmit-len i (EvalSt.registry st))
            (≤-trans (capsOK?-count (frameStep L c) sched st cok)
              (≤-trans (≤-reflexive (frameStep-regAt c L))
                 (regAt-mono {S} {S} {Caps.cReg c} {Caps.cReg c} ≤-refl ≤-refl L≤P)))
  L≤ : L ≤ sizeCount c d
  L≤ = ≤-trans L≤P
         (≤-trans (≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d (suc g₀) P))
                           (reached-room c d P (suc g₀) 2≤S hR))
                  (⊔-lub ≤-refl (size≤sizeCount c d 2≤S (1≤capsAt-reg e sl id))))

-- THE ONE HEAD THAT OWES, AND A CENSUS SAYS WHICH CONJUNCTS THOSE
-- ARE.  The state and slot conjuncts are the frame's own hypotheses,
-- and TWO of the per-entry readings are already recorded: the store
-- predicate carries a written-size field and a width field per NODE,
-- and the lookup hypothesis here names the very node whose queue is
-- being read, so the entry's size and its slot width come off the
-- receipt the frame arrives holding.
--
-- WHAT IS ACTUALLY OWED IS THREE THINGS, and they fail for three
-- different reasons.  The entry's CLOSURE key is recorded nowhere --
-- the store predicate's closure half ranges over the live list and
-- never over the node table -- but it does not want a field, because
-- a key read through a CAPPED telescope is at most the cap times the
-- term's plain size, and the size is recorded; one level absorbs the
-- factor, which is the ratio `clos-lift` already spends.  The ROOM
-- FLOOR comes off the store predicate's own park field, which is what
-- fixes the cap it is read at: the field is re-established one level
-- up at every park, so the floor is a statement about the walk's level
-- and the base reading is available to no queue at all.  And the
-- REACHED level is a fact about the ceiling rather than about the
-- store, so no field could hold it.
--
-- AND THE ACCOUNT THAT REPLACES ALL OF THIS CHARGES THE TERM AT
-- DELIVERY RATHER THAN AT DRAIN (Anthony's ruling).  The demand is not
-- wrong: a drained descent really does run at the global cursor and
-- really does push it.  What cannot be done is to have anyone hold
-- that fact AHEAD of time, because whether it holds is settled jointly
-- by the term's ladder and the budget remaining when the drain
-- happens.  So the store stops carrying a ceiling: what it carries is
-- the term's price at the path it was DELIVERED under, which is fixed
-- when the term is emitted and never climbs, so no level is named and
-- the invariant becomes statable at all.  The drain then derives its
-- ceiling from the parent frame's own remaining budget -- the chain
-- already hands one to every frame, and this one is not special -- and
-- the delivery price is the debit the drain's fold spends.
--
-- AND THE ITERATED FACT IS NOW PROVEN, IN THE CURRENCY THE SUBSCRIBE
-- ALREADY REPORTS IN.  One unit of the operator measure buys one
-- LEVEL, which is not what the drain climbs -- the subscribe's caps
-- lemma hands back a climb it chooses, bounded by a SWEEP rather than
-- in operator units -- and the multi-level step that would have taken
-- it wants a climb under a quadratic in the cap, which nothing
-- supplies.  The repair is that the quadratic was never the price: the
-- entry step spends its room only on lifting a sweep to the level the
-- ladder's own recursion starts a sweep at, so a climb reported
-- DIRECTLY under that sweep needs no room at all.  One operator unit
-- therefore buys a whole sweep, and a queue whose entries each climb
-- within one costs one unit each -- so the fold holds a single
-- frame-level ceiling and spends it entry by entry, and the store
-- carries an offset with a sweep bound in place of a roof.

-- AND THE REACHED LEVEL IS NOT MERELY UNSUPPLIED -- A WITNESS KILLS
-- IT, in the GAS currency, which is the same base-cap defect the
-- three readings above already suffered.  A reached gas is rooted at `suc`
-- the ENTRY size cap and every walk position spends one, so no gas the
-- relation offers exceeds that root; the nesting the ceiling entry is
-- asked for is bounded only at the cap the walk has STEPPED to, and one
-- step multiplies the size by better than the size itself.  So the
-- entry demands a fuel above the entry cap and the relation cannot
-- issue one -- and the fuel is not slack that could be found elsewhere,
-- since the delivery recurrence grows without bound in it while the
-- count it is measured against does not move.  Handing over the walk's
-- OWN ceiling entry does not help: the same reading caps that one too.
-- REFUTED: `Refuted.Drain-Reach-Gas.drain-reach-gas-absurd`, at one
--   level, with `drain-reach-gas-base` beside it proving the same
--   obligation at level zero -- where the room floor the entry already
--   carries IS the gas floor and the bottom constructor supplies the
--   level.
-- REFUTED: `Refuted.Frame-Step-Compose.frameStep-compose-absurd`;
--   `Refuted.Drain-Queue-Flat.drain-spine-flat-absurd` for the
--   conjuncts themselves being unreachable from what the walk holds;
--   and `Refuted.Arr-Cap-Step.arr-cap-step-absurd` for the raise that
--   also re-enters the arrival family one level up, which is the one
--   route the two above leave standing
-- TWIN: `subscribeE-caps` already threads a level exactly this way --
--   invariant at the stepped cap, conclusion at the sum -- and is
--   proven.
-- PROBED: `Probed.Drain-Queue-Ladder` reads the two computable halves
--   at a `mergeAll` limited to one over parked inners, at queue
--   lengths TWO and FOUR -- the queue read off the node the run
--   installed, so the entries are the ones the evaluator parked.  Both
--   dominate with room: the frame reads eighteen and eighty-seven
--   against entries at eleven, charged twenty-nine and thirty once
--   one level per entry is paid for.  Not covered, and the first is
--   the one that matters: the position is CHARGED rather than
--   measured, so nothing here reaches the sweep-currency climb the
--   subscribe actually takes; the ledger comparison the
--   readings feed, symbolic-or-nothing by the descent family's own
--   dead route; the two heads other than `mergeAllᵒ`; and a queue
--   whose entries differ from one another in size.
-- PROBED: `Probed.Drain-Queue-Length` reads the other half the fold
--   names -- the queue's LENGTH, since one unit of the frame's
--   measure is spent per entry.  A limit-one merge over a scripted
--   input parks one short of the script at three lengths, against a
--   syntax size that does not move, so no bound naming the program's
--   own size can hold; the slot vocabulary dominates at all three.
--   Not covered: a source that parks without a script, a limit other
--   than one, a merge nested in another's drain, and the cap, which
--   is a tower and is not instantiated.
postulate
  walk-frame-drain-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (src : Source) (op : AllOp) (allNid : NodeId) (inst : NodeId)
    (p : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    WalkHyps sl id L sf gas nid now src (from-inner op allNid inst ↠ p)
      vals evs fin sched st →
    ∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
      lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
      capsDrainOK (capsAt e sl id) sl (capsH e sl id) L sf allNid p nid now
        lim (pred act) q sched st


-- AND THE DRAIN ONE IS NOW A FRAME-LOCAL STATEMENT, which is what it
-- had to become.  Its conjunct used to charge the walk's LEVEL against
-- the BASE size cap, because the proven consumer climbed the relative
-- ceiling one operator per level from the bottom and that climb is paid
-- for only while the level fits under that cap.  The walk's ladder is
-- denominated in the COUNT instead -- the Σ it hands its tail permits a
-- level anywhere up to `sizeCount c d ⊔ Caps.cSize c`, and the arrival
-- face confirms levels genuinely reach the count -- so at level zero the
-- conjunct was `capsOK?` read through `parkRoom` and the level was the
-- whole of what it asked for and the whole of what the bundle could not
-- give.
--
-- WHAT THE CONJUNCT SAYS NOW IS THE PARKED TERM UNDER THE BASE CAP,
-- with no level term in it, which is the refuted statement minus the
-- refuted part, TOGETHER WITH THE LEVEL BEING REACHED.  A level the
-- cascade's delivery walk actually lands on carries the gas it still
-- has there, and from that its room is derived rather than assumed:
-- the walk recurrence splits so that the budget read from a reached
-- level IS the walk read from the level before it, one gas down, and
-- the bottom is the two bodies.  So the queue asks for the reaching
-- and the arithmetic follows.
--
-- AND THE GAS IS WHY THE RELATION CARRIES ONE.  At the whole cascade's
-- gas a room receipt is false everywhere above the bottom -- the
-- budget read higher is the larger one and the ladder from there is
-- longer, so both sides move the wrong way at once -- while four plus
-- a term's operator count is syntactic and fixed before any level
-- exists.  A level bound cannot say which of the two it has; the
-- reaching relation can, because it is built by spending it.
--
-- AND THE REACHING IS A `≤`, WHICH IS THE ONLY SHAPE THAT COULD BE
-- SUPPLIED.  A chain advances its level by one frame charge at a time
-- while the cascade advances by whole restarts, so the levels a chain
-- visits sit BETWEEN two positions the walk lands on and are almost
-- never positions themselves.  Room survives that gap in the useful
-- direction: the ladder from a level and the budget read at it both
-- grow with the level, so the receipt at the position ABOVE covers
-- every level under it, and what the queue asks for is a position
-- above the walk's level rather than the walk's level itself.
--
-- RECOVERY: git show b927a16 restores `Refuted.Walk-Frame-Drain-Level`,
--   which refuted the levelled conjunct at the empty context with the
--   level taken to be the base size cap, every other premise met by the
--   entry bounds and the proven node installer.  Whoever puts a level
--   back into this statement wants that witness back.

-- AND FOUR OF THE FIVE HEADS OWE NOTHING, which the match says in
-- code rather than in prose.  Only a `from-inner` names a node, so
-- only a `from-inner` can be looking at a `mergeAll` queue; the other
-- four forward what they are handed and their arm is the unit.
walk-frame-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src (f ↠ p) vals evs fin sched st →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) L sf nid now f p vals sched st

walk-frame-drain sl id L sf gas nid now src (map-f _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (scan-f _ _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (take-f _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (thru-outer _ _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (from-inner op allNid inst) p vals evs fin sched st H =
  walk-frame-drain-inner sl id L sf gas nid now src op allNid inst p vals evs fin sched st H



-- THE WALK ITSELF, WHICH IS THE FRAME LAW ITERATED AND NOTHING ELSE.
-- Each frame spends the proven step receipt, which reports its own
-- increment and hands back the caps and the values one level up; the
-- ladder premise pays the ceiling at that frame and reproduces itself
-- for the tail, since `iterL` at a `suc` IS `iterL` at the stepped
-- level.  The path receipt splits the same way -- this frame's, the
-- tail's length, the tail's -- so nothing has to be re-established
-- from outside, which is what made the frame law's data the right
-- thing to state the walk over.
chain-walk-caps sl id L sf gas nid now src root vals evs fin sched st H =
  proj₁ (proj₂ H)
chain-walk-caps sl id L sf gas nid now src (share-sink i) vals evs fin sched st H =
  proj₁ (proj₂ H)
  , walk-sink-caps sl id L sf gas nid now src i vals evs fin sched st H
chain-walk-caps {e = e} sl id L sf gas nid now src (f ↠ p) vals evs fin sched st
  H@(sleq , cok , hvc , hcl , hpz , hdp , (g , P , hfl , hlvP , hR)) =
    cok
  , proj₁ (valsCaps?-parts (frameStep L c) sl vals hvc)
  , slSz
  , hpz
  , walk-frame-clos sl id L sf gas nid now src f p vals evs fin sched st H
  , walk-frame-drain sl id L sf gas nid now src f p vals evs fin sched st H
  , Lt ∸ L
  , subst (_≤ sizeCount c d ⊔ S) (sym hLt) Lt≤TOP
  , subst (λ x → capsWalkOK c (capsAt e sl (suc id)) sl d x sf gas nid now p
                   (proj₁ r) (proj₁ (proj₂ (proj₂ r)))
                   (proj₁ (proj₂ (proj₂ (proj₂ r))))
                   (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      (sym hLt)
      (chain-walk-caps sl id Lt sf gas nid now src p
        (proj₁ r) (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
        (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
        ( trans (KeepsC.slotsEq (stepFrame-keeps sf nid now f p vals fin sched st)) sleq
        , capsOK?-mono (frameStep (L + proj₁ ST) c) (frameStep Lt c)
            (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
            (frameStep-mono-j c 2≤S ST≤t) (proj₁ (proj₂ ST))
        , valsCaps?-lvl _ _ sl (proj₁ r)
            (frameStep-mono-j c 2≤S ST≤t) (proj₁ (proj₂ (proj₂ ST)))
        , all-impl _ _
            (λ v h → nestClosOK?ᵛ-widen sl _ v (frameStep-mono-j c 2≤S STs≤t) h)
            (proj₁ r)
            (clos-lift c (L + proj₁ ST) sl (proj₁ r) 2≤S (slotsCaps?-capsAt e sl id)
              (all-impl _ _
                 (λ v → valCaps?-size (frameStep (L + proj₁ ST) c) sl _ v)
                 (proj₁ r)
                 (proj₁ (valsCaps?-parts (frameStep (L + proj₁ ST) c) sl (proj₁ r)
                           (proj₁ (proj₂ (proj₂ ST)))))))
        , pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S L≤t)) pz2
        , ≤-trans (m≤n⊔m (depthFrame sf nid now f p vals fin sched st) _) hdp
        , (g , P , hfl , hlvP , hR) ))
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  B   = Caps.cSize (frameStep L c)
  pz1 : frameSz? B f ≡ true
  pz1 = proj₁ (∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)
  pzr : ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) ≡ true
  pzr = proj₂ (∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)
  pzl : (suc (pathLen p) ≤ᵇ B) ≡ true
  pzl = proj₁ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) pzr)
  pz2 : pathSz? B p ≡ true
  pz2 = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) pzr)
  r   = stepFrame sf nid now f p vals fin sched st
  ST  = stepFrame-caps c d (frameBud c L) L sf nid now f p vals fin sl sched st
          2≤S (1≤capsAt-reg e sl id) sleq (slotsCaps?-capsAt e sl id) slSz cok
          pz1 pz2 (≤ᵇ⇒≤ (suc (pathLen p)) B (T-to pzl))
          hvc ≤-refl
          (≤-trans (m≤m⊔n (depthFrame sf nid now f p vals fin sched st) _) hdp)
  Lt  = fLvlD S W d L
  STs≤t : suc (L + proj₁ ST) ≤ Lt
  STs≤t = proj₂ (proj₂ (proj₂ (proj₂ ST)))
  ST≤t : L + proj₁ ST ≤ Lt
  ST≤t = ≤-trans (n≤1+n (L + proj₁ ST)) STs≤t
  sucL≤t : suc L ≤ Lt
  sucL≤t = sucJ≤fLvlD S W d L
  L≤t : L ≤ Lt
  L≤t = ≤-trans (n≤1+n L) sucL≤t
  hLt : L + (Lt ∸ L) ≡ Lt
  hLt = m+[n∸m]≡n L≤t
  P≤TOP : P ≤ sizeCount c d ⊔ S
  P≤TOP = ≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d g P))
                  (reached-room c d P g 2≤S hR)
  Lt≤TOP : Lt ≤ sizeCount c d ⊔ S
  Lt≤TOP = ≤-trans (iterL-infl S W d (pathLen p) Lt) (≤-trans hlvP P≤TOP)

-- AND THE CHAIN'S OWN LEAF IS NOW THAT WALK AT ITS ENTRY, with the one
-- step of arithmetic between them real: the premise arrives as a
-- DELIVERY count, which is the currency the cascade fold's invariant is
-- kept in, and the walk wants a FRAME count, which is the currency the
-- level ladder climbs in.  `pathSz?` is the conversion -- a chain is at
-- most `suc (sizeAt S L)` frames, which is exactly one rung -- so the
-- two statements are the same bound read at the two granularities the
-- fold and the walk respectively speak, and neither has to know the
-- other's.
--
-- AND THE REST OF THE HYPOTHESES ARE THE FRAME LAW'S OWN, WHICH IS THE
-- ONLY CLAIM MADE FOR THEM.  A walk is the iterate of one frame's
-- receipt, so it is stated over that receipt's data: the values' caps,
-- the path's size receipt, the depth bound.  Each is what the frame law
-- takes at every frame, each propagates down a path without further
-- hypothesis -- the path receipt splits into this frame's, the tail's
-- length and the tail's -- and the sole caller holds all three already,
-- since it hands the same three to the step face next door.  What is
-- NOT claimed is that a form without them is false: nothing has
-- instantiated that, and the argument here is the twin's shape rather
-- than a witness.
arr-chain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (arrTy a)) (arrVal a ∷ []) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  (Σ ℕ λ g → Σ ℕ λ P →
     (4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g)
     × (lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv 1
          ≤ P)
     × Reached (capsAt e sl id) (capsH e sl id) P g) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv nextId a path sched st
arr-chain-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp
  (g , P , hfl , hlvP , hR) =
  chain-walk-caps sl id Lv (budgetAt e (Sched.slots sched) nextId) n nextId
    (arrTick a) (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
    (sleq , cok , hvc , hcl , hpz , hdp , (g , P , hfl , ENTRY , hR))
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  ENTRY : iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv ≤ P
  ENTRY = ≤-trans (iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz)
                              (n≤1+n _)))
            hlvP


-- ONE CHAIN'S STEP IS THE PATH FOLD, so the level it lands at is the
-- fold's own theorem and not a leaf.  `chainStep` IS `foldPath` at the
-- minted gas, the walk skeleton is instantiated at exactly the caps
-- hypotheses here, and its receipt reports the three things the
-- statement asks for: the level, that the walk only climbed to it, and
-- the state fact there.  The increment is the difference, which is why
-- the conclusion is stated at `Lv + L'` and proven at the absolute
-- level the walk names.
--
-- TWIN: `stepFrame-caps` -- one frame of this same fold, with the same
--   discipline: invariant at the stepped cap, own increment reported.
chainStep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  valCaps? (frameStep Lv (capsAt e sl id)) sl (arrTy a) (arrVal a) ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Σ ℕ λ L′ →
    (Lv + L′ ≤ lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id)
                 Lv (suc (delivN st (proj₂ (proj₂ (chainStep nextId a path sched st))))))
    × (capsOK? (frameStep (Lv + L′) (capsAt e sl id))
         (proj₁ (proj₂ (chainStep nextId a path sched st)))
         (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true)
chainStep-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hpz hvc hdp =
  W.Res.lvl FP ∸ Lv
  , subst (_≤ CEIL) (sym EQ) (≤-trans (W.Res.hi FP) STEP)
  , subst (λ x → capsOK? (frameStep x c)
                   (proj₁ (proj₂ (chainStep nextId a path sched st)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true)
          (sym EQ) (proj₂ (proj₁ (W.Res.good FP)))
  where
  c = capsAt e sl id
  d = capsH e sl id
  2≤S : 2 ≤ Caps.cSize c
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH (λ {n′} {Γ′} {t′} {e′} {u′} →
                            subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
                         (λ {n′} {Γ′} {t′} {e′} {s′} →
                            innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
                         c d sl 2≤S (1≤capsAt-reg e sl id)
                         (slotsCaps?-capsAt e sl id) slSz)
  FP = W.foldPath-go Lv (budgetAt e (Sched.slots sched) nextId) n nextId
         (arrTick a) (arrSource a) path (arrVal a ∷ [])
         (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
         (Arrival.isLast a) sched st
         ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st cok)
         hpz (∧-intro (∧-intro hvc refl) refl)
         (W.eb-seed Lv (arrSource a) (Arrival.isLast a)) tt tt hdp
  EQ : Lv + (W.Res.lvl FP ∸ Lv) ≡ W.Res.lvl FP
  EQ = m+[n∸m]≡n (W.Res.lo FP)
  D = delivN st (proj₂ (proj₂ (chainStep nextId a path sched st)))
  CEIL = lvls (Caps.cSize c) (Caps.cWid c) d Lv (suc D)
  -- one chain is at most `suc (sizeAt S Lv)` frames, so its whole level
  -- climb is peeled off the front of the walk's own ladder as ONE
  -- delivery's charge — which is what makes the ceiling base-relative
  -- and so composable along the cascade
  chain≤ : iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv
             ≤ lvls (Caps.cSize c) (Caps.cWid c) d Lv 1
  chain≤ = iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
             (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz) (n≤1+n _))
  STEP : lvls (Caps.cSize c) (Caps.cWid c) d
           (iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv) D ≤ CEIL
  STEP = ≤-trans (lvls-mono D D 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                 (≤-reflexive (sym (lvls-add (Caps.cSize c) (Caps.cWid c) d Lv 1 D)))

-- ONE CHAIN'S DELIVERIES AGAINST THE BUDGET READ AT ITS OWN POSITION,
-- which is the recursive shape of the whole claim rather than a step
-- of it: the cascade's total is what `cascadeGo-deliveries` bounds at
-- entry, and this is the same statement one round down, at the level
-- the round's ledger has climbed to instead of at the entry level.
-- The gas is the term's own operator budget, and it is what stops the
-- statement being vacuous -- at gas zero the cap is zero and no chain
-- delivering anything can fit.
chain-deliv-cap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) (Lv J g i : ℕ) →
  Sched.slots sched ≡ sl →
  n ≤ g →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  delivN st (proj₂ (proj₂ (chainStep nextId a path sched st)))
    ≤ dCapᶜ (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
            (Caps.cReg (capsAt e sl id)) (capsH e sl id) g
            (Pos (capsAt e sl id) (capsH e sl id) J g i)
chain-deliv-cap {n = n} {e = e} sl id a nextId path sched st Lv J g i
  sleq n≤g cok hpz hvc hdp hLv =
  ≤-trans (W.Res.cnt (W.foldPath-go Lv (budgetAt e (Sched.slots sched) nextId) n nextId
                        (arrTick a) (arrSource a) path (arrVal a ∷ [])
                        (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                        (Arrival.isLast a) sched st
                        ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st cok)
                        hpz hvc refl tt tt hdp))
          (dCapᶜ-mono {S} {S} {Wd} {Wd} {R} {R} {_} {_} {d} n g
             2≤S ≤-refl ≤-refl ≤-refl n≤g CLIMB)
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  R   = Caps.cReg c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  module W = Walk {e = e} S Wd R d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id)
           (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)))
  -- the chain's frames climb at most one restart, which is what
  -- `pathSz?` bounds, and one restart from the round's ledger IS the
  -- position -- so the level the fold reads the budget at dominates
  -- the level the chain's own walk reads it at
  CLIMB : iterL S Wd d (pathLen path) Lv ≤ Pos c d J g i
  CLIMB = ≤-trans (iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)


-- `R` for the tail, related by `lvls-add`.
arr-chains-caps-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv
       (delivN st (proj₂ (proj₂ (cascadeGo a nextId chains sched st))))
    ≤ sizeCount (capsAt e sl id) (capsH e sl id) ⊔ Caps.cSize (capsAt e sl id) →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  (J g i : ℕ) →
  4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g →
  Reached (capsAt e sl id) (capsH e sl id) J (suc g) →
  i + length chains
    ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv a nextId chains sched st
arr-chains-caps-go sl id Lv a nextId [] sched st sleq hlv cok hpz hvc hcl hdp
  J g i hfl hR hlen hLv = tt
arr-chains-caps-go {n = n} {e = e} sl id Lv a nextId ((rid , path) ∷ chains) sched st sleq hlv cok hpz hvc hcl hdp
  J g i hfl hR hlen hLv
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = arr-chains-caps-go sl id Lv a nextId chains sched st sleq hlv cok
                (proj₂ (∧-true _ _ hpz)) hvc hcl
                (lub3-l (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched
                           (record st { delivered = rid ∷ EvalSt.delivered st }))
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))
                           (proj₂ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
                J g i hfl hR
                (≤-trans (+-monoʳ-≤ i (n≤1+n (length chains))) hlen) hLv
... | false =
      arr-chain-caps sl id Lv a nextId path sched st′ sleq cok
        HVC HCL
        (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
        (lub3-m (depthCascade a nextId chains sched st)
                (depthChain nextId a path sched st′)
                (depthCascade a nextId chains
                   (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        (g , Pos c d J g i , hfl , CH≤ , walk J g i HI hR)
    , proj₁ ST
    , FLAT
    , arr-chains-caps-go sl id (Lv + proj₁ ST) a nextId chains
        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
        (proj₂ (proj₂ (chainStep nextId a path sched st′)))
        (trans (chainStep-slots nextId a path sched st′) sleq)
        REC (proj₂ (proj₂ ST))
        (proj₂ (∧-true _ _ hpz)) hvc hcl
        (lub3-r (depthCascade a nextId chains sched st)
                (depthChain nextId a path sched st′)
                (depthCascade a nextId chains
                   (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        J g (suc i) hfl hR
        (subst (_≤ regAt S (Caps.cReg c) J) (+-suc i (length chains)) hlen)
        (≤-trans (proj₁ (proj₂ ST)) STEP)
  where st′ = record st { delivered = rid ∷ EvalSt.delivered st }
        c   = capsAt e sl id
        S   = Caps.cSize c
        W   = Caps.cWid c
        d   = capsH e sl id
        TOP = sizeCount c d ⊔ S
        2≤S = 2≤capsAt-size e sl id
        st₁ = proj₂ (proj₂ (chainStep nextId a path sched st′))
        D   = delivN st′ st₁
        R   = delivN st₁ (proj₂ (proj₂ (cascadeGo a nextId chains
                (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁)))
        step⊑ = frameStep-mono-j c 2≤S (z≤n {Lv})
        c⊑ : c ⊑ᶜ frameStep Lv c
        c⊑ = subst (_⊑ᶜ frameStep Lv c) (frameStep-0 c) step⊑
        HVC0 : valsCaps? c sl (arrVal a ∷ []) ≡ true
        HVC0 = ∧-intro (∧-intro hvc refl) refl
        HVC : valsCaps? (frameStep Lv c) sl (arrVal a ∷ []) ≡ true
        HVC = valsCaps?-lvl c (frameStep Lv c) sl (arrVal a ∷ []) c⊑ HVC0
        HCL : all (nestClosOK?ᵛ (frameStep Lv c) sl (arrTy a)) (arrVal a ∷ []) ≡ true
        HCL = all-impl _ _
                (λ v h → nestClosOK?ᵛ-widen sl _ v c⊑ h)
                (arrVal a ∷ []) (∧-intro hcl refl)
        ST  = chainStep-caps sl id Lv a nextId path sched st′ sleq cok
                (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
                (valCaps?-widen sl (arrTy a) (arrVal a) c⊑ hvc)
                (lub3-m (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched st′)
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                           (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        -- THE CASCADE'S OWN LEDGER LINE, at the state this arm has
        -- already reduced to: an uncancelled registration costs one
        -- delivery, plus this chain's fold, plus the tail's.  It is
        -- written here rather than taken from the ledger stratum
        -- because the `with` has replaced the cascade by its reduct,
        -- and a lemma stated over the unreduced application no longer
        -- applies to what this arm holds.
        CS  = chainStep-deliv nextId a path sched st′
        GO  = cascadeGo-deliv a nextId chains
                (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁
        SPLIT : delivN st (proj₂ (proj₂ (cascadeGo a nextId chains
                  (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁)))
                  ≡ suc (D + R)
        SPLIT = trans (delivN-cons rid st _ (⊑ᵈ-trans CS GO))
                      (cong suc (delivN-split CS GO))
        hlvC : lvls S W d Lv (suc (D + R)) ≤ TOP
        hlvC = subst (λ x → lvls S W d Lv x ≤ TOP) SPLIT hlv
        -- this chain's own charge, which is what both the leaf below
        -- and the Σ above are bounded by
        FLATC : lvls S W d Lv (suc D) ≤ TOP
        FLATC = ≤-trans (lvls-mono (suc D) (suc (D + R)) 2≤S ≤-refl ≤-refl ≤-refl
                           (s≤s (m≤m+n D R)))
                        hlvC
        FLAT = ≤-trans (proj₁ (proj₂ ST)) FLATC
        -- this chain sits at the round's `i`-th position, and one
        -- restart from there is what its own frames may climb
        HI : suc i ≤ regAt S (Caps.cReg c) J
        HI = ≤-trans (subst (suc i ≤_) (sym (+-suc i (length chains)))
                            (s≤s (m≤m+n i (length chains))))
                     hlen
        CH≤ : lvls S W d Lv 1 ≤ Pos c d J g i
        CH≤ = lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl
        hgn = proj₁ (proj₂ (floor-parts (4 + (sizeᵉ e + slotsSize sl)) n n g hfl))
        -- and the fold's own climb lands on the NEXT position exactly
        -- when this chain's deliveries fit the budget read at this one
        STEP : lvls S W d Lv (suc D) ≤ Ent c d J g (suc i)
        STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLv ≤-refl)
                       (ent-step c d J g i D 2≤S
                          (chain-deliv-cap sl id a nextId path sched st′ Lv J g i
                             sleq hgn cok
                             (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
                             HVC
                             (lub3-m (depthCascade a nextId chains sched st)
                                     (depthChain nextId a path sched st′)
                                     (depthCascade a nextId chains
                                        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                                        (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
                             hLv))
        REC  = ≤-trans (lvls-mono R R 2≤S ≤-refl ≤-refl (proj₁ (proj₂ ST)) ≤-refl)
                 (≤-trans (≤-reflexive (sym (lvls-add S W d Lv (suc D) R))) hlvC)

arr-chains-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st) ≤ capsH e sl id →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId (chainsOf a st) sched
    (cascadeLatch a st)
arr-chains-caps {e = e} sl id a nextId sched st sleq cok hpz hvc hcl hdp =
  arr-chains-caps-go sl id 0 a nextId (chainsOf a st) sched (cascadeLatch a st)
    sleq ENTRY
    (subst (λ x → capsOK? x sched (cascadeLatch a st) ≡ true)
           (sym (frameStep-0 (capsAt e sl id))) LATCH)
    hpz hvc hcl hdp
    0 (Caps.cSize (capsAt e sl id)) 0
    (capsAt-round-size e sl id) base REGLEN ≤-refl
  where
  c   = capsAt e sl id
  LATCH = cascadeLatch-caps (capsAt e sl id) a sched st cok
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  -- the round has as many positions as the registry has entries, and
  -- the cascade walks a sublist of it
  REGLEN : 0 + length (chainsOf a st) ≤ regAt (Caps.cSize c) (Caps.cReg c) 0
  REGLEN = ≤-trans (≤-trans (chainsOf-length a st)
                            (capsOK?-count c sched st cok))
                   (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))
  -- the cascade's own delivery total, which is what the fold's
  -- invariant is stated over
  DEL = cascadeGo-deliveries
          (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
          (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
          c d a nextId (chainsOf a st) sl sched (cascadeLatch a st)
          2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) sleq
          (cascadeLatch-caps c a sched st cok) hvc hpz (n≤capsAt-size e sl id)
          (subst (length (chainsOf a st) ≤_) (realWidAt-def e sl id)
                 (chains-count-width sl id a sched st cok))
          slSz hdp
  ENTRY = ≤-trans (lvls-mono (delivN (cascadeLatch a st)
                                (proj₂ (proj₂ (cascadeGo a nextId (chainsOf a st) sched
                                                 (cascadeLatch a st)))))
                             (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl DEL)
                  (≤-trans (≤-reflexive (sym (sizeCount-body c d)))
                           (m≤m⊔n (sizeCount c d) (Caps.cSize c)))

-- ONE ROUND'S DESCENT AGAINST WHAT THE ROUND CAN SEE.  A cascade
-- descends by crossing `thru-outer` frames and by draining a bounded
-- mergeAll, and both crossings are paid for out of structure that is
-- already present when the round starts: the payload it carries, the
-- store it walks, and the program's own wrap unit.  `sightCeil` is
-- that sum scaled by the program's size.
--
-- WHY THE SCALING IS THE WHOLE CONTENT.  Edge by edge a descent
-- TRADES: what a frame takes off the subject it puts on the path, so
-- the bare sum is an equality along the subscribe walk.  The drain is
-- the one level with no edge to come out of -- it runs under a
-- `from-inner`, which the path measure charges nothing for -- and a
-- program whose folds nest spends one per layer.  So the gap grows
-- with a program parameter the sum does not see.
--
-- AND THE SEEN PARAMETER IS A SIZE, WHICH IS WHY THE SUMMANDS COULD
-- NOT BE MADE BIGGER.  All three of them are NESTING depths, so none
-- moves with how many values an instant carries: at two programs
-- differing only in the delivered count, every quantity this statement
-- reads is identical while the descent moves by a third.  The size is
-- the only sighted thing that separates them, and it enters as a
-- FACTOR because as a summand it is outrun -- one per delivered value
-- against the descent's eight.
--
-- AND THE STORE SLOT IS THE CAP, NOT THE READING, WHICH IS WHAT MAKES
-- THE ROUND INDUCIBLE.  A round states its ceiling once and spends it
-- at every chain, and the chains after the first run on states their
-- predecessors moved -- so the slot has to hold across the walk.  The
-- reading does not: a chain subscribes what its delivery reaches and
-- installs the nodes for it, and both the live fold and the node fold
-- are places the measure reads.  The CAP does, and it costs the
-- consumer nothing, because the arithmetic below already collapses all
-- three of the ceiling's summands to that same cap.
--
-- REFUTED: `Refuted.Chain-Step-Store` is why the reading could not be
--   carried -- nine before one chain and sixteen after, at the instant
--   the round's own rows are read at, with two further families in the
--   same corpus growing at the same instant.  What died is the plan to
--   thread the entry store across the chains; the growth has to be
--   priced, and pricing it against the cap is what the leaves below do.
-- DEAD ROUTE: descending into `depthE` and spending `depthE-sighted`
--   cannot close this.  That ceiling carries the FOLD's grant in its
--   subject place -- a tower over the payload -- where this one
--   carries the arrival's own nesting, and two upper bounds stated in
--   different currencies do not compose.  The delivery side needs its
--   own value-nesting walk, which is what the leaf below states.
-- REFUTED: `Refuted.Cascade-Deliv-Depth` is the delivery-side witness
--   the ceiling is calibrated against -- a limit-one mergeAll over
--   three inners, read at the second cascade, whose descent climbs six
--   per fold layer against the bare sum's four.
-- PROBED: `Probed.Depth-Sighted` reads this side at the second cascade
--   along both axes -- fold depths two and eight, delivered counts two,
--   six and twenty -- and at the width family that drains nothing.
--   Those rows are what killed the two cheaper shapes: a bare factor of
--   two fails forty-nine against forty-four, and a size SUMMAND fails
--   one hundred and ninety-three against one hundred and fourteen at
--   the far end of the count axis.  A THIRD cascade is reached too, on
--   one family at fold depths two and eight, and the ceiling holds
--   there with room -- fifteen against three hundred and forty-eight,
--   fifty-seven against one thousand five hundred and ninety.  Not
--   covered: the premises, which do not compute; any instant past the
--   third; and the count axis at the third, which is one family only.
--   The DOUBLING family is covered and is the one axis that turns out
--   not to be one: a step naming its accumulator in both additive
--   slots an inner `scanᵉ` offers -- the family that kills the entry
--   fold's width-free grant -- leaves the descent at TWO across the
--   second instant, the third, and twice the script length, while the
--   ceiling moves eighty-four to ninety-eight.  What that family grows
--   is a SUM over an instant's emitted values and a descent is a JOIN
--   over them, so it cannot reach this side.
--   Every row reads the whole ROUND rather than one chain, and the
--   round's descent is the JOIN over its chains, so a green row is a
--   green row for each chain it contains.  Every row is taken at the
--   entry store itself, which is the statement's own store slot
--   instantiated at the tightest value its hypothesis admits.
postulate
  chain-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    storeNestMax sched st ≤ S →
    depthChain nextId a path sched st
      ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)

-- AND THE BOUND SURVIVES A CHAIN, which is the other half of the same
-- design: the round states its ceiling once and spends it at every
-- later chain, so what a chain may do to the store is exactly what the
-- bound has to absorb.
--
-- AND IT IS NOT A COROLLARY OF THE GROWTH BOUND THIS TREE ALREADY HAS,
-- WHICH IS THE WHOLE OF WHY IT IS A LEAF.  The walk's own store bound
-- lands at the SUCCESSOR cap -- a factor times the cap plus an
-- increment, which is by definition the next instant's -- and the tick
-- statement above it spends exactly that to close an instant.  So the
-- discipline says a round STARTS under its own cap and ENDS under the
-- next one, and says nothing about the states between.  What this leaf
-- claims is that the growth an instant actually performs stays under
-- the instant's own cap, which is the design's intent and is not
-- anywhere derived.  Neither side of it can be instantiated: the cap
-- sits on the caps recurrence, which does not terminate even natively.
-- AND THE STORE IS FOUR PLACES UNDER ONE `⊔`, SO THIS SPLITS FOUR WAYS
-- RATHER THAN INDUCTING ONCE, which is the same split the round's
-- growth statement takes and for the same reason: the four arms are
-- nowhere near equally hard.  The slot arm needs no leaf at all -- a
-- chain threads the vocabulary untouched, so its sum is the one the
-- entry cap already covers -- and the three that survive are each a
-- statement about one thing a delivery writes.
-- THE THREE ARMS PRICE THE GROWTH AGAINST THE PROGRAM AND NOT AGAINST
-- THE STORE THEY START FROM, and that shape is forced rather than
-- chosen.  A growth priced against the entry store COMPOUNDS: each
-- chain's bound is the previous chain's, so no ceiling stated once
-- survives a walk of unknown length.  Charging the increment instead
-- makes preservation a condition on the BOUND -- it holds as soon as
-- the bound already covers one instant's increment -- which is a
-- condition the round discharges once, at its entry, rather than a
-- condition the walk has to re-establish per chain.
--
-- AND THE CHARGE IS THE SAME ONE THE FIRST SUBSCRIPTION PAYS.  The
-- floor rows for a program's own subscribe frame are stated at exactly
-- this quantity, so the three arms are that statement moved from the
-- opening frame to an arbitrary chain, and the two are refutable
-- together at any program where a chain outgrows a first subscription.
--
-- THE UNCONDITIONAL GROWTH BOUND BESIDE THEM CANNOT SUPPLY IT, AND
-- THAT IS WORTH KNOWING BEFORE ANYONE TRIES.  Two of that bound's
-- three disjuncts are places the store measure reads, so the entry
-- bound covers them outright; the third is the chain's own PATH factor
-- times the arrival's size, and the path factor is a PRODUCT over the
-- path's frames while the increment is linear in the caps at the
-- instant.  The product outruns it, and no premise the round can
-- supply changes that -- a legal path of length the size cap already
-- carries a factor exponential in that cap.

-- AND THE CHARGE MAY NOT BE DEPTH-DENOMINATED, WHICH IS WHY IT IS THE
-- INCREMENT AND NOT SOMETHING SMALLER.  The cheap repair replaces the
-- path PRODUCT by the path's additive depth, which holds at every
-- family the corpus reaches -- exactly, four against four, at the
-- transforming frame.  It fails one step further along that same
-- family: both nesting-depth measures read ZERO into a `deferᵉ` body,
-- so a `map-f` whose function is a deferred constant hands the frame a
-- value as deep as the constant while the charge does not move at all.
-- Whatever pays for these arms has to see inside a deferred body, and
-- only a SIZE measure does -- which the size cap carries and no
-- depth-built quantity does.
--
-- AND THE SIZE CAP IS THE LARGEST CHARGE THE FUEL CAN AFFORD, WHICH IS
-- WHY IT IS THAT AND NOT THE INSTANT'S INCREMENT.  A bound covering
-- one chain's growth is not the cap, so the round's ceiling reads the
-- cap PLUS the charge and each half is priced by its own copy of the
-- exponential -- and the fuel carries exactly two.  The size cap fits
-- under one with room, being a quadratic under a double exponential of
-- itself.  Everything about this is index-aligned by construction: the
-- exponential room this face runs on prices no summand at the cap
-- after the one being bounded, so a charge naming the next instant is
-- unaffordable however true it is, and reading the ceiling at the
-- SUCCESSOR cap instead is dead for the same reason.
--
-- AND THE PATH PREMISE IS NOT A CONVENIENCE.  A charge naming the
-- program alone cannot hold against a path built by hand: the path is
-- universally quantified, a frame carries its own function, and a
-- frame whose function wraps twenty times installs a node twenty deep
-- against a program that never mentions it.  So the unconditional form
-- is FALSE and the conditioned one replaces it rather than weakening
-- it.  The premise costs the consumer nothing -- the walk's own caller
-- derives it from the caps invariant it already holds, one
-- application, so it is a fact the round has rather than a fact the
-- round must acquire.
--

-- AND THIS ONE CARRIES THE CHAIN'S OWN DEPTH, which the two arms above
-- do not.  A registration this chain mints sits at the frames of the
-- subscribed value over the REMAINING path, so its depth is the
-- arrival's nesting plus the path's -- and neither of the other
-- premises reaches that quantity: the size premise is about the
-- payload's syntax and `pathSz?` bounds each frame's SIZE and the
-- path's LENGTH, which together allow a nesting quadratic in the cap.
-- The premise is the tree's own cascade-level reading taken one chain
-- at a time, so it is derived where the arm is spent rather than
-- assumed: the selection comes from the registry, and the registry's
-- join is already under the unit there.
--
-- THE BODY IS THE WALK, and the charge it spends is the unit under the
-- path's own FACTOR.  Substitution is multiplicative in this currency,
-- so a walk that survives a map frame carries the factor the frames can
-- still apply -- and the size premise is what bounds it without reading
-- the run: each frame's size is under the cap and the path's length is
-- too, so the factor is two to the cap SQUARED and no more.
-- THE PATH'S OWN DEPTH ONLY GROWS ROOTWARD, which is what lets a
-- premise taken at the chain's entry be spent at every frame the walk
-- reaches: four clauses add a term's depth or nothing, and the outer
-- frame adds one.
pathNestD-step : ∀ {n} {Γ : Ctx n} {s u t} (f : Frame Γ s u) (p : Path Γ u t) →
  pathNestD p ≤ pathNestD (f ↠ p)
pathNestD-step (map-f fn)         p = m≤n+m (pathNestD p) (nestDᵗ fn)
pathNestD-step (scan-f fn _)      p = m≤n+m (pathNestD p) (nestDᵗ fn)
pathNestD-step (take-f _)         p = ≤-refl
pathNestD-step (from-inner _ _ _) p = ≤-refl
pathNestD-step (thru-outer _ _)   p = n≤1+n (pathNestD p)

-- THE GRANT AT ONE OUTER FRAME, which was the whole of what the walk
-- still owed: the four other frame kinds owe nothing, so a path with
-- no `thru-outer` in it needs none of this.  What is owed is a SIGHTED
-- grant covering the values that reach this frame -- a ceiling on each
-- one's depth plus the store's per-slot wrap, which the delivery
-- face's fit demands and the potential does not carry.
--
-- THE GRANT IS NAMED, NOT SEARCHED FOR: the path's remaining depth,
-- plus the maximum depth in flight, plus the wrap the whole context
-- can charge.  The first two come off the premises directly and the
-- input guard is free once the context is read whole, so the only
-- content is that the charge affords it -- and it does, in three
-- pieces that each land on one summand.  The maximum in flight is
-- paid by the outer frame's OWN factor, which is two to the cap and
-- so at least two; the path's depth is under the unit twice over,
-- since the unit is under the cap; and the wrap is charged at the cap
-- while the grant spends it at the context's width, which is smaller.
-- The doubling in the charge is what lets the first piece sit beside
-- the other two rather than competing with them.
walk-thru-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (op : AllOp) (nid : NodeId)
  (p : Path Γ u t) (vals : List (Val Γ (obs u))) (sched : Sched Γ) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (thru-outer op nid ↠ p) ≡ true →
  pathNestD (thru-outer op nid ↠ p) ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
         (thru-outer op nid ↠ p) vals ≡ true →
  FrameΦHyp (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
            (thru-outer op nid) p vals sched
walk-thru-fit {n = n} {e = e} sl id op nid p vals sched hsl hpz hnd hΦ =
  n , G
  , subst (λ z → ValsFit n z G p vals) (sym hsl)
      (valsFit-of-max sl p vals M ≤-refl)
  , *-cancelˡ-≤ 2
      (≤-trans (≤-reflexive spread)
        (≤-trans (+-mono-≤ hA2 hBC2)
                 (≤-reflexive (sym (2X≡X+X (nestWalkAt e sl id))))))
  where
  S    = Caps.cSize (capsAt e sl id)
  Q    = pathΦF S p
  D    = pathNestD p
  M    = nestDᵛˢ vals
  W    = slotWrapSum sl
  X    = nestUnit e sl + S + S * W
  G    = D + M + n * W
  hpp  : pathSz? S p ≡ true
  hpp  = ∧-trueʳ hpz
  2≤S  = 2≤capsAt-size e sl id
  1≤S  = ≤-trans (s≤s z≤n) 2≤S
  Q≤   : Q ≤ 2 ^ (S * S)
  Q≤   = pathΦF-cap S p hpp
  D≤   : D ≤ nestUnit e sl
  D≤   = ≤-trans (n≤1+n D) hnd
  n≤S  : n ≤ S
  n≤S  = n≤capsAt-size e sl id
  2≤2^S : 2 ≤ 2 ^ S
  2≤2^S = ≤-trans (≤-reflexive (sym (*-identityʳ 2))) (^-monoʳ-≤ 2 1≤S)
  -- the values in flight, paid by the outer frame's own factor
  hA   : 2 ^ S * (Q * M) ≤ nestWalkAt e sl id
  hA   = ≤-trans (≤-reflexive (sym (*-assoc (2 ^ S) Q M)))
                 (Φ-to-bound S (nestWalkAt e sl id) (thru-outer op nid ↠ p)
                             vals hΦ)
  hA2  : 2 * (Q * M) ≤ nestWalkAt e sl id
  hA2  = ≤-trans (*-monoˡ-≤ (Q * M) 2≤2^S) hA
  halfShape : ∀ q d → 2 * (q * d) ≡ q * (2 * d)
  halfShape q d = solve 2 (λ q′ d′ → con 2 :* (q′ :* d′) := q′ :* (con 2 :* d′))
                        refl q d
  -- the path's own depth, and the wrap, against the charge's own half
  hBC  : 2 * (Q * D) + Q * (n * W) ≤ 2 ^ (S * S) * X
  hBC  =
    ≤-trans (+-mono-≤
              (≤-trans (≤-reflexive (halfShape Q D))
                       (*-mono-≤ Q≤ (≤-trans (*-monoʳ-≤ 2 D≤)
                                       (≤-trans (≤-reflexive (2X≡X+X (nestUnit e sl)))
                                                (+-monoʳ-≤ (nestUnit e sl)
                                                  (nestUnit≤size e sl id))))))
              (*-mono-≤ Q≤ (*-monoˡ-≤ W n≤S)))
            (≤-reflexive (sym (*-distribˡ-+ (2 ^ (S * S))
                                (nestUnit e sl + S) (S * W))))
  hBC2 : 2 * (2 * (Q * D) + Q * (n * W)) ≤ nestWalkAt e sl id
  hBC2 = subst (2 * (2 * (Q * D) + Q * (n * W)) ≤_)
               (sym (nestWalkAt-def e sl id))
               (≤-trans (*-monoʳ-≤ 2 hBC)
                        (≤-reflexive (sym (*-assoc 2 (2 ^ (S * S)) X))))
  spread : 2 * (Q * (G + D))
             ≡ 2 * (Q * M) + 2 * (2 * (Q * D) + Q * (n * W))
  spread =
    solve 4 (λ q d m w →
               con 2 :* (q :* (d :+ m :+ w :+ d))
                 := con 2 :* (q :* m)
                    :+ con 2 :* (con 2 :* (q :* d) :+ q :* w))
          refl Q D M (n * W)

-- AND THE FRAME'S SIDE-CONDITION IS A CASE SPLIT AND NOTHING ELSE,
-- which is the point of separating it from the walk below: the four
-- silent kinds are units, so the walk's recursion never mentions them.
frameΦ-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (f : Frame Γ s u) (p : Path Γ u t)
  (vals : List (Val Γ s)) (sched : Sched Γ) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (f ↠ p) ≡ true →
  pathNestD (f ↠ p) ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) (f ↠ p) vals ≡ true →
  FrameΦHyp (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
            f p vals sched
frameΦ-fit sl id (map-f _)          p vals sched _ _ _ _ = tt
frameΦ-fit sl id (scan-f _ _)       p vals sched _ _ _ _ = tt
frameΦ-fit sl id (take-f _)         p vals sched _ _ _ _ = tt
frameΦ-fit sl id (from-inner _ _ _) p vals sched _ _ _ _ = tt
frameΦ-fit sl id (thru-outer op nid) p vals sched hsl hpz hnd hΦ =
  walk-thru-fit sl id op nid p vals sched hsl hpz hnd hΦ

-- THE WALK ITSELF, and it is the fold's own recursion with the grant
-- hung off each frame.  Nothing here is arithmetic: the potential is
-- stepped by the frame law, the size receipt and the depth premise are
-- read off the path's head, and the slot equality survives a frame
-- because a frame never rewrites the schedule's slots.
-- THE REGISTRY-SIDE GRANT FOR THE POTENTIAL, and it is the same gap the
-- live arm's is: a sink hands the values to chains whose paths are in
-- the registry, and the potential is a statement about a PATH, so the
-- one the walk carries says nothing about theirs.  What makes it
-- statable is that the registry is priced by the same size cap: an
-- admitted path's factor is under the cap's exponential exactly as this
-- chain's is, and its depth is under the same unit.
postulate
  walk-share-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (j : ℕ)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
              (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
    nestUnit e sl ≤ nestUnit e sl →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
      (share-sink {t = t} i) vals ≡ true →
    DispatchΦHyp sf gas nid now (Caps.cSize (capsAt e sl id))
      (nestWalkAt e sl id) i vals fin sched st

walk-ΦHyp-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (j : ℕ)
  (path : Path Γ u t) (vals : List (Val Γ u)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  valsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) vals ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) path vals ≡ true →
  PathΦHyp sf gas nid now (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    path vals fin sched st
walk-ΦHyp-go sl id sf gas nid now j root vals fin sched st _ _ _ _ _ _ = tt
walk-ΦHyp-go sl id sf gas nid now j (share-sink i) vals fin sched st hsl _ _ hreg hnd hΦ =
  walk-share-ΦHyp sl id sf gas nid now j i vals fin sched st hsl hreg ≤-refl hΦ
walk-ΦHyp-go {e = e} sl id sf gas nid now j (f ↠ p) vals fin sched st hsl hpz hsz hreg hnd hΦ =
    hF
  , walk-ΦHyp-go sl id sf gas nid now (suc j) p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
      (trans (KeepsC.slotsEq (stepFrame-keeps sf nid now f p vals fin sched st)) hsl)
      hpz′
      (stepFrame-sz sf nid now f p vals fin sched st B j hfz hsz)
      (stepFrame-regsSz sf nid now f p vals fin sched st B j hsz
        (pathSz?-widen (f ↠ p) (iterSize-infl B 1≤B j B) hpz) hreg)
      (≤-trans (pathNestD-step f p) hnd)
      (stepFrame-nest-Φ sf nid now f p vals fin sched st
        (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) hΦ hF)
  where
  step = stepFrame sf nid now f p vals fin sched st
  hF = frameΦ-fit sl id f p vals sched hsl hpz hnd hΦ
  B  = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  hfz : frameSz? B f ≡ true
  hfz = proj₁ (∧-true (frameSz? B f)
                ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)
  hpz′ : pathSz? B p ≡ true
  hpz′ = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                 (proj₂ (∧-true (frameSz? B f)
                          ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)))

-- THE ARRIVAL'S OWN POTENTIAL, which is the entry reading BOTH the
-- walk's side-condition and the fold's own premise are spent at: one
-- value on the path, so the depth premise the arm was stated with is
-- the whole of it once the path's factor is applied.
entryΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (path : Path Γ (arrTy a) t) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) path
         (arrVal a ∷ []) ≡ true
entryΦ {e = e} sl id a path hp hΦ = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ Φfit)) refl
  where
  Sz = Caps.cSize (capsAt e sl id)
  Φfit : pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathNestD path)
           ≤ nestWalkAt e sl id
  Φfit = subst (pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathNestD path) ≤_)
               (sym (nestWalkAt-def e sl id))
               (*-mono-≤ (≤-trans (pathΦF-cap Sz path hp)
                                  (^-monoʳ-≤ 2 (n≤1+n (Sz * Sz))))
                         (≤-trans (≤-trans hΦ (m≤m+n (nestUnit e sl) Sz))
                                  (m≤m+n (nestUnit e sl + Sz)
                                         (Sz * slotWrapSum sl))))

-- AND THE CHAIN ENTERS THE WALK WITH IT, the path's remaining depth
-- being under the same unit the arrival's is read against.
chain-walk-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (gas : ℕ) (j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  PathΦHyp (budgetAt e (Sched.slots sched) nextId) gas nextId (arrTick a)
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    path (arrVal a ∷ []) (Arrival.isLast a) sched st
chain-walk-ΦHyp {e = e} sl id a nextId gas j path sched st hsl hsz hp hreg hΦ =
  walk-ΦHyp-go sl id _ gas nextId (arrTick a) j path (arrVal a ∷ [])
    (Arrival.isLast a) sched st hsl hp
    (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans hsz (iterSize-infl B 1≤B j B)))) refl) hreg
    (≤-trans (m≤n+m (pathNestD path) (nestDᵛ (arrTy a) (arrVal a))) hΦ)
    (entryΦ sl id a path hp hΦ)
  where
  B   = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)

chainStep-nest-regsC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  regsNestMax (EvalSt.registry (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≤ regsNestMax (EvalSt.registry st)
      ⊔ (nestWalkAt e sl id)
chainStep-nest-regsC {e = e} sl id a nextId j path sched st hsl hsz hp hreg hΦ =
  foldPath-nest-regs _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id a nextId _ j path sched st hsl hsz hp hreg hΦ)

-- THE NODES ARM IS THE SAME WALK AT THE OTHER PLACE A FRAME STORES,
-- and it is the same three inputs: the entry potential, the walk's
-- per-frame side-condition, and the fold.  What it adds to the
-- registry arm's conclusion is the registry's own join, because a
-- chain that reaches a share fans into paths this one does not walk
-- and stores at their nodes -- the term the path-denominated reading
-- was refuted for missing.  The consumer pays nothing for it: the
-- round already holds the registry under the same ceiling.
--
-- AND IT TAKES THE DEPTH PREMISE THE REGISTRY ARM TAKES.  That is not
-- a convenience of the one call site -- without it the walk has no
-- entry potential, so there is no induction to run at all, and the
-- monolithic form it replaces was asserting the whole walk rather
-- than owing this.
chainStep-nest-nodesC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
        (EvalSt.nodes (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
        ⊔ regsNestMax (EvalSt.registry st)
        ⊔ (nestWalkAt e sl id)
chainStep-nest-nodesC {e = e} sl id a nextId j path sched st hsl hsz hp hreg hΦ =
  foldPath-nest-nodes _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id a nextId _ j path sched st hsl hsz hp hreg hΦ)

-- THE SIZE-SIDE SIDE CONDITION, DISCHARGED.  The walk reads the bound
-- at the level it has reached and each frame moves the level by one,
-- so what the caller owes is the entry reading -- which is the size
-- premise it already carries -- and affordability at every level the
-- path can reach.
--
-- AND AFFORDABILITY IS THE CALLER'S, BECAUSE THE LEVEL A CHAIN ENTERS
-- AT IS THE CALLER'S.  `iterSize≤walkFac` discharges it outright for a
-- chain entered at level zero, which is why this used to carry no such
-- premise; a cascade enters its k-th chain at whatever the first k-1
-- left, so the range that has to be afforded is a property of the
-- SELECTION and cannot be recovered from anything in hand here.
chain-walk-LiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (gas : ℕ) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  (∀ k → k ≤ Lv →
     iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
       ≤ nestWalkAt e sl id) →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  j + pathLen path ≤ Lv →
  PathLiveHyp (budgetAt e (Sched.slots sched) nextId) gas nextId (arrTick a)
    (nestWalkAt e sl id) path (arrVal a ∷ []) (Arrival.isLast a) sched st
chain-walk-LiveHyp {e = e} sl id a nextId gas Lv j path sched st hsl afford hsz hp hreg hj =
  walk-LiveHyp-go _ gas nextId (arrTick a) S (nestWalkAt e sl id) Lv j path
    (arrVal a ∷ []) (Arrival.isLast a) sched st afford 1≤S entrySz hp hreg hj
  where
  S = Caps.cSize (capsAt e sl id)
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  entrySz : valsSz? (iterSize S j S) (arrVal a ∷ []) ≡ true
  entrySz = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
              (≤-trans hsz (iterSize-infl S 1≤S j S)))) refl

-- THE LIVE ARM, the third and last of the chain's arms to become the
-- walk rather than an assertion about it.  Two extra terms over the
-- registry arm's conclusion: the slots, because a scripted slot's
-- subscribe mints out of script data, and the registry's join, because
-- a share fans into chains that mint out of their own.  The round
-- holds all three under the same ceiling, so the consumer pays for
-- neither.
chainStep-nest-liveC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  (∀ k → k ≤ Lv →
     iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
       ≤ nestWalkAt e sl id) →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  j + pathLen path ≤ Lv →
  foldr (λ l acc → liveNest l ⊔ acc) 0
        (Sched.live (proj₁ (proj₂ (chainStep nextId a path sched st))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched)
        ⊔ regsNestMax (EvalSt.registry st)
        ⊔ (nestWalkAt e sl id)
chainStep-nest-liveC {e = e} sl id a nextId Lv j path sched st hsl afford hsz hp hreg hΦ hj =
  foldPath-nest-live _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id a nextId _ j path sched st hsl hsz hp hreg hΦ)
    (chain-walk-LiveHyp sl id a nextId _ Lv j path sched st hsl afford hsz hp hreg hj)

-- AND THE UNIT IS UNDER EVERY CAP, being the cap at instant zero and
-- the recurrence nondecreasing after it.
unit≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestUnit e sl ≤ nestCapAt e sl id
unit≤cap e sl id =
  ≤-trans (≤-reflexive (sym (nestCapAt-0 e sl))) (nestCap-mono₀ e sl id)

-- AND THAT IS WHAT A WALK CAN CARRY.  A bound the chains preserve has
-- to be one the growth cannot climb past however many chains run, and
-- a growth priced against the ENTRY store is not one -- it compounds.
-- These three price it against the program instead, so the walk's
-- bound survives a chain exactly when it already covers one instant's
-- increment, which is a condition on the bound and not on the walk.
-- REFUTED: Refuted.Chain-Step-Nodes
-- REFUTED: Refuted.Chain-Step-Live-Additive
-- DEAD ROUTE: spending the unconditional live-growth bound and
--   discharging its three disjuncts against the entry cap.  Two go;
--   the third is the path factor above, and it is not repairable by a
--   premise, only by a tighter growth statement.
-- DEAD ROUTE: restating the whole walk one instant up, so the arms
--   preserve the successor cap and the round's ceiling is read there.
--   The entry lifts and the arms carry over, but the consumer does
--   not: its fuel is the exponential at THIS instant, which the caps
--   recurrence pins to this instant's cap.
-- DEAD ROUTE: charging the arms the instant's INCREMENT, which is what
--   they carried while they mirrored the entry burst.  The increment's
--   own exponent reads the delivery at the NEXT instant, and the size
--   there is already a blowup story above the fuel available here, so
--   no reading of it fits under this instant's exponential.
chainStep-store≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  (∀ k → k ≤ Lv →
     iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
       ≤ nestWalkAt e sl id) →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  j + pathLen path ≤ Lv →
  nestWalkAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  storeNestMax (proj₁ (proj₂ (chainStep nextId a path sched st)))
               (proj₂ (proj₂ (chainStep nextId a path sched st))) ≤ S
chainStep-store≤ {e = e} sl id a nextId S Lv j path sched st hsl afford hsz hp hreg hΦ hj hinc hS =
  storeNestMax-lub sd′ st′ S SL
    (≤-trans (chainStep-nest-liveC  sl id a nextId Lv j path sched st hsl afford hsz hp hreg hΦ hj)
             (⊔-lub (⊔-lub (⊔-lub (≤-trans (storeNest-live≤  sched st) hS)
                                  (≤-trans (storeNest-slots≤ sched st) hS))
                           (≤-trans (storeNest-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-nodesC sl id a nextId j path sched st hsl hsz hp hreg hΦ)
             (⊔-lub (⊔-lub (≤-trans (storeNest-nodes≤ sched st) hS)
                           (≤-trans (storeNest-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-regsC  sl id a nextId j path sched st hsl hsz hp hreg hΦ)
             (⊔-lub (≤-trans (storeNest-regs≤  sched st) hS) hinc))
  where
  sd′ = proj₁ (proj₂ (chainStep nextId a path sched st))
  st′ = proj₂ (proj₂ (chainStep nextId a path sched st))
  flat = unit+size≤nestWalkAt e sl id
  SL : slotsNestSum (Sched.slots sd′) ≤ S
  SL = ≤-trans (≤-reflexive (cong slotsNestSum
                              (chainStep-slots nextId a path sched st)))
               (≤-trans (storeNest-slots≤ sched st) hS)

-- THE ROUND IS A WALK OVER ITS CHAINS, and the three-callee clause is
-- the one `depthCascade` reports: the tail at the incoming state, the
-- live chain at the delivered-marked one, and the tail again at the
-- state that chain left.
-- ONE CHAIN'S DEPTH OUT OF THE SELECTION'S JOIN.  The cascade-level
-- reading is a ⊔-fold over the whole selection, and the walk spends it
-- one chain at a time, so the fold has to be taken apart before the
-- first `chainStep` sees it.
chainsNest-all : ∀ {n} {Γ : Ctx n} {s t} (D U : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  D + chainsNestD cs ≤ U →
  all (λ rc → D + pathNestD (proj₂ rc) ≤ᵇ U) cs ≡ true
chainsNest-all D U []       h = refl
chainsNest-all D U (c ∷ cs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (+-monoʳ-≤ D
                       (m≤m⊔n (pathNestD (proj₂ c)) (chainsNestD cs))) h)))
          (chainsNest-all D U cs
            (≤-trans (+-monoʳ-≤ D (m≤n⊔m (pathNestD (proj₂ c))
                                          (chainsNestD cs))) h))

-- THE REGISTRY ACROSS A WHOLE CHAIN, AT ONE LEVEL PER CHAIN.  The
-- walked path is priced at the program's cap and the registry at the
-- level, which is the reading the rest of this spine's walk already
-- uses; what this adds is that one chain moves the level by exactly
-- one, a DETERMINED count and not a witness chosen after the fact.
--
-- AND ONE LEVEL IS WHAT A CHAIN COSTS BECAUSE OF WHAT A SUBSCRIBE
-- REGISTERS.  `chainStep` is `foldPath`, and a subscribing frame does
-- not register the path it was walking: it swaps its head for a
-- `from-inner` and pushes one frame per operator of the inner, so the
-- registered chain outruns the walked one by the inner's own count --
-- which the arrival's size premise caps, `sizeᵛ` at an observable
-- being `sizeᵉ`.  So the growth is `+ S` on the length and `S` on the
-- new frames, and `sizeStep S L` is `S·(1+2L)`, which dominates both.
--
-- SO THE LEVEL ACCUMULATES DOWN THE SELECTION RATHER THAN COLLAPSING
-- AT THIS DOOR.  The consumer spends this once per chain, feeding each
-- output registry in as the next chain's premise, and what must bound
-- the run is `nestWalkAt` -- the way `iterSize≤walkFac` already makes a
-- bounded run of levels affordable against the walk factor, which is
-- why the store side now carries a `j + pathLen` premise beside it.
--
-- REFUTED: `Refuted.Chain-Step-Regs-Cap` -- the fixed-cap form this
--   replaces, at a five-node inner and a six-frame chain against a cap
--   of six.  Both premises hold and the registered chain has length
--   eight, so what broke was the length ledger rather than any size
--   reading, and no further hypothesis repairs it.
postulate
  chainStep-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (S j : ℕ) (a : Arrival Γ) (nextId : Id)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
    1 ≤ S →
    sizeᵛ (arrTy a) (arrVal a) ≤ S →
    pathSz? S path ≡ true →
    regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
    regsSz? (iterSize S (suc j) S)
      (EvalSt.registry (proj₂ (proj₂ (chainStep nextId a path sched st))))
      ≡ true

-- AND THE SELECTION'S LEVEL BUDGET IS ONE NUMBER, PEELED THREE WAYS
-- PER CHAIN.  The head chain walks at the level reached so far, so it
-- owes its own frames; the tail is re-entered twice, once at that same
-- level and once one above it, and both times with one fewer chain in
-- hand.  `chainsLenSum + length` is what makes those three fit under
-- one premise: the sum pays the frames and the count pays the levels.
--
-- AND THE BUDGET IS NOT THE SIZE CAP, WHICH IS THE WHOLE FINDING HERE.
-- A cap admits chains of a cap's length and a selection as wide as the
-- registry, so its own `chainsLenSum` already outruns it -- there is no
-- arrangement of the arithmetic under which a cascade's levels fit
-- under the number one chain's frames fit under.  So the budget rides
-- as a parameter with the affordability that pays for it, and the
-- caller carries a ledger it can actually meet.
cascade-depth-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  (∀ k → k ≤ Lv →
     iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
       ≤ nestWalkAt e sl id) →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) chains ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  j + chainsLenSum chains + length chains ≤ Lv →
  nestWalkAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  depthCascade a nextId chains sched st
    ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
cascade-depth-go sl id a nextId S Lv j [] sched st hsl afford hsz hps hΦs hreg hbud hinc hS = z≤n
cascade-depth-go {e = e} sl id a nextId S Lv j ((rid , c) ∷ cs) sched st
  hsl afford hsz hps hΦs hreg hbud hinc hS =
  ⊔-lub (cascade-depth-go sl id a nextId S Lv j cs sched st
           hsl afford hsz hpr hΦr hreg hbud-tail hinc hS)
        (⊔-lub (chain-depth-sighted sl a nextId S c sched st₀ hsl hS)
               (cascade-depth-go sl id a nextId S Lv (suc j) cs
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  (trans (chainStep-slots nextId a c sched st₀) hsl)
                  afford hsz hpr hΦr
                  (chainStep-regsSz B j a nextId c sched st₀ 1≤B hsz hpc hreg)
                  hbud-next
                  hinc
                  (chainStep-store≤ sl id a nextId S Lv j c sched st₀ hsl afford hsz hpc hreg
                     (≤ᵇ⇒≤ (nestDᵛ (arrTy a) (arrVal a) + pathNestD c)
                           (nestUnit e sl) (T-to hΦc))
                     hbud-head hinc hS)))
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  r   = chainStep nextId a c sched st₀
  B   = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  hpc = proj₁ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hpr = proj₂ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hΦc = proj₁ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hΦr = proj₂ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hbud-head : j + pathLen c ≤ Lv
  hbud-head =
    ≤-trans (≤-trans (+-monoʳ-≤ j (m≤m+n (pathLen c) (chainsLenSum cs)))
                     (m≤m+n (j + (pathLen c + chainsLenSum cs)) (suc (length cs))))
            hbud
  hbud-tail : j + chainsLenSum cs + length cs ≤ Lv
  hbud-tail =
    ≤-trans (+-mono-≤ (+-monoʳ-≤ j (m≤n+m (chainsLenSum cs) (pathLen c)))
                      (n≤1+n (length cs)))
            hbud
  hbud-next : suc j + chainsLenSum cs + length cs ≤ Lv
  hbud-next =
    ≤-trans (s≤s (+-monoˡ-≤ (length cs)
                    (+-monoʳ-≤ j (m≤n+m (chainsLenSum cs) (pathLen c)))))
            (≤-trans (≤-reflexive
                       (sym (+-suc (j + (pathLen c + chainsLenSum cs)) (length cs))))
                     hbud)

-- the cascade's opening ledger write is not a registry write, on
-- either branch of the spent-source test
latch-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (st : EvalSt e) →
  regsSz? B (EvalSt.registry st) ≡ true →
  regsSz? B (EvalSt.registry (cascadeLatch a st)) ≡ true
latch-regsSz B a st h with Arrival.isLast a
... | true  = h
... | false = h

-- EVERY LEVEL A WHOLE CASCADE REACHES IS AFFORDABLE, and this is the
-- one place the level ledger has to meet the walk's ceiling.  The
-- selection enters its k-th chain at the level the first k-1 left and
-- climbs one per frame inside it, so the levels it reaches run to the
-- chains' total length plus their count -- and that ledger is what
-- `cascade-depth-go` now carries, precisely so this obligation can be
-- stated once for the whole selection rather than re-derived per chain.
--
-- AND IT IS NOT THE ONE-CHAIN FACT WIDENED.  `iterSize≤walkFac` pays
-- for `k ≤ S`, which is exactly a chain's own frames, and the ceiling
-- it lands under carries one exponential of the cap SQUARED.  The count
-- here is a WIDTH times a cap, since the registry admits a selection as
-- wide as itself and each chain is legal at a cap's length -- so the
-- power that has to fit is a cap CUBED, and at the smallest admitted
-- caps that is above the exponential currently on offer.  The expected
-- repair is therefore in `nestWalkAt`, whose own consumer bounds it by
-- a tower two exponentials up and so has the room; what is NOT expected
-- to work is any rearrangement that keeps the ceiling where it is.
--
-- DEAD ROUTE: keying the cascade's budget to the size cap, so that the
--   existing one-chain affordability discharges it unchanged.  The cap
--   admits chains of a cap's length and the registry admits a selection
--   as wide as itself, so the selection's own `chainsLenSum` already
--   outruns the cap -- the premise is unsatisfiable at the caller
--   rather than merely hard to prove there.
postulate
  cascade-afford-wide : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (st : EvalSt e) (k : ℕ) →
    Caps.cSize (capsAt e sl id) ≤ k →
    k ≤ chainsLenSum (chainsOf a st) + length (chainsOf a st) →
    iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
      ≤ nestWalkAt e sl id

-- AND THE SPLIT IS AT THE CAP, so the half the existing arithmetic
-- already pays for stays paid.  Below the cap this IS the one-chain
-- fact, spent unchanged; above it nothing in hand applies, and that
-- half alone is what the leaf above carries -- which is the risky
-- region named rather than the whole range assumed.
cascade-afford : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (st : EvalSt e) (k : ℕ) →
  k ≤ chainsLenSum (chainsOf a st) + length (chainsOf a st) →
  iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
    ≤ nestWalkAt e sl id
cascade-afford {e = e} sl id a st k hk
  with ≤-total k (Caps.cSize (capsAt e sl id))
... | inj₁ k≤S =
  ≤-trans (iterSize≤walkFac (Caps.cSize (capsAt e sl id)) k
             (Caps.cSize (capsAt e sl id)) (8≤capsAt-size e sl id) k≤S ≤-refl)
          (walkFac≤nestWalkAt e sl id)
... | inj₂ S≤k = cascade-afford-wide sl id a st k S≤k hk

cascade-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a))
                (nestCapAt e sl id + (nestWalkAt e sl id))
                (nestUnit e sl)
cascade-depth-sighted {e = e} sl id a nextId sched st hsl hok hn hsz =
  cascade-depth-go sl id a nextId (nestCapAt e sl id + (nestWalkAt e sl id))
    (chainsLenSum (chainsOf a st) + length (chainsOf a st)) 0
    (chainsOf a st) sched (cascadeLatch a st) hsl
    (cascade-afford sl id a st) hsz
    (chainsOf-caps (Caps.cSize (capsAt e sl id)) a st
      (capsOK?-regs (capsAt e sl id) sched st hok))
    (chainsNest-all (nestDᵛ (arrTy a) (arrVal a)) (nestUnit e sl) (chainsOf a st)
      (arr-chains-nest-syn sl id a sched st hsl hok hn))
    (latch-regsSz (Caps.cSize (capsAt e sl id)) a st
      (capsOK?-regs (capsAt e sl id) sched st hok))
    ≤-refl
    (m≤n+m (nestWalkAt e sl id)
           (nestCapAt e sl id))
    (≤-trans (nestOK?-store e sl id sched (cascadeLatch a st)
               (trans (nestOK?-latch e sl id a sched st) hn))
             (m≤m+n (nestCapAt e sl id) (nestWalkAt e sl id)))

-- AND ALL THREE OF THE CEILING'S SUMMANDS ARE THE SAME CAP.  The
-- arrival's nesting is held under it by the caller's premise, the
-- store's by the nesting invariant, and the wrap unit IS the cap at
-- instant zero -- so the sighted sum is three readings of one number
-- and the ceiling collapses to a multiple of it.  That collapse is the
-- whole of what the run-side hypotheses buy.
sight-collapse : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (a : Arrival Γ) (B S : ℕ) →
  S ≤ B →
  nestDᵛ (arrTy a) (arrVal a) ≤ B →
  nestUnit e sl ≤ B →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ suc (sizeᵉ e) * suc (3 * B)
sight-collapse {e = e} sl a B S hS hval hu =
  *-monoʳ-≤ (suc (sizeᵉ e)) (s≤s sum≤3B)
  where
  eq : B + B + B ≡ 3 * B
  eq = solve 1 (λ b → b :+ b :+ b := con 3 :* b) refl B
  sum≤3B : nestDᵛ (arrTy a) (arrVal a) + S + nestUnit e sl ≤ 3 * B
  sum≤3B =
    ≤-trans (+-mono-≤ (+-mono-≤ hval hS) hu) (≤-reflexive eq)


-- AND THE FUEL HAS THAT ROOM, so the comparison the depth face owes
-- the height is assembled rather than asserted.  The caps recurrence
-- steps by a blowup the fuel itself drives and `blowH` is what the
-- fuel climbs by, so the size at an instant and the fuel at that
-- instant are one quantity read once each -- with two exponentials
-- between them, bought by the single spare registration the tower
-- bracket leaves in the pooled walk.
sighted-nest≤capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (B S : ℕ) →
  S ≤ B →
  nestDᵛ (arrTy a) (arrVal a) ≤ B →
  nestUnit e sl ≤ B →
  suc (sizeᵉ e) * suc (3 * B) ≤ capsH e sl id →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ capsH e sl id
sighted-nest≤capsH {e = e} sl id a B S hS hval hu room =
  ≤-trans (sight-collapse {e = e} sl a B S hS hval hu) room

-- THE ROUND'S DEPTH FITS THE INSTANT'S FUEL, assembled rather than
-- asserted: the descent goes under what the round can see, and what
-- the round can see goes under the fuel.  The split is the point -- the
-- first half is a statement about the evaluator at concrete programs
-- and the second is arithmetic about two currencies, and only the
-- second is where the height comparison lives.
--
-- THE SIZE PREMISE IS CARRIED AND NOT SPENT.  It is the caller's, and
-- it belongs to the statement rather than to this route: a descent
-- bounded through the payload's NESTING says nothing about the
-- payload's size, and the consumers that hand this premise in are
-- pricing the same arrival on the size axis in the same breath.
cascade-depth-capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ capsH e sl id
cascade-depth-capsH {e = e} sl id a nextId sched st hsl hcaps hnest hval hsz =
  ≤-trans (cascade-depth-sighted sl id a nextId sched st hsl hcaps hnest hsz)
          (sighted-nest≤capsH sl id a B B ≤-refl
             (≤-trans hval (m≤m+n (nestCapAt e sl id) (nestWalkAt e sl id)))
             (≤-trans (unit≤cap e sl id)
               (m≤m+n (nestCapAt e sl id) (nestWalkAt e sl id)))
             (nestCap-inc-sight≤capsH e sl id))
  where
  B = nestCapAt e sl id + (nestWalkAt e sl id)

caps-tick :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
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
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
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
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  let r = cascade a nextId sched st
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
caps-tick siC ifc {e = e} sl id a nextId sched st slEq pre nok bnd val =
  cascadeFinish-caps (capsAt e sl (suc id)) a (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
    (capsOK?-mono (frameStep j c) (capsAt e sl (suc id))
                  (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
                  (frameStep-mono-j c (2≤capsAt-size e sl id) jFits)
                  (proj₂ (proj₂ GO)))
  where
  c    = capsAt e sl id
  st₀  = cascadeLatch a st
  GO   = cascadeGo-caps siC ifc c (capsH e sl id) a nextId (chainsOf a st) sl sched st₀
           (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)
           (slotsCaps?-capsAt e sl id) slEq
           (cascadeLatch-caps c a sched st pre) val
           (chainsOf-caps (Caps.cSize c) a st (capsOK?-regs c sched st pre))
           (n≤capsAt-size e sl id)
           (≤-trans (chainsOf-length a st) (capsOK?-count c sched st pre))
           -- H1 is FREE here: capsAt's base formula already contains the
           -- slot store as a summand
           (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e))
                    (capsAt-base-size e sl id))
           (cascade-depth-capsH sl id a nextId sched st slEq pre nok bnd
             (≤ᵇ⇒≤ (sizeᵛ (arrTy a) (arrVal a)) (Caps.cSize c)
                   (T-to (valCaps?-size c sl (arrTy a) (arrVal a) val))))
  GOr   = cascadeGo a nextId (chainsOf a st) sched st₀
  j     = proj₁ GO
  jFits = proj₁ (proj₂ GO)

-- REFUTED: `caps-frame-boundary-absurd`
--   (sizeStep C C ≤ C is impossible for 1 ≤ C) and `reach-via-size-absurd`
--   (2 ^ C ≤ C is impossible) now live in `refuted/Refuted/Caps-Face.agda`,
--   checked by `make refuted`.  Do not re-attempt either bound here.


-- (`reach-resets`, the reset cluster this section's prose names, is
-- declared ABOVE the face postulate block — `thruOuter-face` consumes
-- it and is itself consumed before this point in the file.)

------------------------------------------------------------------
-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.

