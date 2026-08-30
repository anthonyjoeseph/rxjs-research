-- Verify-Budget-Sufficient.Caps-Face.Part7
-- thruOuter-face … reach-via-size-absurd
module Verify-Budget-Sufficient.Caps-Face.Part7 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (m+[n∸m]≡n; <⇒≤; *-assoc; *-identityˡ; ^-distribˡ-+-*; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤; ≤-trans;
  ≤-refl; ≤-reflexive; +-identityʳ; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; *-mono-≤; *-monoʳ-≤;
  +-monoʳ-≤; +-monoˡ-≤; +-assoc; ⊔-lub; m≤m⊔n; m≤n⊔m; +-mono-≤; ⊔-mono-≤; ⊔-identityʳ; m⊔n≤m+n;
  *-distribˡ-+; *-distribʳ-+; m≤m*n; ^-*-assoc; *-comm; +-suc; +-comm; ≤-pred)
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
open import Data.Maybe   using (nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted;
  InstEvent)
open import Rx.Exp       using (_×ᵗ_; obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵛ; Fn; applyFn;
                                syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; ent-step; reached-room; base; walk)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-def; nestFac-monoS; 1≤nestFac; nestU; nestU-def; nestU-mono; nestU-room)
open import Verify-Budget-Sufficient.Subscribe-Face using (subscribeInner-caps; innerFinish-caps; stepFrame-caps)
open import Verify-Budget-Sufficient.Nest-Walk using
  (foldPath-nodes; nodesMax; burstsOK; capsWalkOK; dispatchCapsOK; frameClosOK; frameDrainOK;
  fac-hoist; one-pow; FaceOK; faceAt; nestClosOK?; shareCapsOK)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade; depthChain; depthFold; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (pathSzSum-cap; deliverLen; deliverNestD; deliverNestF; 1≤deliverNestF; chainsLenSum;
  chainsDelLen; chainsDelNestD; chainsDelNestF; 1≤chainsDelNestF; chainsDelSzSum;
  chainsDelNestF≡; chainsDelLen-chains; chainsDelNestD-chains; chainsDelSzSum-chains;
  chainsNestF≤; nestDᵉ≤sizeᵉ; shareAdmit-len; shareAdmit-sz)
open import Verify-Budget-Sufficient.Fan-Caps using
  (fanLen; fanSq; delSize; delSq; delSq-monoᶜ; delSize-cap; delSq-cap; delSize-def; delSq-def;
  delSize-exp)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; chainsNestF; chainsSzSum; pathNestF; 1≤pathNestF; 1≤chainsNestF; nest-telescope;
  nest-scale; pow-distrib-*; storeNestMax; nestCapAt; nestOK?; nestFacAt; nestFacAt-def;
  1≤nestFacAt; nest-inflate; realWidAt; realWidAt-def; nestIncAt; nestIncAt-def;
  size≤nestIncAt; m≤m^burst; nestBurstAt; 1≤nestBurstAt; nestUnit; slotsNestSum; liveNest;
  nodeNest; regsNestMax; sightCeil; nestCapAt-0; nestCap-mono₀; nestOK?-store; slotNest; nestBurstAt-def; nestCapAt-suc)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; scanVals; RegId; Chain; scan-st; take-st; mergeAll-st;
  switch-st; exhaust-st; setNode; lookupNode; takeVals; NodeId; _↠_; Frame; AllOp; map-f; scan-f; take-f;
  from-inner; thru-outer; cascadeLatch; cascadeFinish; takeDispatch; arrSource; chainsOf;
  chainsGo; cascadeGo; Path; arrTy; stepFrame; subscribeInner; mergeAllᵒ; switchᵒ; exhaustᵒ;
  thruWalk; thruWrap; innerFinish; innerReact; aliveThroughᶠ; cascade; sameSource; regAt;
  share-sink; root;
  dCapᶜ; fLvlD; lvls; iterL; sLvlD; chainStep; budgetAt; arrTick; shareAdmit; shareLatch;
  dispatchShare; foldPath)
open import Rx.Slots using (Slot; Slots; scripted; shared; slotSize; slotsSize)

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
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; 8≤capsAt-size; B2-cReg≤cSize; Caps; capsAt; capsAt-base-size;
  capsAt-size-mono; capsAt-wid<size; capsAt-suc-full;
  capsAt-⊑-suc; capsAt-exp≤capsH; capsH; cDel; _⊑ᶜ_; cDel-body; dCapᶜ-mono; dWalkᶜ-mono; frameStep; frameStep-0;
  frameStep-mono-j; frameStep-reg-mono; iterL-infl; iterL-mono; iterSize-mono-count; J+n≤iterL; lvls-add;
  lvls-infl; lvls-mono; capsAt-exp-gain; size≤sizeCount; sizeCount; sizeCount-body;
  frameBlowup; iterSize-pow; size-lower)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; reach-reset; ∧-true; n<2^n; sq≤2^; sum-tab-mono; 2X≡X+X; 1≤pow;
   syncSize≤sizeᵉ)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over (see below, ~6307).  The rest of the family
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
  (capsAt-gas-size; capsOK?; capsOK?-mono; eventCaps?; frameSz?; n≤capsAt-size; pathSz?; powʳ1; sq≤pow;
  pathSz?-widen; regsSz?; slotsCaps?; valCaps?; widNode)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (face-charge; face-charge1; face-vals; mapFrame-caps; scanFrame-caps;
   scanVals-len; stepFrame-face-zero; takeDispatch-len; valsCaps?-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (foldPath-slots; capsOK?-count; capsOK?-delivered; capsOK?-nodeSz; capsOK?-nodeWid;
   capsOK?-regs; capsOK?-setNode; dropSweep-caps; face-lift; frameBud;
   FrameFace; lookupNode-caps; pathSz?-len; pathSz?-tail; shareLatch-caps;
   slotsCaps?-capsAt; takeDispatch-caps; valsCaps?; valsCaps?-lvl; walkOK;
   walkOK-finish; cutThrough-regsSz)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (frameStep-⊑-+; valCaps?-size; valCaps?-wid; valCaps?-widen)
open import Decide using (T-to; T⇒≡true; ∧-intro; ∧-trueˡ; ∧-trueʳ)

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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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
  pathSz? (Caps.cSize c) path ≡ true →
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
  all (λ rc → pathSz? (Caps.cSize cp) (proj₂ rc)) chains ≡ true →
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
         hburst hcw hdep hpz z≤n
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

-- AND THE LAST TWO CONJUNCTS ARE THE REGISTRY'S PRICING AT THE BASE
-- CAP, carried unstepped where everything above them steps.  The sink
-- opens by pricing the admitted list at the base cap -- its paths under
-- `cSize` and its length under `cReg` -- while every other hypothesis
-- here reads at `frameStep L`, the cap L frames of climbing have
-- already stepped to.  The stepped cap is the larger one at both
-- fields and both predicates are upward-closed in the bound, so the
-- receipt beside them is the weaker statement: a sink at the end of a
-- non-empty path is exactly where the two come apart, and at `L` zero
-- they coincide, which is why the flatness read as harmless.
--
-- SO THE PRICING IS CARRIED RATHER THAN DERIVED, and it is carried
-- here because it is not a fact about the level at all.  A registered
-- path is program syntax and the base cap already dominates the
-- program's size and its slots, so what the sink was missing is a fact
-- about the REGISTRY that no state receipt at any level supplies.
-- Every registry mutation but one is a filter, which preserves any
-- `all`-shaped pricing outright; the one that is not owes that an
-- installed path is base-priced, and that is the whole preservation
-- obligation the walk now carries.
--
-- DEAD ROUTE: reading the two off the `capsOK?` beside them.  That
--   predicate does carry both, at the size and at the register count,
--   but only at the level's cap, and the bound runs the wrong way.
--   Stepping the sink's own conjuncts to match its siblings does not
--   repair it either: the nodes face consumes them FLAT, and the same
--   flat path receipt is what its fold and its unit lemma both spend,
--   so that restatement cascades into the whole face rather than
--   stopping at the sink.
WalkHyps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
WalkHyps {e = e} sl id L sf gas nid now src p vals evs fin sched st =
  (Sched.slots sched ≡ sl)
  × (capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true)
  × (valsCaps? (frameStep L (capsAt e sl id)) sl vals ≡ true)
  × (pathSz? (Caps.cSize (frameStep L (capsAt e sl id))) p ≡ true)
  × (depthFold sf gas nid now src p vals evs fin sched st ≤ capsH e sl id)
  × (Σ ℕ λ g → Σ ℕ λ P →
      (4 + (sizeᵉ e + slotsSize sl) ≤ g)
      × (iterL (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id)
               (pathLen p) L
           ≤ P)
      × Reached (capsAt e sl id) (capsH e sl id) P g)
  × (regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true)
  × (pathSz? (Caps.cSize (capsAt e sl id)) p ≡ true)

-- THE ONE VALUE THE FRAME-LOCAL LEAF IS ACTUALLY ABOUT: an inner
-- observable a `thru-outer` is handed, measured through the slot
-- telescope rather than as syntax.  `valCaps?` charges the value's own
-- size and nothing the slots it names expand to, and the two readings
-- come apart at the first shared definition, so this is a strictly
-- stronger statement about the same value and not a repackaging of the
-- receipt beside it.
--
-- AND THE FLAT SLOT MEASURE CANNOT PAY FOR IT EITHER, which is the
-- finding recorded at `nestClosOK?`'s own definition and the reason the
-- state receipt is carried here rather than the sum: the closure
-- reading is multiplicative in the telescope's depth where the sum is
-- flat, so what has to dominate is `capsAt`'s own size -- an `iterSize`
-- at a count of the caps counting family -- and that family is the one
-- the harness quarantines as unreachable by measurement.  So this leaf
-- is symbolic-or-nothing on the conclusion side, and the arithmetic
-- already in the tree that could reach it is `exp-iterSize`, which puts
-- a power of two under that size.
--
-- REFUTED: `Refuted.Thru-Fit-Frame-Slot` -- the frame head WITHOUT a
--   resolved-size premise, at a telescope each of whose layers doubles
--   its predecessor: every term of the grant is pinned at its floor by
--   an arrival that merely NAMES the slot, so the deficit diverges
--   rather than crossing.  That is the argument for this leaf existing
--   at all, and its `parent-premise-absurd` is the other half -- the
--   cap those rows are read at does not admit the telescope, so what
--   they kill is the premise-free form and not this one.
-- REFUTED: `Refuted.Nest-Clos-Flat` -- the same reading stated over an
--   ARBITRARY cap rather than `capsAt`'s.  The witness cap is the
--   value's own `sizeᵉ`, so the premise holds by construction at every
--   size the family reaches and raising the cap raises the admitted
--   value with it; three references to one slot read `4 6 8` of syntax
--   against `10 18 26` of closure.  What that closes is the cheap
--   route: no proof of this leaf can go through `valCaps?` alone, so
--   the specific size of `capsAt` is the only thing left to pay.
postulate
  nest-clos-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (L : ℕ) (sched : Sched Γ) (st : EvalSt e)
    (o : Val Γ (obs u)) →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
    valCaps? (frameStep L (capsAt e sl id)) sl (obs u) o ≡ true →
    nestClosOK? (frameStep L (capsAt e sl id)) sl o ≡ true

-- the leaf over a whole delivered list, which is the shape the frame
-- head reads it at
nest-clos-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sched : Sched Γ) (st : EvalSt e)
  (vs : List (Val Γ (obs u))) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
  all (valCaps? (frameStep L (capsAt e sl id)) sl (obs u)) vs ≡ true →
  all (nestClosOK? (frameStep L (capsAt e sl id)) sl) vs ≡ true
nest-clos-all sl id L sched st []       sleq cok h = refl
nest-clos-all sl id L sched st (v ∷ vs) sleq cok h =
  ∧-intro (nest-clos-caps sl id L sched st v sleq cok (∧-trueˡ h))
          (nest-clos-all sl id L sched st vs sleq cok (∧-trueʳ h))

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
walk-frame-clos {e = e} sl id L sf gas nid now src (thru-outer _ _) p vals evs fin sched st
  (sleq , cok , hvc , _) =
  nest-clos-all sl id L sched st vals sleq cok
    (proj₁ (valsCaps?-parts (frameStep L (capsAt e sl id)) sl vals hvc))

-- THE RING ITSELF, which is the whole of what the sink still owes: the
-- walk's SECOND recursion, over admitted registrations rather than over
-- a path, and the one arm the path induction hands off rather than
-- closes.  The two conjuncts in front of it are the registry pricing,
-- both of which the walk's own receipts supply, so what is left here is
-- the recursion and nothing else.
postulate
  sink-ring-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (src : Source) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    WalkHyps {t = t} sl id L sf (suc gas) nid now src (share-sink i) vals evs fin sched st →
    shareCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

walk-sink-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps {t = t} sl id L sf gas nid now src (share-sink i) vals evs fin sched st →
  dispatchCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now i vals fin sched st
walk-sink-caps sl id L sf zero nid now src i vals evs fin sched st H = tt
walk-sink-caps {Γ = Γ} {t = t} {e = e} sl id L sf (suc gas) nid now src i vals evs fin sched st
  H@(_ , cok , _ , _ , _ , (g , P , _ , hlvP , hR) , hrsz , _) =
    shareAdmit-sz i (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) hrsz
  , ≤-trans (shareAdmit-len i (EvalSt.registry st))
            (≤-trans (capsOK?-count (frameStep L c) sched st cok)
                     (subst (λ x → Caps.cReg (frameStep L c) ≤ Caps.cReg x)
                            (sym (capsAt-suc-full e sl id))
                            (frameStep-reg-mono c L≤)))
  , sink-ring-caps sl id L sf gas nid now src i vals evs fin sched st H
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  L≤ : L ≤ sizeCount c d
  L≤ = ≤-trans (iterL-infl S W d (pathLen {Γ = Γ} {t = t} (share-sink i)) L)
         (≤-trans hlvP
           (≤-trans (≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d g P))
                             (reached-room c d P g 2≤S hR))
                    (⊔-lub ≤-refl (size≤sizeCount c d 2≤S (1≤capsAt-reg e sl id)))))

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
postulate
  walk-frame-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (src : Source) (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    WalkHyps sl id L sf gas nid now src (f ↠ p) vals evs fin sched st →
    frameDrainOK (capsAt e sl id) sl (capsH e sl id) L sf nid now f p vals sched st


-- THE ONE THING A FRAME OWES THE REGISTRY'S PRICING, and it is the
-- whole preservation obligation the walk carries about it.  A frame
-- either leaves the registry alone or filters it -- and a filter
-- preserves an `all`-shaped receipt -- so the single content here is
-- the frame that REGISTERS: what it appends must be priced under the
-- base cap, which is a claim about program syntax rather than about
-- the level the frame sits at, and syntax is what a path receipt in
-- hand already bounds.
--
-- WHAT IS NOT HERE IS A LENGTH, AND THAT ABSENCE IS THE POINT.  A
-- COUNT cannot be preserved across a subscribe at all: `register` puts
-- one entry on the end per source leaf it reaches, so a conclusion
-- needing the old length PLUS the registrations under the SAME cap has
-- no source in a preservation hypothesis, and no cleverer proof of one
-- exists.  The count is READ instead, at each state that wants it,
-- from the levelled caps receipt the walk already holds: the stepped
-- cap's registry field IS the entry cap times the level, the walk's
-- own ladder puts every level it reaches under the instant's step
-- count, and the cap at that count is the instant's EXIT cap.  So the
-- registrations are accounted for at the index the walk actually
-- moves, and nothing about them has to be threaded.
RegsBase : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (st : EvalSt e) → Set
RegsBase {e = e} sl id st =
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true

-- THE THREE HEADS THAT CAN TOUCH THE REGISTRY, one leaf each, because
-- what each of them appends is a different object and only the shapes
-- share a conclusion.  A `take` dispatch filters and can only shorten;
-- the other two SUBSCRIBE, and what they hand `register` is where the
-- pricing is actually at stake -- a `thru` appends the very path being
-- walked, which the receipt above already prices, while an inner
-- reaction appends a path built from the inner observable, which it
-- does not.
-- A `take` DISPATCH ONLY EVER FILTERS, so the pricing survives it
-- without any claim about what the frame sits under.  The one arm that
-- touches the registry replaces it by `cutThrough`'s kept list, which
-- is a sublist of what it was handed, and the `all`-shaped receipt is
-- closed under that by `cutThrough-regsSz`.  Every other arm rewrites
-- the nodes map alone.
take-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (nid : Id) (now : Tick) (tnid : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  RegsBase sl id st →
  RegsBase sl id
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf nid now (take-f tnid) p vals fin sched st)))))
take-regs-base {e = e} sl id sf nid now tnid p vals fin sched st hrsz
  with lookupNode tnid (EvalSt.nodes st)
... | nothing                    = hrsz
... | just (scan-st _)           = hrsz
... | just (mergeAll-st _ _ _ _) = hrsz
... | just (switch-st _ _)       = hrsz
... | just (exhaust-st _ _)      = hrsz
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false = hrsz
...   | true  =
  cutThrough-regsSz (Caps.cSize (capsAt e sl id)) tnid (EvalSt.delivered st)
    (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st) hrsz

postulate
  inner-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (nid : Id) (now : Tick)
    (op : AllOp) (allNid : NodeId) (inst : NodeId)
    (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    RegsBase sl id st →
    pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
    RegsBase sl id
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf nid now (from-inner op allNid inst) p vals fin sched st)))))

  thru-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (nid : Id) (now : Tick)
    (op : AllOp) (tnid : NodeId)
    (p : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    RegsBase sl id st →
    pathSz? (Caps.cSize (capsAt e sl id)) (thru-outer op tnid ↠ p) ≡ true →
    RegsBase sl id
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf nid now (thru-outer op tnid) p vals fin sched st)))))

step-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (nid : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true →
  pathSz? (Caps.cSize (capsAt e sl id)) (f ↠ p) ≡ true →
  RegsBase sl id
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf nid now f p vals fin sched st)))))
step-regs-base sl id sf nid now (map-f _) p vals fin sched st hrsz hpb =
  hrsz
step-regs-base {u = u} sl id sf nid now (scan-f _ snid) p vals fin sched st hrsz hpb
  with lookupNode snid (EvalSt.nodes st)
... | nothing                    = hrsz
... | just (take-st _)           = hrsz
... | just (mergeAll-st _ _ _ _) = hrsz
... | just (switch-st _ _)       = hrsz
... | just (exhaust-st _ _)      = hrsz
... | just (scan-st {w} _) with w ≟ᵗ u
...   | yes refl = hrsz
...   | no _     = hrsz
step-regs-base sl id sf nid now (take-f tnid) p vals fin sched st hrsz hpb =
  take-regs-base sl id sf nid now tnid p vals fin sched st hrsz
step-regs-base sl id sf nid now (from-inner op an inst) p vals fin sched st hrsz hpb =
  inner-regs-base sl id sf nid now op an inst p vals fin sched st hrsz hpb
step-regs-base sl id sf nid now (thru-outer op tnid) p vals fin sched st hrsz hpb =
  thru-regs-base sl id sf nid now op tnid p vals fin sched st hrsz hpb

-- THE WALK ITSELF, WHICH IS THE FRAME LAW ITERATED AND NOTHING ELSE.
-- Each frame spends the proven step receipt, which reports its own
-- increment and hands back the caps and the values one level up; the
-- ladder premise pays the ceiling at that frame and reproduces itself
-- for the tail, since `iterL` at a `suc` IS `iterL` at the stepped
-- level.  The path receipt splits the same way -- this frame's, the
-- tail's length, the tail's -- so nothing has to be re-established
-- from outside, which is what made the frame law's data the right
-- thing to state the walk over.
chain-walk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src p vals evs fin sched st →
  capsWalkOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now p vals fin sched st
chain-walk-caps sl id L sf gas nid now src root vals evs fin sched st H =
  proj₁ (proj₂ H)
chain-walk-caps sl id L sf gas nid now src (share-sink i) vals evs fin sched st H =
  proj₁ (proj₂ H)
  , walk-sink-caps sl id L sf gas nid now src i vals evs fin sched st H
chain-walk-caps {e = e} sl id L sf gas nid now src (f ↠ p) vals evs fin sched st
  H@(sleq , cok , hvc , hpz , hdp , (g , P , hg , hlvP , hR) , hrsz , hpb) =
    cok
  , proj₁ (valsCaps?-parts (frameStep L c) sl vals hvc)
  , slSz
  , walk-frame-clos sl id L sf gas nid now src f p vals evs fin sched st H
  , walk-frame-drain sl id L sf gas nid now src f p vals evs fin sched st H
  , proj₁ ST
  , ≤-trans (m≤m+n (L + proj₁ ST) (pathLen p))
            (≤-trans (J+n≤iterL S W d (pathLen p) (L + proj₁ ST))
                     (≤-trans TAIL P≤TOP))
  , chain-walk-caps sl id (L + proj₁ ST) sf gas nid now src p
      (proj₁ r) (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
      (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
      ( trans (KeepsC.slotsEq (stepFrame-keeps sf nid now f p vals fin sched st)) sleq
      , proj₁ (proj₂ ST)
      , proj₁ (proj₂ (proj₂ ST))
      , pathSz?-widen p (proj₁ (frameStep-⊑-+ c 2≤S L (proj₁ ST))) pz2
      , ≤-trans (m≤n⊔m (depthFrame sf nid now f p vals fin sched st) _) hdp
      , (g , P , hg , TAIL , hR)
      , step-regs-base sl id sf nid now f p vals fin sched st hrsz hpb
      , pathSz?-tail (Caps.cSize c) f p hpb )
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
  TAIL : iterL S W d (pathLen p) (L + proj₁ ST) ≤ P
  TAIL = ≤-trans (iterL-mono (pathLen p) (pathLen p) 2≤S ≤-refl ≤-refl
                    (proj₂ (proj₂ (proj₂ (proj₂ ST)))) ≤-refl)
                 hlvP
  P≤TOP : P ≤ sizeCount c d ⊔ S
  P≤TOP = ≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d g P))
                  (reached-room c d P g 2≤S hR)

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
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  (Σ ℕ λ g → Σ ℕ λ P →
     (4 + (sizeᵉ e + slotsSize sl) ≤ g)
     × (lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv 1
          ≤ P)
     × Reached (capsAt e sl id) (capsH e sl id) P g) →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv nextId a path sched st
arr-chain-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hvc hpz hdp
  (g , P , hg , hlvP , hR) hrsz hpb =
  chain-walk-caps sl id Lv (budgetAt e (Sched.slots sched) nextId) n nextId
    (arrTick a) (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
    (sleq , cok , hvc , hpz , hdp , (g , P , hg , ENTRY , hR) , hrsz , hpb)
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

-- THE FOLD ALONG A CASCADE'S CHAINS, carrying the ONE invariant that
-- makes the ceiling composable: from here, the level the WHOLE
-- REMAINING cascade will climb to still fits.  A flat `Lv ≤ ceiling`
-- cannot be maintained -- it says nothing about how much of the count
-- is unspent, so the tail's climb has no budget -- while this one is
-- exactly the quantity `cascadeGo-deliveries` bounds at entry, and the
-- two ledger lines split it chain by chain: `suc D` for this chain,
-- AND ONE CHAIN'S STEP OWES THE REGISTRY'S PRICING THE SAME WAY A
-- FRAME DOES, since a chain's step is a walk and the walk's frames are
-- where a registration is appended.  Separate from the frame's because
-- the cascade recurses on chains rather than on frames, so this is the
-- statement at the granularity the ring below actually advances at.
-- AND THE SHARE ARM IS THE ONE THE PATH INDUCTION HANDS OFF, exactly
-- as the caps walk does: a sink re-enters chain evaluation over the
-- admitted registrations, so its preservation is the ring's and not a
-- frame's.  Everything else about a chain's step is the frame law
-- iterated, which is why the fold below is a real body over this one
-- leaf.
postulate
  dispatch-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    RegsBase sl id st →
    RegsBase sl id (proj₂ (proj₂ (dispatchShare {t = t} sf gas nid now i vals fin sched st)))

foldPath-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (envSrc : Source) (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  RegsBase sl id st →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  RegsBase sl id (proj₂ (proj₂ (foldPath sf gas nid now envSrc path vals evs fin sched st)))
foldPath-regs-base sl id sf gas nid now envSrc root vals evs fin sched st R hpb = R
foldPath-regs-base sl id sf gas nid now envSrc (share-sink i) vals evs fin sched st R hpb =
  dispatch-regs-base sl id sf gas nid now i vals fin sched st R
foldPath-regs-base {e = e} sl id sf gas nid now envSrc (f ↠ p) vals evs fin sched st R hpb =
  foldPath-regs-base sl id sf gas nid now envSrc p
    (proj₁ r) (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
    (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
    (step-regs-base sl id sf nid now f p vals fin sched st R hpb)
    (pathSz?-tail (Caps.cSize (capsAt e sl id)) f p hpb)
  where r = stepFrame sf nid now f p vals fin sched st

chainStep-regs-base : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  RegsBase sl id (proj₂ (proj₂ (chainStep nextId a path sched st)))
chainStep-regs-base {n = n} {e = e} sl id a nextId path sched st hrsz hpb =
  foldPath-regs-base sl id (budgetAt e (Sched.slots sched) nextId) n nextId
    (arrTick a) (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st hrsz hpb

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
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  (J g i : ℕ) →
  4 + (sizeᵉ e + slotsSize sl) ≤ g →
  n ≤ g →
  Reached (capsAt e sl id) (capsH e sl id) J (suc g) →
  i + length chains
    ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv a nextId chains sched st
arr-chains-caps-go sl id Lv a nextId [] sched st sleq hlv cok hpz hvc hdp
  J g i hg hgn hR hlen hLv hrsz = tt
arr-chains-caps-go {e = e} sl id Lv a nextId ((rid , path) ∷ chains) sched st sleq hlv cok hpz hvc hdp
  J g i hg hgn hR hlen hLv hrsz
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = arr-chains-caps-go sl id Lv a nextId chains sched st sleq hlv cok
                (proj₂ (∧-true _ _ hpz)) hvc
                (lub3-l (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched
                           (record st { delivered = rid ∷ EvalSt.delivered st }))
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))
                           (proj₂ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
                J g i hg hgn hR
                (≤-trans (+-monoʳ-≤ i (n≤1+n (length chains))) hlen) hLv hrsz
... | false =
      arr-chain-caps sl id Lv a nextId path sched st′ sleq cok
        HVC
        (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
        (lub3-m (depthCascade a nextId chains sched st)
                (depthChain nextId a path sched st′)
                (depthCascade a nextId chains
                   (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        (g , Pos c d J g i , hg , CH≤ , walk J g i HI hR) hrsz
        (proj₁ (∧-true _ _ hpz))
    , proj₁ ST
    , FLAT
    , arr-chains-caps-go sl id (Lv + proj₁ ST) a nextId chains
        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
        (proj₂ (proj₂ (chainStep nextId a path sched st′)))
        (trans (chainStep-slots nextId a path sched st′) sleq)
        REC (proj₂ (proj₂ ST))
        (proj₂ (∧-true _ _ hpz)) hvc
        (lub3-r (depthCascade a nextId chains sched st)
                (depthChain nextId a path sched st′)
                (depthCascade a nextId chains
                   (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        J g (suc i) hg hgn hR
        (subst (_≤ regAt S (Caps.cReg c) J) (+-suc i (length chains)) hlen)
        (≤-trans (proj₁ (proj₂ ST)) STEP)
        (chainStep-regs-base sl id a nextId path sched st′ hrsz
           (proj₁ (∧-true _ _ hpz)))
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
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st) ≤ capsH e sl id →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId (chainsOf a st) sched
    (cascadeLatch a st)
arr-chains-caps {e = e} sl id a nextId sched st sleq cok hpz hvc hdp =
  arr-chains-caps-go sl id 0 a nextId (chainsOf a st) sched (cascadeLatch a st)
    sleq ENTRY
    (subst (λ x → capsOK? x sched (cascadeLatch a st) ≡ true)
           (sym (frameStep-0 (capsAt e sl id))) LATCH)
    hpz hvc hdp
    0 (Caps.cSize (capsAt e sl id)) 0
    (capsAt-gas-size e sl id) (n≤capsAt-size e sl id) base REGLEN ≤-refl
    (capsOK?-regs c sched (cascadeLatch a st) LATCH)
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
-- that sum scaled by the program's size, and the whole right-hand side
-- is read at the current instant off the run.
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
postulate
  cascade-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
      ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a))
                  (storeNestMax sched st) (nestUnit e sl)

-- THE SLOT VOCABULARY'S NESTING UNDER ITS SIZE, slot by slot: a
-- scripted slot's own index makes its nesting zero, and a shared one's
-- is its expression's, which that expression's size dominates.
slotNest≤slotSize : ∀ {n} {Γ : Ctx n} {k t} (s : Slot Γ k t) →
  slotNest s ≤ slotSize s
slotNest≤slotSize (scripted _) = z≤n
slotNest≤slotSize (shared d)   = nestDᵉ≤sizeᵉ d

slotsNestSum≤slotsSize : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) →
  slotsNestSum sl ≤ slotsSize sl
slotsNestSum≤slotsSize sl =
  sum-tab-mono (λ i → slotNest (sl i)) (λ i → slotSize (sl i))
               (λ i → slotNest≤slotSize (sl i))

-- FOUR SQUARES UNDER THE EXPONENTIAL, which is where the base case's
-- room comes from and why the size floor is eight rather than six.
sq4≤2^ : ∀ (S : ℕ) → 8 ≤ S → 4 * (S * S) ≤ 2 ^ S
sq4≤2^ (suc (suc k)) (s≤s (s≤s 6≤k)) =
  ≤-trans (*-monoʳ-≤ 4 (sq≤2^ k 6≤k))
          (≤-reflexive (sym (^-distribˡ-+-* 2 2 k)))

-- THE STEP'S ARITHMETIC, OVER BARE NUMBERS, and it is a body rather
-- than a leaf.  Nothing about caps survives here: a cap that steps by
-- multiplying an exponential onto a sum fits two exponentials of the
-- next size exactly when that exponent, the increment's own exponent,
-- the previous budget and the next size all fit ONE.  Stating it over
-- numerals is what makes the step instantiable at all -- both sides of
-- the caps-indexed form sit on a recurrence that does not terminate
-- natively, so the statement it came from could not be reached by any
-- row.
nest-step-ℕ : ∀ (S S′ C I C′ L M : ℕ) → 1 ≤ S →
  C′ ≤ 2 ^ L * (C + I) →
  I ≤ 2 ^ M →
  S′ + 3 + (2 ^ S + M) + L ≤ 2 ^ S′ →
  S * (4 * C) ≤ 2 ^ (2 ^ S) →
  S′ * (4 * C′) ≤ 2 ^ (2 ^ S′)
nest-step-ℕ S S′ C I C′ L M 1≤S hC′ hI hroom ih =
  ≤-trans (*-mono-≤ (<⇒≤ (n<2^n S′)) (*-monoʳ-≤ 4 hC′E))
          (≤-trans (≤-reflexive (sym collect)) (^-monoʳ-≤ 2 hroom′))
  where
  K = 2 ^ S + M
  C≤4C : C ≤ 4 * C
  C≤4C = ≤-trans (≤-reflexive (sym (*-identityˡ C)))
                 (*-monoˡ-≤ C {1} {4} (s≤s z≤n))
  4C≤S4C : 4 * C ≤ S * (4 * C)
  4C≤S4C = ≤-trans (≤-reflexive (sym (*-identityˡ (4 * C))))
                   (*-monoˡ-≤ (4 * C) 1≤S)
  C≤ : C ≤ 2 ^ K
  C≤ = ≤-trans (≤-trans C≤4C 4C≤S4C)
               (≤-trans ih (^-monoʳ-≤ 2 (m≤m+n (2 ^ S) M)))
  I≤ : I ≤ 2 ^ K
  I≤ = ≤-trans hI (^-monoʳ-≤ 2 (m≤n+m M (2 ^ S)))
  CI≤ : C + I ≤ 2 ^ suc K
  CI≤ = ≤-trans (+-mono-≤ C≤ I≤) (≤-reflexive (sym (2X≡X+X (2 ^ K))))
  hC′E : C′ ≤ 2 ^ L * 2 ^ suc K
  hC′E = ≤-trans hC′ (*-monoʳ-≤ (2 ^ L) CI≤)
  collect : 2 ^ (S′ + (2 + (L + suc K))) ≡ 2 ^ S′ * (4 * (2 ^ L * 2 ^ suc K))
  collect = trans (^-distribˡ-+-* 2 S′ (2 + (L + suc K)))
                  (cong (2 ^ S′ *_)
                    (trans (^-distribˡ-+-* 2 2 (L + suc K))
                           (cong (4 *_) (^-distribˡ-+-* 2 L (suc K)))))
  reshape : S′ + (2 + (L + suc K)) ≡ S′ + 3 + K + L
  reshape = solve 3 (λ s l k → s :+ (con 2 :+ (l :+ (con 1 :+ k)))
                                 := s :+ con 3 :+ k :+ l)
                  refl S′ L K
  hroom′ : S′ + (2 + (L + suc K)) ≤ 2 ^ S′
  hroom′ = ≤-trans (≤-reflexive reshape) hroom

-- THE PROGRAM'S OWN VOCABULARY UNDER THE INSTANT'S SIZE.  The wrap
-- unit reads the expression's nesting and the slots', each of which its
-- own size dominates, and the caps recurrence's base bound already
-- holds that sum -- so the unit is a caps quantity and the increment
-- below can be priced without any syntax in it.
nestUnit≤size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestUnit e sl ≤ Caps.cSize (capsAt e sl id)
nestUnit≤size e sl id =
  ≤-trans (≤-trans (s≤s (+-mono-≤ (nestDᵉ≤sizeᵉ e) (slotsNestSum≤slotsSize sl)))
                   (n≤1+n _))
          (capsAt-base-size e sl id)

-- THE INCREMENT'S EXPONENT, AND EVERY FIELD IN IT READ AT THE NEXT
-- INSTANT'S SIZE.  The burst is a `suc` of the width and the width at
-- an instant is strictly under the size at the next one; the registry
-- is under its own size and that size is under the next; the wrap unit
-- is under the size too.  What stays unreduced is the delivery, at both
-- instants -- which is the recurrence the room has to pay for.
nestIncLog : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
nestIncLog {n = n} e sl id =
  S′ * (S′ * (suc (suc (S′ * delSize n (capsAt e sl (suc id))))
              * (suc (delSq n (capsAt e sl (suc id))) * S′)))
  where S′ = Caps.cSize (capsAt e sl (suc id))

-- the burst and the registry at the next size, which both exponents want
burst≤size′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestBurstAt e sl id ≤ Caps.cSize (capsAt e sl (suc id))
burst≤size′ e sl id =
  ≤-trans (≤-reflexive (nestBurstAt-def e sl id)) (capsAt-wid<size e sl id)

reg≤size′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  realWidAt e sl id ≤ Caps.cSize (capsAt e sl (suc id))
reg≤size′ e sl id =
  ≤-trans (≤-trans (≤-reflexive (realWidAt-def e sl id))
                   (B2-cReg≤cSize e sl id))
          (capsAt-size-mono e sl id)

nestInc≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestIncAt e sl id ≤ 2 ^ nestIncLog e sl id
nestInc≤exp {n = n} e sl id =
  ≤-trans (≤-trans (≤-reflexive (nestIncAt-def e sl id)) shape)
          (<⇒≤ (n<2^n (nestIncLog e sl id)))
  where
  shape : realWidAt e sl id
            * (nestBurstAt e sl id
               * (suc (suc (realWidAt e sl id * delSize n (capsAt e sl (suc id))))
                  * nestU (delSq n (capsAt e sl (suc id))) (nestUnit e sl)))
            ≤ nestIncLog e sl id
  shape =
    *-mono-≤ (reg≤size′ e sl id)
      (*-mono-≤ (burst≤size′ e sl id)
        (*-mono-≤ (s≤s (s≤s (*-monoˡ-≤ (delSize n (capsAt e sl (suc id)))
                                      (reg≤size′ e sl id))))
                  (≤-trans (≤-reflexive (nestU-def (delSq n (capsAt e sl (suc id)))
                                                   (nestUnit e sl)))
                           (*-monoʳ-≤ (suc (delSq n (capsAt e sl (suc id))))
                                      (≤-trans (nestUnit≤size e sl id)
                                               (capsAt-size-mono e sl id))))))

-- THE FACTOR'S EXPONENT, read the same way and with the same residue.
nestFacLog : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
nestFacLog {n = n} e sl id =
  suc S′ * suc S′ * (suc (delSize n (capsAt e sl (suc id)))
                     * (S′ * delSq n (capsAt e sl (suc id))))
  where S′ = Caps.cSize (capsAt e sl (suc id))

nestFac≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestFacAt e sl id ≤ 2 ^ nestFacLog e sl id
nestFac≤exp {n = n} e sl id =
  ≤-trans (≤-reflexive (nestFacAt-def e sl id))
          (^-monoʳ-≤ 2 (*-mono-≤ (*-mono-≤ (s≤s (burst≤size′ e sl id))
                                           (s≤s (burst≤size′ e sl id)))
                                 (*-monoʳ-≤ (suc (delSize n (capsAt e sl (suc id))))
                                            (*-monoˡ-≤ (delSq n (capsAt e sl (suc id)))
                                                       (reg≤size′ e sl id)))))

-- BOTH EXPONENTS UNDER ONE POWER OF THE NEXT SIZE.  Each is a product
-- whose only non-size factors are a delivery size and a delivery
-- square, and a delivery size is a closed power of `suc cSize` -- two
-- factors per unit of context depth, since the length recurrence
-- multiplies a registry by a successor of the size and the registry
-- is under that size.  Counting the factors of the two products gives
-- the same ceiling for both, so the room the step needs stops being
-- stated over two recurrences and becomes one inequality in three
-- numbers.
--
-- The delivery size at the PREVIOUS instant is read against the next
-- instant's base too, which is what lets one power serve both: the
-- size is monotone across the instant, and the bound is monotone in
-- its base.
bump : ∀ (a b z : ℕ) → 1 ≤ z → a + 1 ≤ b → a + z ≤ b * z
bump a b z 1≤z h =
  ≤-trans (+-monoˡ-≤ z (≤-trans (≤-reflexive (sym (*-identityʳ a)))
                                (*-monoʳ-≤ a 1≤z)))
  (≤-trans (+-monoʳ-≤ (a * z) (≤-reflexive (sym (*-identityˡ z))))
  (≤-trans (≤-reflexive (sym (*-distribʳ-+ z a 1)))
           (*-monoˡ-≤ z h)))

pow3 : ∀ (b a k : ℕ) → b ^ a * (b ^ k * (b ^ k * b ^ k)) ≡ b ^ (a + (k + (k + k)))
pow3 b a k =
  sym (trans (^-distribˡ-+-* b a (k + (k + k)))
             (cong (b ^ a *_)
               (trans (^-distribˡ-+-* b k (k + k))
                      (cong (b ^ k *_) (^-distribˡ-+-* b k k)))))

del-pow′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (delSize n (capsAt e sl (suc id)))
    ≤ suc (Caps.cSize (capsAt e sl (suc id))) ^ suc (n + n)
del-pow′ {n = n} e sl id =
  delSize-exp n (capsAt e sl (suc id)) (B2-cReg≤cSize e sl (suc id))

nestIncLog≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestIncLog e sl id ≤ suc (Caps.cSize (capsAt e sl (suc id))) ^ (6 * n + 9)
nestIncLog≤pow {n = n} e sl id =
  ≤-trans (*-mono-≤ S′≤B
            (*-mono-≤ S′≤B (*-mono-≤ f3 (*-mono-≤ f4 S′≤B))))
          (≤-trans (≤-reflexive collect)
                   (≤-reflexive (trans (pow3 B 6 K1) (cong (B ^_) expo))))
  where
  S′ : ℕ
  S′ = Caps.cSize (capsAt e sl (suc id))
  B : ℕ
  B = suc S′
  K1 : ℕ
  K1 = suc (n + n)
  P : ℕ
  P = B ^ K1
  S′≤B : S′ ≤ B
  S′≤B = n≤1+n S′
  1≤P : 1 ≤ P
  1≤P = 1≤pow S′ K1
  1≤BP : 1 ≤ B * P
  1≤BP = 1≤pow S′ (suc K1)
  1≤PP : 1 ≤ P * P
  1≤PP = ≤-trans (1≤pow S′ (K1 + K1)) (≤-reflexive (^-distribˡ-+-* B K1 K1))
  3≤B : 2 + 1 ≤ B
  3≤B = s≤s (2≤capsAt-size e sl (suc id))
  2≤B : 1 + 1 ≤ B
  2≤B = ≤-trans (s≤s (s≤s z≤n)) 3≤B
  f3 : suc (suc (S′ * delSize n (capsAt e sl (suc id)))) ≤ B * (B * P)
  f3 = ≤-trans (+-monoʳ-≤ 2 (*-mono-≤ S′≤B
                              (≤-trans (n≤1+n (delSize n (capsAt e sl (suc id))))
                                       (del-pow′ e sl id))))
               (bump 2 B (B * P) 1≤BP 3≤B)
  f4 : suc (delSq n (capsAt e sl (suc id))) ≤ B * (P * P)
  f4 = ≤-trans (+-monoʳ-≤ 1
                 (≤-trans (≤-reflexive (delSq-def n (capsAt e sl (suc id))))
                          (*-mono-≤ (≤-trans (n≤1+n _) (del-pow′ e sl id))
                                    (≤-trans (n≤1+n _) (del-pow′ e sl id)))))
               (bump 1 B (P * P) 1≤PP 2≤B)
  collect : B * (B * ((B * (B * P)) * ((B * (P * P)) * B)))
              ≡ B ^ 6 * (P * (P * P))
  collect =
    solve 2 (λ b p → b :* (b :* ((b :* (b :* p)) :* ((b :* (p :* p)) :* b)))
                  := (b :* (b :* (b :* (b :* (b :* (b :* con 1)))))) :* (p :* (p :* p)))
            refl B P
  expo : 6 + (K1 + (K1 + K1)) ≡ 6 * n + 9
  expo = solve 1 (λ x → con 6 :+ ((con 1 :+ (x :+ x))
                                   :+ ((con 1 :+ (x :+ x)) :+ (con 1 :+ (x :+ x))))
                     := con 6 :* x :+ con 9)
               refl n

nestFacLog≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestFacLog e sl id ≤ suc (Caps.cSize (capsAt e sl (suc id))) ^ (6 * n + 9)
nestFacLog≤pow {n = n} e sl id =
  ≤-trans (*-mono-≤ (≤-refl {B * B}) (*-mono-≤ (del-pow′ e sl id) (*-mono-≤ S′≤B f4)))
          (≤-trans (≤-reflexive collect)
                   (≤-trans (≤-reflexive (trans (pow3 B 3 K1) (cong (B ^_) expo)))
                            (powʳ1 B (s≤s z≤n)
                                   (+-monoʳ-≤ (6 * n) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
  where
  S′ : ℕ
  S′ = Caps.cSize (capsAt e sl (suc id))
  B : ℕ
  B = suc S′
  K1 : ℕ
  K1 = suc (n + n)
  P : ℕ
  P = B ^ K1
  S′≤B : S′ ≤ B
  S′≤B = n≤1+n S′
  f4 : delSq n (capsAt e sl (suc id)) ≤ P * P
  f4 = ≤-trans (≤-reflexive (delSq-def n (capsAt e sl (suc id))))
               (*-mono-≤ (≤-trans (n≤1+n _) (del-pow′ e sl id))
                         (≤-trans (n≤1+n _) (del-pow′ e sl id)))
  collect : B * B * (P * (B * (P * P))) ≡ B ^ 3 * (P * (P * P))
  collect =
    solve 2 (λ b p → b :* b :* (p :* (b :* (p :* p)))
                  := (b :* (b :* (b :* con 1))) :* (p :* (p :* p)))
            refl B P
  expo : 3 + (K1 + (K1 + K1)) ≡ 6 * n + 6
  expo = solve 1 (λ x → con 3 :+ ((con 1 :+ (x :+ x))
                                   :+ ((con 1 :+ (x :+ x)) :+ (con 1 :+ (x :+ x))))
                     := con 6 :* x :+ con 6)
               refl n

-- THE CEILING ON THE NEXT SIZE, which is what makes its BIT LENGTH a
-- nameable number: the step is a quadratic iterated count-many times,
-- and once the size is at least four its square already sits under two
-- to it, so every factor the iteration contributes is a power of two
-- and the whole product is one.
size-upper : ∀ (c : Caps) (d : ℕ) → 4 ≤ Caps.cSize c →
  suc (Caps.cSize (frameBlowup c d))
    ≤ 2 ^ (Caps.cSize c * sizeCount c d + Caps.cSize c + 1)
size-upper c d 4≤S =
  ≤-trans (s≤s (≤-trans (iterSize-pow S S J S 1≤S ≤-refl ≤-refl) body))
          (≤-trans (+-monoˡ-≤ X (1≤pow≤ 2 (S * J + S) (s≤s z≤n)))
                   (≤-reflexive fin))
  where
  S : ℕ
  S = Caps.cSize c
  J : ℕ
  J = sizeCount c d
  X : ℕ
  X = 2 ^ (S * J + S)
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 4≤S
  3S≤ : 3 * S ≤ 2 ^ S
  3S≤ = ≤-trans (*-monoˡ-≤ S (≤-trans (n≤1+n 3) 4≤S)) (sq≤pow S 4≤S)
  body : (3 * S) ^ J * S ≤ 2 ^ (S * J + S)
  body =
    ≤-trans (*-mono-≤ (≤-trans (^-monoˡ-≤ J 3S≤)
                               (≤-reflexive (^-*-assoc 2 S J)))
                      (<⇒≤ (n<2^n S)))
            (≤-reflexive (sym (^-distribˡ-+-* 2 (S * J) S)))
  fin : X + X ≡ 2 ^ (S * J + S + 1)
  fin = trans (sym (2X≡X+X X))
              (trans (*-comm 2 X) (sym (^-distribˡ-+-* 2 (S * J + S) 1)))

capsAt-size-lower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Caps.cSize (capsAt e sl id)
    ^ suc (sizeCount (capsAt e sl id) (capsH e sl id))
    ≤ Caps.cSize (capsAt e sl (suc id))
capsAt-size-lower e sl id =
  size-lower (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))

capsAt-size-upper : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (Caps.cSize (capsAt e sl (suc id)))
    ≤ 2 ^ (Caps.cSize (capsAt e sl id)
             * sizeCount (capsAt e sl id) (capsH e sl id)
           + Caps.cSize (capsAt e sl id) + 1)
capsAt-size-upper e sl id =
  size-upper (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) (8≤capsAt-size e sl id))

-- A LINEAR TERM UNDER A POWER, with four factors of the base already
-- spent.  The induction is on the exponent past five: one more step
-- multiplies the right by the base and the left by less than two, and
-- the base is at least eight.  Five is where the base case fits --
-- five copies of the fourth power are under the fifth once the base is
-- above five.
lin≤pow : ∀ (S j : ℕ) → 8 ≤ S → S * S * S * S * (5 + j) ≤ S ^ (5 + j)
lin≤pow S zero    8≤S =
  ≤-trans (*-monoʳ-≤ (S * S * S * S) (≤-trans (≤ᵇ⇒≤ 5 8 tt) 8≤S))
          (≤-reflexive (solve 1 (λ x → x :* x :* x :* x :* x
                                    := x :* (x :* (x :* (x :* (x :* con 1)))))
                              refl S))
lin≤pow S (suc j) 8≤S =
  ≤-trans (*-monoʳ-≤ (S * S * S * S) grow)
  (≤-trans (≤-reflexive shape)
  (≤-trans (*-monoˡ-≤ (S * S * S * S * (5 + j)) 2≤S)
           (*-monoʳ-≤ S (lin≤pow S j 8≤S))))
  where
  grow : 5 + suc j ≤ 2 * (5 + j)
  grow = ≤-trans (m≤m+n (5 + suc j) (4 + j))
                 (≤-reflexive (solve 1 (λ x → (con 6 :+ x) :+ (con 4 :+ x)
                                            := con 2 :* (con 5 :+ x))
                                     refl j))
  shape : S * S * S * S * (2 * (5 + j)) ≡ 2 * (S * S * S * S * (5 + j))
  shape = solve 2 (λ a y → a :* (con 2 :* y) := con 2 :* (a :* y))
                  refl (S * S * S * S) (5 + j)
  2≤S : 2 ≤ S
  2≤S = ≤-trans (≤ᵇ⇒≤ 2 8 tt) 8≤S

lin≤powJ : ∀ (S J : ℕ) → 8 ≤ S → 5 ≤ J → S * S * S * S * J ≤ S ^ J
lin≤powJ S _ 8≤S (s≤s (s≤s (s≤s (s≤s (s≤s _))))) = lin≤pow S _ 8≤S

-- WHAT THE STEP HAS TO PAY FOR, in the currency the room is stated
-- in: the exponent times the bit length of the next size, plus the
-- four constant terms.  Every factor here is linear in the size or in
-- the count, so the whole obligation is a fourth power of the size
-- times the count -- and the next size is a power of the size whose
-- exponent IS the count, which swallows it with four factors to
-- spare.
room-arith : ∀ (S J K : ℕ) → 8 ≤ S → S ≤ J → K ≤ 6 * S + 9 →
  K * (S * J + S + 1) + 4 ≤ S ^ suc J
room-arith S J K 8≤S S≤J K≤ =
  ≤-trans (+-monoˡ-≤ 4 (*-mono-≤ (≤-trans K≤ K15) bIsSmall))
  (≤-trans (+-mono-≤ (≤-reflexive collect) 4≤SSJ)
  (≤-trans (≤-reflexive (solve 1 (λ y → con 45 :* y :+ y := con 46 :* y)
                               refl (S * S * J)))
  (≤-trans (*-monoˡ-≤ (S * S * J) 46≤SS)
  (≤-trans (≤-reflexive (solve 3 (λ a b y → (a :* b) :* (a :* b :* y)
                                         := a :* b :* a :* b :* y)
                               refl S S J))
  (≤-trans (lin≤powJ S J 8≤S (≤-trans (≤ᵇ⇒≤ 5 8 tt) (≤-trans 8≤S S≤J)))
           (powʳ1 S (≤-trans (s≤s z≤n) 8≤S) (n≤1+n J)))))))
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 8≤S
  1≤J : 1 ≤ J
  1≤J = ≤-trans 1≤S S≤J
  1≤SJ : 1 ≤ S * J
  1≤SJ = *-mono-≤ 1≤S 1≤J
  S≤SJ : S ≤ S * J
  S≤SJ = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤J)
  K15 : 6 * S + 9 ≤ 15 * S
  K15 = ≤-trans (+-monoʳ-≤ (6 * S)
                  (≤-trans (≤-reflexive (sym (*-identityʳ 9))) (*-monoʳ-≤ 9 1≤S)))
                (≤-reflexive (solve 1 (λ x → con 6 :* x :+ con 9 :* x := con 15 :* x)
                                    refl S))
  bIsSmall : S * J + S + 1 ≤ 3 * (S * J)
  bIsSmall = ≤-trans (+-mono-≤ (+-monoʳ-≤ (S * J) S≤SJ) 1≤SJ)
                     (≤-reflexive (solve 1 (λ y → y :+ y :+ y := con 3 :* y)
                                         refl (S * J)))
  collect : 15 * S * (3 * (S * J)) ≡ 45 * (S * S * J)
  collect = solve 2 (λ x y → con 15 :* x :* (con 3 :* (x :* y))
                          := con 45 :* (x :* x :* y))
                  refl S J
  4≤SSJ : 4 ≤ S * S * J
  4≤SSJ = ≤-trans (≤ᵇ⇒≤ 4 64 tt) (*-mono-≤ (*-mono-≤ 8≤S 8≤S) 1≤J)
  46≤SS : 46 ≤ S * S
  46≤SS = ≤-trans (≤ᵇ⇒≤ 46 64 tt) (*-mono-≤ 8≤S 8≤S)

-- THE CONSTANT PART OF THE ROOM: twice a size and three more sits
-- under two to that size, once the size is at least six.  The square
-- lemma does it -- a successor squared is already above a linear term
-- with four to spare.
lin≤2^ : ∀ (m : ℕ) → 6 ≤ m → 2 * suc m + 3 ≤ 2 ^ m
lin≤2^ m 6≤m =
  ≤-trans (≤-reflexive lhs)
  (≤-trans (+-monoʳ-≤ (2 * m + 4) 1≤mm)
  (≤-trans (≤-reflexive (sym rhs)) (sq≤2^ m 6≤m)))
  where
  lhs : 2 * suc m + 3 ≡ 2 * m + 4 + 1
  lhs = solve 1 (λ x → con 2 :* (con 1 :+ x) :+ con 3
                    := con 2 :* x :+ con 4 :+ con 1)
              refl m
  rhs : (2 + m) * (2 + m) ≡ 2 * m + 4 + m * (2 + m)
  rhs = solve 1 (λ x → (con 2 :+ x) :* (con 2 :+ x)
                    := con 2 :* x :+ con 4 :+ x :* (con 2 :+ x))
              refl m
  1≤mm : 1 ≤ m * (2 + m)
  1≤mm = *-mono-≤ (≤-trans (≤ᵇ⇒≤ 1 6 tt) 6≤m) (s≤s z≤n)

-- THE ROOM ITSELF, and it is three numbers now.  The budget is two to
-- the next size; the next size and its bit length are named
-- separately, because what has to be paid for is the exponent TIMES
-- that length, and the hypothesis says the next size covers it with
-- four to spare.  The two halves are then each under half the budget:
-- the constant part by the square lemma, the two powers because the
-- length was bought.
room-gen : ∀ (E S′ K b : ℕ) → 7 ≤ S′ → E ≤ S′ → suc S′ ≤ 2 ^ b →
  K * b + 4 ≤ S′ →
  S′ + 3 + (E + suc S′ ^ K) + suc S′ ^ K ≤ 2 ^ S′
room-gen E (suc S″) K b (s≤s 6≤S″) hE hB hK =
  ≤-trans (+-monoˡ-≤ P (+-monoʳ-≤ (suc S″ + 3) (+-monoˡ-≤ P hE)))
  (≤-trans (≤-reflexive regroup)
  (≤-trans (+-mono-≤ (lin≤2^ S″ 6≤S″) twoP)
           (≤-reflexive (sym (2X≡X+X (2 ^ S″))))))
  where
  P : ℕ
  P = suc (suc S″) ^ K
  regroup : suc S″ + 3 + (suc S″ + P) + P ≡ 2 * suc S″ + 3 + (P + P)
  regroup = solve 2 (λ x p → (con 1 :+ x) :+ con 3 :+ ((con 1 :+ x) :+ p) :+ p
                          := con 2 :* (con 1 :+ x) :+ con 3 :+ (p :+ p))
                  refl S″ P
  P≤ : P ≤ 2 ^ (b * K)
  P≤ = ≤-trans (^-monoˡ-≤ K hB) (≤-reflexive (^-*-assoc 2 b K))
  bK+1≤ : suc (b * K) ≤ S″
  bK+1≤ = ≤-trans (s≤s (≤-reflexive (*-comm b K)))
                  (≤-pred (≤-trans (≤-reflexive (+-comm 2 (K * b)))
                          (≤-trans (+-monoʳ-≤ (K * b) (≤ᵇ⇒≤ 2 4 tt)) hK)))
  twoP : P + P ≤ 2 ^ S″
  twoP = ≤-trans (+-mono-≤ P≤ P≤)
         (≤-trans (≤-reflexive (sym (2X≡X+X (2 ^ (b * K)))))
                  (^-monoʳ-≤ 2 bK+1≤))

nestFac-room : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl (suc id)) + 3
    + (2 ^ Caps.cSize (capsAt e sl id) + nestIncLog e sl id)
    + nestFacLog e sl id
    ≤ 2 ^ Caps.cSize (capsAt e sl (suc id))
nestFac-room {n = n} e sl id =
  ≤-trans (+-mono-≤ (+-monoʳ-≤ (Caps.cSize (capsAt e sl (suc id)) + 3)
                      (+-monoʳ-≤ (2 ^ Caps.cSize (capsAt e sl id))
                                 (nestIncLog≤pow e sl id)))
                    (nestFacLog≤pow e sl id))
          (room-gen (2 ^ Caps.cSize (capsAt e sl id))
                    (Caps.cSize (capsAt e sl (suc id)))
                    (6 * n + 9)
                    (Caps.cSize (capsAt e sl id) * J
                      + Caps.cSize (capsAt e sl id) + 1)
                    (≤-trans (≤ᵇ⇒≤ 7 8 tt) (8≤capsAt-size e sl (suc id)))
                    (≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ _)))
                                      (*-monoʳ-≤ (2 ^ Caps.cSize (capsAt e sl id))
                                                 (≤-trans (s≤s z≤n)
                                                   (2≤capsAt-size e sl id))))
                             (capsAt-exp-gain e sl id))
                    (capsAt-size-upper e sl id)
                    (≤-trans (room-arith (Caps.cSize (capsAt e sl id)) J (6 * n + 9)
                                (8≤capsAt-size e sl id)
                                (size≤sizeCount (capsAt e sl id) (capsH e sl id)
                                  (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id))
                                (+-monoˡ-≤ 9 (*-monoʳ-≤ 6 (n≤capsAt-size e sl id))))
                             (capsAt-size-lower e sl id)))
  where
  J : ℕ
  J = sizeCount (capsAt e sl id) (capsH e sl id)

-- WHY THE EXPONENT AND NOT THE SIZE.  The cap exponentiates a caps
-- field once per instant, so it stands above the size at its own
-- instant and no bound denominated in the size can hold it.  Two
-- exponentials is what it costs and not one, because the exponent the
-- cap raises is a POLYNOMIAL of the caps field rather than the field:
-- it reads a delivery SQUARE of the caps at the next instant, which is
-- cubic in a size one exponential would only have matched linearly.
--
-- AND THE CONSTRAINT THE SHAPE HAS TO RESPECT IS THE INDEX: no summand
-- may price the cap at the instant AFTER the one being bounded.  The
-- hypothesis and the conclusion are read one instant apart and that is
-- the whole of it -- the delivery the exponents read is the next
-- instant's, which is what the room, not the cap, is charged for.
nestCap≤exp-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl id) * (4 * nestCapAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id)) →
  Caps.cSize (capsAt e sl (suc id)) * (4 * nestCapAt e sl (suc id))
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl (suc id)))
nestCap≤exp-suc e sl id ih =
  nest-step-ℕ (Caps.cSize (capsAt e sl id))
              (Caps.cSize (capsAt e sl (suc id)))
              (nestCapAt e sl id) (nestIncAt e sl id)
              (nestCapAt e sl (suc id))
              (nestFacLog e sl id) (nestIncLog e sl id)
              (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))
              hC′ (nestInc≤exp e sl id) (nestFac-room e sl id) ih
  where
  hC′ : nestCapAt e sl (suc id)
          ≤ 2 ^ nestFacLog e sl id
              * (nestCapAt e sl id + nestIncAt e sl id)
  hC′ = ≤-trans (≤-reflexive (nestCapAt-suc e sl id))
                (*-monoˡ-≤ (nestCapAt e sl id + nestIncAt e sl id)
                           (nestFac≤exp e sl id))

nestCap≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl id) * (4 * nestCapAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
nestCap≤exp e sl zero =
  ≤-trans (*-monoʳ-≤ S (*-monoʳ-≤ 4 C≤S))
          (≤-trans (≤-reflexive shape)
                   (≤-trans (sq4≤2^ S (8≤capsAt-size e sl 0))
                            (^-monoʳ-≤ 2 (<⇒≤ (n<2^n S)))))
  where
  S = Caps.cSize (capsAt e sl 0)
  shape : S * (4 * S) ≡ 4 * (S * S)
  shape = solve 1 (λ s → s :* (con 4 :* s) := con 4 :* (s :* s)) refl S
  C≤S : nestCapAt e sl 0 ≤ S
  C≤S = ≤-trans (≤-reflexive (nestCapAt-0 e sl)) (nestUnit≤size e sl 0)
nestCap≤exp e sl (suc id) =
  nestCap≤exp-suc e sl id (nestCap≤exp e sl id)

-- AND THE CEILING'S SYNTAX IS PAID BY THE SIZE CAP, which is what lets
-- the leaf above be stated in caps alone.  The ceiling reads the
-- program's own size as a factor, and the caps recurrence carries the
-- base bound at every instant, so that factor sits under the size cap
-- with no run consulted; the `suc` beside the tripled cap is under a
-- fourth copy of it because the cap is at least one, being the wrap
-- unit at instant zero and nondecreasing after.
nestCap-sight≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  suc (sizeᵉ e) * suc (3 * nestCapAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
nestCap-sight≤exp e sl id =
  ≤-trans (*-mono-≤ 1+z≤S h4) (nestCap≤exp e sl id)
  where
  C = nestCapAt e sl id
  1≤C : 1 ≤ C
  1≤C = ≤-trans (subst (1 ≤_) (sym (nestCapAt-0 e sl)) (s≤s z≤n))
                (nestCap-mono₀ e sl id)
  four : 4 * C ≡ C + 3 * C
  four = solve 1 (λ c → con 4 :* c := c :+ con 3 :* c) refl C
  h4 : suc (3 * C) ≤ 4 * C
  h4 = ≤-trans (+-monoˡ-≤ (3 * C) 1≤C) (≤-reflexive (sym four))
  1+z≤S : suc (sizeᵉ e) ≤ Caps.cSize (capsAt e sl id)
  1+z≤S = ≤-trans (≤-trans (n≤1+n (suc (sizeᵉ e))) (m≤m+n (2 + sizeᵉ e) _))
                  (capsAt-base-size e sl id)

-- AND THE SCALE THE DESCENT CARRIES IS AFFORDABLE AT THE ENTRY, which
-- is what lets the sighted ceiling price a BUILT value.  A descent that
-- evaluates a term pays once per OCCURRENCE of the syntax that builds
-- it, so its ceiling reads `2 ^ syncSizeᵉ e` in front of the nesting.
-- That factor is bounded by two exponentials of the entry cap's size --
-- the program's sync size is under its own size and its size is under
-- the cap's -- while the target here is a DOUBLE exponential of that
-- size, and the unscaled route below spends only one of the two.
nestCap-sight-scaled≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  suc (sizeᵉ e) * suc ((2 ^ syncSizeᵉ e + 2) * nestCapAt e sl 0)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl 0))
nestCap-sight-scaled≤exp e sl = ≤-trans (*-mono-≤ 1+z≤S hstep) big
  where
  S = Caps.cSize (capsAt e sl 0)
  C = nestCapAt e sl 0
  K = syncSizeᵉ e
  8≤S : 8 ≤ S
  8≤S = 8≤capsAt-size e sl 0
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 8≤S
  1+z≤S : suc (sizeᵉ e) ≤ S
  1+z≤S = ≤-trans (≤-trans (n≤1+n (suc (sizeᵉ e))) (m≤m+n (2 + sizeᵉ e) _))
                  (capsAt-base-size e sl 0)
  C≤S : C ≤ S
  C≤S = ≤-trans (≤-reflexive (nestCapAt-0 e sl)) (nestUnit≤size e sl 0)
  1≤C : 1 ≤ C
  1≤C = subst (1 ≤_) (sym (nestCapAt-0 e sl)) (s≤s z≤n)
  2^K≤2^S : 2 ^ K ≤ 2 ^ S
  2^K≤2^S =
    ^-monoʳ-≤ 2 (≤-trans (syncSize≤sizeᵉ e) (≤-trans (n≤1+n (sizeᵉ e)) 1+z≤S))
  eq3 : (2 ^ K + 2) * C + C ≡ (2 ^ K + 3) * C
  eq3 = solve 2 (λ k c → (k :+ con 2) :* c :+ c := (k :+ con 3) :* c)
              refl (2 ^ K) C
  hstep : suc ((2 ^ K + 2) * C) ≤ (2 ^ S + 3) * S
  hstep = ≤-trans (≤-trans (≤-reflexive (+-comm 1 ((2 ^ K + 2) * C)))
                           (+-monoʳ-≤ ((2 ^ K + 2) * C) 1≤C))
                  (≤-trans (≤-reflexive eq3)
                           (*-mono-≤ (+-monoˡ-≤ 3 2^K≤2^S) C≤S))
  1≤2^S : 1 ≤ 2 ^ S
  1≤2^S = 1≤pow 1 S
  four′ : 4 * (2 ^ S) ≡ 2 ^ S + 3 * (2 ^ S)
  four′ = solve 1 (λ p → con 4 :* p := p :+ con 3 :* p) refl (2 ^ S)
  h4 : 2 ^ S + 3 ≤ 4 * (2 ^ S)
  h4 = ≤-trans (+-monoʳ-≤ (2 ^ S)
                 (≤-trans (≤-reflexive (sym (*-identityʳ 3)))
                          (*-monoʳ-≤ 3 1≤2^S)))
               (≤-reflexive (sym four′))
  shape : S * ((4 * (2 ^ S)) * S) ≡ (4 * (S * S)) * (2 ^ S)
  shape = solve 2 (λ s p → s :* ((con 4 :* p) :* s) := (con 4 :* (s :* s)) :* p)
                refl S (2 ^ S)
  S≤SS : S ≤ S * S
  S≤SS = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤S)
  fourEq : (S * S + S * S) + (S * S + S * S) ≡ 4 * (S * S)
  fourEq = solve 1 (λ x → (x :+ x) :+ (x :+ x) := con 4 :* x) refl (S * S)
  S+S≤2^S : S + S ≤ 2 ^ S
  S+S≤2^S = ≤-trans (≤-trans (+-mono-≤ S≤SS S≤SS)
                             (≤-trans (m≤m+n (S * S + S * S) (S * S + S * S))
                                      (≤-reflexive fourEq)))
                    (sq4≤2^ S 8≤S)
  big : S * ((2 ^ S + 3) * S) ≤ 2 ^ (2 ^ S)
  big = ≤-trans (*-monoʳ-≤ S (*-monoˡ-≤ S h4))
        (≤-trans (≤-reflexive shape)
        (≤-trans (*-monoˡ-≤ (2 ^ S) (sq4≤2^ S 8≤S))
        (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 S S)))
                 (^-monoʳ-≤ 2 S+S≤2^S))))

-- AND ALL THREE OF THE CEILING'S SUMMANDS ARE THE SAME CAP.  The
-- arrival's nesting is held under it by the caller's premise, the
-- store's by the nesting invariant, and the wrap unit IS the cap at
-- instant zero -- so the sighted sum is three readings of one number
-- and the ceiling collapses to a multiple of it.  That collapse is the
-- whole of what the run-side hypotheses buy.
sight-nest≤exp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ)
  (sched : Sched Γ) (st : EvalSt e) →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a))
            (storeNestMax sched st) (nestUnit e sl)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
sight-nest≤exp {e = e} sl id a sched st hnest hval =
  ≤-trans (*-monoʳ-≤ (suc (sizeᵉ e)) (s≤s sum≤3C))
          (nestCap-sight≤exp e sl id)
  where
  C = nestCapAt e sl id
  hu : nestUnit e sl ≤ C
  hu = ≤-trans (≤-reflexive (sym (nestCapAt-0 e sl))) (nestCap-mono₀ e sl id)
  eq : C + C + C ≡ 3 * C
  eq = solve 1 (λ c → c :+ c :+ c := con 3 :* c) refl C
  sum≤3C : nestDᵛ (arrTy a) (arrVal a) + storeNestMax sched st + nestUnit e sl
             ≤ 3 * C
  sum≤3C =
    ≤-trans (+-mono-≤ (+-mono-≤ hval (nestOK?-store e sl id sched st hnest)) hu)
            (≤-reflexive eq)

-- AND THE FUEL HAS THAT ROOM, so the comparison the depth face owes
-- the height is assembled rather than asserted.  The caps recurrence
-- steps by a blowup the fuel itself drives and `blowH` is what the
-- fuel climbs by, so the size at an instant and the fuel at that
-- instant are one quantity read once each -- with two exponentials
-- between them, bought by the single spare registration the tower
-- bracket leaves in the pooled walk.
sighted-nest≤capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ)
  (sched : Sched Γ) (st : EvalSt e) →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a))
            (storeNestMax sched st) (nestUnit e sl)
    ≤ capsH e sl id
sighted-nest≤capsH {e = e} sl id a sched st hnest hval =
  ≤-trans (sight-nest≤exp sl id a sched st hnest hval)
          (capsAt-exp≤capsH e sl id)

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
cascade-depth-capsH sl id a nextId sched st hsl hcaps hnest hval hsz =
  ≤-trans (cascade-depth-sighted sl id a nextId sched st hsl hcaps)
          (sighted-nest≤capsH sl id a sched st hnest hval)

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
       × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
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

