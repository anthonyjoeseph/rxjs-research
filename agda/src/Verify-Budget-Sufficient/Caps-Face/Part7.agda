-- Verify-Budget-Sufficient.Caps-Face.Part7
-- thruOuter-face … reach-via-size-absurd
module Verify-Budget-Sufficient.Caps-Face.Part7 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; *-identityˡ; ^-distribˡ-+-*; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤; ≤-trans;
  ≤-refl; ≤-reflexive; +-identityʳ; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; *-mono-≤; *-monoʳ-≤;
  +-monoʳ-≤; +-monoˡ-≤; +-assoc; ⊔-lub; m≤m⊔n; m≤n⊔m; +-mono-≤; ⊔-mono-≤; ⊔-identityʳ; m⊔n≤m+n;
  *-distribˡ-+; *-distribʳ-+; m≤m*n; ^-*-assoc; *-comm)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length; map; foldr)
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

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted)
open import Rx.Exp       using (_×ᵗ_; obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵛ; Fn; applyFn)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-def; nestFac-monoS; 1≤nestFac; nestU; nestU-mono; nestU-room)
open import Verify-Budget-Sufficient.Nest-Walk using
  (foldPath-nodes; nodesMax; burstsOK; capsWalkOK; fac-hoist; one-pow; FaceOK; faceAt;
  faceHere; pathSz?-lvl)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade; depthChain; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (pathSzSum-cap; deliverLen; deliverNestD; deliverNestF; 1≤deliverNestF; chainsLenSum;
  chainsDelLen; chainsDelNestD; chainsDelNestF; 1≤chainsDelNestF; chainsDelSzSum;
  chainsDelNestF≡; chainsDelLen-chains; chainsDelNestD-chains; chainsDelSzSum-chains;
  chainsNestF≤)
open import Verify-Budget-Sufficient.Fan-Caps using
  (fanLen; fanSq; delSize; delSq; delSq-monoᶜ; delSize-monoᶜ; delSize-cap; delSq-cap; delSize-def; delSq-def)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; chainsNestF; chainsSzSum; pathNestD; pathNestF; 1≤pathNestF; 1≤chainsNestF;
  nest-telescope; nest-scale; pow-distrib-*; storeNestMax; nestCapAt; nestOK?; nestOK?-latch;
  nestOK?-store; nest-sum-fac; nestFacAt; nestFacAt-def; 1≤nestFacAt; nest-inflate;
  storeNest-latch; realWidAt; realWidAt-def; nestIncAt; nestIncAt-def; size≤nestIncAt;
  16≤nestFacAt;
  m≤m^burst; nestBurstAt; 1≤nestBurstAt; nestUnit; slotsNestSum; liveNest; nodeNest;
  regsNestMax)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; scanVals; RegId; Chain; scan-st; take-st; mergeAll-st;
  switch-st; exhaust-st; setNode; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f; take-f;
  from-inner; thru-outer; cascadeLatch; cascadeFinish; takeDispatch; arrSource; chainsOf;
  chainsGo; cascadeGo; Path; arrTy; stepFrame; subscribeInner; mergeAllᵒ; switchᵒ; exhaustᵒ;
  thruWalk; thruWrap; innerFinish; innerReact; aliveThroughᶠ; cascade; sameSource; regAt;
  fLvlD; lvls; sLvlD; chainStep; budgetAt; arrTick)
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
  (delivN; foldPath-sink-N; shareGo-cons-N; shareGo-skip-N)
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsAt-suc-full;
  capsAt-⊑-suc; capsH; cDel; _⊑ᶜ_; cDel-body; dWalkᶜ-mono; frameStep; frameStep-0;
  frameStep-mono-j; frameStep-reg-mono; iterSize-mono-count; lvls-mono; size≤sizeCount;
  sizeCount; sizeCount-body)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; reach-reset; ∧-true)
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
  (capsOK?; capsOK?-mono; eventCaps?; frameSz?; n≤capsAt-size; pathSz?; pathSz?-widen; regsSz?;
  slotsCaps?; valCaps?; widNode)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (face-charge; face-charge1; face-vals; mapFrame-caps; scanFrame-caps;
   scanVals-len; stepFrame-face-zero; takeDispatch-len; valsCaps?-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (foldPath-slots; capsOK?-count; capsOK?-delivered; capsOK?-nodeSz; capsOK?-nodeWid;
   capsOK?-regs; capsOK?-setNode; dropSweep-caps; face-lift; frameBud;
   FrameFace; lookupNode-caps; pathSz?-len; pathSz?-tail; shareLatch-caps;
   slotsCaps?-capsAt; takeDispatch-caps; valsCaps?; valsCaps?-lvl; walkOK;
   walkOK-finish)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (frameStep-⊑-+; valCaps?-size; valCaps?-wid)
open import Decide using (T-to; T⇒≡true; ∧-intro)

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
  (c : Caps) (sl : Slots Γ) (d : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainCapsOK {n = n} {e = e} c sl d id a path sched st =
  capsWalkOK c sl d 0 (budgetAt e (Sched.slots sched) id) n id (arrTick a) path
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
  (c : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c →
  chainBurstOK W id a path sched st →
  chainCapsOK c sl d id a path sched st →
  depthChain id a path sched st ≤ d →
  pathSz? (Caps.cSize c) path ≡ true →
  ⦃ _ : FaceOK c sl ⦄ →
  let r = chainStep id a path sched st in
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ nestFac (Caps.cSize c′) W ^ deliverLen n c path
      * (deliverNestF n c path ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + W * (nestDᵛ (arrTy a) (arrVal a) + deliverNestD n c path
                   + suc (deliverLen n c path) * nestU (delSq n c′) (nestUnit e sl)))))
chainStep-nodes {n = n} {e = e} c d W sl id a path sched st hsl 1≤W 1≤S hb hc hdp hpz =
  proj₁ FP ,
  proj₁ (proj₂ FP) ,
  ≤-trans (proj₂ (proj₂ FP))
    (*-monoʳ-≤ (nestFac (Caps.cSize c′) W ^ deliverLen n c path)
    (*-monoʳ-≤ (deliverNestF n c path ^ W)
      (≤-trans (+-monoˡ-≤ (W * (deliverNestD n c path + U))
                          (≤-trans (⊔-mono-≤ (≤-refl {nodesMax st})
                                             (≤-reflexive (⊔-identityʳ V)))
                                   (m⊔n≤m+n (nodesMax st) V)))
      (≤-trans (≤-reflexive (+-assoc (nodesMax st) V (W * (deliverNestD n c path + U))))
               (+-monoʳ-≤ (nodesMax st) spread)))))
  where
  FP = foldPath-nodes c d W sl 0 (budgetAt e (Sched.slots sched) id) n id
         (arrTick a) (arrSource a) path (arrVal a ∷ [])
         (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
         (Arrival.isLast a) sched st hsl 1≤W 1≤S hb hc hdp
         (pathSz?-lvl c 0 path (FaceOK.fSize faceHere) hpz)
  c′ = frameStep (proj₁ FP) c
  V = nestDᵛ (arrTy a) (arrVal a)
  U = suc (deliverLen n c path) * nestU (delSq n c′) (nestUnit e sl)

  spread : V + W * (deliverNestD n c path + U) ≤ W * (V + deliverNestD n c path + U)
  spread =
    ≤-trans (+-monoˡ-≤ (W * (deliverNestD n c path + U)) (nest-inflate W V 1≤W))
      (≤-trans (≤-reflexive (sym (*-distribˡ-+ W V (deliverNestD n c path + U))))
               (≤-reflexive (cong (W *_) (sym (+-assoc V (deliverNestD n c path) U)))))

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
  (cp : Caps) (sl : Slots Γ) (d : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) → Set
chainsCapsOK cp sl d a nextId []               sched st = ⊤
chainsCapsOK cp sl d a nextId ((rid , c) ∷ chains) sched st =
  if any (_≡ᵇ rid) (EvalSt.cancelled st)
  then chainsCapsOK cp sl d a nextId chains sched st
  else (chainCapsOK cp sl d nextId a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
        × chainsCapsOK cp sl d a nextId chains
            (proj₁ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st }))))
            (proj₂ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st })))))

cascadeGo-nodes-chains : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cp : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize cp →
  chainsBurstOK W a nextId chains sched st →
  chainsCapsOK cp sl d a nextId chains sched st →
  depthCascade a nextId chains sched st ≤ d →
  all (λ rc → pathSz? (Caps.cSize cp) (proj₂ rc)) chains ≡ true →
  ⦃ _ : FaceOK cp sl ⦄ →
  let r = cascadeGo a nextId chains sched st in
  Σ ℕ λ j →
  let cp′ = frameStep j cp in
  (j ≤ sizeCount cp d ⊔ Caps.cSize cp)
  × (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ nestFac (Caps.cSize cp′) W ^ chainsDelLen n cp chains
      * (chainsDelNestF n cp chains ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + length chains
                * (W * (nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n cp chains
                        + suc (chainsDelLen n cp chains) * nestU (delSq n cp′) (nestUnit e sl))))))
cascadeGo-nodes-chains cp d W sl a nextId [] sched st hsl 1≤W 1≤S hb hc hdp hpz =
  0 , z≤n ,
  ≤-trans (≤-trans (m≤m+n _ 0) (one-pow W _)) (≤-reflexive (sym (*-identityˡ _)))
cascadeGo-nodes-chains {n = n} {e = e} cp d W sl a nextId ((rid , c) ∷ chains) sched st hsl 1≤W 1≤S hb hc hdp hpz
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | hb | hc
... | true | hb′ | hc′ =
  proj₁ TL ,
  proj₁ (proj₂ TL) ,
  ≤-trans (proj₂ (proj₂ TL))
    (≤-trans (*-monoʳ-≤ (R ^ K)
      (≤-trans (*-monoʳ-≤ (G ^ W) (+-monoʳ-≤ M grow))
               (≤-trans (nest-scale (deliverNestF n cp c ^ W) (G ^ W)
                           (M + suc (length chains) * (W * (V + C′ + U)))
                           (1≤pow≤ (deliverNestF n cp c) W (1≤deliverNestF n cp c)))
                        (≤-reflexive
                          (cong (_* (M + suc (length chains) * (W * (V + C′ + U))))
                                (sym (pow-distrib-* W (deliverNestF n cp c) G)))))))
    (≤-trans (nest-scale (R ^ deliverLen n cp c) (R ^ K) Xc (1≤pow≤ R (deliverLen n cp c) 1≤R))
             (≤-reflexive (cong (_* Xc) (sym (^-distribˡ-+-* R (deliverLen n cp c) K))))))
  where
  TL = cascadeGo-nodes-chains cp d W sl a nextId chains sched st hsl 1≤W 1≤S hb′ hc′
         (lub3-l (depthCascade a nextId chains sched st)
                 (depthChain nextId a c sched
                    (record st { delivered = rid ∷ EvalSt.delivered st }))
                 (depthCascade a nextId chains
                    (proj₁ (proj₂ (chainStep nextId a c sched
                       (record st { delivered = rid ∷ EvalSt.delivered st }))))
                    (proj₂ (proj₂ (chainStep nextId a c sched
                       (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
         (proj₂ (∧-true _ _ hpz))
  cp′ = frameStep (proj₁ TL) cp
  R  = nestFac (Caps.cSize cp′) W
  1≤R : 1 ≤ R
  1≤R = 1≤nestFac (Caps.cSize cp′) W
  K  = chainsDelLen n cp chains
  M  = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V  = nestDᵛ (arrTy a) (arrVal a)
  C  = chainsDelNestD n cp chains
  C′ = deliverNestD n cp c ⊔ C
  Uz = nestU (delSq n cp′) (nestUnit e sl)
  U  = suc (deliverLen n cp c + K) * Uz
  Uₜ = suc K * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (deliverLen n cp c)))
  G  = chainsDelNestF n cp chains
  Xc = (deliverNestF n cp c * G) ^ W * (M + suc (length chains) * (W * (V + C′ + U)))
  grow : length chains * (W * (V + C + Uₜ)) ≤ suc (length chains) * (W * (V + C′ + U))
  grow = *-mono-≤ (n≤1+n (length chains))
                  (*-monoʳ-≤ W
                    (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (deliverNestD n cp c) C)) Uₜ≤U))
... | false | hb′ | hc′ =
  jt ,
  ⊔-lub (proj₁ (proj₂ TAILr)) (proj₁ (proj₂ HEADr)) ,
  ≤-trans TAILw
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (*-monoʳ-≤ (G ^ W)
                        (+-monoˡ-≤ (length chains * (W * (V + C + Uₜ)))
                                   HEADw)))
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (fac-hoist (R ^ deliverLen n cp c) (G ^ W) A Z (1≤pow≤ R (deliverLen n cp c) 1≤R)))
          (≤-trans (≤-reflexive (sym (*-assoc (R ^ K) (R ^ deliverLen n cp c) Y)))
          (≤-trans (≤-reflexive
                      (cong (_* Y) (trans (*-comm (R ^ K) (R ^ deliverLen n cp c))
                                          (sym (^-distribˡ-+-* R (deliverLen n cp c) K)))))
                   (*-monoʳ-≤ (R ^ (deliverLen n cp c + K))
          (≤-trans (nest-telescope (deliverNestF n cp c ^ W) (G ^ W) M
                                   (W * (V + deliverNestD n cp c + Uc))
                                   (length chains * (W * (V + C + Uₜ)))
                                   (1≤pow≤ (deliverNestF n cp c) W (1≤deliverNestF n cp c)))
                   (≤-trans (≤-reflexive
                               (cong (_* (M + (W * (V + deliverNestD n cp c + Uc)
                                               + length chains * (W * (V + C + Uₜ)))))
                                     (sym (pow-distrib-* W (deliverNestF n cp c) G))))
                     (*-monoʳ-≤ ((deliverNestF n cp c * G) ^ W)
                       (+-monoʳ-≤ M
                         (+-mono-≤ (*-monoʳ-≤ W
                                     (+-mono-≤ (+-monoʳ-≤ V (m≤m⊔n (deliverNestD n cp c) C)) Uc≤U))
                                   (*-monoʳ-≤ (length chains)
                                     (*-monoʳ-≤ W
                                       (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (deliverNestD n cp c) C))
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
  HEADr = chainStep-nodes cp d W sl nextId a c sched st′ hsl
            1≤W 1≤S (proj₁ hb′) (proj₁ hc′)
            (lub3-m (depthCascade a nextId chains sched st)
                    (depthChain nextId a c sched st′)
                    (depthCascade a nextId chains sd₁ st₁) hdp)
            (proj₁ (∧-true _ _ hpz))
  TAILr = cascadeGo-nodes-chains cp d W sl a nextId chains sd₁ st₁
            (trans (chainStep-slots nextId a c sched st′) hsl) 1≤W 1≤S
            (proj₂ hb′) (proj₂ hc′)
            (lub3-r (depthCascade a nextId chains sched st)
                    (depthChain nextId a c sched st′)
                    (depthCascade a nextId chains sd₁ st₁) hdp)
            (proj₂ (∧-true _ _ hpz))
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
  C   = chainsDelNestD n cp chains
  Uz  = nestU (delSq n cp′) (nestUnit e sl)
  G   = chainsDelNestF n cp chains
  R   = nestFac (Caps.cSize cp′) W
  1≤R : 1 ≤ R
  1≤R = 1≤nestFac (Caps.cSize cp′) W
  K   = chainsDelLen n cp chains

  HEADw = ≤-trans (proj₂ (proj₂ HEADr))
            (*-mono-≤ (^-monoˡ-≤ (deliverLen n cp c) (nestFac-monoS sizeₕ W))
              (*-monoʳ-≤ (deliverNestF n cp c ^ W)
                (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st′))
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a) + deliverNestD n cp c)
                      (*-monoʳ-≤ (suc (deliverLen n cp c))
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
  U   = suc (deliverLen n cp c + K) * Uz
  Uₜ  = suc K * Uz
  Uc  = suc (deliverLen n cp c) * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (deliverLen n cp c)))
  Uc≤U : Uc ≤ U
  Uc≤U = *-monoˡ-≤ Uz (s≤s (m≤m+n (deliverLen n cp c) K))
  A   = deliverNestF n cp c ^ W * (M + W * (V + deliverNestD n cp c + Uc))
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
  chainsDelLen n (capsAt e sl id) chains
    ≤ realWidAt e sl id * delSize n (capsAt e sl id) →
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
      ^ chainsDelLen n (capsAt e sl id) chains
    * chainsDelNestF n (capsAt e sl id) chains ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) sl (capsH e sl id) a nextId chains sched st →
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
                                     ^ chainsDelLen n (capsAt e sl id) chains)
                                   (chainsDelNestF n (capsAt e sl id) chains
                                     ^ nestBurstAt e sl id) _))))
    (*-mono-≤ hfac
      (+-mono-≤ nodes≤store
        (≤-trans (*-mono-≤ hcnt
                    (*-monoʳ-≤ (nestBurstAt e sl id)
                      (≤-trans (+-monoˡ-≤ (suc (chainsDelLen n (capsAt e sl id) chains) * UU)
                                          depth≤)
                               (*-monoˡ-≤ UU (s≤s (s≤s hls))))))
                 (≤-reflexive (sym (nestIncAt-def e sl id))))))
  where

  SS = delSq n (capsAt e sl (suc id))
  UU = nestU SS (nestUnit e sl)

  CH = cascadeGo-nodes-chains (capsAt e sl id) (capsH e sl id) (nestBurstAt e sl id)
         sl a nextId chains sched st hsl (1≤nestBurstAt e sl id)
         (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)) hburst hcw hdep hpz
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

  lift = *-mono-≤ (^-monoˡ-≤ (chainsDelLen n (capsAt e sl id) chains)
                     (nestFac-monoS (proj₁ lift-⊑) (nestBurstAt e sl id)))
           (*-monoʳ-≤ (chainsDelNestF n (capsAt e sl id) chains ^ nestBurstAt e sl id)
             (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
               (*-monoʳ-≤ (length chains)
                 (*-monoʳ-≤ (nestBurstAt e sl id)
                   (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a)
                                + chainsDelNestD n (capsAt e sl id) chains)
                     (*-monoʳ-≤ (suc (chainsDelLen n (capsAt e sl id) chains))
                       (nestU-mono (delSq n (frameStep (proj₁ CH) (capsAt e sl id)))
                                   SS (nestUnit e sl)
                         (delSq-monoᶜ n (frameStep (proj₁ CH) (capsAt e sl id))
                                      (capsAt e sl (suc id))
                                      (proj₁ lift-⊑) (proj₂ (proj₂ lift-⊑))))))))))

  -- the walk charges its depth in the delivery currency and the
  -- selection bound is a path fact, so the fan allowance is what sits
  -- between them -- and the unit is priced at the delivery square
  -- precisely so it has room for one
  depth≤id : nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n (capsAt e sl id) chains
               ≤ nestU (delSq n (capsAt e sl id)) (nestUnit e sl)
  depth≤id =
    ≤-trans (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a))
                       (chainsDelNestD-chains n (capsAt e sl id) chains))
      (≤-trans (≤-reflexive (sym (+-assoc (nestDᵛ (arrTy a) (arrVal a))
                                          (chainsNestD chains)
                                          (fanSq n (capsAt e sl id)))))
        (≤-trans (+-monoˡ-≤ (fanSq n (capsAt e sl id)) hchg)
                 (nestU-room (delSq n (capsAt e sl id)) (nestUnit e sl)
                             (fanSq n (capsAt e sl id))
                             (≤-trans (s≤s z≤n) ≤-refl)
                             (≤-trans (m≤n+m (fanSq n (capsAt e sl id))
                                             (Caps.cSize (capsAt e sl id)
                                                * Caps.cSize (capsAt e sl id)))
                                      (delSq-cap n (capsAt e sl id)
                                                 (1≤capsAt-reg e sl id))))))

  depth≤ : nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n (capsAt e sl id) chains ≤ UU
  depth≤ =
    ≤-trans depth≤id
            (nestU-mono (delSq n (capsAt e sl id)) SS (nestUnit e sl)
              (delSq-monoᶜ n (capsAt e sl id) (capsAt e sl (suc id))
                (proj₁ (capsAt-⊑-suc e sl id))
                (proj₂ (proj₂ (capsAt-⊑-suc e sl id)))))


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
  chainsDelLen n (capsAt e sl id) chains
    ≤ realWidAt e sl id * delSize n (capsAt e sl id) →
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl id) chains
    * chainsDelNestF n (capsAt e sl id) chains ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) sl (capsH e sl id) a nextId chains sched st →
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
    ≤-trans (chainsNestF≤ n (capsAt e sl id) chains)
      (≤-trans (m≤m^burst e sl id (chainsDelNestF n (capsAt e sl id) chains)
                          (1≤chainsDelNestF n (capsAt e sl id) chains))
               (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ _)))
                                 (*-monoˡ-≤ _ (1≤pow≤ (nestFac (Caps.cSize (capsAt e sl (suc id)))
                                                               (nestBurstAt e sl id))
                                                      (chainsDelLen n (capsAt e sl id) chains)
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
  chainsDelLen n (capsAt e sl id) (chainsOf a st)
    ≤ realWidAt e sl id * delSize n (capsAt e sl id)
arr-chains-len-sum {n = n} {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsDelLen-chains n C (chainsOf a st))
    (≤-trans (+-mono-≤ (≤-trans (chainsLenSum-bound B (chainsOf a st)
                                   (chainsGo-sz B a (EvalSt.registry st) regsz))
                                (*-monoˡ-≤ B wid))
                       (*-monoˡ-≤ (fanLen n C) wid))
             (≤-reflexive (trans (sym (*-distribˡ-+ (realWidAt e sl id) B (fanLen n C)))
                                 (cong (realWidAt e sl id *_) (sym (delSize-def n C))))))
  where
  C = capsAt e sl id
  B = Caps.cSize C
  wid = chains-count-width sl id a sched st hcaps
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs C sched st hcaps

arr-chains-sz-sum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsDelSzSum n (capsAt e sl id) (chainsOf a st)
    ≤ realWidAt e sl id * delSq n (capsAt e sl id)
arr-chains-sz-sum {n = n} {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsDelSzSum-chains n C (chainsOf a st))
    (≤-trans (+-mono-≤ (≤-trans (chainsSzSum-bound B (chainsOf a st)
                                   (chainsGo-sz B a (EvalSt.registry st) regsz))
                                (*-monoˡ-≤ (B * B) wid))
                       (*-monoˡ-≤ (fanSq n C) wid))
    (≤-trans (≤-reflexive (sym (*-distribˡ-+ (realWidAt e sl id) (B * B) (fanSq n C))))
             (*-monoʳ-≤ (realWidAt e sl id) (delSq-cap n C (1≤capsAt-reg e sl id)))))
  where
  C = capsAt e sl id
  B = Caps.cSize C
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
      ^ chainsDelLen n (capsAt e sl id) (chainsOf a st)
    * chainsDelNestF n (capsAt e sl id) (chainsOf a st) ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id
arr-chains-nest-fac {n = n} {e = e} sl id a sched st hsl hcaps hnest =
  ≤-trans (≤-reflexive
             (cong₂ _*_ (trans (cong (_^ L)
                                 (trans (nestFac-def B K)
                                   (trans (cong (_^ B) (^-*-assoc 2 B (suc K)))
                                          (^-*-assoc 2 (B * suc K) B))))
                               (^-*-assoc 2 (B * suc K * B) L))
                        (trans (cong (_^ K) (chainsDelNestF≡ n C₀ (chainsOf a st)))
                               (^-*-assoc 2 S K))))
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (B * suc K * B * L) (S * K))))
      (≤-trans (^-monoʳ-≤ 2 expo)
               (≤-reflexive (sym (nestFacAt-def e sl id)))))
  where
  C₀ = capsAt e sl id
  C = capsAt e sl (suc id)
  B = Caps.cSize C
  K = nestBurstAt e sl id
  L = chainsDelLen n C₀ (chainsOf a st)
  S = chainsDelSzSum n C₀ (chainsOf a st)
  D = delSize n C
  X = realWidAt e sl id * delSq n C
  Xʹ = suc D * X

  -- the selection's own two measures are read at the instant's ENTRY
  -- cap -- they count what the registry already holds -- while the
  -- factor is priced at the EXIT cap, so each crosses on the
  -- recurrence's own widening
  D₀≤D : delSize n C₀ ≤ D
  D₀≤D = delSize-monoᶜ n C₀ C (proj₁ (capsAt-⊑-suc e sl id))
                              (proj₂ (proj₂ (capsAt-⊑-suc e sl id)))

  X≤Xʹ : X ≤ Xʹ
  X≤Xʹ = m≤m+n X (D * X)

  -- the length half lands on the fresh `suc`, the size half on the
  -- burst term the factor already had
  lenX : B * L ≤ X
  lenX =
    ≤-trans (*-mono-≤ (delSize-cap n C)
                      (≤-trans (arr-chains-len-sum sl id a sched st hsl hcaps)
                               (*-monoʳ-≤ (realWidAt e sl id) D₀≤D)))
            (≤-reflexive
              (trans (sym (*-assoc D (realWidAt e sl id) D))
                     (trans (cong (_* D) (*-comm D (realWidAt e sl id)))
                            (trans (*-assoc (realWidAt e sl id) D D)
                                   (cong (realWidAt e sl id *_) (sym (delSq-def n C)))))))

  szX : S * K ≤ K * Xʹ
  szX = ≤-trans (≤-reflexive (*-comm S K))
                (*-monoʳ-≤ K (≤-trans (arr-chains-sz-sum sl id a sched st hsl hcaps)
                               (≤-trans (*-monoʳ-≤ (realWidAt e sl id)
                                          (delSq-monoᶜ n C₀ C
                                            (proj₁ (capsAt-⊑-suc e sl id))
                                            (proj₂ (proj₂ (capsAt-⊑-suc e sl id)))))
                                        X≤Xʹ)))

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
--
-- PROBED: `Probed.Chain-Caps-Flat` measures what that asks for.  The
--   cap itself cannot be instantiated -- it spends `capsH`, which the
--   harness's own quarantine records as divergent in COMPILED code at
--   the smallest arguments -- so the rows report the SMALLEST concrete
--   cap each state fits, before the cascade and after it, one component
--   at a time, over three families.  Only the SIZE ever moves: the
--   width and the registry come back at or below where they started on
--   every row, so two of the three conjuncts are preservation outright
--   and the slack claim is about one component.  Not covered: the cap's
--   own value, and therefore the verdict itself; the `valCaps?`
--   conjunct past the first frame, since a mid-walk value list is not
--   addressable from outside the fold; and the sink arm's
--   registry-versus-unit conjunct, which no row addresses.
postulate
  arr-chain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    chainCapsOK (capsAt e sl id) sl (capsH e sl id) nextId a path sched st

  chainStep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    capsOK? (capsAt e sl id)
      (proj₁ (proj₂ (chainStep nextId a path sched st)))
      (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true

arr-chains-caps-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsCapsOK (capsAt e sl id) sl (capsH e sl id) a nextId chains sched st
arr-chains-caps-go sl id a nextId [] sched st sleq cok = tt
arr-chains-caps-go sl id a nextId ((rid , path) ∷ chains) sched st sleq cok
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = arr-chains-caps-go sl id a nextId chains sched st sleq cok
... | false =
      arr-chain-caps sl id a nextId path sched st′ sleq cok
    , arr-chains-caps-go sl id a nextId chains
        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
        (proj₂ (proj₂ (chainStep nextId a path sched st′)))
        (trans (chainStep-slots nextId a path sched st′) sleq)
        (chainStep-caps sl id a nextId path sched st′ sleq cok)
  where st′ = record st { delivered = rid ∷ EvalSt.delivered st }

arr-chains-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsCapsOK (capsAt e sl id) sl (capsH e sl id) a nextId (chainsOf a st) sched
    (cascadeLatch a st)
arr-chains-caps {e = e} sl id a nextId sched st sleq cok =
  arr-chains-caps-go sl id a nextId (chainsOf a st) sched (cascadeLatch a st)
    sleq (cascadeLatch-caps (capsAt e sl id) a sched st cok)

-- ONE CASCADE'S DESCENT AGAINST A COMPUTABLE CEILING, which is what
-- the statement below is now read off.  Every term here computes --
-- the arrival's nesting, the chains' nesting, the store the cascade
-- arrives at, and the arrival's own size -- so a row can print a
-- verdict on this one, which is the whole reason it is stated apart
-- from the statement it carries.
--
-- THE SIXTEEN IS HEADROOM, NOT A MEASUREMENT.  A power of two sits
-- under the sealed factor at any numeral, since that factor's
-- exponent is a squared burst successor times a product of quantities
-- already proven positive; sixteen is several times the largest least
-- factor any sweep has reported, which is where a bound that must not
-- be re-tuned every time the evaluator moves wants to sit.
--
-- DEAD ROUTE: the same form at a factor of ONE is false at the
--   evaluator.  That is the reading the factor's mere POSITIVITY
--   licenses, and `Harness.Main`'s series Y prints the least factor it
--   actually needs: two across the fan and width families at every
--   depth and width swept, three on the unbounded ones, one only where
--   the store already dominates the descent.  A consumer reaching for
--   the positivity rather than for the exponent therefore gets a
--   refuted statement, and the exponent is what makes any larger
--   numeral available.
--
-- PROBED: `Probed.Cascade-Nest-Flat` pins the conclusion by `refl` at
--   three families -- the parked drain read one instant in, the skip
--   branch whose selection outruns its delivery, and a family that
--   delivers on every chain it selects -- each with its chain count
--   and its descent pinned beside the verdict, so no row is reading an
--   empty selection.  NOT covered: any PREMISE, all of which compare
--   against a sealed cap and therefore do not reduce; and any state a
--   root subscribe does not reach.
postulate
  cascade-nest-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
    depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
      ≤ nestDᵛ (arrTy a) (arrVal a)
        + chainsNestD (chainsOf a st)
        + 16 * (storeNestMax sched (cascadeLatch a st)
                + sizeᵛ (arrTy a) (arrVal a))


-- ONE CASCADE'S DESCENT AGAINST THE INSTANT'S OWN GRANT, and it is
-- primitive rather than assembled -- which is a change, and the reason
-- is a CYCLE the walk's level device made visible.
--
-- The route that used to assemble this read the descent's depth off
-- the store the walk PRODUCES and then bounded that store by the
-- instant's grant.  That composition is no longer
-- available, because the store bound now needs a depth bound of its
-- own: a walk widens the caps as it descends, the caps recurrence says
-- the widening ends at the instant's EXIT cap, and the per-store depth
-- unit is therefore priced there -- so the increment's own unit reads
-- `capsAt (suc id)`, and the level that gets it there is bounded by
-- `sizeCount (capsAt id) (capsH id)`, which is exactly a depth premise
-- `depthCascade ≤ capsH`.  Assembling depth from store then requires
-- store from depth.
--
-- The break is to state the depth bound outright rather than through
-- the store, which is what the two sides were always saying anyway:
-- the old assembly rested on a postulated store bound throughout, so
-- nothing that was proven has become assumed.  The delivery side's
-- `cascade-depth-capsH` still assembles FROM this, so the tie back to
-- the syntactic ceiling is unchanged.
--
-- THE FORM IT IS READ OFF IS COMPUTABLE, AND THAT IS WHERE THE RISK
-- NOW SITS.  This statement's right-hand side reads two sealed
-- families, so no row prints a verdict on it directly; the leaf above
-- replaces both by quantities that compute, and the two proven
-- inequalities that carry it back -- a power of two under the factor,
-- the arrival's own size under the increment -- are what this body
-- spends.  So the instantiable statement and the consumable one are
-- separated, and only the first has to be probed.
--
-- RECOVERY: git show ae75251:agda/src/Verify-Budget-Sufficient/Caps-Face/Part7.agda
--   restores the store-mediated assembly and the produced-store
--   statement it spent, for whichever side of the cycle is broken
--   another way.  `git show
--   ae75251:agda/evidence/probed/Probed/Cascade-Nest-Store.agda`
--   restores the instantiation harness that pinned it -- three
--   arrivals reaching the bounded drain and the skip branch -- and
--   `git show ae75251:agda/src/Harness/Main.agda` the prefix sweep
--   that asked whether the store growth saturates.  Neither transfers
--   as it stands: this statement's right-hand side reads two sealed
--   families, so no row prints a verdict on it, only on the forms
--   underneath it.
cascade-nest-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ nestDᵛ (arrTy a) (arrVal a)
      + chainsNestD (chainsOf a st)
      + nestFacAt e sl id
        * (storeNestMax sched (cascadeLatch a st)
           + nestIncAt e sl id)
cascade-nest-compositional {e = e} sl id a nextId sched st slEq cok nok harr hsz =
  ≤-trans (cascade-nest-flat sl id a nextId sched st slEq cok nok harr hsz)
          (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a) + chainsNestD (chainsOf a st))
            (*-mono-≤ (16≤nestFacAt e sl id)
              (+-monoʳ-≤ (storeNestMax sched (cascadeLatch a st))
                (≤-trans hsz (size≤nestIncAt e sl id)))))


-- A CASCADE'S CHAINS ARE A SELECTION FROM THE REGISTRY, which the store
-- measure charges, so this premise does not have to be threaded from the
-- caller: `chainsOf` filters the registry by source and type, and a
-- `⊔`-fold dominates any sublist of what it folds.  The arriving
-- PAYLOAD is the one quantity that genuinely is not in the state — the
-- schedule has already popped it — so that one stays a premise, exactly
-- as `valCaps?` does beside it.
--
chainsGo-nest : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  chainsNestD (chainsGo a rs) ≤ regsNestMax rs
chainsGo-nest a [] = z≤n
chainsGo-nest a ((rid , s , (u , p)) ∷ r)
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = ≤-trans (chainsGo-nest a r) (m≤n⊔m (pathNestD p) (regsNestMax r))
... | true  | no  _    = ≤-trans (chainsGo-nest a r) (m≤n⊔m (pathNestD p) (regsNestMax r))
... | true  | yes refl = ⊔-mono-≤ ≤-refl (chainsGo-nest a r)

chainsNest≤store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  chainsNestD (chainsOf a st) ≤ storeNestMax sched st
chainsNest≤store a sched st =
  ≤-trans (chainsGo-nest a (EvalSt.registry st))
          (m≤n⊔m _ (regsNestMax (EvalSt.registry st)))

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
cascade-depth-capsH {e = e} sl id a nextId sched st slEq cok nok harr hsz =
  ≤-trans (cascade-nest-compositional sl id a nextId sched st slEq cok nok harr hsz)
          (nest-sum-fac e sl id _ _ _ harr
            (≤-trans (chainsNest≤store a sched st)
                     (≤-trans (≤-reflexive
                                (sym (storeNest-latch a sched st)))
                              store≤cap))
            store≤cap)
  where
  store≤cap = nestOK?-store e sl id sched (cascadeLatch a st)
                (trans (nestOK?-latch e sl id a sched st) nok)

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
