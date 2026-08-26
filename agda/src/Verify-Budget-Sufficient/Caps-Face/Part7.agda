-- Verify-Budget-Sufficient.Caps-Face.Part7
-- thruOuter-face … reach-via-size-absurd
module Verify-Budget-Sufficient.Caps-Face.Part7 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; *-identityˡ; ^-distribˡ-+-*; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; *-monoˡ-≤; ≤-trans; ≤-refl; ≤-reflexive; +-identityʳ; m≤m+n; m≤n+m;
  n≤1+n; *-identityʳ; <⇒≤; *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; +-assoc; ⊔-lub; m≤m⊔n;
  m≤n⊔m; +-mono-≤; ⊔-mono-≤; ⊔-identityʳ; m⊔n≤m+n; *-distribˡ-+; ^-*-assoc; *-comm)
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
open import Rx.Exp       using (_×ᵗ_; obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; Exp; Tm; Fn; μᵉ; unfoldμ; evalTm;
  applyFn)
open import Rx.Frame-Width using (pWᵛ; dWᵉ; dWᵗ; dWᵗˢ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Walk using
  (foldPath-nodes; nodesMax; burstsOK; capsWalkOK; fac-hoist; one-pow)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; chainsNestF; chainsNestF≡; chainsSzSum; pathSzSum; frameSzD; pathNestD;
  pathNestF; 1≤pathNestF; nest-telescope; nest-scale; pow-distrib-*; storeNestMax; nestCapAt;
  nestOK?; nestOK?-latch; nestOK?-store; nest-sum-fac; nestFacAt; nestFacAt-def; 1≤nestFacAt;
  nest-inflate; storeNest-latch; realWidAt; realWidAt-def; nestIncAt; nestIncAt-def;
  nestBurstAt; 1≤nestBurstAt; nestUnit; slotsNestSum; liveNest; nodeNest; regsNestMax)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; scanVals; RegId; Chain; scan-st; take-st; mergeAll-st;
  switch-st; exhaust-st; setNode; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f; take-f;
  from-inner; thru-outer; root; share-sink; cascadeLatch; cascadeFinish; takeDispatch; arrSource; chainsOf;
  chainsGo; cascadeGo; Path; arrTy; stepFrame; subscribeInner; mergeAllᵒ; switchᵒ; exhaustᵒ;
  thruWalk; thruWrap; innerFinish; innerReact; aliveThroughᶠ; cascade; sameSource; regAt;
  iterSize; fLvlD; lvls; sLvlD; chainStep; budgetAt; arrTick)
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
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsH; cDel;
   cDel-body; dWalkᶜ-mono; frameStep; frameStep-0; frameStep-mono-j;
   iterFold-infl; iterFold-mono-count; iterSize-mono-count; lvls-mono;
   sizeCount; sizeCount-body)
open import Verify-Budget-Sufficient.Measures using
  (n<2^n; pathLen; reach-reset; ∧-true)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; size-unfoldμ; stepFrame-keeps)
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
  (capsOK?; capsOK?-mono; evalTm-iterSize; eventCaps?; frameSz?; iterSize-+;
   iterSize-2^; iterSize-mono-s; n≤capsAt-size; pathSz?; pathSz?-widen;
   regsSz?; slotsCaps?; SlotWid; valCaps?; widNode)
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
  (evalTm-iterFold; expWid-fromSize; frameStep-⊑-+; valCaps?-size;
   valCaps?-wid; wid-lift)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using
  (slotsCaps?-slotWid; SlotWid-mono)
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
       sched st refl refl inv)
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
       sched st refl refl inv)
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
-- THE THREE CLAUSES subscribeE-caps CANNOT DISCHARGE IN PLACE, GROUND
-- BESIDE IT.
--
-- Two of subscribeE's clauses BUILD VALUES BY EVALUATION and one
-- REBUILDS ITS OWN SYNTAX, and all three land exactly where
-- mapFrame-caps / scanFrame-caps already are: `evalTm` is `evalWith`
-- with an empty environment, an EVALUATION rather than a substitution,
-- and evalWith-size is a TOWER in the term's syntax (evalWith-sharp
-- only moves the exponent to `3 ^ caseWᵗ`).  So none of the three is
-- `sizeᵛ ≤ sizeᵗ` and each wants an existential j′ of its own — which
-- is affordable, because iterSize runs away faster than the clause
-- does, and is the same reason the two frame members are true.
--
-- Stated as tightly as the clauses consume them, so the difficulty has
-- a NAME and a boundary — no state, no recursion, no chain, just the
-- evaluator's own arithmetic — instead of being buried in the hub.
--
-- THE μ CLAUSE IS THE ONE THAT IS NOT ABOUT evalTm — and it is the one
-- that cost a refuted draft.  `unfoldμ body` is LARGER than `μᵉ body`
-- on the size axis, and the width axis was assumed stable and is not:
-- see the note on unfoldμ-caps below, and Hop-Descent-Probe's μwide,
-- which measures 0 ↦ 6.  Both halves now come off ONE size receipt:
-- size-unfoldμ (the μ's size squared) for the size, and the width
-- bridge above for the width.
------------------------------------------------------------------

-- `ofᵉ ts` bursts `map evalTm ts`, GROUND AND SYNTAX-COUNTED.  Both
-- halves of valCaps? are owed and each comes off its OWN receipt at the
-- same count: evalTm-iterSize spends one iterSize fold per syntax node
-- from an empty environment, evalTm-iterFold one foldStep per syntax
-- node from the telescope's leaf bound.  j′ = suc (sizeᵗˢ ts)
evalTms-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (ts : List (Tm Γ [] [] [] u)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵗˢ ts ≤ Caps.cSize (frameStep j c) →
  dWᵗˢ n sl ts ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → all (valCaps? (frameStep (j + j′) c) sl u)
                 (map (λ tm → evalTm tm) ts) ≡ true
evalTms-caps {n = n} {Γ = Γ} {u = u} c j sl ts 2≤S slC szb wdb =
  suc a , go ts ≤-refl
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗˢ ts
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  one : (tm : Tm Γ [] [] [] u) → sizeᵗ tm ≤ a →
        valCaps? (frameStep (j + suc a) c) sl u (evalTm tm) ≡ true
  one tm h =
    ∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ
        (≤-trans (≤-trans (≤-trans (evalTm-iterSize S 1≤S tm)
                            (≤-trans (iterSize-mono-count S 0 1≤S h)
                                     (iterSize-mono-s S a z≤n)))
                          (≤-reflexive (sym (iterSize-+ S j a S))))
                 (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
      (T⇒≡true _ (≤⇒≤ᵇ
        (wid-lift c j a 2≤S
          (≤-trans (evalTm-iterFold S M 2≤S (s≤s z≤n) sl slW tm)
                   (iterFold-mono-count S M 2≤S h)))))
  go : (vs : List (Tm Γ [] [] [] u)) → sizeᵗˢ vs ≤ a →
       all (valCaps? (frameStep (j + suc a) c) sl u)
           (map (λ tm → evalTm tm) vs) ≡ true
  go []       h = refl
  go (y ∷ ys) h =
    ∧-intro (one y (≤-trans (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)) h))
            (go ys (≤-trans (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)) h))

-- `scanᵉ f seed b` installs `scan-st (evalTm seed)`: the same statement
-- for one term, and the accumulator has to come back bounded on both
-- axes because capsOK? reads it on both.  j′ = suc (sizeᵗ z)
evalSeed-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (z : Tm Γ [] [] [] u) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵗ z ≤ Caps.cSize (frameStep j c) →
  dWᵗ n sl z ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → valCaps? (frameStep (j + j′) c) sl u (evalTm z) ≡ true
evalSeed-caps {n = n} {u = u} c j sl z 2≤S slC szz wdz =
  suc a
    , ∧-intro
        (T⇒≡true _ (≤⇒≤ᵇ
          (≤-trans (≤-trans (≤-trans (evalTm-iterSize S 1≤S z)
                              (iterSize-mono-s S a z≤n))
                            (≤-reflexive (sym (iterSize-+ S j a S))))
                   (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
        (T⇒≡true _ (≤⇒≤ᵇ
          (wid-lift c j a 2≤S (evalTm-iterFold S M 2≤S (s≤s z≤n) sl slW z))))
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗ z
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)

-- `μᵉ body` subscribes `unfoldμ body`, and BOTH AXES MOVE.  The size
-- axis was always going to: the unfolding is larger than the μ (only
-- syncSizeᵉ is preserved — syncSize-unfoldμ) by an amount no syntactic
-- measure in the file bounds.
--
-- THE WIDTH AXIS MOVES TOO, and the first draft of this said it did
-- not.  `dWᵉ (unfoldμ body) ≤ dWᵉ (μᵉ body)` reads plausible — the
-- plug lands at `varᵉ` positions and dWᵉ is 0 there — and it is
-- FALSE, refuted by Hop-Descent-Probe's μwide (0 ↦ 6).  hopD survives
-- an unfold because Δᵍ variables are reachable only under deferᵉ and
-- hopD CUTS a defer to 0; dW's whole reason to exist is that it does
-- NOT cut there, so the plug lands exactly where dW is looking and
-- exposes the μ's own outW — which dW does not bound.  Nor is it off
-- by a constant: k copies of the var in the template multiply through
-- innW's slope, so any true bound is affine in the plug's width with
-- the pmO/pmI coefficients, i.e. the hopD-subΘ machinery.
--
-- So the two axes are stated TOGETHER, at ONE existential j′ (which
-- is what the recursive call needs — both hypotheses at the same
-- level), and the width half is derived from the SIZE hypothesis the
-- telescope already carries rather than from the width one.  That is
-- affordable for the same reason the two frame postulates are:
-- iterFold is a tower in the cap and outW of an expression is a tower
-- in its size, so a large enough j′ covers it
unfoldμ-caps : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵉ (μᵉ body) ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl (μᵉ body) ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → (sizeᵉ (unfoldμ body) ≤ Caps.cSize (frameStep (j + j′) c))
           × (dWᵉ n sl (unfoldμ body) ≤ Caps.cWid (frameStep (j + j′) c))
unfoldμ-caps c j sl body 2≤S slC szb wdb =
  (m + suc (m * m))
    , ≤-trans SZ (iterSize-mono-count S S 1≤S
                    (+-monoʳ-≤ j (m≤m+n m (suc (m * m)))))
    , expWid-fromSize c j m (m * m) sl 2≤S slC (unfoldμ body)
        (size-unfoldμ body)
  where
  S   = Caps.cSize c
  B   = Caps.cSize (frameStep j c)
  m   = sizeᵉ (μᵉ body)
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  -- QUADRATIC, AND ONE ROUND OF DOUBLING PER NODE CLEARS IT: unfolding
  -- plants the whole μ at each of the body's global-var positions
  -- (size-unfoldμ, the shared prerequisite in .Keeps-Ring), so the
  -- growth is the μ's size SQUARED — and iterSize at least doubles per
  -- fold (iterSize-2^), so the μ's OWN SIZE many folds cover the factor
  -- of m the squaring costs.  Both halves are counted in syntax: the
  -- unfolding IS syntax, so its width needs no cap read either
  quad : m * m ≤ iterSize S m B
  quad = ≤-trans (*-mono-≤ (<⇒≤ (n<2^n m)) szb) (iterSize-2^ S m B 1≤S)
  SZ : sizeᵉ (unfoldμ body) ≤ Caps.cSize (frameStep (j + m) c)
  SZ = ≤-trans (≤-trans (size-unfoldμ body) quad)
               (≤-reflexive (sym (iterSize-+ S j m S)))

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

-- THE PENDING-SOURCE COMPONENT, and it is the one corner of the store
-- that no instantiation in this campaign has ever reached.  A live
-- source carries the values an emit has queued but not yet dispatched,
-- so the walk can in principle leave one holding a value nested deeper
-- than anything the store held before -- and the width term is there
-- to pay for exactly that.  Every family the harness drives reads this
-- component as ZERO at every instant -- and the reason is the FAMILIES,
-- not the component: their sources script plain numerals, whose nesting
-- is zero whatever a walk does with them, so reaching this corner at all
-- needs a source scripting OBSERVABLES.  That is why it is stated
-- separately rather than folded in: a component with no coverage is a
-- component whose cheapness is a guess, and guessing it cheap inside a
-- larger proof is how a corner stops being looked at.
postulate
  cascadeGo-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    let r = cascadeGo a nextId chains sched st
    in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
         ≤ storeNestMax sched st + nestIncAt e sl id

-- THE BURST BOUND AT THE INDICES A CHAIN STEP FIXES, so that the fold
-- below and the caps face above name the same hypothesis.
chainBurstOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (W : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainBurstOK {n = n} {e = e} W id a path sched st =
  burstsOK W (budgetAt e (Sched.slots sched) id) id (arrTick a) path
           (arrVal a ∷ []) (Arrival.isLast a) sched st

-- AND THE SAME PACKAGING FOR THE CAPS THE `*All` FRAMES SPEND, so a
-- consumer states one hypothesis per walk rather than one per frame.
chainCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainCapsOK {n = n} {e = e} c sl id a path sched st =
  capsWalkOK c sl (budgetAt e (Sched.slots sched) id) id (arrTick a) path
             (arrVal a ∷ []) (Arrival.isLast a) sched st

-- THE EXPONENT THE CAPS RIDER TELESCOPES TO OVER A CHAIN LIST.  One
-- factor is spent per FRAME, so the fold's exponent is the total frame
-- count and not the chain count -- the same reason `chainsNestF` is a
-- product where `chainsNestD` is a max.  It is stated here rather than
-- beside those two because the frame count is `pathLen`, and the module
-- that holds them would have to import the measures tower to say it.
chainsLenSum : ∀ {n} {Γ : Ctx n} {s t} →
  List (RegId × Path Γ s t) → ℕ
chainsLenSum = foldr (λ rc acc → pathLen (proj₂ rc) + acc) 0

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
  (c : Caps) (W : ℕ) (sl : Slots Γ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → chainBurstOK W id a path sched st →
  chainCapsOK c sl id a path sched st →
  let r = chainStep id a path sched st in
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ (2 ^ Caps.cSize c) ^ pathLen path
      * (pathNestF path ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + W * (nestDᵛ (arrTy a) (arrVal a) + pathNestD path
                   + suc (pathLen path) * nestUnit e sl)))
chainStep-nodes {n = n} {e = e} c W sl id a path sched st hsl 1≤W hb hc =
  ≤-trans (foldPath-nodes c W sl (budgetAt e (Sched.slots sched) id) n id
             (arrTick a) (arrSource a) path (arrVal a ∷ [])
             (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
             (Arrival.isLast a) sched st hsl 1≤W hb hc)
    (*-monoʳ-≤ ((2 ^ Caps.cSize c) ^ pathLen path)
    (*-monoʳ-≤ (pathNestF path ^ W)
      (≤-trans (+-monoˡ-≤ (W * (pathNestD path + U))
                          (≤-trans (⊔-mono-≤ (≤-refl {nodesMax st})
                                             (≤-reflexive (⊔-identityʳ V)))
                                   (m⊔n≤m+n (nodesMax st) V)))
      (≤-trans (≤-reflexive (+-assoc (nodesMax st) V (W * (pathNestD path + U))))
               (+-monoʳ-≤ (nodesMax st) spread)))))
  where
  V = nestDᵛ (arrTy a) (arrVal a)
  U = suc (pathLen path) * nestUnit e sl

  spread : V + W * (pathNestD path + U) ≤ W * (V + pathNestD path + U)
  spread =
    ≤-trans (+-monoˡ-≤ (W * (pathNestD path + U)) (nest-inflate W V 1≤W))
      (≤-trans (≤-reflexive (sym (*-distribˡ-+ W V (pathNestD path + U))))
               (≤-reflexive (cong (W *_) (sym (+-assoc V (pathNestD path) U)))))

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
  (cp : Caps) (sl : Slots Γ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) → Set
chainsCapsOK cp sl a nextId []               sched st = ⊤
chainsCapsOK cp sl a nextId ((rid , c) ∷ chains) sched st =
  if any (_≡ᵇ rid) (EvalSt.cancelled st)
  then chainsCapsOK cp sl a nextId chains sched st
  else (chainCapsOK cp sl nextId a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
        × chainsCapsOK cp sl a nextId chains
            (proj₁ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st }))))
            (proj₂ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st })))))

cascadeGo-nodes-chains : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cp : Caps) (W : ℕ) (sl : Slots Γ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → chainsBurstOK W a nextId chains sched st →
  chainsCapsOK cp sl a nextId chains sched st →
  let r = cascadeGo a nextId chains sched st in
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ (2 ^ Caps.cSize cp) ^ chainsLenSum chains
      * (chainsNestF chains ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + length chains
                * (W * (nestDᵛ (arrTy a) (arrVal a) + chainsNestD chains
                        + suc (chainsLenSum chains) * nestUnit e sl))))
cascadeGo-nodes-chains cp W sl a nextId [] sched st hsl 1≤W hb hc =
  ≤-trans (≤-trans (m≤m+n _ 0) (one-pow W _)) (≤-reflexive (sym (*-identityˡ _)))
cascadeGo-nodes-chains {e = e} cp W sl a nextId ((rid , c) ∷ chains) sched st hsl 1≤W hb hc
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | hb | hc
... | true | hb′ | hc′ =
  ≤-trans (cascadeGo-nodes-chains cp W sl a nextId chains sched st hsl 1≤W hb′ hc′)
    (≤-trans (*-monoʳ-≤ (R ^ K)
      (≤-trans (*-monoʳ-≤ (G ^ W) (+-monoʳ-≤ M grow))
               (≤-trans (nest-scale (pathNestF c ^ W) (G ^ W)
                           (M + suc (length chains) * (W * (V + C′ + U)))
                           (1≤pow≤ (pathNestF c) W (1≤pathNestF c)))
                        (≤-reflexive
                          (cong (_* (M + suc (length chains) * (W * (V + C′ + U))))
                                (sym (pow-distrib-* W (pathNestF c) G)))))))
    (≤-trans (nest-scale (R ^ pathLen c) (R ^ K) Xc (1≤pow≤ R (pathLen c) 1≤R))
             (≤-reflexive (cong (_* Xc) (sym (^-distribˡ-+-* R (pathLen c) K))))))
  where
  R  = 2 ^ Caps.cSize cp
  1≤R : 1 ≤ R
  1≤R = 1≤pow≤ 2 (Caps.cSize cp) (s≤s z≤n)
  K  = chainsLenSum chains
  M  = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V  = nestDᵛ (arrTy a) (arrVal a)
  C  = chainsNestD chains
  C′ = pathNestD c ⊔ C
  Uz = nestUnit e sl
  U  = suc (pathLen c + K) * Uz
  Uₜ = suc K * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (pathLen c)))
  G  = chainsNestF chains
  Xc = (pathNestF c * G) ^ W * (M + suc (length chains) * (W * (V + C′ + U)))
  grow : length chains * (W * (V + C + Uₜ)) ≤ suc (length chains) * (W * (V + C′ + U))
  grow = *-mono-≤ (n≤1+n (length chains))
                  (*-monoʳ-≤ W
                    (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (pathNestD c) C)) Uₜ≤U))
... | false | hb′ | hc′ =
  ≤-trans (cascadeGo-nodes-chains cp W sl a nextId chains sd₁ st₁
             (trans (chainStep-slots nextId a c sched st′) hsl) 1≤W (proj₂ hb′) (proj₂ hc′))
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (*-monoʳ-≤ (G ^ W)
                        (+-monoˡ-≤ (length chains * (W * (V + C + Uₜ)))
                                   (chainStep-nodes cp W sl nextId a c sched st′ hsl
                                      1≤W (proj₁ hb′) (proj₁ hc′)))))
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (fac-hoist (R ^ pathLen c) (G ^ W) A Z (1≤pow≤ R (pathLen c) 1≤R)))
          (≤-trans (≤-reflexive (sym (*-assoc (R ^ K) (R ^ pathLen c) Y)))
          (≤-trans (≤-reflexive
                      (cong (_* Y) (trans (*-comm (R ^ K) (R ^ pathLen c))
                                          (sym (^-distribˡ-+-* R (pathLen c) K)))))
                   (*-monoʳ-≤ (R ^ (pathLen c + K))
          (≤-trans (nest-telescope (pathNestF c ^ W) (G ^ W) M
                                   (W * (V + pathNestD c + Uc))
                                   (length chains * (W * (V + C + Uₜ)))
                                   (1≤pow≤ (pathNestF c) W (1≤pathNestF c)))
                   (≤-trans (≤-reflexive
                               (cong (_* (M + (W * (V + pathNestD c + Uc)
                                               + length chains * (W * (V + C + Uₜ)))))
                                     (sym (pow-distrib-* W (pathNestF c) G))))
                     (*-monoʳ-≤ ((pathNestF c * G) ^ W)
                       (+-monoʳ-≤ M
                         (+-mono-≤ (*-monoʳ-≤ W
                                     (+-mono-≤ (+-monoʳ-≤ V (m≤m⊔n (pathNestD c) C)) Uc≤U))
                                   (*-monoʳ-≤ (length chains)
                                     (*-monoʳ-≤ W
                                       (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (pathNestD c) C))
                                                 Uₜ≤U)))))))))))))
  where
  M   = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V   = nestDᵛ (arrTy a) (arrVal a)
  C   = chainsNestD chains
  Uz  = nestUnit e sl
  G   = chainsNestF chains
  R   = 2 ^ Caps.cSize cp
  1≤R : 1 ≤ R
  1≤R = 1≤pow≤ 2 (Caps.cSize cp) (s≤s z≤n)
  K   = chainsLenSum chains
  U   = suc (pathLen c + K) * Uz
  Uₜ  = suc K * Uz
  Uc  = suc (pathLen c) * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (pathLen c)))
  Uc≤U : Uc ≤ U
  Uc≤U = *-monoˡ-≤ Uz (s≤s (m≤m+n (pathLen c) K))
  A   = pathNestF c ^ W * (M + W * (V + pathNestD c + Uc))
  Z   = length chains * (W * (V + C + Uₜ))
  Y   = G ^ W * (A + Z)
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  r₁  = chainStep nextId a c sched st′
  sd₁ = proj₁ (proj₂ r₁)
  st₁ = proj₂ (proj₂ r₁)

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
  chainsLenSum chains ≤ realWidAt e sl id * Caps.cSize (capsAt e sl id) →
  (2 ^ Caps.cSize (capsAt e sl id)) ^ chainsLenSum chains
    * chainsNestF chains ^ nestBurstAt e sl id ≤ nestFacAt e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) sl a nextId chains sched st →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
       ≤ nestFacAt e sl id
         * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest-nodes {e = e} sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls hfac hburst hcw =
  ≤-trans (≤-trans (cascadeGo-nodes-chains (capsAt e sl id) (nestBurstAt e sl id) sl a nextId
                      chains sched st hsl (1≤nestBurstAt e sl id) hburst hcw)
                   (≤-reflexive
                     (sym (*-assoc ((2 ^ Caps.cSize (capsAt e sl id)) ^ chainsLenSum chains)
                                   (chainsNestF chains ^ nestBurstAt e sl id) _))))
    (*-mono-≤ hfac
      (+-mono-≤ nodes≤store
        (≤-trans (*-mono-≤ hcnt
                    (*-monoʳ-≤ (nestBurstAt e sl id)
                      (≤-trans (+-monoˡ-≤ (suc (chainsLenSum chains) * nestUnit e sl) hchg)
                               (*-monoˡ-≤ (nestUnit e sl) (s≤s (s≤s hls))))))
                 (≤-reflexive (sym (nestIncAt-def e sl id))))))
  where

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
  chainsLenSum chains ≤ realWidAt e sl id * Caps.cSize (capsAt e sl id) →
  (2 ^ Caps.cSize (capsAt e sl id)) ^ chainsLenSum chains
    * chainsNestF chains ^ nestBurstAt e sl id ≤ nestFacAt e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) sl a nextId chains sched st →
  let r = cascadeGo a nextId chains sched st
  in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
       ≤ nestFacAt e sl id
         * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest {e = e} sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls hfac hburst hcw =
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

  LV : foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sd′) ≤ nestFacAt e sl id * RHS
  LV = ≤-trans (cascadeGo-nest-live sl id a nextId chains sched st hsl hcaps hnest hval) up

  ND : foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st′)
         ≤ nestFacAt e sl id * RHS
  ND = cascadeGo-nest-nodes sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls
         hfac hburst hcw

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

-- THE DESCENT IS THE STORE IT LEAVES BEHIND, AND THAT IS WHERE THE
-- WIDTH COMES FROM.  A cascade's descent is bounded by its base terms
-- plus the store measure AFTER the walk -- not the one it started at,
-- which is the whole content: the drain's unpaid levels are unpaid
-- precisely because nothing SYNTACTIC accounts for them, and the one
-- quantity that does account for them is what the drain actually did
-- to the store.  So the depth face carries no width of its own; it
-- inherits the walk's, and the two faces of this row are one fact read
-- twice.  Stated with no premise at all, because none is needed: both
-- sides compute from the same walk, and a bound stated at the walk's
-- own result cannot be violated by a state the walk could not reach.
--
-- PROBED: `Probed.Cascade-Nest-Store` pins three arrivals by `refl`,
--   chosen for the two regions every refutation in this face turned on
--   -- the BOUNDED drain, at the exact witness that killed both narrow
--   readings, and the SKIP branch, where the selection outruns the
--   deliveries and the phantom tail is charged.  Each row pins its
--   chain count beside its verdict, since an empty selection makes the
--   descent zero outright.  Not covered: arrivals whose payload is an
--   observable, so the payload term is zero on every row; and the
--   width axis, which this statement does not mention.
postulate
  cascade-nest-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    let r = cascadeGo a nextId chains sched st
    in depthCascade a nextId chains sched st
         ≤ nestDᵛ (arrTy a) (arrVal a) + chainsNestD chains
           + storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

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
-- a path charges at most one cap per frame
frameSzD≤ : ∀ {n} {Γ : Ctx n} {s u} (B : ℕ) (f : Frame Γ s u) →
  frameSz? B f ≡ true → frameSzD f ≤ B
frameSzD≤ B (map-f fn)          h = ≤ᵇ⇒≤ (sizeᵗ fn) B (T-to h)
frameSzD≤ B (scan-f fn _)       h = ≤ᵇ⇒≤ (sizeᵗ fn) B (T-to h)
frameSzD≤ B (take-f _)          h = z≤n
frameSzD≤ B (from-inner _ _ _)  h = z≤n
frameSzD≤ B (thru-outer _ _)    h = z≤n

pathSzSum-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathSzSum p ≤ pathLen p * B
pathSzSum-len B root           h = z≤n
pathSzSum-len B (share-sink i) h = z≤n
pathSzSum-len B (f ↠ p)        h
  with ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
... | _ , hp = +-mono-≤ (frameSzD≤ B f hf) (pathSzSum-len B p hp)

pathSzSum-cap : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathSzSum p ≤ B * B
pathSzSum-cap B p h =
  ≤-trans (pathSzSum-len B p h) (*-monoˡ-≤ B (pathSz?-len B p h))

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
  chainsLenSum (chainsOf a st) ≤ realWidAt e sl id * Caps.cSize (capsAt e sl id)
arr-chains-len-sum {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsLenSum-bound B (chainsOf a st)
             (chainsGo-sz B a (EvalSt.registry st) regsz))
          (*-monoˡ-≤ B (chains-count-width sl id a sched st hcaps))
  where
  B = Caps.cSize (capsAt e sl id)
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs (capsAt e sl id) sched st hcaps

arr-chains-sz-sum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsSzSum (chainsOf a st)
    ≤ realWidAt e sl id
      * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
arr-chains-sz-sum {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsSzSum-bound B (chainsOf a st) (chainsGo-sz B a (EvalSt.registry st) regsz))
          (*-monoˡ-≤ (B * B) (chains-count-width sl id a sched st hcaps))
  where
  B = Caps.cSize (capsAt e sl id)
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs (capsAt e sl id) sched st hcaps

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
  (2 ^ Caps.cSize (capsAt e sl id)) ^ chainsLenSum (chainsOf a st)
    * chainsNestF (chainsOf a st) ^ nestBurstAt e sl id ≤ nestFacAt e sl id
arr-chains-nest-fac {e = e} sl id a sched st hsl hcaps hnest =
  ≤-trans (≤-reflexive
             (cong₂ _*_ (^-*-assoc 2 B L)
                        (trans (cong (_^ K) (chainsNestF≡ (chainsOf a st)))
                               (^-*-assoc 2 S K))))
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (B * L) (S * K))))
      (≤-trans (^-monoʳ-≤ 2 expo)
               (≤-reflexive (sym (nestFacAt-def e sl id)))))
  where
  B = Caps.cSize (capsAt e sl id)
  K = nestBurstAt e sl id
  L = chainsLenSum (chainsOf a st)
  S = chainsSzSum (chainsOf a st)
  X = realWidAt e sl id * (B * B)

  -- the length half lands on the fresh `suc`, the size half on the
  -- burst term the factor already had
  lenX : B * L ≤ X
  lenX =
    ≤-trans (*-monoʳ-≤ B (arr-chains-len-sum sl id a sched st hsl hcaps))
            (≤-reflexive
              (trans (sym (*-assoc B (realWidAt e sl id) B))
                     (trans (cong (_* B) (*-comm B (realWidAt e sl id)))
                            (*-assoc (realWidAt e sl id) B B))))

  szX : S * K ≤ K * X
  szX = ≤-trans (≤-reflexive (*-comm S K))
                (*-monoʳ-≤ K (arr-chains-sz-sum sl id a sched st hsl hcaps))

  expo : B * L + S * K ≤ suc K * X
  expo = +-mono-≤ lenX szX

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
-- is `all valCaps?` conjoined with exactly this length bound, and the
-- walk face propagates it ACROSS THE FEARED HOP: `thruWalk-walk` takes
-- it in at one level and hands it back at another, with that level's
-- growth bounded in the same tuple.  The remaining distance is
-- arithmetic and not a walk: every level a cascade reaches is under
-- `sizeCount`, so `frameStep-mono-j` puts its width under
-- `frameStep sizeCount`, which `capsAt-suc-full` says IS the cap at
-- the next instant -- which is the one this burst is read from.  The
-- grind is the induction that carries a flat bound where the walk face
-- carries a moving one, and it is a transcription rather than a
-- discovery.
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
postulate
  arr-chains-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    chainsCapsOK (capsAt e sl id) sl a nextId (chainsOf a st) sched
      (cascadeLatch a st)

cascade-nest-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ nestDᵛ (arrTy a) (arrVal a)
      + chainsNestD (chainsOf a st)
      + nestFacAt e sl id
        * (storeNestMax sched (cascadeLatch a st)
           + nestIncAt e sl id)
cascade-nest-compositional {e = e} sl id a nextId sched st hsl hcaps hnest hval =
  ≤-trans (cascade-nest-store a nextId (chainsOf a st) sched st₀)
          (+-monoʳ-≤ BASE goNest)
  where
  st₀   = cascadeLatch a st
  BASE  = nestDᵛ (arrTy a) (arrVal a) + chainsNestD (chainsOf a st)
  GO    = cascadeGo a nextId (chainsOf a st) sched st₀

  goNest : storeNestMax (proj₁ (proj₂ GO)) (proj₂ (proj₂ GO))
             ≤ nestFacAt e sl id
               * (storeNestMax sched st₀ + nestIncAt e sl id)
  goNest =
    cascadeGo-nest sl id a nextId (chainsOf a st) sched st₀ hsl
      (cascadeLatch-caps (capsAt e sl id) a sched st hcaps)
      (trans (nestOK?-latch e sl id a sched st) hnest)
      hval
      (chains-count-width sl id a sched st hcaps)
      (arr-chains-nest-syn sl id a sched st hsl hcaps hnest)
      (arr-chains-len-sum sl id a sched st hsl hcaps)
      (arr-chains-nest-fac sl id a sched st hsl hcaps hnest)
      (arr-chains-bursts sl id a nextId sched st hsl hcaps)
      (arr-chains-caps sl id a nextId sched st hsl hcaps)


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
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ capsH e sl id
cascade-depth-capsH {e = e} sl id a nextId sched st slEq cok nok harr =
  ≤-trans (cascade-nest-compositional sl id a nextId sched st slEq cok nok harr)
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
           (cascade-depth-capsH sl id a nextId sched st slEq pre nok bnd)
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
