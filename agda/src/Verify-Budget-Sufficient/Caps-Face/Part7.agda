-- Verify-Budget-Sufficient.Caps-Face.Part7
-- thruOuter-face … reach-via-size-absurd
module Verify-Budget-Sufficient.Caps-Face.Part7 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive; +-identityʳ; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; <⇒≤;
  *-mono-≤; +-monoʳ-≤)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length; map)
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
  using (_≡_; refl; sym; trans; subst)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted)
open import Rx.Exp       using (_×ᵗ_; obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; Exp; Tm; Fn; μᵉ; unfoldμ; evalTm;
  applyFn)
open import Rx.Frame-Width using (pWᵛ; dWᵉ; dWᵗ; dWᵗˢ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; storeNestMax; nestCapAt; nestOK?; nestOK?-latch; nestOK?-store; nest-sum-3;
  storeNest-latch; realWidAt; nestSyn)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; scanVals; RegId; Chain; scan-st; take-st; flatten-st; switch-st; exhaust-st; setNode; lookupNode; NodeId; _↠_; Frame; AllOp; map-f;
  scan-f; take-f; from-inner; thru-outer; cascadeLatch; cascadeFinish; takeDispatch; arrSource;
  chainsOf; chainsGo; cascadeGo; Path; arrTy; stepFrame; subscribeInner; flattenᵒ;
  switchᵒ; exhaustᵒ; thruWalk; thruWrap; innerFinish; innerReact; aliveThroughᶠ; cascade;
  sameSource; regAt; iterSize; fLvlD; lvls; sLvlD; chainStep; budgetAt; arrTick)
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
  (1≤capsAt-reg; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsH; cDel;
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
  (innerFinish-flatten-face; innerFinish-face-keep; thruOuter-face-core)
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
-- above under one node write; flatten's is the drain, now landed
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
innerFinish-face ifc c d j g flattenᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC slSz hD =
  innerFinish-flatten-face ifc c d j g allNid inst κ id now vals sl sched st
    2≤S 1≤R slEq slC inv pC lC vC slSz hD

-- SWITCH: clear the current-inner slot if this was it
innerFinish-face _ c d j g switchᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC _ _
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (scan-st _)       = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (take-st _)       = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (flatten-st _ _ _ _)    = innerFinish-face-keep c d j sl vals false sched st inv vC
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
... | just (flatten-st _ _ _ _)    = innerFinish-face-keep c d j sl vals false sched st inv vC
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
... | just (flatten-st _ _ _ _)    | _ = stepFrame-face-zero c d j u sl fin sched st inv
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

------------------------------------------------------------------
-- THE DELIVERY-SIDE DEPTH BOUND — the cascade axis's mirror of
-- `depthE≤capsH-root`, and the one genuinely NEW obligation the P3/#9
-- signature pass creates.
--
-- WHY IT IS A POSTULATE AND NOT A DERIVATION.  Its subscribe-side
-- sibling `subscribe-depth-capsH` (.Caps-Bridge) bounds `depthE`, and
-- reaches none of the DELIVERY side: `depthCascade` gets to frames
-- through `chainStep`/`foldPath`/`stepFrame`, and every one of those is
-- outside `depthE`'s induction.  So this is a real gap with a real
-- statement, not a repackaging of one already proven — and the sibling
-- is itself open, so neither is the other's precedent.
--
-- WHERE THE LEVELS COME FROM.  A cascade climbs one nesting level per
-- thru-outer frame — `depthFrame`'s only `suc` on this side — so the
-- quantity to bound is how many such frames one arrival can drive.  One
-- induction should cover this and the subscribe side together, and
-- neither home is where it will live.
--
-- AND COUNTING THEM BY THE PATH LENGTH IS THE TRAP.  `pathSz?` caps a
-- chain's frames at `sizeAt S J`, so the count is available — as a
-- SIZE, which sits exponentially above `capsH` at every level, and the
-- gap is not an arithmetic one.  The sibling carries that finding and
-- the four dead currencies behind it; this row inherits all of it,
-- including which measure replaced them.
--
-- SO IT IS STATED IN THE NESTING CURRENCY, and split the same way: the
-- leaf is the delivery induction, bounding the cascade by the RAW
-- nesting of the arriving payload, of the chains it fans out to, and of
-- the store, plus the instant's fresh growth `realWidAt · nestSyn` —
-- the layers its own deliveries pile onto accumulators after the entry
-- reading.  The arithmetic half is `nest-sum-3` (.Nest-Store), which
-- the subscribe side spends too — genuinely shared rather than
-- mirrored.  `capsOK?` is still a premise, because the delivery
-- induction's fresh-mint bookkeeping is expected to spend the walk's
-- receipts; the fact the conclusion needs comes from `nestOK?`.
--
-- THIS ONE PROBES CLEANLY, WHICH ITS SIBLING DOES NOT.  Its only
-- uncomputable premise is `capsOK?`, so a row is a straight comparison
-- with nothing to satisfy first — where the sibling's `nestOK?` premise
-- goes unsatisfiable on the programs worth testing.  `Harness.Main`
-- Series F takes the evaluator's own next arrival off the schedule the
-- root subscribe hands over and computes both sides at the entry index,
-- the one whose fresh term is `capsBase` rather than the wrap tower.
--
-- The margin GROWS, and by an order rather than a factor.  On the
-- family's diagonal the measure is quadratic in the parameter while the
-- bound is cubic, so the ratio bottoms out in the middle of the range
-- and rises after it — the opposite of the subscribe side, which settles
-- on a constant.  Nothing refuted.
--
-- THE INDEX IS THE BOUNDARY, exactly as it is for `store-growth`: the
-- entry index is the only one where a row can fail, and no run reaches
-- it, because the instant loop starts one above and only climbs.  Rows
-- at a reachable index are slack by construction and are not run.

-- THE STATE AXIS HOLDS TOO, AND ONE FAMILY IS NEEDED TO SEE THAT IT IS
-- SAYING ANYTHING.  The parameter sweep reads one state — the one the
-- root subscribe produced — so a bound that widened with the program
-- said nothing about a bound walked along a run, where the store is the
-- term that grows.  Stepping real cascades nine deep over the arrival
-- family, the measure climbs and the difference between the two sides
-- does not move by one: the store's growth enters both sides in the
-- same amount.  Read alone that is a WEAK row, because a difference
-- that never moves is equally what a statement insensitive to the run
-- would report.
--
-- A family that connects its shared slot MID-RUN rather than in the
-- subscribe burst is what separates the two.  There the measure jumps
-- at the connect instant and the difference really does shrink, so the
-- rows can fail and the invariance above is a finding rather than an
-- artefact.  It does not fail: sweeping the shared program's value
-- count, the jump grows by ONE per value while the bound grows
-- quadratically in the same parameter, so the one instant that spends
-- margin spends a linear amount of a quadratic supply.
-- `Harness.Main`, measured-not-rechecked.
-- AND THE REAL-WIDTH COMPARISON MEASURES SAFE, WITH ROOM THAT WIDENS.
-- Both sides of `delivN ≤ realWidAt` compute — the count off the
-- evaluator's own delivered ledger, the width off `nwAt` — which is
-- what makes the real-denominated question instantiable where the
-- cap-denominated one was not.  Measured in `Harness.Main`
-- (measured-not-rechecked, so this discharges nothing): at the entry
-- index the count runs at one per registered chain while the width runs
-- at ten per chain, and sweeping the fan alone leaves the count linear
-- against a width of ten times the slope.  Widening the async length,
-- the source list and the shared def's own size moves the width up by
-- hundreds and the count not at all.

-- WHAT MAKES THE ROWS ROWS is that the fan is on a HOT slot.  Every
-- other family here reaches the arriving slot through a cold source,
-- and a cold source is re-created per subscription — so fanning one out
-- buys separate arrival INSTANTS each carrying a single chain, and the
-- count sits at one however wide the fan.  A count that cannot vary is
-- not evidence about a bound on counts, whatever the margin under it.
-- Shared once, the same references land as that many chains on ONE
-- arrival and the count becomes free.

-- AND THE MARGIN HAS A REASON, WHICH IS WHY IT IS NOT LUCK.  A chain is
-- a registration, a registration is a syntactic reference, and the
-- entry width is seeded from `capsBase`, which counts the program's
-- size and its entry ceiling.  So the only way to buy another delivery
-- is to buy program size first, and the width is what size is spent on.
-- That is the argument the leaf would have to make; the rows say it is
-- worth making.

-- SO THE COUNT MUST COME FROM A REAL WIDTH, AND THAT IS THE OPEN DESIGN
-- QUESTION under this row.  The walk invariant is unaffected and is
-- still worth having in deliveries; what has no supplier is the step
-- from a delivery count to this increment.  A cap cannot supply it, and
-- the evaluator's own per-instant burst width is what the increment was
-- named after — so the fact to look for, or to state, is one bounding
-- the walk's deliveries by that width and not by a ceiling above it.
--
-- DEAD ROUTE: reusing the proven lemma's CORE and swapping its final
--   widening.  `cascadeGo-deliveries` reads as core-plus-three-widenings
--   — the walk at level zero, then the dispatch gas to `cSize`, the walk
--   length to `cReg`, and `dCapᶜ`'s unfolding — which invites keeping the
--   core and landing it somewhere real instead.  It does not work, and
--   the reason is one level deeper than the widenings: the walk module is
--   PARAMETERISED BY THE CAPS, so its result type already reads
--   `dWalkᶜ cSize cWid cReg …`.  The count is cap-denominated inside the
--   apparatus and `cDel` is only its final form.  Re-instantiating the
--   module at real numbers is not available either, since its invariants
--   are the `capsOK?` ones, true of the caps and of nothing else.  So a
--   real-width delivery bound needs new machinery rather than a different
--   exit from the old, and the proven lemma is not a transferable twin
--   however exactly its left side matches.
-- DEAD ROUTE: counting the walk's deliveries with `cascadeGo-deliveries`
--   and dominating its bound by this increment.  The bound is cap-side,
--   the increment is real, and the denomination law rules out the
--   comparison in that direction at the entry index and worse above it.
--   The lemma is proven and stays useful elsewhere; it is unspendable
--   HERE.
postulate
  cascadeGo-deliv-real : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    let r = cascadeGo a nextId chains sched st
    in delivN st (proj₂ (proj₂ r)) ≤ realWidAt e sl id

-- THE SLOT STORE SURVIVES A CHAIN STEP, one call into `foldPath` and so
-- one composition of `foldPath-slots`.  It sits here rather than beside
-- its sibling for the cascade fold, because the per-chain induction
-- below needs it and lives one layer under that one.
chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st))) ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st


-- ONE ARRIVAL'S WHOLE CASCADE, IN THE WIDTH CURRENCY -- and the width
-- factor is the content, not decoration over a narrower truth.  A
-- delivery walks an already-registered chain, so the tempting reading is
-- that it deepens by one operator's worth and the sum over chains is
-- `length chains` single `nestSyn`s.  Both halves of that reading are
-- false, and the mechanism is one arc: flatten's DRAIN spends a nesting
-- level through `depthFinC`, and it is reached through a `from-inner`
-- frame, which `pathNestD` charges nothing for.  Every other level this
-- family spends is paid by a path term -- `pathNestD` charges the
-- `thru-outer` frame and only that frame -- so the drain's levels have
-- nothing to come out of but the constant, and a program whose folds
-- nest spends arbitrarily many of them.  The width factor is what pays
-- for them, and it pays with room to spare: on the crossing family the
-- descent runs three orders of magnitude under it.
--
-- REFUTED: `Refuted.Nest-Depth-One`, which pins the subscribe-side
--   sibling of the narrow form at its first crossing -- descent 21
--   against a bound of 19 on `progU 5 2`.  The delivery side and the
--   per-chain sum cross the same way and for the same reason, read by
--   `Harness.Main`'s SERIES Q and SERIES R on the same family
--   (measured-not-rechecked): the per-chain sum reads 601 against 367
--   at a fold depth of 120, having tied and crossed near depth 5.
--
-- RECOVERY: `git show f53fff4:agda/src/Verify-Budget-Sufficient/Caps-Face/Part7.agda`
--   restores the per-chain assembly and its four leaves -- the marked-state
--   helper, the chain-step store and caps-at-the-next-index transports, and
--   the registry count under the real width.  The chain-step transports are
--   about `chainStep` alone and survive the refutation of what consumed
--   them; the assembly does not.

-- THE BOUNDED LIMIT WAS SWEPT AND FOUND NOTHING, AND THE REGION IS
-- WORTH NAMING because it is the one this campaign had no coverage of
-- at all: every earlier family predates flatten's `concurrent`
-- argument, so all of them sit at one of the two saturated ends.
-- `Harness.Main`'s SERIES V moves the limit alone over a source whose
-- width outruns it (measured-not-rechecked): limits one to four,
-- source widths three to twelve, fold depths and list lengths to nine.
-- Not one row crosses this bound, and the margin WIDENS in every
-- direction -- the descent grows by the fold depth per added lane
-- while the width factor grows by better than an order of magnitude
-- more.  What the sweep did NOT reach is a limit that binds while the
-- store is loaded: its slot table is the one-arrival table throughout,
-- so a bounded gate interacting with a shared def is uncovered.
-- THE WALK'S PER-DELIVERY HALF, which is the half that has to be an
-- induction.  It charges the store measure by what the walk actually
-- DID rather than by what it was allowed to do: one `nestSyn` per
-- delivery on the evaluator's own ledger, with no cap anywhere in the
-- statement.  That is what lets the counting half be a separate leaf —
-- and lets it be a comparison between two static quantities, which is
-- the only reason it can be settled without the run.

-- AND THE CHARGE OVERSHOOTS BY A CONSTANT PER DELIVERY, WHICH IS WHAT
-- SAYS THE SHAPE IS RIGHT RATHER THAN MERELY SAFE.  Every quantity here
-- computes and none is a cap, so the statement instantiates directly;
-- measured in `Harness.Main` (measured-not-rechecked, so this
-- discharges nothing).  Driving the stored values' nesting from one
-- wrap level to nine, the store measure and the charge rise in lockstep
-- and the margin sits at four the whole way — it never widens, so the
-- rows are tight enough to have broken.  Driving the delivery count
-- instead, the margin is four times the count, and the two axes compose
-- linearly rather than interacting.
--
-- THE REASON IS THE ONE THE CURRENCY WAS BUILT ON: `nestSyn` is a
-- SYNTACTIC ceiling on nesting, so deepening what a delivery stores
-- deepens the ceiling by the same step.  A per-delivery charge in this
-- currency cannot be outrun by depth, only by a step that stores
-- without delivering — which is the residue the induction owes, and
-- which no row in the sweep produced.
postulate
  cascadeGo-nest-perDeliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    let r = cascadeGo a nextId chains sched st
    in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
         ≤ storeNestMax sched st
             + delivN st (proj₂ (proj₂ r)) * nestSyn e sl

-- THE PER-DELIVERY HALF OF THE DEPTH FACE, and the split is the store
-- face's, taken at the same two joints.  `cascadeGo-nest` charges the
-- store measure by what the walk DID -- one `nestSyn` per delivery on
-- the evaluator's own ledger, no cap in the statement -- and then
-- widens that count to the static width in a second step.  This is the
-- first of those two halves for the descent, and the second is already
-- available: `cascadeGo-deliv-real` is the same widening, stated once
-- and spent by both faces.  Splitting here is what makes the counting
-- question a comparison of two static quantities rather than something
-- the induction has to carry, which is the property that let the store
-- face settle its own counting leaf without a run.
--
-- TWIN: `cascadeGo-nest`, whose body is the assembly below with the
--   store measure in place of the descent, over the same `cascadeGo`
--   and the same widening lemma.

-- AND THE TWO PER-DELIVERY LEAVES ARE ONE INDUCTION SEEN FROM TWO
-- SIDES, which is a fact about how to prove this and not about what it
-- says.  `depthCascade`'s cons clause reports its tail TWICE, once at
-- the entry state and once at the state the live chain left, and the
-- second of those needs the store measure at the stepped state bounded
-- by the entry store plus the deliveries made so far -- which is
-- `cascadeGo-nest-perDeliv`'s conclusion exactly.  So neither leaf's
-- induction closes without the other's statement, and proving them
-- apart means carrying one as a hypothesis of the other -- which
-- launders a counted postulate into an invisible premise.  The store
-- leaf is stated directly above for that reason: it was one module up
-- and out of reach, and moving it down is what makes a joint induction
-- possible at all rather than a threading exercise.  The two nesting
-- hypotheses are here because that leaf demands them, and they cost
-- nothing to carry: the store face's own two statements carry exactly
-- this pair, so they are the family's hypotheses rather than one
-- caller's, and the only consumer of the parent already binds both for
-- other summands and was simply not passing them down.

-- THE RESIDUE IS A PHANTOM BRANCH, AND IT IS NOT THE STORE LEAF'S.
-- That one owes a step that stores without delivering; this one owes
-- the opposite.  `depthCascade`'s cons clause reports its tail at BOTH
-- states, because the evaluator's cancellation test is with-abstracted
-- by the consumer and the mirror cannot branch on it.  The
-- stepped-state summand composes -- the induction hypothesis, the store
-- leaf at a SINGLETON chain list, where `cascadeGo` degenerates to one
-- `chainStep`, and `delivN-split` close it between them.
--
-- THE STATEMENT SURVIVES THE BRANCH THAT KILLS THE ROUTE, and the
-- measurement is what separates the two.  `Harness.Main`'s SERIES P is
-- this statement over a family built to reach the skip branch, and it
-- reports the chain count, the deliveries and the cancellations so that
-- a row says whether it bore on that branch at all
-- (measured-not-rechecked, so it discharges nothing).  The load-bearing
-- region is reached: rows at ten chains, four deliveries and ten
-- cancellations -- six chains phantom -- with margins running from
-- seven against twenty-eight to twenty-five against sixty-one.  The
-- left side does not move with the chain count at fixed deliveries,
-- which is the part that matters: the phantom tail contributes its own
-- DEPTH and not a count, and depth at the entry state is what the state
-- terms on the right already pay for.  The sibling family never enters
-- the branch -- every row has chains equal to deliveries -- so it is
-- evidence about the live arm only, whatever its margin.
--
-- DEAD ROUTE: closing the ENTRY-state summand by the same induction
--   hypothesis.  It concludes in the delivery count of a run begun
--   before the head stepped, and every chain the head cancels still
--   delivers in that run, so what it leaves owed is a comparison
--   between two different runs' counts, which nothing bounds by one.
--   The summand wants a bound off the STATE terms alone -- it is a
--   depth at the entry state, where `chainsNestD` and the store measure
--   are already on the right -- and that route goes through no count.

postulate
  cascadeGo-depth-perDeliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    let r = cascadeGo a nextId chains sched st
    in depthCascade a nextId chains sched st
         ≤ nestDᵛ (arrTy a) (arrVal a)
           + chainsNestD chains
           + storeNestMax sched st
           + delivN st (proj₂ (proj₂ r)) * nestSyn e sl

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
      + storeNestMax sched (cascadeLatch a st)
      + realWidAt e sl id * nestSyn e sl
cascade-nest-compositional {e = e} sl id a nextId sched st hsl hcaps hnest hval =
  ≤-trans (cascadeGo-depth-perDeliv sl id a nextId (chainsOf a st) sched
             (cascadeLatch a st) hsl hcapsL
             (trans (nestOK?-latch e sl id a sched st) hnest) hval)
          (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a)
                      + chainsNestD (chainsOf a st)
                      + storeNestMax sched (cascadeLatch a st))
             (*-mono-≤ (cascadeGo-deliv-real sl id a nextId (chainsOf a st)
                          sched (cascadeLatch a st) hsl hcapsL)
                       (≤-refl {nestSyn e sl})))
  where
  hcapsL = cascadeLatch-caps (capsAt e sl id) a sched st hcaps


-- A CASCADE'S CHAINS ARE A SELECTION FROM THE REGISTRY, which the store
-- measure charges, so this premise does not have to be threaded from the
-- caller: `chainsOf` filters the registry by source and type, and a
-- `⊔`-fold dominates any sublist of what it folds.  The arriving
-- PAYLOAD is the one quantity that genuinely is not in the state — the
-- schedule has already popped it — so that one stays a premise, exactly
-- as `valCaps?` does beside it.
--
-- TWIN: `chainsOf-caps` above takes `regsSz?` to the same bound over the
--   same selection, by recursion on the registry through `chainsGo-caps`.
postulate
  chainsNest≤store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    chainsNestD (chainsOf a st) ≤ storeNestMax sched st

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
          (nest-sum-3 e sl id _ _ _ harr
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
