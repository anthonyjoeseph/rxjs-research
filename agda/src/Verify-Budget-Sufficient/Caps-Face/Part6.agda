-- Verify-Budget-Sufficient.Caps-Face.Part6
-- innerFinish-face-keep … innerFinish-concat-face
-- (lines 6074–7013 of the original Caps-Face.agda)
module Verify-Budget-Sufficient.Caps-Face.Part6 where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _∸_; _≤_; _<_;
                                _⊔_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ⊔-mono-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤; *-assoc;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ;
                                       *-distribʳ-+; *-distribˡ-+; *-identityʳ; <⇒≤;
                                       ^-monoˡ-≤; ^-*-assoc;
                                       ^-distribˡ-+-*; *-mono-≤;
                                       +-monoʳ-≤; *-comm;
                                       m≤m⊔n; m≤n⊔m; ⊔-lub; *-zeroʳ; *-identityˡ;
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; tabulate; concat; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++; length-map)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                _at_from_as_; EmitKind; subscribe;
                                InstEvent; init; value; close; handoff;
                                complete; exhausted; delivery;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                subΘExp; subΘTm; subΘTms;
                                varIx;
                                renExp; renTm; renTms; Ren∈; ext∈; ++Ren;
                                wkExp; wkTm; reify;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms;
                                elimDExp; elimDTm; elimDTms;
                                compare∈; _⊟_; ⊟-++ˡ; ⊟-++ʳ; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Frame-Width using (pWᵉ; pWᵛ; dWᵉ; dWᵗ; dWᵗˢ; dWᵛ; outWᵛ;
                                outWᵉ; innWᵉ; innWᵗ; innWᵗˢ;
                                pmOᵉ; pmOᵗ; pmIᵉ; pmIᵗ; pmIᵗˢ;
                                _∈ᵇ_; outWⱽ; innWⱽ; innWᵗⱽ; innWᵗˢⱽ;
                                pmOⱽ; pmOᵗⱽ; pmIⱽ; pmIᵗⱽ; pmIᵗˢⱽ;
                                dWⱽ; dWᵗⱽ; dWᵗˢⱽ;
                                slotPW; slotsPW; slotsPWgo;
                                slotIW; slotsIW; slotsIWgo;
                                slotsPW≤entryCeil; slotsIW≤entryCeil)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                oneShotBurst; installNode; setNode; lookupNode;
                                NodeId;
                                root; share-sink; _↠_; Frame; AllOp;
                                map-f; scan-f; take-f; from-inner;
                                thru-outer; Stream;
                                sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                takeVals; takeDispatch; cutThrough; pathHasNode;
                                dropSource; arrSource; chainsOf; chainsGo; cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; mintSource; mintOrdinal; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; splitBurst; retagEvents;
                                mergeBump; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                concatDrain; innerFinish; innerReact;
                                sizeAt;
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                dryBurst;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize; fCharge; regAt;
                                sizeStep; iterSize; foldStep; iterFold;
                                fLvl; fLvlD; iterL; dLvl; lvls;
                                sIterD; sLvlD)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted 2026-08-01 so that a grind here no longer
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
open import Verify-Budget-Sufficient.Delivery-Walk public
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
open import Verify-Budget-Sufficient.Caps-Nest public
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
  using (depthInner; depthFrame; depthReact; depthFin; depthWalk; depthCascade;
         depthConsume)
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers
open import Verify-Budget-Sufficient.Caps-Chain
  using (walk-nil; inner-nil; walk-index; frame-step; queue-push)
open import Verify-Budget-Sufficient.Caps-Sadd using (walk-step-suc)

open import Verify-Budget-Sufficient.Caps-Face.Part5 public

-- innerFinish's clauses that hand the payload straight back — merge's
-- counter, switch's cleared slot, exhaust's cleared flag, the absorb
-- path, and every op/node pair the evaluator's catch-all covers.  None
-- of them touches a value, so j′ = 0 and both conjuncts are the
-- hypotheses with `j + 0` massaged to `j`
innerFinish-face-keep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d j : ℕ) (sl : Slots Γ) (vals : List (Val Γ s)) (b : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  FrameFace {t = t} c d j sl (vals , [] , b , sched , st)
innerFinish-face-keep c d j sl vals b sched st inv vC =
  0 , face-lift c d j 0 z≤n
    , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

-- THE ONE from-inner CLAUSE THAT IS NOT j′ = 0.  Every other clause
-- of innerReact / innerFinish hands `vals` straight back — merge
-- decrements a counter, switch clears a slot, exhaust clears a flag,
-- the absorb path and every catch-all return the payload untouched —
-- and all of those are ground below.  concatAll's is the exception:
-- `innerFinish` returns `vals ++ concatDrain …`, and concatDrain
-- subscribes each parked inner and CONCATENATES the bursts, so its
-- output width is a sum over the queue of one subscribeE burst's
-- value count — conjunct (b) of the two named above.  Its receipt (a)
-- is the drain's one subscribe per queued inner, and that is the
-- second number, the one nothing in the tree reports
--
-- ASSEMBLY (2026-08-06): narrowed over the burst-construction and
-- slot-transport toolkit stated at ~3608-3645, which is exactly the
-- kit the drain's output needs — one `∷` per queued inner's burst,
-- and the four `*-slots` substitutions that move a bound from the
-- entry telescope to the drain's.
-- TAKES THE NODE READ EXPLICITLY, and that is load-bearing rather than
-- cosmetic.  Writing this as a `with w ≟ᵗ s` inside the assembly makes
-- `dpt` reduce to `suc (depthDrain …) ≤ d` while re-evaluating
-- `depthFin` on a variable `s` yields `depthFinC … (s ≟ᵗ s) ≤ d` —
-- and for a VARIABLE `s`, `s ≟ᵗ s` is not definitionally `yes refl`,
-- so the two types never meet.  With `nd` an argument, the assembly
-- below passes `lookupNode allNid (EvalSt.nodes st)` with NO
-- intervening with-abstraction and the premise's type is literally the
-- one the goal wants.  This head dispatches every node case itself:
-- nothing / scan / take / merge / switch / exhaust / concat+no all go
-- to `innerFinish-face-keep` at j′ = 0, and concat+yes is the one real
-- obligation — `innerFinish-caps` (Subscribe-Face:1761), which is
-- exactly what H1 and H2 were added to feed.
-- LANDED from InnerFinish-Concat-Go-Probe (DELETED; git history) (2026-08-10):
-- `ifc` (IfcFace = innerFinish-caps' type) threads as a new first kit
-- arg so the proof can call innerFinish-caps without creating a circular
-- import (Subscribe-Face already imports Caps-Face public).
innerFinish-concat-face-go :
    -- ifc  (innerFinish-caps, Verify-Budget-Sufficient/Subscribe-Face.agda:1760)
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
    -- burstCaps?-∷  (Verify-Budget-Sufficient/Caps-Face.agda:3608)
    (∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
      (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
      all (eventCaps? c sl) (InstEmit.events em) ≡ true →
      burstCaps? c sl str ≡ true →
      burstCaps? c sl (em ∷ str) ≡ true
     ) →
    -- valsCaps?-slots  (Verify-Budget-Sufficient/Caps-Face.agda:3625)
    (∀ {n} {Γ : Ctx n} {c : Caps} {sl sl′ : Slots Γ}
      (u : Ty) (vs : List (Val Γ u)) → sl′ ≡ sl →
      all (valCaps? c sl u) vs ≡ true → all (valCaps? c sl′ u) vs ≡ true
     ) →
    -- eventsCaps?-slots  (Verify-Budget-Sufficient/Caps-Face.agda:3630)
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (evs : List (InstEvent (Val Γ u))) → sl′ ≡ sl →
      all (eventCaps? c sl) evs ≡ true → all (eventCaps? c sl′) evs ≡ true
     ) →
    -- burstCaps?-slots  (Verify-Budget-Sufficient/Caps-Face.agda:3635)
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (str : Stream Γ u) → sl′ ≡ sl →
      burstCaps? c sl str ≡ true → burstCaps? c sl′ str ≡ true
     ) →
    -- obsListCaps?-slots  (Verify-Budget-Sufficient/Caps-Face.agda:3640)
    (∀ {n} {Γ : Ctx n} {s} {c : Caps} {sl sl′ : Slots Γ}
      (q : List (Closed Γ s)) → sl′ ≡ sl →
      all (obsCaps? c sl) q ≡ true → all (obsCaps? c sl′) q ≡ true
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (d j : ℕ) (g : Gas) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (nd : Maybe (NodeState Γ)) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    -- H1: the total slot store fits the size cap.  Every route through
    -- the drain (`obsList→mList-strict`, `concatDrain-caps`,
    -- `innerFinish-caps`) wants it, and it is NOT derivable from
    -- `slotsCaps?`, which bounds per-element sizes and not the sum
    slotsSize sl ≤ Caps.cSize c →
    -- H2: this finish's depth fits the walk's budget.  `innerFinish-caps`'s
    -- concat+yes branch is unreachable at `dep = 0`, so its budget lands
    -- in `fLvlD S W dep j` and widening to `d` needs exactly this
    depthFin g concatᵒ allNid inst κ id now vals sched st nd ≤ d →
    nd ≡ lookupNode allNid (EvalSt.nodes st) →
    FrameFace c d j sl (innerFinish g concatᵒ allNid inst κ id now vals sched st nd)

-- § 1  TRIVIAL CASES — innerFinish returns vals , [] , false , sched , st
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    nothing _ _ _ _ inv _ _ vC _ _ _
  = innerFinish-face-keep c d j sl vals false sched st inv vC
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    (just (scan-st _)) _ _ _ _ inv _ _ vC _ _ _
  = innerFinish-face-keep c d j sl vals false sched st inv vC
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    (just (take-st _)) _ _ _ _ inv _ _ vC _ _ _
  = innerFinish-face-keep c d j sl vals false sched st inv vC
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    (just (merge-st _ _)) _ _ _ _ inv _ _ vC _ _ _
  = innerFinish-face-keep c d j sl vals false sched st inv vC
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    (just (switch-st _ _)) _ _ _ _ inv _ _ vC _ _ _
  = innerFinish-face-keep c d j sl vals false sched st inv vC
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    (just (exhaust-st _ _)) _ _ _ _ inv _ _ vC _ _ _
  = innerFinish-face-keep c d j sl vals false sched st inv vC

-- § 2  CONCAT CASE — delegate entirely to ifc (= innerFinish-caps).
-- Both sub-cases (w ≠ s → trivial, w = s → drain) are handled inside
-- ifc via its own `with w ≟ᵗ s | dpt` trick.
innerFinish-concat-face-go ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    (just (concat-st {w} q act od))
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt ndEq
  = let
      -- Step 1: transport dpt from nd to (lookupNode …)
      dpt′ = subst
               (λ nd′ → depthFin g concatᵒ allNid inst κ id now vals sched st nd′ ≤ d)
               ndEq dpt
      -- Step 2: call ifc (= innerFinish-caps) at dep=d, bud=frameBud c j
      res = ifc c d (frameBud c j) j g concatᵒ allNid inst κ id now vals
              sl sched st 2≤S 1≤R slEq slC slSz inv pC lC vC ≤-refl dpt′
      -- Step 3: rearrange tuple
      --   ifc returns: (j′ , capsOK , valsCaps , evts , level)
      --   FrameFace expects: (j′ , level , capsOK , valsCaps , evts)
      rearranged : FrameFace c d j sl
                     (innerFinish g concatᵒ allNid inst κ id now vals sched st
                        (lookupNode allNid (EvalSt.nodes st)))
      rearranged =
        ( proj₁ res
        , proj₂ (proj₂ (proj₂ (proj₂ res)))
        , proj₁ (proj₂ res)
        , proj₁ (proj₂ (proj₂ res))
        , proj₁ (proj₂ (proj₂ (proj₂ res))))
    -- Step 4: transport conclusion from (lookupNode …) back to nd
    in subst
         (λ nd′ → FrameFace c d j sl
                    (innerFinish g concatᵒ allNid inst κ id now vals sched st nd′))
         (sym ndEq)
         rearranged

-- thruOuter-face-core: PROVED (2026-08-11) by landing the body from
-- ThruOuter-Face-Core-Probe (DELETED; git history).  Private helpers inline
-- Subscribe-Face's walk machinery against a `siC` hypothesis instead
-- of a direct call to subscribeInner-caps.  Abstract to keep VWF
-- from reaching the walk helpers on the budget-sufficient spine.

private
  -- valsOf / valsLen / valsIn / lenWiden: wrappers around valsCaps?-parts
  valsOf′ : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ) (vs : List (Val Γ s)) →
    valsCaps? c sl vs ≡ true → all (valCaps? c sl s) vs ≡ true
  valsOf′ c sl vs h = proj₁ (valsCaps?-parts c sl vs h)

  valsLen′ : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ) (vs : List (Val Γ s)) →
    valsCaps? c sl vs ≡ true → length vs ≤ suc (Caps.cWid c)
  valsLen′ c sl vs h = proj₂ (valsCaps?-parts c sl vs h)

  valsIn′ : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ) (vs : List (Val Γ s)) →
    all (valCaps? c sl s) vs ≡ true → length vs ≤ suc (Caps.cWid c) →
    valsCaps? c sl vs ≡ true
  valsIn′ c sl vs h hl = ∧-intro h (T⇒≡true _ (≤⇒≤ᵇ hl))

  lenWiden′ : ∀ {A : Set} {c c′ : Caps} (xs : List A) → c ⊑ᶜ c′ →
    length xs ≤ suc (Caps.cWid c) → length xs ≤ suc (Caps.cWid c′)
  lenWiden′ xs (_ , wd≤ , _) h = ≤-trans h (s≤s wd≤)

  frameStep-+suc′ : ∀ (c : Caps) (j a b : ℕ) → 2 ≤ Caps.cSize c →
    frameStep ((j + a) + b) c ⊑ᶜ frameStep (j + suc (a + b)) c
  frameStep-+suc′ c j a b 2≤S =
    frameStep-mono-j c 2≤S
      (≤-trans (≤-reflexive (+-assoc j a b))
        (≤-trans (n≤1+n (j + (a + b)))
                 (≤-reflexive (sym (+-suc j (a + b))))))

  thruWrap-vals′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (op : AllOp) (nid : NodeId) (fin : Bool)
    (r : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
    proj₁ (thruWrap op nid fin r) ≡ proj₁ r
  thruWrap-vals′ op nid false _ = refl
  thruWrap-vals′ mergeᵒ nid true (vs , bs , sd , st)
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (merge-st _ _)    = refl
  ... | just (concat-st _ _ _) = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl
  thruWrap-vals′ concatᵒ nid true (vs , bs , sd , st)
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (merge-st _ _)    = refl
  ... | just (concat-st _ _ _) = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl
  thruWrap-vals′ switchᵒ nid true (vs , bs , sd , st)
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (merge-st _ _)    = refl
  ... | just (concat-st _ _ _) = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl
  thruWrap-vals′ exhaustᵒ nid true (vs , bs , sd , st)
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (merge-st _ _)    = refl
  ... | just (concat-st _ _ _) = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl

  dbl-suc : ∀ (w : ℕ) → suc w + suc w ≡ 2 * suc w
  dbl-suc w = sym (trans (cong (λ x → suc w + x) (+-identityʳ (suc w))) refl)

  2*suc≤2^suc : ∀ (w : ℕ) → 2 * suc w ≤ 2 ^ suc w
  2*suc≤2^suc w = *-monoʳ-≤ 2 (n<2^n w)

  double≤foldStep′ : ∀ (S w : ℕ) → 2 ≤ S → 2 * suc w ≤ foldStep S w
  double≤foldStep′ S w hS = ≤-trans (2*suc≤2^suc w) (^-monoˡ-≤ (suc w) hS)

  sum-fold′ : ∀ (S W a b : ℕ) → 2 ≤ S →
    a ≤ suc W → b ≤ suc W → a + b ≤ suc (foldStep S W)
  sum-fold′ S W a b hS ha hb =
    ≤-trans (+-mono-≤ ha hb)
            (≤-trans (≤-reflexive (dbl-suc W))
                     (≤-trans (double≤foldStep′ S W hS) (n≤1+n (foldStep S W))))

  concat-fits′ : ∀ {A : Set} (c : Caps) (L : ℕ) (xs ys : List A) →
    2 ≤ Caps.cSize c →
    length xs ≤ suc (Caps.cWid (frameStep L c)) →
    length ys ≤ suc (Caps.cWid (frameStep L c)) →
    length (xs ++ ys) ≤ suc (Caps.cWid (frameStep (suc L) c))
  concat-fits′ c L xs ys hS hx hy =
    subst (λ x → length (xs ++ ys) ≤ suc x) (sym (frameStep-wid-suc c L))
      (≤-trans (≤-reflexive (length-++ xs))
               (sum-fold′ (Caps.cSize c) (Caps.cWid (frameStep L c))
                          (length xs) (length ys) hS hx hy))

  SiCType : Set
  SiCType =
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
      (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
      (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
      2 ≤ Caps.cSize c →
      1 ≤ Caps.cReg c →
      Sched.slots sched ≡ sl →
      slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
      slotsSize sl ≤ Caps.cSize c →
      capsOK? (frameStep j c) sched st ≡ true →
      valCaps? (frameStep j c) sl (obs u) o ≡ true →
      pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
      suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
      nest o sl (EvalSt.connectedShares st) ≤ bud →
      depthInner g op allNid κ id now o sched st ≤ dep →
      let r = subscribeInner g op allNid κ id now o sched st
      in Σ ℕ λ j′ →
         (capsOK? (frameStep (j + j′) c)
                  (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                  (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
         × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
         × (all (eventCaps? (frameStep (j + j′) c) sl)
                (proj₁ (proj₂ (proj₂ r))) ≡ true)
         × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))

  thruConsume-caps-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (siC : SiCType)
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    valCaps? (frameStep j c) sl (obs u) o ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest o sl (EvalSt.connectedShares st) ≤ bud →
    depthConsume g op nid κ id now o sched st ≤ dep →
    let r = thruConsume g op nid κ id now o sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
  thruConsume-caps-go siC c dep bud j g mergeᵒ nid κ id now o sl sched st
                      2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt =
    j′ , capsOK?-mergeBump (frameStep (j + j′) c) nid
           (proj₁ (proj₂ (proj₂ (proj₂ R))))
           (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           (proj₁ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ (proj₂ SI)))
       , proj₂ (proj₂ (proj₂ (proj₂ SI)))
    where
    SI = siC c dep bud j g mergeᵒ nid κ id now o sl sched st
           2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
    j′ = proj₁ SI
    R  = subscribeInner g mergeᵒ nid κ id now o sched st
  thruConsume-caps-go {n = n} {u = u} siC c dep bud j g concatᵒ nid κ id now o sl sched st
                      2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
    with lookupNode nid (EvalSt.nodes st)
       | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
           (capsOK?-nodeSz (frameStep j c) sched st inv)
           (capsOK?-nodeWid (frameStep j c) sched st inv)
  ... | nothing                | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (scan-st _)       | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (take-st _)       | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (merge-st _ _)    | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (switch-st _ _)   | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (exhaust-st _ _)  | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (concat-st {w} q false od) | (bn , wn) =
    j′ , capsOK?-setNode (frameStep (j + j′) c) nid (concat-st {t = u} [] (not done) od)
           (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           refl refl (proj₁ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ (proj₂ SI)))
       , proj₂ (proj₂ (proj₂ (proj₂ SI)))
    where
    SI = siC c dep bud j g concatᵒ nid κ id now o sl sched st
           2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
    j′ = proj₁ SI
    R  = subscribeInner g concatᵒ nid κ id now o sched st
    done = proj₁ (proj₂ (proj₂ (proj₂ R)))
  ... | just (concat-st {w} q true od) | (bn , wn) with w ≟ᵗ u
  ...   | no _ = 0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
                            (sym (+-identityʳ j)) inv
                , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  ...   | yes refl =
    1 , subst (λ x → capsOK? (frameStep x c) sched
                       (record st { nodes = setNode nid (concat-st (q ++ o ∷ []) true od)
                                              (EvalSt.nodes st) }) ≡ true)
              (sym lvl)
              (capsOK?-setNode (frameStep (suc j) c)
                 nid (concat-st (q ++ o ∷ []) true od)
                 sched st BN WN
                 (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st
                    (frameStep-mono-j c 2≤S (n≤1+n j)) inv))
      , refl , refl
      , queue-push (Caps.cSize c) (Caps.cWid c) dep (suc bud) j (s≤s z≤n)
    where
    lvl : j + 1 ≡ suc j
    lvl = +-comm j 1
    BN = all-++-intro (λ x → sizeᵉ x ≤ᵇ Caps.cSize (frameStep (suc j) c)) q (o ∷ [])
           (all-impl _ _ (λ x → ≤ᵇ-widen (sizeᵉ x)
                                  (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j)))) q bn)
           (∧-intro (≤ᵇ-widen (sizeᵉ o) (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j)))
                      (valCaps?-size (frameStep j c) sl (obs u) o vC))
                    refl)
    WN = widNode-push c j (Sched.slots sched) q o true od 2≤S wn
           (subst (λ y → (pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                  (sym slEq) (valCaps?-wid (frameStep j c) sl (obs u) o vC))
  thruConsume-caps-go siC c dep bud j g switchᵒ nid κ id now o sl sched st
                      2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
    with lookupNode nid (EvalSt.nodes st) | dpt
  ... | nothing                | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (scan-st _)       | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (take-st _)       | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (merge-st _ _)    | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (concat-st _ _ _) | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (exhaust-st _ _)  | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (switch-st cur od) | dpt′ =
    j′ , capsOK?-setNode (frameStep (j + j′) c) nid
           (switch-st (if proj₁ (proj₂ (proj₂ (proj₂ R))) then nothing
                       else just (proj₁ R)) od)
           (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           refl refl (proj₁ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ SI))
       , all-++-intro (eventCaps? (frameStep (j + j′) c) sl)
           (proj₁ KILL) _
           (switchKill-closes-caps (frameStep (j + j′) c) sl cur sched st)
           (proj₁ (proj₂ (proj₂ (proj₂ SI))))
       , proj₂ (proj₂ (proj₂ (proj₂ SI)))
    where
    KILL = switchKill cur sched st
    sched₁ = proj₁ (proj₂ KILL)
    st₁    = proj₂ (proj₂ KILL)
    SI = siC c dep bud j g switchᵒ nid κ id now o sl sched₁ st₁
           2≤S 1≤R (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slEq) slC slSz
           (switchKill-caps (frameStep j c) cur sched st inv) vC pC lC
           (nest-keeps o sl _ _ bud
              (KeepsC.connMono (switchKill-keeps cur sched st)) nst)
           dpt′
    j′ = proj₁ SI
    R  = subscribeInner g switchᵒ nid κ id now o sched₁ st₁
  thruConsume-caps-go siC c dep bud j g exhaustᵒ nid κ id now o sl sched st
                      2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (scan-st _)       = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (take-st _)       = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (merge-st _ _)    = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (concat-st _ _ _) = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (switch-st _ _)   = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (exhaust-st true od)  = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    where ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
  ... | just (exhaust-st false od) =
    j′ , capsOK?-setNode (frameStep (j + j′) c) nid
           (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ R))))) od)
           (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
           refl refl (proj₁ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ SI))
       , proj₁ (proj₂ (proj₂ (proj₂ SI)))
       , proj₂ (proj₂ (proj₂ (proj₂ SI)))
    where
    SI = siC c dep bud j g exhaustᵒ nid κ id now o sl sched st
           2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
    j′ = proj₁ SI
    R  = subscribeInner g exhaustᵒ nid κ id now o sched st

  thruWalk-caps-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (siC : SiCType)
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    valsCaps? (frameStep j c) sl vals ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    mList? bud sl (EvalSt.connectedShares st) vals ≡ true →
    depthWalk g op nid κ id now vals sched st ≤ dep →
    let r = thruWalk g op nid κ id now vals sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (j + j′ ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) j)
  thruWalk-caps-go siC c dep bud j g op nid κ id now [] sl sched st
                   2≤S 1≤R slEq slC slSz inv pC vC lC nst dpt =
    0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
      , refl , refl , walk-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  thruWalk-caps-go {u = u} siC c dep bud j g op nid κ id now (o ∷ os) sl sched st
                   2≤S 1≤R slEq slC slSz inv pC vC lC nst dpt =
    suc (j₁ + j₂)
      , capsOK?-mono (frameStep ((j + j₁) + j₂) c) (frameStep (j + suc (j₁ + j₂)) c)
          (proj₁ (proj₂ (proj₂ REST))) (proj₂ (proj₂ (proj₂ REST)))
          ⊑ˢ (proj₁ (proj₂ IH))
      , valsIn′ (frameStep (j + suc (j₁ + j₂)) c) sl (proj₁ TC ++ proj₁ REST)
          (valsCaps?-widen sl u (proj₁ TC ++ proj₁ REST) ⊑ˢ
             (all-++-intro (valCaps? (frameStep ((j + j₁) + j₂) c) sl u)
                (proj₁ TC) (proj₁ REST)
                (valsCaps?-widen sl u (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                   (valsOf′ (frameStep (j + j₁) c) sl (proj₁ TC)
                      (proj₁ (proj₂ (proj₂ HD)))))
                (valsOf′ (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST)
                   (proj₁ (proj₂ (proj₂ IH))))))
          (subst (λ x → length (proj₁ TC ++ proj₁ REST)
                          ≤ suc (Caps.cWid (frameStep x c)))
                 (sym lvlW)
                 (concat-fits′ c ((j + j₁) + j₂) (proj₁ TC) (proj₁ REST) 2≤S
                    (lenWiden′ (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                       (valsLen′ (frameStep (j + j₁) c) sl (proj₁ TC)
                          (proj₁ (proj₂ (proj₂ HD)))))
                    (valsLen′ (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST)
                       (proj₁ (proj₂ (proj₂ IH))))))
      , eventsCaps?-widen sl (proj₁ (proj₂ TC) ++ proj₁ (proj₂ REST)) ⊑ˢ
          (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
             (proj₁ (proj₂ TC)) (proj₁ (proj₂ REST))
             (eventsCaps?-widen sl (proj₁ (proj₂ TC))
                (frameStep-⊑-+ c 2≤S (j + j₁) j₂) (proj₁ (proj₂ (proj₂ (proj₂ HD)))))
             (proj₁ (proj₂ (proj₂ (proj₂ IH)))))
      , walk-step-suc (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length os) j j₁ j₂ 2≤S
          (proj₂ (proj₂ (proj₂ (proj₂ HD))))
          (proj₂ (proj₂ (proj₂ (proj₂ IH))))
    where
    vCa = valsOf′ (frameStep j c) sl (o ∷ os) vC
    HD  = thruConsume-caps-go siC c dep bud j g op nid κ id now o sl sched st
            2≤S 1≤R slEq slC slSz inv (proj₁ (∧-true _ _ vCa)) pC lC
            (mList?-head bud sl _ o os nst)
            (≤-trans (m≤m⊔n _ _) dpt)
    j₁  = proj₁ HD
    TC  = thruConsume g op nid κ id now o sched st
    sd₁ = proj₁ (proj₂ (proj₂ TC))
    st₁ = proj₂ (proj₂ (proj₂ TC))
    IH  = thruWalk-caps-go siC c dep bud (j + j₁) g op nid κ id now os sl sd₁ st₁
            2≤S 1≤R
            (trans (KeepsC.slotsEq (thruConsume-keeps g op nid κ id now o sched st))
                   slEq)
            slC slSz (proj₁ (proj₂ HD))
            (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
            (valsIn′ (frameStep (j + j₁) c) sl os
               (valsCaps?-widen sl (obs u) os (frameStep-⊑-+ c 2≤S j j₁)
                  (proj₂ (∧-true _ _ vCa)))
               (lenWiden′ os (frameStep-⊑-+ c 2≤S j j₁)
                  (≤-trans (n≤1+n (length os))
                           (valsLen′ (frameStep j c) sl (o ∷ os) vC))))
            (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
            (mList?-keeps bud sl _ _ os
               (KeepsC.connMono (thruConsume-keeps g op nid κ id now o sched st))
               (mList?-tail bud sl _ o os nst))
            (≤-trans (m≤n⊔m _ _) dpt)
    j₂   = proj₁ IH
    REST = thruWalk g op nid κ id now os sd₁ st₁
    ⊑ˢ   = frameStep-+suc′ c j j₁ j₂ 2≤S
    lvlW : j + suc (j₁ + j₂) ≡ suc ((j + j₁) + j₂)
    lvlW = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))

  thruOuter-face-core-go :
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
      (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
      (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
      2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
      Sched.slots sched ≡ sl →
      slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
      slotsSize sl ≤ Caps.cSize c →
      capsOK? (frameStep j c) sched st ≡ true →
      valCaps? (frameStep j c) sl (obs u) o ≡ true →
      pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
      suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
      nest o sl (EvalSt.connectedShares st) ≤ bud →
      depthInner g op allNid κ id now o sched st ≤ dep →
      let r = subscribeInner g op allNid κ id now o sched st
      in Σ ℕ λ j′ →
         (capsOK? (frameStep (j + j′) c)
                  (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                  (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
         × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
         × (all (eventCaps? (frameStep (j + j′) c) sl)
                (proj₁ (proj₂ (proj₂ r))) ≡ true)
         × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))) →
    (∀ (C : ℕ) → 2 ≤ C →
      ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} (η : Fin n → ℕ) → (∀ i → η i ≤ szB C 1) →
      (o : Exp Γ Δᵍ Δ Θ u) → sizeᵉ o ≤ C →
      (syncSizeᵉ o ≤ C) × (hopDᵉ C η o ≤ hopR C)) →
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
        (vals : List (Val Γ (lookup Γ i))) (evs : List (InstEvent (Val Γ t)))
        (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
        delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc (share-sink i)
                                   vals evs fin sched st)))
          ≡ delivN st (proj₂ (proj₂ (dispatchShare sf gas id now i vals fin sched st)))) →
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
        (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
        (p : Path Γ (lookup Γ i) t) (ps : List (RegId × Path Γ (lookup Γ i) t))
        (sched : Sched Γ) (st : EvalSt e) →
        any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
        delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st)))
          ≡ delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))) →
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
        (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
        (p : Path Γ (lookup Γ i) t) (ps : List (RegId × Path Γ (lookup Γ i) t))
        (sched : Sched Γ) (st : EvalSt e) →
        any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
        let st₀ = consᵈ rid st
            fp  = foldPath sf gas id now (toℕ i) p vals
                    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
            st₁ = proj₂ (proj₂ fp) in
        delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st)))
          ≡ suc (delivN st₀ st₁
                 + delivN st₁ (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps
                                              (proj₁ (proj₂ fp)) st₁))))) →
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
      length (EvalSt.registry (proj₂ (proj₂ (shareFinish i fin out))))
        ≤ length (EvalSt.registry (proj₂ (proj₂ out)))) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (d j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (vals : List (Val Γ (obs u))) (fin : Bool)
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    suc (depthWalk g op nid κ id now vals sched st) ≤ d →
    FrameFace c d j sl
      (thruWrap op nid fin (thruWalk g op nid κ id now vals sched st))
  thruOuter-face-core-go siC rr fpN sgN sgC sfL c zero j g op nid κ id now vals fin sl sched st
      2≤S 1≤R slEq slC inv pS lC vC slSz ()
  thruOuter-face-core-go siC rr fpN sgN sgC sfL c (suc dep′) j g op nid κ id now vals fin sl sched st
      2≤S 1≤R slEq slC inv pS lC vC slSz hd =
    j′ , frame-step (Caps.cSize c) (Caps.cWid c) dep′ j 0 j′ 2≤S z≤n
           (subst (λ x → x + j′
                           ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep′
                               (frameBud c j) (suc (Caps.cWid (frameStep j c))) x)
                  (sym (+-identityʳ j))
                  (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ TW))))
                     (walk-index (Caps.cSize c) (Caps.cWid c) dep′ (frameBud c j)
                        (length vals) j j 2≤S
                        (valsLen′ (frameStep j c) sl vals vC))))
       , proj₁ WR
       , valsIn′ (frameStep (j + j′) c) sl (proj₁ (thruWrap op nid fin WK))
           (proj₁ (proj₂ WR))
           (subst (λ x → length x ≤ suc (Caps.cWid (frameStep (j + j′) c)))
                  (sym (thruWrap-vals′ op nid fin WK))
                  (valsLen′ (frameStep (j + j′) c) sl (proj₁ WK)
                     (proj₁ (proj₂ (proj₂ TW)))))
       , proj₂ (proj₂ WR)
    where
    TW = thruWalk-caps-go siC c dep′ (sizeAt (Caps.cSize c) (suc j)) j g op nid κ id now vals sl sched st
           2≤S 1≤R slEq slC slSz inv pS vC lC
           (valsCaps→mList-strict c j sl _ vals (≤-trans (s≤s z≤n) 2≤S) slSz
              (valsOf′ (frameStep j c) sl vals vC))
           (≤-pred hd)
    j′ = proj₁ TW
    WK = thruWalk g op nid κ id now vals sched st
    WR = thruWrap-caps (frameStep (j + j′) c) op nid fin sl WK
           (proj₁ (proj₂ TW))
           (valsOf′ (frameStep (j + j′) c) sl (proj₁ WK)
              (proj₁ (proj₂ (proj₂ TW))))
           (proj₁ (proj₂ (proj₂ (proj₂ TW))))

abstract
  thruOuter-face-core :
    -- subscribeInner-caps  (Verify-Budget-Sufficient/Subscribe-Face.agda:951)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
      (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
      (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
      2 ≤ Caps.cSize c →
      1 ≤ Caps.cReg c →
      Sched.slots sched ≡ sl →
      slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
      slotsSize sl ≤ Caps.cSize c →
      capsOK? (frameStep j c) sched st ≡ true →
      valCaps? (frameStep j c) sl (obs u) o ≡ true →
      pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
      suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
      nest o sl (EvalSt.connectedShares st) ≤ bud →
      depthInner g op allNid κ id now o sched st ≤ dep →
      let r = subscribeInner g op allNid κ id now o sched st
      in Σ ℕ λ j′ →
         (capsOK? (frameStep (j + j′) c)
                  (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                  (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
         × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
         × (all (eventCaps? (frameStep (j + j′) c) sl)
                (proj₁ (proj₂ (proj₂ r))) ≡ true)
         × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
     ) →
    -- reach-resets  (Verify-Budget-Sufficient/Caps-Face.agda, above)
    (∀ (C : ℕ) → 2 ≤ C →
      ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} (η : Fin n → ℕ) → (∀ i → η i ≤ szB C 1) →
      (o : Exp Γ Δᵍ Δ Θ u) → sizeᵉ o ≤ C →
      (syncSizeᵉ o ≤ C) × (hopDᵉ C η o ≤ hopR C)
     ) →
    -- foldPath-sink-N  (Verify-Budget-Sufficient/Deliveries.agda:787)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
        (vals : List (Val Γ (lookup Γ i))) (evs : List (InstEvent (Val Γ t)))
        (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
        delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc (share-sink i)
                                   vals evs fin sched st)))
          ≡ delivN st (proj₂ (proj₂ (dispatchShare sf gas id now i vals fin sched st)))
     ) →
    -- shareGo-skip-N  (Verify-Budget-Sufficient/Deliveries.agda:824)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
        (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
        (p : Path Γ (lookup Γ i) t) (ps : List (RegId × Path Γ (lookup Γ i) t))
        (sched : Sched Γ) (st : EvalSt e) →
        any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
        delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st)))
          ≡ delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
     ) →
    -- shareGo-cons-N  (Verify-Budget-Sufficient/Deliveries.agda:840)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
        (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
        (p : Path Γ (lookup Γ i) t) (ps : List (RegId × Path Γ (lookup Γ i) t))
        (sched : Sched Γ) (st : EvalSt e) →
        any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
        let st₀ = consᵈ rid st
            fp  = foldPath sf gas id now (toℕ i) p vals
                    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
            st₁ = proj₂ (proj₂ fp) in
        delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st)))
          ≡ suc (delivN st₀ st₁
                 + delivN st₁ (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps
                                              (proj₁ (proj₂ fp)) st₁))))
     ) →
    -- shareFinish-len  (Verify-Budget-Sufficient/Delivery-Walk.agda:129)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
      length (EvalSt.registry (proj₂ (proj₂ (shareFinish i fin out))))
        ≤ length (EvalSt.registry (proj₂ (proj₂ out)))
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
    -- H1 and H2, matching `innerFinish-concat-face-go`'s.  Here H2 is the
    -- `suc` form: a thru-outer frame re-reads the budget, so its own walk
    -- runs one level DOWN and the premise must leave that unit spare
    slotsSize sl ≤ Caps.cSize c →
    suc (depthWalk g op nid κ id now vals sched st) ≤ d →
    FrameFace c d j sl
      (thruWrap op nid fin (thruWalk g op nid κ id now vals sched st))
  thruOuter-face-core = thruOuter-face-core-go

-- the two faces, assembled over their cores
-- P3's ASSEMBLY, landed from `InnerFinish-Concat-Probe (DELETED; git history)`.
-- `innerFinish-concat-face-core` is a REAL DEFINITION now: one call to
-- the sub-postulate at `nd = lookupNode allNid (EvalSt.nodes st)`, with
-- no with-abstraction anywhere between, so `dpt`'s type and the
-- sub-postulate's H2 are the same expression rather than merely equal
-- ones.  The five kit hypotheses are passed STRAIGHT THROUGH rather than
-- dropped: the drain is what eventually consumes them, and dropping them
-- here would orphan `burstCaps?-∷` and the four `*-slots` transports
innerFinish-concat-face-core :
    -- ifc  (innerFinish-caps, Verify-Budget-Sufficient/Subscribe-Face.agda:1760)
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
    (∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
      (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
      all (eventCaps? c sl) (InstEmit.events em) ≡ true →
      burstCaps? c sl str ≡ true →
      burstCaps? c sl (em ∷ str) ≡ true
     ) →
    (∀ {n} {Γ : Ctx n} {c : Caps} {sl sl′ : Slots Γ}
      (u : Ty) (vs : List (Val Γ u)) → sl′ ≡ sl →
      all (valCaps? c sl u) vs ≡ true → all (valCaps? c sl′ u) vs ≡ true
     ) →
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (evs : List (InstEvent (Val Γ u))) → sl′ ≡ sl →
      all (eventCaps? c sl) evs ≡ true → all (eventCaps? c sl′) evs ≡ true
     ) →
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (str : Stream Γ u) → sl′ ≡ sl →
      burstCaps? c sl str ≡ true → burstCaps? c sl′ str ≡ true
     ) →
    (∀ {n} {Γ : Ctx n} {s} {c : Caps} {sl sl′ : Slots Γ}
      (q : List (Closed Γ s)) → sl′ ≡ sl →
      all (obsCaps? c sl) q ≡ true → all (obsCaps? c sl′) q ≡ true
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (d j : ℕ) (g : Gas) (allNid inst : NodeId)
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
    depthFin g concatᵒ allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ d →
    FrameFace c d j sl (innerFinish g concatᵒ allNid inst κ id now vals sched st
                          (lookupNode allNid (EvalSt.nodes st)))
innerFinish-concat-face-core ifc k₁ k₂ k₃ k₄ k₅
    c d j g allNid inst κ id now vals sl sched st
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt =
  -- the five kit hypotheses are ETA-EXPANDED, not passed bare: their
  -- implicits are not determined by any explicit argument, so a bare
  -- `k₂`/`k₅` leaves unsolved metas.  Fresh binder names so the lambdas
  -- do not shadow this clause's own `c`/`sl`
  innerFinish-concat-face-go ifc
    (λ {n′} {Γ′} {u′} → k₁ {n′} {Γ′} {u′})
    (λ {n′} {Γ′} {c′} {sa} {sb} → k₂ {n′} {Γ′} {c′} {sa} {sb})
    (λ {n′} {Γ′} {u′} {c′} {sa} {sb} → k₃ {n′} {Γ′} {u′} {c′} {sa} {sb})
    (λ {n′} {Γ′} {u′} {c′} {sa} {sb} → k₄ {n′} {Γ′} {u′} {c′} {sa} {sb})
    (λ {n′} {Γ′} {s′} {c′} {sa} {sb} → k₅ {n′} {Γ′} {s′} {c′} {sa} {sb})
    c d j g allNid inst κ id now vals sl sched st
    (lookupNode allNid (EvalSt.nodes st))
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt
    refl

innerFinish-concat-face :
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
  (c : Caps) (d j : ℕ) (g : Gas) (allNid inst : NodeId)
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
  depthFin g concatᵒ allNid inst κ id now vals sched st
    (lookupNode allNid (EvalSt.nodes st)) ≤ d →
  FrameFace c d j sl (innerFinish g concatᵒ allNid inst κ id now vals sched st
                        (lookupNode allNid (EvalSt.nodes st)))
innerFinish-concat-face ifc =
  innerFinish-concat-face-core ifc
    (λ {n} {Γ} {u} → burstCaps?-∷ {n} {Γ} {u})
    (λ {n} {Γ} {c} {sl} {sl′} → valsCaps?-slots {n} {Γ} {c} {sl} {sl′})
    (λ {n} {Γ} {u} {c} {sl} {sl′} → eventsCaps?-slots {n} {Γ} {u} {c} {sl} {sl′})
    (λ {n} {Γ} {u} {c} {sl} {sl′} → burstCaps?-slots {n} {Γ} {u} {c} {sl} {sl′})
    (λ {n} {Γ} {s} {c} {sl} {sl′} → obsListCaps?-slots {n} {Γ} {s} {c} {sl} {sl′})

