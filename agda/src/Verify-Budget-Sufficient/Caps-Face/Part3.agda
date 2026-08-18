-- Verify-Budget-Sufficient.Caps-Face.Part3
-- wid-subΘ … closeList-caps
-- (lines 2766–3663 of the original Caps-Face.agda)
module Verify-Budget-Sufficient.Caps-Face.Part3 where

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

open import Verify-Budget-Sufficient.Caps-Face.Part2 public

------------------------------------------------------------------
-- THE SAME INDUCTION, ON A SUBSTITUTION INSTANCE.  subΘExp commutes
-- with every constructor, so every clause is the one above with the
-- subterms substituted — the count stays the ORIGINAL syntax's size
------------------------------------------------------------------

module _ (S M : ℕ) (hS : 2 ≤ S) (hM : 1 ≤ M) where

  mutual
    wsᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      Wᴱ sl (iterFold S (sizeᵉ e) M) (subΘExp Θloc σ e)
    wsᵉ {n = n} sl hI Θloc σ hσ (input i) =
      ≤-trans (proj₁ (hI i)) INFL , ≤-trans (proj₁ (proj₂ (hI i))) INFL
      , (λ k → z≤n) , (λ k → z≤n)
      where INFL = foldStep-infl S M hS
    wsᵉ {n = n} sl hI Θloc σ hσ emptyᵉ =
      ≤-trans (≤-reflexive (Red.oW-empty n sl)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-empty n sl)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵉ {n = n} sl hI Θloc σ hσ (varᵉ x) =
      ≤-trans (≤-reflexive (Red.oW-var n sl x)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-var n sl x)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵉ {n = n} sl hI Θloc σ hσ (deferᵉ e₀) =
      ≤-trans (≤-reflexive (Red.oW-defer n sl (subΘExp Θloc σ e₀))) z≤n
      , ≤-trans (≤-reflexive (Red.iW-defer n sl (subΘExp Θloc σ e₀))) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    wsᵉ {n = n} sl hI Θloc σ hσ (ofᵉ ts₀) =
      ≤-trans (≤-reflexive (trans (Red.oW-of n sl (subΘTms Θloc σ ts₀))
                                  (len-subΘTms Θloc σ ts₀)))
              (up (≤-trans (len≤sizeᵗˢ ts₀) (k≤iterFold S (sizeᵗˢ ts₀) M hS)))
      , ≤-trans (≤-reflexive (Red.iW-of n sl (subΘTms Θloc σ ts₀))) (up (proj₁ IH))
      , (λ k → z≤n) , (λ k → up (proj₂ IH k))
      where
      IH = wsᵗˢ sl hI Θloc σ hσ ts₀
      up : ∀ {x} → x ≤ iterFold S (sizeᵗˢ ts₀) M → x ≤ iterFold S (suc (sizeᵗˢ ts₀)) M
      up h = ≤-trans (≤-trans h (foldStep-infl S _ hS))
                     (node1 S M (sizeᵗˢ ts₀) (suc (sizeᵗˢ ts₀)) hS ≤-refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (mapᵉ {s = s} f₀ e₀) =
      ≤-trans (≤-reflexive (Red.oW-map n sl f e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-map n sl f e)) (FIT INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → FIT (PMI k))
      where
      f   = subΘTm (s ∷ Θloc) σ f₀
      e   = subΘExp Θloc σ e₀
      m   = sizeᵗ f₀ ⊔ sizeᵉ e₀
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM (≤-trans (sizeᵗ-pos f₀) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ f₀) (sizeᵉ e₀)))
              (wsᵗ sl hI (s ∷ Θloc) σ hσ f₀)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ f₀) (sizeᵉ e₀)))
              (wsᵉ sl hI Θloc σ hσ e₀)
      step = node1 S M m (suc (sizeᵗ f₀ + sizeᵉ e₀)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ f₀) (sizeᵉ e₀)) (m≤n+m (sizeᵉ e₀) (sizeᵗ f₀))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ f₀ + sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc (sizeᵗ f₀ + sizeᵉ e₀)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      INN : innWᵗ n sl f + (pmIᵗ n sl 0 f ⊔ 1) * innWᵉ n sl e ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (proj₁ IHf) (T≤TT Tb 1≤T))
                     (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T) (proj₁ (proj₂ IHe)))
      PMI : ∀ k → pmIᵗ n sl (suc k) f + (pmIᵗ n sl 0 f ⊔ 1) * pmIᵉ n sl k e
                    ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (proj₂ (proj₂ IHf) (suc k)) (T≤TT Tb 1≤T))
                       (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T)
                                 (proj₂ (proj₂ (proj₂ IHe)) k))
    wsᵉ {n = n} sl hI Θloc σ hσ (takeᵉ c₀ e₀) =
      ≤-trans (≤-reflexive (Red.oW-take n sl c e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-take n sl c e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      c    = subΘTm Θloc σ c₀
      e    = subΘExp Θloc σ e₀
      Tb   = iterFold S (sizeᵉ e₀) M
      IHe  = wsᵉ sl hI Θloc σ hσ e₀
      step = node1 S M (sizeᵉ e₀) (suc (sizeᵗ c₀ + sizeᵉ e₀)) hS
               (s≤s (m≤n+m (sizeᵉ e₀) (sizeᵗ c₀)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c₀ + sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵉ {n = n} sl hI Θloc σ hσ (mergeAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (mergeAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-merge n sl _) (Red.iW-merge n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (concatAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (concatAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-concat n sl _) (Red.iW-concat n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (switchAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (switchAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-switch n sl _) (Red.iW-switch n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (exhaustAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (exhaustAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-exhaust n sl _) (Red.iW-exhaust n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (μᵉ e₀) =
      ≤-trans (≤-reflexive (Red.oW-μ n sl e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-μ n sl e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      e    = subΘExp Θloc σ e₀
      Tb   = iterFold S (sizeᵉ e₀) M
      IHe  = wsᵉ sl hI Θloc σ hσ e₀
      step = node1 S M (sizeᵉ e₀) (suc (sizeᵉ e₀)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵉ {n = n} sl hI Θloc σ hσ (scanᵉ {s = s} {t = t} f₀ z₀ e₀) =
      ≤-trans (≤-reflexive (Red.oW-scan n sl f z e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-scan n sl f z e)) (FIT2 INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k)) , (λ k → FIT2 (PMI k))
      where
      f   = subΘTm ((t ×ᵗ s) ∷ Θloc) σ f₀
      z   = subΘTm Θloc σ z₀
      e   = subΘExp Θloc σ e₀
      m   = sizeᵗ f₀ ⊔ sizeᵗ z₀ ⊔ sizeᵉ e₀
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos f₀) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))))
              (wsᵗ sl hI ((t ×ᵗ s) ∷ Θloc) σ hσ f₀)
      IHz = Wᵀ-mono sl z (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))))
              (wsᵗ sl hI Θloc σ hσ z₀)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ f₀ ⊔ sizeᵗ z₀) (sizeᵉ e₀))) (wsᵉ sl hI Θloc σ hσ e₀)
      Σ3    = sizeᵗ f₀ + sizeᵗ z₀ + sizeᵉ e₀
      step2 = node2 S M m (suc Σ3) hS
                (s≤s (max3-suc (sizeᵗ f₀) (sizeᵗ z₀) (sizeᵉ e₀)
                        (sizeᵗ-pos f₀) (sizeᵗ-pos z₀) (sizeᵉ-pos e₀)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc Σ3) M
      up0 h = ≤-trans (≤-trans (≤-trans h (foldStep-infl S Tb hS))
                               (foldStep-infl S (foldStep S Tb) hS)) step2
      FIT2 : ∀ {x} → x ≤ Tb ^ Tb * (3 * Tb + 1) → x ≤ iterFold S (suc Σ3) M
      FIT2 h = ≤-trans (≤-trans h (two-folds S Tb hS hT)) step2
      base≤ : pmIᵗ n sl 0 f ⊔ 1 ≤ Tb
      base≤ = ⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T
      pw : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e ≤ Tb ^ Tb
      pw = ≤-trans (^-monoˡ-≤ (outWᵉ n sl e) base≤) (powʳ1 Tb 1≤T (proj₁ IHe))
      INN : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
              * (innWᵗ n sl f + innWᵗ n sl z + innWᵉ n sl e + 1)
            ≤ Tb ^ Tb * (3 * Tb + 1)
      INN = *-mono-≤ pw
              (≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ (proj₁ IHf) (proj₁ IHz))
                                           (proj₁ (proj₂ IHe)))
                                 (≤-refl {1}))
                       (≤-reflexive (thr Tb)))
      PMI : ∀ k → (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
                    * (pmIᵗ n sl (suc k) f + pmIᵗ n sl k z + pmIᵉ n sl k e)
                  ≤ Tb ^ Tb * (3 * Tb + 1)
      PMI k = *-mono-≤ pw
                (≤-trans (+-mono-≤ (+-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                                             (proj₂ (proj₂ IHz) k))
                                   (proj₂ (proj₂ (proj₂ IHe)) k))
                         (≤-trans (≤-reflexive (thr3 Tb)) (m≤m+n (3 * Tb) 1)))

    -- the four *All nodes, which share a clause.  Parameterised by the
    -- child's own bound rather than computing it, so that the count is
    -- the ORIGINAL syntax's size and the child is the substituted one
    wsAll : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) (m : ℕ) → 1 ≤ m →
      (e : Exp Γ Δᵍ Δ Θ (obs t)) (E : Exp Γ Δᵍ Δ Θ t) →
      Wᴱ sl (iterFold S m M) e →
      outWᵉ n sl E ≡ outWᵉ n sl e * innWᵉ n sl e →
      innWᵉ n sl E ≡ innWᵉ n sl e →
      ((k : ℕ) → pmOᵉ n sl k E
                   ≡ outWᵉ n sl e * pmIᵉ n sl k e + pmOᵉ n sl k e * innWᵉ n sl e) →
      ((k : ℕ) → pmIᵉ n sl k E ≡ pmIᵉ n sl k e) →
      Wᴱ sl (iterFold S (suc m) M) E
    wsAll {n = n} sl m 1≤m e E IHe eo ei ep eq =
      ≤-trans (≤-reflexive eo)
              (FIT (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                            (m≤m+n (Tb * Tb) (Tb * Tb))))
      , ≤-trans (≤-reflexive ei) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → ≤-trans (≤-reflexive (ep k))
                 (FIT (+-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                                (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                          (proj₁ (proj₂ IHe))))))
      , (λ k → ≤-trans (≤-reflexive (eq k)) (up0 (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      Tb   = iterFold S m M
      hT   = 4≤iterFold S M m hS hM 1≤m
      step = node1 S M m (suc m) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc m) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc m) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step

    wsᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      Wᵀ sl (iterFold S (sizeᵗ tm) M) (subΘTm Θloc σ tm)
    wsᵗ {n = n} sl hI Θloc σ hσ (varᵗ x) with ∈-++⁻ Θloc x
    ... | inj₁ y =
      z≤n , (λ k → z≤n)
      , (λ k → ite≤ _ (≤-trans (≤ᵇ⇒≤ 1 4 tt) (4≤iterFold S M 1 hS hM ≤-refl)))
    ... | inj₂ z =
      ≤-trans (plug-iW sl _ (lookupEnv σ z))
              (≤-trans (envW-lookup M sl σ hσ z) (iterFold-infl S hS 1 M))
      , (λ k → ≤-trans (≤-reflexive (plug-pO k sl _ (lookupEnv σ z))) z≤n)
      , (λ k → ≤-trans (≤-reflexive (plug-pI k sl _ (lookupEnv σ z))) z≤n)
    wsᵗ sl hI Θloc σ hσ unit̂        = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (bool̂ _)    = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (nat̂ _)     = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (primᵗ _ a) = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (pairᵗ a₀ b₀) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      a   = subΘTm Θloc σ a₀
      b   = subΘTm Θloc σ b₀
      m   = sizeᵗ a₀ ⊔ sizeᵗ b₀
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ a₀)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ b₀)
      step = node1 S M m (suc (sizeᵗ a₀ + sizeᵗ b₀)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ a₀) (sizeᵗ b₀)) (m≤n+m (sizeᵗ b₀) (sizeᵗ a₀))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ a₀ + sizeᵗ b₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵗ sl hI Θloc σ hσ (fstᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (sndᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (inlᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (inrᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (strmᵗ e₀) =
      up0 (proj₁ IHe) , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      where
      Tb   = iterFold S (sizeᵉ e₀) M
      IHe  = wsᵉ sl hI Θloc σ hσ e₀
      step = node1 S M (sizeᵉ e₀) (suc (sizeᵉ e₀)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵗ sl hI Θloc σ hσ (ifᵗ c₀ a₀ b₀) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      a   = subΘTm Θloc σ a₀
      b   = subΘTm Θloc σ b₀
      m   = sizeᵗ a₀ ⊔ sizeᵗ b₀
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ a₀)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ b₀)
      step = node1 S M m (suc (sizeᵗ c₀ + sizeᵗ a₀ + sizeᵗ b₀)) hS
               (s≤s (⊔-lub (≤-trans (m≤n+m (sizeᵗ a₀) (sizeᵗ c₀))
                                    (m≤m+n (sizeᵗ c₀ + sizeᵗ a₀) (sizeᵗ b₀)))
                           (m≤n+m (sizeᵗ b₀) (sizeᵗ c₀ + sizeᵗ a₀))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c₀ + sizeᵗ a₀ + sizeᵗ b₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵗ {n = n} sl hI Θloc σ hσ (caseᵗ {s = s} {t = t} s₀ l₀ r₀) =
      FIT INN , (λ k → FIT (PMO k)) , (λ k → FIT (PMI k))
      where
      sc  = subΘTm Θloc σ s₀
      l   = subΘTm (s ∷ Θloc) σ l₀
      r   = subΘTm (t ∷ Θloc) σ r₀
      m   = sizeᵗ s₀ ⊔ sizeᵗ l₀ ⊔ sizeᵗ r₀
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos s₀) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHs = Wᵀ-mono sl sc (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ s₀) (sizeᵗ l₀)) (m≤m⊔n _ (sizeᵗ r₀))))
              (wsᵗ sl hI Θloc σ hσ s₀)
      IHl = Wᵀ-mono sl l (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ s₀) (sizeᵗ l₀)) (m≤m⊔n _ (sizeᵗ r₀))))
              (wsᵗ sl hI (s ∷ Θloc) σ hσ l₀)
      IHr = Wᵀ-mono sl r (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ s₀ ⊔ sizeᵗ l₀) (sizeᵗ r₀)))
              (wsᵗ sl hI (t ∷ Θloc) σ hσ r₀)
      step = node1 S M m (suc (sizeᵗ s₀ + sizeᵗ l₀ + sizeᵗ r₀)) hS
               (s≤s (⊔-lub (⊔-lub (≤-trans (m≤m+n (sizeᵗ s₀) (sizeᵗ l₀))
                                           (m≤m+n (sizeᵗ s₀ + sizeᵗ l₀) (sizeᵗ r₀)))
                                  (≤-trans (m≤n+m (sizeᵗ l₀) (sizeᵗ s₀))
                                           (m≤m+n (sizeᵗ s₀ + sizeᵗ l₀) (sizeᵗ r₀))))
                           (m≤n+m (sizeᵗ r₀) (sizeᵗ s₀ + sizeᵗ l₀))))
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb →
            x ≤ iterFold S (suc (sizeᵗ s₀ + sizeᵗ l₀ + sizeᵗ r₀)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      C≤ : pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1 ≤ Tb
      C≤ = ⊔-lub (⊔-lub (proj₂ (proj₂ IHl) 0) (proj₂ (proj₂ IHr) 0)) 1≤T
      INN : (innWᵗ n sl l ⊔ innWᵗ n sl r)
              + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * innWᵗ n sl sc
            ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (⊔-lub (proj₁ IHl) (proj₁ IHr)) (T≤TT Tb 1≤T))
                     (*-mono-≤ C≤ (proj₁ IHs))
      PMO : ∀ k → pmOᵗ n sl (suc k) l ⊔ pmOᵗ n sl (suc k) r
                    ⊔ (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmOᵗ n sl k sc
                  ≤ Tb * Tb + Tb * Tb
      PMO k = ⊔-lub (≤-trans (⊔-lub (proj₁ (proj₂ IHl) (suc k))
                                    (proj₁ (proj₂ IHr) (suc k)))
                             (≤-trans (T≤TT Tb 1≤T) (m≤m+n _ _)))
                    (≤-trans (*-mono-≤ C≤ (proj₁ (proj₂ IHs) k)) (m≤m+n _ _))
      PMI : ∀ k → (pmIᵗ n sl (suc k) l ⊔ pmIᵗ n sl (suc k) r)
                    + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmIᵗ n sl k sc
                  ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (⊔-lub (proj₂ (proj₂ IHl) (suc k))
                                       (proj₂ (proj₂ IHr) (suc k)))
                                (T≤TT Tb 1≤T))
                       (*-mono-≤ C≤ (proj₂ (proj₂ IHs) k))

    wsUnary : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) (m : ℕ)
      (p : Tm Γ Δᵍ Δ Θ t) → Wᵀ sl (iterFold S m M) p →
      (innWᵗ n sl p ≤ iterFold S (suc m) M)
      × ((k : ℕ) → pmOᵗ n sl k p ≤ iterFold S (suc m) M)
      × ((k : ℕ) → pmIᵗ n sl k p ≤ iterFold S (suc m) M)
    wsUnary sl m p IH =
      up0 (proj₁ IH) , (λ k → up0 (proj₁ (proj₂ IH) k))
      , (λ k → up0 (proj₂ (proj₂ IH) k))
      where
      Tb   = iterFold S m M
      step = node1 S M m (suc m) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc m) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step

    wsᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
      Wᴸ sl (iterFold S (sizeᵗˢ ts) M) (subΘTms Θloc σ ts)
    wsᵗˢ sl hI Θloc σ hσ []       = z≤n , (λ k → z≤n)
    wsᵗˢ sl hI Θloc σ hσ (y₀ ∷ ys₀) =
      ⊔-lub (proj₁ IHy) (proj₁ IHys)
      , (λ k → ⊔-lub (proj₂ (proj₂ IHy) k) (proj₂ IHys k))
      where
      IHy  = Wᵀ-mono sl (subΘTm Θloc σ y₀)
               (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y₀) (sizeᵗˢ ys₀)))
               (wsᵗ sl hI Θloc σ hσ y₀)
      IHys = Wᴸ-mono sl (subΘTms Θloc σ ys₀)
               (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys₀) (sizeᵗ y₀)))
               (wsᵗˢ sl hI Θloc σ hσ ys₀)

  -- THE PARKED HALF of the same, and it reads the delivered half above
  -- at the defer exactly as wdᵉ does
  mutual
    wsdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      dWᵉ n sl (subΘExp Θloc σ e) ≤ iterFold S (sizeᵉ e) M
    wsdᵉ sl hI Θloc σ hσ (input i) =
      ≤-trans (proj₂ (proj₂ (hI i))) (foldStep-infl S M hS)
    wsdᵉ sl hI Θloc σ hσ emptyᵉ    = z≤n
    wsdᵉ sl hI Θloc σ hσ (varᵉ x)  = z≤n
    wsdᵉ sl hI Θloc σ hσ (ofᵉ ts₀) =
      ≤-trans (wsdᵗˢ sl hI Θloc σ hσ ts₀)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗˢ ts₀) (suc (sizeᵗˢ ts₀)) hS ≤-refl))
    wsdᵉ sl hI Θloc σ hσ (deferᵉ e₀) =
      ≤-trans (⊔-lub (proj₁ (wsᵉ sl hI Θloc σ hσ e₀)) (wsdᵉ sl hI Θloc σ hσ e₀))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵉ e₀) (suc (sizeᵉ e₀)) hS ≤-refl))
    wsdᵉ sl hI Θloc σ hσ (mapᵉ {s = s} f₀ e₀) =
      ≤-trans (⊔-lub (≤-trans (wsdᵗ sl hI (s ∷ Θloc) σ hσ f₀)
                              (mono (m≤m⊔n (sizeᵗ f₀) (sizeᵉ e₀))))
                     (≤-trans (wsdᵉ sl hI Θloc σ hσ e₀)
                              (mono (m≤n⊔m (sizeᵗ f₀) (sizeᵉ e₀)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ f₀ ⊔ sizeᵉ e₀) (suc (sizeᵗ f₀ + sizeᵉ e₀)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ f₀) (sizeᵉ e₀))
                                     (m≤n+m (sizeᵉ e₀) (sizeᵗ f₀))))))
      where mono = iterFold-mono-count S M hS
    wsdᵉ sl hI Θloc σ hσ (takeᵉ c₀ e₀) =
      ≤-trans (⊔-lub (≤-trans (wsdᵗ sl hI Θloc σ hσ c₀)
                              (mono (m≤m⊔n (sizeᵗ c₀) (sizeᵉ e₀))))
                     (≤-trans (wsdᵉ sl hI Θloc σ hσ e₀)
                              (mono (m≤n⊔m (sizeᵗ c₀) (sizeᵉ e₀)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ c₀ ⊔ sizeᵉ e₀) (suc (sizeᵗ c₀ + sizeᵉ e₀)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ c₀) (sizeᵉ e₀))
                                     (m≤n+m (sizeᵉ e₀) (sizeᵗ c₀))))))
      where mono = iterFold-mono-count S M hS
    wsdᵉ sl hI Θloc σ hσ (scanᵉ {s = s} {t = t} f₀ z₀ e₀) =
      ≤-trans (⊔-lub (⊔-lub (≤-trans (wsdᵗ sl hI ((t ×ᵗ s) ∷ Θloc) σ hσ f₀)
                                     (mono up-f))
                            (≤-trans (wsdᵗ sl hI Θloc σ hσ z₀) (mono up-z)))
                     (≤-trans (wsdᵉ sl hI Θloc σ hσ e₀) (mono up-e)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (sizeᵗ f₀ + sizeᵗ z₀ + sizeᵉ e₀)) hS
                         (≤-trans (max3-suc (sizeᵗ f₀) (sizeᵗ z₀) (sizeᵉ e₀)
                                     (sizeᵗ-pos f₀) (sizeᵗ-pos z₀) (sizeᵉ-pos e₀))
                                  (n≤1+n _))))
      where
      m    = sizeᵗ f₀ ⊔ sizeᵗ z₀ ⊔ sizeᵉ e₀
      mono = iterFold-mono-count S M hS
      up-f = ≤-trans (m≤m⊔n (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))
      up-z = ≤-trans (m≤n⊔m (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))
      up-e = m≤n⊔m (sizeᵗ f₀ ⊔ sizeᵗ z₀) (sizeᵉ e₀)
    wsdᵉ sl hI Θloc σ hσ (mergeAllᵉ e₀)   = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (concatAllᵉ e₀)  = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (switchAllᵉ e₀)  = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (exhaustAllᵉ e₀) = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (μᵉ e₀)          = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)

    -- one node's worth of fold, off the child's own bound
    wsPass : ∀ {x : ℕ} (m : ℕ) → x ≤ iterFold S m M → x ≤ iterFold S (suc m) M
    wsPass m h =
      ≤-trans h (≤-trans (foldStep-infl S _ hS) (node1 S M m (suc m) hS ≤-refl))

    wsdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      dWᵗ n sl (subΘTm Θloc σ tm) ≤ iterFold S (sizeᵗ tm) M
    wsdᵗ {n = n} sl hI Θloc σ hσ (varᵗ x) with ∈-++⁻ Θloc x
    ... | inj₁ y = z≤n
    ... | inj₂ z =
      ≤-trans (plug-dW sl _ (lookupEnv σ z))
              (≤-trans (envW-lookup M sl σ hσ z) (iterFold-infl S hS 1 M))
    wsdᵗ sl hI Θloc σ hσ unit̂     = z≤n
    wsdᵗ sl hI Θloc σ hσ (bool̂ _) = z≤n
    wsdᵗ sl hI Θloc σ hσ (nat̂ _)  = z≤n
    wsdᵗ sl hI Θloc σ hσ (strmᵗ e₀) = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵗ sl hI Θloc σ hσ (fstᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (sndᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (inlᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (inrᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (primᵗ _ p₀) = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (pairᵗ a₀ b₀) =
      ≤-trans (⊔-lub (≤-trans (wsdᵗ sl hI Θloc σ hσ a₀)
                              (mono (m≤m⊔n (sizeᵗ a₀) (sizeᵗ b₀))))
                     (≤-trans (wsdᵗ sl hI Θloc σ hσ b₀)
                              (mono (m≤n⊔m (sizeᵗ a₀) (sizeᵗ b₀)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ a₀ ⊔ sizeᵗ b₀) (suc (sizeᵗ a₀ + sizeᵗ b₀)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ a₀) (sizeᵗ b₀))
                                     (m≤n+m (sizeᵗ b₀) (sizeᵗ a₀))))))
      where mono = iterFold-mono-count S M hS
    wsdᵗ sl hI Θloc σ hσ (caseᵗ {s = s} {t = t} s₀ l₀ r₀) =
      wsThree (sizeᵗ s₀) (sizeᵗ l₀) (sizeᵗ r₀)
              (sizeᵗ-pos s₀) (sizeᵗ-pos l₀) (sizeᵗ-pos r₀)
              (wsdᵗ sl hI Θloc σ hσ s₀) (wsdᵗ sl hI (s ∷ Θloc) σ hσ l₀)
              (wsdᵗ sl hI (t ∷ Θloc) σ hσ r₀)
    wsdᵗ sl hI Θloc σ hσ (ifᵗ c₀ a₀ b₀) =
      wsThree (sizeᵗ c₀) (sizeᵗ a₀) (sizeᵗ b₀)
              (sizeᵗ-pos c₀) (sizeᵗ-pos a₀) (sizeᵗ-pos b₀)
              (wsdᵗ sl hI Θloc σ hσ c₀) (wsdᵗ sl hI Θloc σ hσ a₀)
              (wsdᵗ sl hI Θloc σ hσ b₀)

    wsThree : ∀ {x y w : ℕ} (ma mb mc : ℕ) → 1 ≤ ma → 1 ≤ mb → 1 ≤ mc →
      x ≤ iterFold S ma M → y ≤ iterFold S mb M → w ≤ iterFold S mc M →
      x ⊔ y ⊔ w ≤ iterFold S (suc (ma + mb + mc)) M
    wsThree ma mb mc pa pb pc ha hb hc =
      ≤-trans (⊔-lub (⊔-lub (≤-trans ha (mono up-a)) (≤-trans hb (mono up-b)))
                     (≤-trans hc (mono up-c)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (ma + mb + mc)) hS
                         (≤-trans (max3-suc ma mb mc pa pb pc) (n≤1+n _))))
      where
      m    = ma ⊔ mb ⊔ mc
      mono = iterFold-mono-count S M hS
      up-a = ≤-trans (m≤m⊔n ma mb) (m≤m⊔n _ mc)
      up-b = ≤-trans (m≤n⊔m ma mb) (m≤m⊔n _ mc)
      up-c = m≤n⊔m (ma ⊔ mb) mc

    wsdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
      dWᵗˢ n sl (subΘTms Θloc σ ts) ≤ iterFold S (sizeᵗˢ ts) M
    wsdᵗˢ sl hI Θloc σ hσ []         = z≤n
    wsdᵗˢ sl hI Θloc σ hσ (y₀ ∷ ys₀) =
      ⊔-lub (≤-trans (wsdᵗ sl hI Θloc σ hσ y₀)
                     (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y₀) (sizeᵗˢ ys₀))))
            (≤-trans (wsdᵗˢ sl hI Θloc σ hσ ys₀)
                     (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys₀) (sizeᵗ y₀))))

-- THE PIECE THE ROUTE RESTS ON, PROVEN: plugging an M-bounded
-- environment leaves both width faces under one foldStep per node of
-- the ORIGINAL syntax.  subΘExp commutes with every constructor, so
-- every clause's arithmetic is the one wid-iterFold already runs; the
-- two leaves that move are `varᵗ`, where a plug lands and the
-- induction's leaf bound is already M, and the plug itself, whose
-- measures are the plugged value's and whose slopes vanish because it
-- is Θ-closed
wid-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
  (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  (outWᵉ n sl (subΘExp Θloc σ e) ≤ iterFold S (sizeᵉ e) M)
  × (dWᵉ n sl (subΘExp Θloc σ e) ≤ iterFold S (sizeᵉ e) M)
wid-subΘ S M hS hM sl hI Θloc σ hσ e =
  proj₁ (wsᵉ S M hS hM sl hI Θloc σ hσ e) , wsdᵉ S M hS hM sl hI Θloc σ hσ e

-- AND THE EVALUATOR, one foldStep per syntax node of the term.  The
-- caseᵗ clause is the one that moves the seed: the scrutinee's value is
-- pushed on the environment, so the branch runs at the seed the
-- scrutinee's own receipt bought, and the two counts ADD — which is
-- exactly what `sizeᵗ (caseᵗ s l r)` already pays for
evalWith-iterFold : ∀ {n} {Γ : Ctx n} {Θ u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ) → EnvW sl M env →
  pWᵛ n sl u (evalWith tm env) ≤ iterFold S (sizeᵗ tm) M
evalWith-iterFold S M hS hM sl hI (varᵗ x) env hσ =
  ≤-trans (envW-lookup M sl env hσ x) (iterFold-infl S hS 1 M)
evalWith-iterFold S M hS hM sl hI unit̂     env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (bool̂ b) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (nat̂ k)  env hσ = z≤n
evalWith-iterFold {n = n} S M hS hM sl hI (pairᵗ {s = s} {t = u} a b) env hσ =
  ≤-trans (pWᵛ-pair sl s u (evalWith a env) (evalWith b env))
          (⊔-lub (≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
                    (iterFold-mono-count S M hS
                       (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b)) (n≤1+n _))))
                 (≤-trans (evalWith-iterFold S M hS hM sl hI b env hσ)
                    (iterFold-mono-count S M hS
                       (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a)) (n≤1+n _)))))
evalWith-iterFold {n = n} S M hS hM sl hI (fstᵗ {s = s} {t = u} p) env hσ
  with evalWith p env | evalWith-iterFold S M hS hM sl hI p env hσ
... | (a , b) | ih =
  ≤-trans (≤-trans (pWᵛ-fst sl s u a b) ih)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ p)))
evalWith-iterFold {n = n} S M hS hM sl hI (sndᵗ {s = s} {t = u} p) env hσ
  with evalWith p env | evalWith-iterFold S M hS hM sl hI p env hσ
... | (a , b) | ih =
  ≤-trans (≤-trans (pWᵛ-snd sl s u a b) ih)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ p)))
evalWith-iterFold S M hS hM sl hI (inlᵗ a) env hσ =
  ≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ a)))
evalWith-iterFold S M hS hM sl hI (inrᵗ a) env hσ =
  ≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ a)))
evalWith-iterFold S M hS hM sl hI (primᵗ add  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ sub  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ mul  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ eqᵖ  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ ltᵖ  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ notᵖ a) env hσ = z≤n
evalWith-iterFold {n = n} S M hS hM sl hI (strmᵗ e) []ᵃ hσ =
  ⊔-lub (≤-trans (proj₁ (wid-iterFold S M hS hM sl hI e))
                 (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
        (≤-trans (proj₂ (proj₂ (wid-iterFold S M hS hM sl hI e)))
                 (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
evalWith-iterFold {n = n} S M hS hM sl hI (strmᵗ e) (v ∷ᵃ vs) hσ =
  ⊔-lub (≤-trans (proj₁ SUB) (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
        (≤-trans (proj₂ SUB) (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
  where SUB = wid-subΘ S M hS hM sl hI [] (v ∷ᵃ vs) hσ e
evalWith-iterFold S M hS hM sl hI (ifᵗ c a b) env hσ
  with evalWith c env
... | true  = ≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
                (iterFold-mono-count S M hS
                   (≤-trans (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                     (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))
                            (n≤1+n _)))
... | false = ≤-trans (evalWith-iterFold S M hS hM sl hI b env hσ)
                (iterFold-mono-count S M hS
                   (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))
                            (n≤1+n _)))
evalWith-iterFold {n = n} S M hS hM sl hI (caseᵗ {s = s} {t = u} sc l r) env hσ
  with evalWith sc env | evalWith-iterFold S M hS hM sl hI sc env hσ
... | inj₁ x | ih =
  ≤-trans (evalWith-iterFold S M₁ hS
             (≤-trans hM (iterFold-infl S hS (sizeᵗ sc) M)) sl
             (SlotWid-mono sl (iterFold-infl S hS (sizeᵗ sc) M) hI)
             l (x ∷ᵃ env)
             (ih , envW-mono sl env (iterFold-infl S hS (sizeᵗ sc) M) hσ))
          (≤-trans (≤-reflexive (sym (iterFold-+ S (sizeᵗ sc) (sizeᵗ l) M)))
                   (iterFold-mono-count S M hS
                      (≤-trans (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
                               (n≤1+n _))))
  where M₁ = iterFold S (sizeᵗ sc) M
... | inj₂ y | ih =
  ≤-trans (evalWith-iterFold S M₁ hS
             (≤-trans hM (iterFold-infl S hS (sizeᵗ sc) M)) sl
             (SlotWid-mono sl (iterFold-infl S hS (sizeᵗ sc) M) hI)
             r (y ∷ᵃ env)
             (ih , envW-mono sl env (iterFold-infl S hS (sizeᵗ sc) M) hσ))
          (≤-trans (≤-reflexive (sym (iterFold-+ S (sizeᵗ sc) (sizeᵗ r) M)))
                   (iterFold-mono-count S M hS
                      (≤-trans (+-monoˡ-≤ (sizeᵗ r) (m≤m+n (sizeᵗ sc) (sizeᵗ l)))
                               (n≤1+n _))))
  where M₁ = iterFold S (sizeᵗ sc) M

-- THE TWO FACES THE CLUSTER CONSUMES, the width mirrors of
-- applyFn-iterSize / evalTm-iterSize: a closed term evaluates under the
-- telescope's own leaf bound, and a step function under that bound
-- raised to cover its payload
evalTm-iterFold : ∀ {n} {Γ : Ctx n} {u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M → (z : Tm Γ [] [] [] u) →
  pWᵛ n sl u (evalTm z) ≤ iterFold S (sizeᵗ z) M
evalTm-iterFold S M hS hM sl hI z = evalWith-iterFold S M hS hM sl hI z []ᵃ tt

applyFn-iterFold : ∀ {n} {Γ : Ctx n} {s u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (fn : Fn Γ [] [] [] s u) (v : Val Γ s) → pWᵛ n sl s v ≤ M →
  pWᵛ n sl u (applyFn fn v) ≤ iterFold S (sizeᵗ fn) M
applyFn-iterFold S M hS hM sl hI fn v hv =
  evalWith-iterFold S M hS hM sl hI fn (v ∷ᵃ []ᵃ) (hv , tt)

-- THE SEED LIFT, and it is the whole of the syntax-counted width half:
-- a width read `a` folds above the RUNNING width cap is a width at
-- `suc a` levels on.  One fold absorbs the seed's `suc`; the other `a`
-- are the syntax's own
wid-lift : ∀ (c : Caps) (j a : ℕ) → 2 ≤ Caps.cSize c → ∀ {x} →
  x ≤ iterFold (Caps.cSize c) a (suc (Caps.cWid (frameStep j c))) →
  x ≤ Caps.cWid (frameStep (j + suc a) c)
wid-lift c j a 2≤S {x} h =
  ≤-trans h
    (≤-trans (iterFold-mono-w S a 2≤S
                (≤-trans (suc≤foldStep S (iterFold S j W) 2≤S)
                         (≤-reflexive (sym (iterFold-suc S j W)))))
      (≤-reflexive (trans (sym (iterFold-+ S (suc j) a W))
                          (cong (λ y → iterFold S y W) (shuffle j a)))))
  where
  S = Caps.cSize c
  W = Caps.cWid c
  shuffle : ∀ (j a : ℕ) → suc j + a ≡ j + suc a
  shuffle j a = trans (cong suc (+-comm j a))
                      (trans (cong suc (+-comm a j)) (sym (+-suc j a)))

-- the width bridge the μ edge still runs on: its conclusion is a raw
-- dWᵉ on SYNTAX (the unfolding is a syntactic transform of the
-- program), so the count is syntactic and the cap is never read
expWid-fromSize : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (c : Caps) (j a k : ℕ)
  (sl : Slots Γ) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  (e : Exp Γ Δᵍ Δ Θ t) → sizeᵉ e ≤ k →
  dWᵉ n sl e ≤ Caps.cWid (frameStep (j + (a + suc k)) c)
expWid-fromSize {n = n} c j a k sl 2≤S slC e hk =
  subst (λ x → dWᵉ n sl e ≤ iterFold S x W) (sym (+-shuffle j a k))
    (≤-trans (≤-trans (proj₂ (proj₂ (wid-iterFold S (suc W) 2≤S (s≤s z≤n) sl
                                       (slotsCaps?-slotWid S W sl slC) e)))
                      (iterFold-mono-count S (suc W) 2≤S hk))
             (iterFold-lift S W k (j + a) 2≤S))
  where
  S = Caps.cSize c
  W = Caps.cWid c

------------------------------------------------------------------
-- THE WIDENING TOOLKIT, stated here rather than inlined per clause.
--
-- Every clause of the companion tree below runs two or more sub-calls in
-- sequence, and the SECOND one's hypotheses are stated at the first
-- one's OUTPUT level: a bound established at frameStep j has to be read
-- at frameStep (j + j₁), and a value carried out of the first call at
-- frameStep (j + j₁) has to be reported at frameStep ((j + j₁) + j₂).
-- That is the only arithmetic the tree needs — the receipts compose by
-- +-assoc, not by iterating frameStep — so the whole obligation is
-- monotonicity, once per predicate, at ⊑ᶜ.
--
-- Note what is NOT here: a frameStep-COMPOSITION law,
-- frameStep (j + j′) c ≡ frameStep j′ (frameStep j c).  It is FALSE, and
-- not marginally.  frameStep reads its step base S off the ARGUMENT's
-- cSize, so the right-hand side iterates at S = cSize (frameStep j c)
-- while the left iterates at S = cSize c; and the cReg component is
-- linear rather than iterated, cReg c * suc ((j + j′) * S) against
-- cReg c * suc (j * S) * suc (j′ * S).  Neither side is a rewriting of
-- the other.  The tree is shaped to never need it: every companion
-- takes (c , j) rather than a stepped cap, so a sub-call at a later
-- level is the SAME c with a bigger j, and bigger-j is exactly
-- frameStep-mono-j.
------------------------------------------------------------------

⊑ᶜ-trans : ∀ {a b c : Caps} → a ⊑ᶜ b → b ⊑ᶜ c → a ⊑ᶜ c
⊑ᶜ-trans (s₁ , w₁ , r₁) (s₂ , w₂ , r₂) =
  ≤-trans s₁ s₂ , ≤-trans w₁ w₂ , ≤-trans r₁ r₂

-- THE SHAPE THE CLAUSES ACTUALLY USE: spending more folds only widens.
-- Every companion reports `j + j′`, so this is the widening from a
-- sub-call's entry level to its exit level, with no arithmetic at the
-- call site
frameStep-⊑-+ : ∀ (c : Caps) → 2 ≤ Caps.cSize c → ∀ (j j′ : ℕ) →
  frameStep j c ⊑ᶜ frameStep (j + j′) c
frameStep-⊑-+ c hS j j′ = frameStep-mono-j c hS (m≤m+n j j′)

------------------------------------------------------------------
-- THE ABSORPTION MECHANIC — what replaces the joint bound, and the one
-- piece of arithmetic the *All edge runs on.
--
-- Joint-Probe measured `pathLen κ + sizeᵉ b ≤ cSize` FALSE at the tight
-- admissible cSize on all seventeen families, and adm + 1 EXACTLY on
-- every family carrying a scan: the payload being subscribed IS the
-- stored accumulator, so its size alone already attains the cap and any
-- chain at all overshoots.  No constant slackening survives that, so the
-- joint form is gone and the subscribe side carries the two bounds the
-- delivery side can actually supply, `suc (pathLen κ) ≤ cSize` and
-- `sizeᵉ b ≤ cSize`, SEPARATELY.
--
-- WHY THE INDUCTION STILL CLOSES.  Each *All hop extends the chain by
-- ONE from-inner frame and PAYS ONE j for it.  One j at least doubles
-- cSize — frameStep-size-suc says the next level is
-- `sizeStep S B = S * suc (2 B)`, which for S ≥ 1 dominates `suc B` —
-- so the +1 the frame adds fits under the stepped cap with room, and
-- the receipt joins the sum exactly like the fold receipts do.  The
-- chain grows by one per hop and the cap grows by a factor per hop, so
-- the two do not race.
------------------------------------------------------------------

sucB≤sizeStep : ∀ (S B : ℕ) → 1 ≤ S → suc B ≤ sizeStep S B
sucB≤sizeStep S B hS =
  ≤-trans (s≤s (s≤2s B))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * B)))))
                   (*-monoˡ-≤ (suc (2 * B)) hS))

-- ONE HOP: a chain that fits at level j, extended by one frame, fits at
-- level suc j.  This is the whole content of the repair
frameStep-chain-suc : ∀ (c : Caps) (j k : ℕ) → 2 ≤ Caps.cSize c →
  suc k ≤ Caps.cSize (frameStep j c) →
  suc (suc k) ≤ Caps.cSize (frameStep (suc j) c)
frameStep-chain-suc c j k 2≤S h =
  subst (suc (suc k) ≤_) (sym (frameStep-size-suc c j))
    (≤-trans (s≤s h)
             (sucB≤sizeStep (Caps.cSize c) (Caps.cSize (frameStep j c))
                (≤-trans (s≤s z≤n) 2≤S)))

-- THE SAME HOP AT AN ARBITRARY x, which is what a payload subscribe needs
-- rather than a chain: its operator index must be the level's size cap
-- ITSELF and not the cap's successor, so its own `suc (sizeᵉ o) ≤ …`
-- hypothesis has to be got STRICTLY across one frame.  `frameStep-chain
-- -suc` above is the instance `x := suc k`; the strictness in both comes
-- from the same place, that one hop multiplies the cap while the thing
-- being bounded grows by one
frameStep-size-strict-suc : ∀ (c : Caps) (j x : ℕ) → 1 ≤ Caps.cSize c →
  x ≤ Caps.cSize (frameStep j c) →
  suc x ≤ Caps.cSize (frameStep (suc j) c)
frameStep-size-strict-suc c j x 1≤S hx =
  subst (suc x ≤_) (sym (frameStep-size-suc c j))
    (≤-trans (s≤s hx)
             (sucB≤sizeStep (Caps.cSize c) (Caps.cSize (frameStep j c)) 1≤S))

-- and `2 ≤ cSize` survives every level, which the degenerate chains
-- (root, share-sink — both of length zero) need to discharge their own
-- `1 ≤ cSize`
2≤frameStep-size : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  2 ≤ Caps.cSize (frameStep j c)
2≤frameStep-size c j h =
  ≤-trans h (iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h) j (Caps.cSize c))

frameSz?-widen : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) {B B′ : ℕ} →
  B ≤ B′ → frameSz? B f ≡ true → frameSz? B′ f ≡ true
frameSz?-widen (map-f fn)      le h = ≤ᵇ-widen (sizeᵗ fn) le h
frameSz?-widen (scan-f fn _)   le h = ≤ᵇ-widen (sizeᵗ fn) le h
frameSz?-widen (take-f _)      le h = refl
frameSz?-widen (from-inner _ _ _) le h = refl
frameSz?-widen (thru-outer _ _)   le h = refl

valCaps?-widen : ∀ {n} {Γ : Ctx n} {c c′ : Caps} (sl : Slots Γ)
  (u : Ty) (v : Val Γ u) →
  c ⊑ᶜ c′ → valCaps? c sl u v ≡ true → valCaps? c′ sl u v ≡ true
valCaps?-widen {n = n} {c = c} sl u v (sz≤ , wd≤ , _) h
  with ∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (pWᵛ n sl u v ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵛ u v) sz≤ hsz)
                          (≤ᵇ-widen (pWᵛ n sl u v) wd≤ hwd)

-- the two halves of valCaps?, which are literally boundedNode's and
-- widNode's scan-st clauses, so a stored accumulator reads either way
valCaps?-size : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  valCaps? c sl u v ≡ true → (sizeᵛ u v ≤ᵇ Caps.cSize c) ≡ true
valCaps?-size {n = n} c sl u v h =
  proj₁ (∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (pWᵛ n sl u v ≤ᵇ Caps.cWid c) h)

valCaps?-wid : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  valCaps? c sl u v ≡ true → (pWᵛ n sl u v ≤ᵇ Caps.cWid c) ≡ true
valCaps?-wid {n = n} c sl u v h =
  proj₂ (∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (pWᵛ n sl u v ≤ᵇ Caps.cWid c) h)

valsCaps?-widen : ∀ {n} {Γ : Ctx n} {c c′ : Caps} (sl : Slots Γ)
  (u : Ty) (vs : List (Val Γ u)) →
  c ⊑ᶜ c′ → all (valCaps? c sl u) vs ≡ true
          → all (valCaps? c′ sl u) vs ≡ true
valsCaps?-widen sl u vs le =
  all-impl _ _ (λ v → valCaps?-widen sl u v le) vs

eventCaps?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ)
  (ev : InstEvent (Val Γ u)) →
  c ⊑ᶜ c′ → eventCaps? c sl ev ≡ true → eventCaps? c′ sl ev ≡ true
eventCaps?-widen {u = u} sl (value v) le h = valCaps?-widen sl u v le h
eventCaps?-widen sl (init _)    le h = refl
eventCaps?-widen sl (close _ _) le h = refl
eventCaps?-widen sl (handoff _) le h = refl
eventCaps?-widen sl complete    le h = refl

eventsCaps?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ)
  (evs : List (InstEvent (Val Γ u))) →
  c ⊑ᶜ c′ → all (eventCaps? c sl) evs ≡ true
          → all (eventCaps? c′ sl) evs ≡ true
eventsCaps?-widen sl evs le =
  all-impl _ _ (λ ev → eventCaps?-widen sl ev le) evs

burstCaps?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ)
  (str : Stream Γ u) →
  c ⊑ᶜ c′ → burstCaps? c sl str ≡ true → burstCaps? c′ sl str ≡ true
burstCaps?-widen sl str le =
  all-impl _ _ (λ em → eventsCaps?-widen sl (InstEmit.events em) le) str

obsCaps?-widen : ∀ {n} {Γ : Ctx n} {s} {c c′ : Caps} (sl : Slots Γ)
  (o : Closed Γ s) →
  c ⊑ᶜ c′ → obsCaps? c sl o ≡ true → obsCaps? c′ sl o ≡ true
obsCaps?-widen {n = n} {c = c} sl o (sz≤ , wd≤ , _) h
  with ∧-true (sizeᵉ o ≤ᵇ Caps.cSize c) (pWᵉ n sl o ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵉ o) sz≤ hsz)
                          (≤ᵇ-widen (pWᵉ n sl o) wd≤ hwd)

obsListCaps?-widen : ∀ {n} {Γ : Ctx n} {s} {c c′ : Caps} (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  c ⊑ᶜ c′ → all (obsCaps? c sl) q ≡ true
          → all (obsCaps? c′ sl) q ≡ true
obsListCaps?-widen sl q le =
  all-impl _ _ (λ o → obsCaps?-widen sl o le) q

-- rebracketing a two-step receipt.  (j + j₁) + j₂ is what the clauses
-- build; j + (j₁ + j₂) is what they must report
frameStep-+assoc-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j a b : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep ((j + a) + b) c) sched st ≡ true →
  capsOK? (frameStep (j + (a + b)) c) sched st ≡ true
frameStep-+assoc-caps c j a b sched st =
  subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (+-assoc j a b)

frameStep-+assoc-burst : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j a b : ℕ)
  (sl : Slots Γ) (str : Stream Γ u) →
  burstCaps? (frameStep ((j + a) + b) c) sl str ≡ true →
  burstCaps? (frameStep (j + (a + b)) c) sl str ≡ true
frameStep-+assoc-burst c j a b sl str =
  subst (λ x → burstCaps? (frameStep x c) sl str ≡ true) (+-assoc j a b)

-- pathSz? and regsSz? read cSize alone, so they widen at ⊑ᶜ too — same
-- lemmas as above, projected
pathSz?-⊑ : ∀ {n} {Γ : Ctx n} {s t} {c c′ : Caps} (p : Path Γ s t) →
  c ⊑ᶜ c′ → pathSz? (Caps.cSize c) p ≡ true → pathSz? (Caps.cSize c′) p ≡ true
pathSz?-⊑ p (sz≤ , _ , _) = pathSz?-widen p sz≤

pathsSz?-⊑ : ∀ {n} {Γ : Ctx n} {s t} {A : Set} {c c′ : Caps}
  (ps : List (A × Path Γ s t)) →
  c ⊑ᶜ c′ → all (λ rp → pathSz? (Caps.cSize c) (proj₂ rp)) ps ≡ true
          → all (λ rp → pathSz? (Caps.cSize c′) (proj₂ rp)) ps ≡ true
pathsSz?-⊑ ps le = all-impl _ _ (λ rp → pathSz?-⊑ (proj₂ rp) le) ps

-- the burst constructors the delivery clique assembles its emits from
burstCaps?-∷ : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
  all (eventCaps? c sl) (InstEmit.events em) ≡ true →
  burstCaps? c sl str ≡ true →
  burstCaps? c sl (em ∷ str) ≡ true
burstCaps?-∷ c sl em str he hst = ∧-intro he hst

burstCaps?-++ : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (xs ys : Stream Γ u) →
  burstCaps? c sl xs ≡ true → burstCaps? c sl ys ≡ true →
  burstCaps? c sl (xs ++ ys) ≡ true
burstCaps?-++ c sl xs ys hx hy =
  all-++-intro (λ em → all (eventCaps? c sl) (InstEmit.events em)) xs ys hx hy

-- THE SLOT TRANSPORT.  Everything above is at a fixed telescope; this
-- is what moves a bound from one Sched's telescope to another's, and
-- it is a plain subst precisely because the predicates take Slots
valsCaps?-slots : ∀ {n} {Γ : Ctx n} {c : Caps} {sl sl′ : Slots Γ}
  (u : Ty) (vs : List (Val Γ u)) → sl′ ≡ sl →
  all (valCaps? c sl u) vs ≡ true → all (valCaps? c sl′ u) vs ≡ true
valsCaps?-slots {c = c} u vs eq = subst (λ x → all (valCaps? c x u) vs ≡ true) (sym eq)

eventsCaps?-slots : ∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
  (evs : List (InstEvent (Val Γ u))) → sl′ ≡ sl →
  all (eventCaps? c sl) evs ≡ true → all (eventCaps? c sl′) evs ≡ true
eventsCaps?-slots {c = c} evs eq = subst (λ x → all (eventCaps? c x) evs ≡ true) (sym eq)

burstCaps?-slots : ∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
  (str : Stream Γ u) → sl′ ≡ sl →
  burstCaps? c sl str ≡ true → burstCaps? c sl′ str ≡ true
burstCaps?-slots {c = c} str eq = subst (λ x → burstCaps? c x str ≡ true) (sym eq)

obsListCaps?-slots : ∀ {n} {Γ : Ctx n} {s} {c : Caps} {sl sl′ : Slots Γ}
  (q : List (Closed Γ s)) → sl′ ≡ sl →
  all (obsCaps? c sl) q ≡ true → all (obsCaps? c sl′) q ≡ true
obsListCaps?-slots {c = c} q eq = subst (λ x → all (obsCaps? c x) q ≡ true) (sym eq)

-- and the two event-list constructors the delivery clique builds emits
-- from: a payload list becomes `value` events, a completion flag becomes
-- at most a `complete`
mapValue-caps : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ)
  (u : Ty) (vs : List (Val Γ u)) →
  all (valCaps? c sl u) vs ≡ true → all (eventCaps? c sl) (map value vs) ≡ true
mapValue-caps c sl u []       h = refl
mapValue-caps c sl u (v ∷ vs) h with ∧-true (valCaps? c sl u v) (all (valCaps? c sl u) vs) h
... | hv , hvs = ∧-intro hv (mapValue-caps c sl u vs hvs)

finList-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ) (b : Bool) →
  all (eventCaps? {n = n} {Γ = Γ} {u = u} c sl)
      (if b then complete ∷ [] else []) ≡ true
finList-caps c sl true  = refl
finList-caps c sl false = refl

closeList-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (src : Source) (b : Bool) →
  all (eventCaps? {n = n} {Γ = Γ} {u = u} c sl)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-caps c sl src true  = refl
closeList-caps c sl src false = refl

