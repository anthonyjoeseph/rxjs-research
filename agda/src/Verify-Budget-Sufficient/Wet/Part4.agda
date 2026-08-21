-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY, part 4 of 6.
--
-- THE WIDTH WALK's 13-member block (one genuine cycle of 12).
--
-- Split from Verify-Budget-Sufficient.Wet on 2026-08-12.  The three
-- multi-member blocks (36/13/5 members, genuine cycles) each get their
-- own module so an edit re-checks one part instead of 4.7k lines.
-- Consumers import the Wet umbrella and are unaffected.

module Verify-Budget-Sufficient.Wet.Part4 where


open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _<_;
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
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡;
                                       +-cancelʳ-≤)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; tabulate; concat; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                _at_from_as_; EmitKind; subscribe;
                                InstEvent; init; value; close; handoff;
                                complete; exhausted;
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
                                dropSource; arrSource; chainsOf; chainsGo;
                                cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; mintSource; mintOrdinal; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; splitBurst; retagEvents;
                                mergeBump; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                concatDrain; innerFinish; innerReact;
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize; capsHgo; capsBase)

-- .Caps re-exports .Keeps-Ring (which re-exports .Measures), so this one
-- import carries the whole stratum below.  It is here for `Caps` /
-- `capsAt` / the supply lemmas only — this module reads NOTHING from the
-- caps FACE, which is why the recurrence was extracted out of it.
open import Verify-Budget-Sufficient.Caps public

------------------------------------------------------------------
-- the Keeps ring and the share-boundary facts moved to
-- .Keeps-Ring: the caps face needs slotsEq too, and a shared
-- prerequisite must not sit inside one of the two faces.
------------------------------------------------------------------
------------------------------------------------------------------
-- the walk contracts, store half — the SHAPE the clause grind
-- threads (receipts E′ ≤ E · spendᴱ … attach with the cost
-- instrumentation; the landing stays in the cores below).  Stated
-- against the frozen instant base W and a ledger position E ≥ 3.
------------------------------------------------------------------


open import Verify-Budget-Sufficient.Wet.Part3 public

------------------------------------------------------------------
-- THE WIDTH WALK's entry point.  Its clause grind and the clique it
-- re-enters follow below; the delivery clique after that.
------------------------------------------------------------------

subscribeE-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id)
  (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeE g b κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

------------------------------------------------------------------
-- (W11-D) THE SUBSCRIPTION CLIQUE, width face.  Same shape as the
-- wet clique — subscribeE re-enters through subscribeAll/pushBurst,
-- through subscribeInner under the *All frames, and through a
-- share's connect — but with Ω flat the whole thing is one
-- preservation statement per clause.  The ONE width mint in the
-- machine is ofᵉ, and it mints exactly its own list, which the
-- entry seed already dominates.
------------------------------------------------------------------

subscribeAll-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWNode Ω ns ≡ true →
  ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeAll g op ns b κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

pushBurst-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (str : Stream Γ s)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω f ≡ true → pathΩ? Ω κ ≡ true → burstΩ? Ω str ≡ true →
  let r = pushBurst g id now f κ str sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

stepFrame-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω f ≡ true → pathΩ? Ω κ ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

subscribeInner-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  (ofWᵛ (obs u) o ≤ᵇ Ω) ≡ true → pathΩ? Ω κ ≡ true →
  let r = subscribeInner g op allNid κ id now o sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ (proj₂ r)) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ (proj₂ r))) ≡ true)

thruConsume-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  (ofWᵛ (obs u) o ≤ᵇ Ω) ≡ true → pathΩ? Ω κ ≡ true →
  let r = thruConsume g op nid κ id now o sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

thruWalk-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  all (λ v → ofWᵛ (obs u) v ≤ᵇ Ω) vals ≡ true →
  let r = thruWalk g op nid κ id now vals sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

concatDrain-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  all (λ o → ofWᵉ o ≤ᵇ Ω) q ≡ true →
  let r = concatDrain g allNid κ id now q sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
     × (all (λ o → ofWᵉ o ≤ᵇ Ω) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)

innerFinish-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

subscribeE-input-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  let r = subscribeE g (input i) κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

sharedSlot-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ d ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeSharedSlot g i d κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

sharedConnect-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ d ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = sharedConnect g i d κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

------------------------------------------------------------------
-- the *All shape: mint, install, subscribe under the thru-outer
-- frame, push the burst
------------------------------------------------------------------

subscribeAll-width Ω g op ns b κ id now sched st inv nΩ bΩ pΩ =
  pushBurst-width Ω g id now (thru-outer op nid) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) refl pΩ (proj₂ IH)
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  sE     = subscribeE g b (thru-outer op nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-width Ω g b (thru-outer op nid ↠ κ) id now sched₁ st₀
             (install-width Ω sched₁ st nid ns nΩ inv) bΩ (∧-intro refl pΩ)

------------------------------------------------------------------
-- the burst re-entry: split each emit, step its frame, reassemble
------------------------------------------------------------------

pushBurst-width Ω g id now f κ [] sched st inv fΩ pΩ bΩ = inv , refl
pushBurst-width {Γ = Γ} {s = s} {u = u} Ω g id now f κ (em ∷ ems) sched st
                inv fΩ pΩ bΩ =
  proj₁ IH ,
  ∧-intro
    (all-++-intro _ (proj₁ (proj₂ sp)) _
      (splitEvents-bk-Ω {u = u} Ω (InstEmit.events em))
      (all-++-intro _ (retagEvents (proj₁ (proj₂ SF))) _
        (retag-Ω {u = u} Ω (proj₁ (proj₂ SF)))
        (all-++-intro _ (map value (proj₁ SF)) _
          (mapValue-Ω Ω u (proj₁ SF) (proj₁ (proj₂ SFw)))
          (finList-Ω Ω (proj₁ (proj₂ (proj₂ SF)))))))
    (proj₂ IH)
  where
  sp  = splitEvents {A = Val Γ u} (InstEmit.events em)
  SF  = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  SFw = stepFrame-width Ω g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
          inv fΩ pΩ
          (splitEvents-vals-Ω {u = u} Ω (InstEmit.events em)
            (proj₁ (∧-true _ _ bΩ)))
  IH  = pushBurst-width Ω g id now f κ ems
          (proj₁ (proj₂ (proj₂ (proj₂ SF))))
          (proj₂ (proj₂ (proj₂ (proj₂ SF))))
          (proj₁ SFw) fΩ pΩ (proj₂ (∧-true _ _ bΩ))

------------------------------------------------------------------
-- the frame dispatch: map is the one real computation (and even it
-- cannot widen), scan and take are proven above, the two *All
-- frames re-enter the clique
------------------------------------------------------------------

stepFrame-width Ω g id now (map-f fn) κ vals fin sched st inv fΩ pΩ vΩ =
  inv , map-applyFn-Ω Ω fn (≤ᵇ⇒≤ _ _ (T-to fΩ)) vals vΩ , refl
stepFrame-width Ω g id now (scan-f fn nid) κ vals fin sched st inv fΩ pΩ vΩ =
  stepFrame-scan-width Ω g id now fn nid κ vals fin sched st inv fΩ vΩ
stepFrame-width Ω g id now (take-f nid) κ vals fin sched st inv fΩ pΩ vΩ =
  stepFrame-take-width Ω g id now nid κ vals fin sched st inv vΩ
stepFrame-width Ω g id now (from-inner op allNid inst) κ vals false sched st
                inv fΩ pΩ vΩ = inv , vΩ , refl
stepFrame-width Ω g id now (from-inner op allNid inst) κ vals true sched st
                inv fΩ pΩ vΩ
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = inv , vΩ , refl
... | false = innerFinish-width Ω g op allNid inst κ id now vals sched st
                inv pΩ vΩ
stepFrame-width Ω g id now (thru-outer op nid) κ vals fin sched st
                inv fΩ pΩ vΩ =
  thruWrap-width Ω op nid fin (proj₁ wr) (proj₁ (proj₂ wr))
    (proj₁ (proj₂ (proj₂ wr))) (proj₂ (proj₂ (proj₂ wr)))
    (proj₁ WK) (proj₁ (proj₂ WK)) (proj₂ (proj₂ WK))
  where
  wr = thruWalk g op nid κ id now vals sched st
  WK = thruWalk-width Ω g op nid κ id now vals sched st inv pΩ vΩ

------------------------------------------------------------------
-- one inner subscription: g0 is the dry stub, gs re-enters
------------------------------------------------------------------

subscribeInner-width Ω g0 op allNid κ id now o sched st inv oΩ pΩ =
  inv , refl , refl
subscribeInner-width {t = t} {u = u} Ω (gs fuel) op allNid κ id now o sched st
                     inv oΩ pΩ =
  proj₁ IH ,
  splitBurst-vals-Ω {s = u} {u = t} Ω (proj₁ sE) (proj₂ IH) ,
  splitBurst-bk-Ω {s = u} {u = t} Ω (proj₁ sE)
  where
  inst   = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc inst }
  sE     = subscribeE fuel o (from-inner op allNid inst ↠ κ) id now sched₀ st
  IH     = subscribeE-width Ω fuel o (from-inner op allNid inst ↠ κ) id now
             sched₀ st inv (≤ᵇ⇒≤ _ _ (T-to oΩ)) (∧-intro refl pΩ)

------------------------------------------------------------------
-- the outer *All walk, one emitted inner at a time
------------------------------------------------------------------

thruConsume-width Ω g mergeᵒ nid κ id now o sched st inv oΩ pΩ =
  mergeBump-width Ω nid done sched₁ st₁ (proj₁ SI) ,
  proj₁ (proj₂ SI) , proj₂ (proj₂ SI)
  where
  SI     = subscribeInner-width Ω g mergeᵒ nid κ id now o sched st inv oΩ pΩ
  SI₄    = subscribeInner g mergeᵒ nid κ id now o sched st
  done   = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
thruConsume-width {u = u} Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st {w} q true od) | nb with w ≟ᵗ u
...   | yes refl =
  install-width Ω sched st nid (concat-st (q ++ o ∷ []) true od)
    (all-++-intro _ q _ nb (∧-intro oΩ refl)) inv ,
  refl , refl
...   | no _ = inv , refl , refl
thruConsume-width {u = u} Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (concat-st q false od) | nb =
  install-width Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (concat-st {t = u} [] (not done) od) refl (proj₁ SI) ,
  proj₁ (proj₂ SI) , proj₂ (proj₂ SI)
  where
  SI   = subscribeInner-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
  SI₄  = subscribeInner g concatᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | nothing | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (scan-st _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (take-st _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (merge-st _ _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (switch-st _ _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (exhaust-st _ _) | _ = inv , refl , refl
thruConsume-width Ω g switchᵒ nid κ id now o sched st inv oΩ pΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
  install-width Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₂ nid
    (switch-st (if done then nothing else just inst) od) refl (proj₁ SI) ,
  proj₁ (proj₂ SI) ,
  all-++-intro _ closes _ (proj₂ KL) (proj₂ (proj₂ SI))
  where
  KL     = switchKill-width Ω cur sched st inv
  closes = proj₁ (switchKill cur sched st)
  sched₁ = proj₁ (proj₂ (switchKill cur sched st))
  st₁    = proj₂ (proj₂ (switchKill cur sched st))
  SI     = subscribeInner-width Ω g switchᵒ nid κ id now o sched₁ st₁
             (proj₁ KL) oΩ pΩ
  SI₄    = subscribeInner g switchᵒ nid κ id now o sched₁ st₁
  inst   = proj₁ SI₄
  done   = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (take-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (exhaust-st _ _)  = inv , refl , refl
thruConsume-width Ω g exhaustᵒ nid κ id now o sched st inv oΩ pΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = inv , refl , refl
... | just (exhaust-st false od) =
  install-width Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (exhaust-st (not done) od) refl (proj₁ SI) ,
  proj₁ (proj₂ SI) , proj₂ (proj₂ SI)
  where
  SI   = subscribeInner-width Ω g exhaustᵒ nid κ id now o sched st inv oΩ pΩ
  SI₄  = subscribeInner g exhaustᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (take-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (switch-st _ _)   = inv , refl , refl

thruWalk-width Ω g op nid κ id now [] sched st inv pΩ vΩ = inv , refl , refl
thruWalk-width {u = u} Ω g op nid κ id now (o ∷ os) sched st inv pΩ vΩ =
  proj₁ IH ,
  all-++-intro _ (proj₁ cr) _ (proj₁ (proj₂ CS)) (proj₁ (proj₂ IH)) ,
  all-++-intro _ (proj₁ (proj₂ cr)) _ (proj₂ (proj₂ CS)) (proj₂ (proj₂ IH))
  where
  CS = thruConsume-width Ω g op nid κ id now o sched st inv
         (proj₁ (∧-true _ _ vΩ)) pΩ
  cr = thruConsume g op nid κ id now o sched st
  IH = thruWalk-width Ω g op nid κ id now os
         (proj₁ (proj₂ (proj₂ cr))) (proj₂ (proj₂ (proj₂ cr)))
         (proj₁ CS) pΩ (proj₂ (∧-true _ _ vΩ))

------------------------------------------------------------------
-- the inner *All frame's drain and finish
------------------------------------------------------------------

concatDrain-width Ω g allNid κ id now [] sched st inv pΩ qΩ =
  inv , refl , refl , refl
concatDrain-width {s = s} Ω g allNid κ id now (o ∷ q) sched st inv pΩ qΩ
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-width Ω g concatᵒ allNid κ id now o sched st inv
         (proj₁ (∧-true (ofWᵉ o ≤ᵇ Ω) _ qΩ)) pΩ
... | (_ , vs , bs , false , sched₁ , st₁) | (inv₁ , vsΩ , bsΩ) =
  inv₁ , vsΩ , bsΩ , proj₂ (∧-true (ofWᵉ o ≤ᵇ Ω) _ qΩ)
... | (_ , vs , bs , true , sched₁ , st₁) | (inv₁ , vsΩ , bsΩ) =
  proj₁ IH ,
  all-++-intro _ vs _ vsΩ (proj₁ (proj₂ IH)) ,
  all-++-intro _ bs _ bsΩ (proj₁ (proj₂ (proj₂ IH))) ,
  proj₂ (proj₂ (proj₂ IH))
  where
  IH = concatDrain-width Ω g allNid κ id now q sched₁ st₁ inv₁ pΩ
         (proj₂ (∧-true (ofWᵉ o ≤ᵇ Ω) _ qΩ))

innerFinish-width Ω g mergeᵒ allNid inst κ id now vals sched st inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od)   =
  install-width Ω sched st allNid (merge-st (pred k) od) refl inv , vΩ , refl
... | nothing                = inv , vΩ , refl
... | just (scan-st _)       = inv , vΩ , refl
... | just (take-st _)       = inv , vΩ , refl
... | just (concat-st _ _ _) = inv , vΩ , refl
... | just (switch-st _ _)   = inv , vΩ , refl
... | just (exhaust-st _ _)  = inv , vΩ , refl
innerFinish-width {s = s} Ω g concatᵒ allNid inst κ id now vals sched st
                  inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-Ω Ω allNid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st {w} q act od) | nb with w ≟ᵗ s
...   | yes refl =
  install-width Ω sched′ st′ allNid (concat-st q′ act′ od)
    (proj₂ (proj₂ (proj₂ DR))) (proj₁ DR) ,
  all-++-intro _ vals _ vΩ (proj₁ (proj₂ DR)) ,
  proj₁ (proj₂ (proj₂ DR))
  where
  DR     = concatDrain-width Ω g allNid κ id now q sched st inv pΩ nb
  dr     = concatDrain g allNid κ id now q sched st
  act′   = proj₁ (proj₂ (proj₂ dr))
  q′     = proj₁ (proj₂ (proj₂ (proj₂ dr)))
  sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
  st′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
...   | no _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | nothing               | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (scan-st _)      | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (take-st _)      | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (merge-st _ _)   | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (switch-st _ _)  | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (exhaust-st _ _) | _ = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
... | just (switch-st (just c) od) with c ≡ᵇ inst
...   | true  =
  install-width Ω sched st allNid (switch-st nothing od) refl inv , vΩ , refl
...   | false = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (switch-st nothing od) = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | nothing                = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (scan-st _)       = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (take-st _)       = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (merge-st _ _)    = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (concat-st _ _ _) = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (exhaust-st _ _)  = inv , vΩ , refl
innerFinish-width Ω g exhaustᵒ allNid inst κ id now vals sched st inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
... | just (exhaust-st act od) =
  install-width Ω sched st allNid (exhaust-st false od) refl inv , vΩ , refl
... | nothing                = inv , vΩ , refl
... | just (scan-st _)       = inv , vΩ , refl
... | just (take-st _)       = inv , vΩ , refl
... | just (merge-st _ _)    = inv , vΩ , refl
... | just (concat-st _ _ _) = inv , vΩ , refl
... | just (switch-st _ _)   = inv , vΩ , refl

------------------------------------------------------------------
-- THE INPUT CLAUSE, width face.  slotOfW-at cuts the one slot's
-- width out of widthOK?'s slots sum; that is all the clause knows.
------------------------------------------------------------------

sharedSlot-width Ω g i d κ id now sched st inv dΩ pΩ
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = inv , refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  = register-width Ω (toℕ i) κ sched st inv pΩ , refl
...   | false = sharedConnect-width Ω g i d κ id now sched st inv dΩ pΩ

sharedConnect-width Ω g0 i d κ id now sched st inv dΩ pΩ = inv , refl
sharedConnect-width Ω (gs fuel) i d κ id now sched st inv dΩ pΩ =
  connectWrap-width Ω i id (burstCompleted (proj₁ SE))
    (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)) (proj₁ IH) (proj₂ IH)
  where
  st₀  = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁  = register (toℕ i) κ st₀
  inv₁ = register-width Ω (toℕ i) κ sched st₀
           (connectShare-width Ω (toℕ i) sched st inv) pΩ
  IH   = subscribeE-width Ω fuel d (share-sink i) id now sched st₁ inv₁ dΩ refl
  SE   = subscribeE fuel d (share-sink i) id now sched st₁

subscribeE-input-width {Γ = Γ} Ω g i κ id now sched st inv pΩ
  with Sched.slots sched i | slotOfW-at Ω i sched st inv

-- a shared def: connect once, ever; then join
... | shared d | dΩ = sharedSlot-width Ω g i d κ id now sched st inv dΩ pΩ

-- a cold with no async tail: born and spent inside its own burst
... | scripted (cold sy []) | sΩ =
      inv ,
      ∧-intro
        (all-++-intro _ (map value sy) _
          (mapValue-Ω Ω (lookup Γ i) sy
            (sumVals-Ω Ω (lookup Γ i) sy (≤-trans (m≤m+n _ 0) sΩ)))
          refl)
        refl

-- a cold WITH a tail: fresh source and ordinal, the tail resolved
-- against this subscription's tick, one registration
... | scripted (cold sy (tv ∷ tvs)) | sΩ =
      register-width Ω src κ sched₃ st inv₃ pΩ ,
      ∧-intro (mapValue-Ω Ω (lookup Γ i) sy syΩ) refl
      where
      src    = Sched.nextSource sched
      sched₁ = proj₂ (mintSource sched)
      ord    = Sched.nextOrdinal sched₁
      sched₂ = proj₂ (mintOrdinal sched₁)
      anchored : LiveSource Γ
      anchored = record { source = src ; ordinal = ord ; elemTy = lookup Γ i
                        ; pending = resolve now (tv ∷ tvs) }
      sched₃ = record sched₂ { live = anchored ∷ Sched.live sched₂ }
      -- both summands named: nothing can recover the sync side by
      -- inverting _+_
      syncW  = sum (map (ofWᵛ (lookup Γ i)) sy)
      tailW  = sum (map (λ p → ofWᵛ (lookup Γ i) (Timed.val p)) (tv ∷ tvs))
      syΩ    = sumVals-Ω Ω (lookup Γ i) sy (≤-trans (m≤m+n syncW tailW) sΩ)
      inv₃   = addLive-width Ω sched₂ st anchored
                 (resolve-measure (ofWᵛ (lookup Γ i)) Ω now (tv ∷ tvs)
                   (≤-trans (m≤n+m tailW syncW) sΩ))
                 inv

-- a hot: already live at the slot's own source/ordinal
... | scripted (hot _) | sΩ
      with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = inv , refl
...   | false = register-width Ω (toℕ i) κ sched st inv pΩ , refl

------------------------------------------------------------------
-- deferᵉ: mint a node, a source and an ordinal, install the merge
-- node, park the BODY as the lone pending value of a fresh live
-- source, register the outer chain.  A parked obs value's width IS
-- the body's own, so the live entry needs no arithmetic.
------------------------------------------------------------------

subscribeE-defer-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (body : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ body ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeE g (deferᵉ body) κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)
subscribeE-defer-width {Γ = Γ} {u = u} Ω g body κ id now sched st inv bΩ pΩ =
  register-width Ω src (thru-outer mergeᵒ nid ↠ κ) sched₄ st₀ inv₂
    (∧-intro refl pΩ) ,
  refl
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  src    = proj₁ (mintSource sched₁)
  sched₂ = proj₂ (mintSource sched₁)
  ord    = proj₁ (mintOrdinal sched₂)
  sched₃ = proj₂ (mintOrdinal sched₂)
  hop : LiveSource Γ
  hop = record { source = src ; ordinal = ord ; elemTy = obs u
               ; pending = (suc now , body) ∷ [] }
  sched₄ = record sched₃ { live = hop ∷ Sched.live sched₃ }
  st₀    = installNode nid (merge-st 0 false) st
  inv₂   = addLive-width Ω sched₃ st₀ hop
             (∧-intro (T⇒≡true _ (≤⇒≤ᵇ bΩ)) refl)
             (install-width Ω sched₃ st nid (merge-st 0 false) refl inv)

------------------------------------------------------------------
-- THE WIDTH WALK ITSELF.  Thirteen clauses, each a ⊔-projection of
-- the entry bound: ofᵉ is the only width MINT and it mints exactly
-- its own list; every other clause hands its sub-bound down.
------------------------------------------------------------------

subscribeE-width Ω g (input i) κ id now sched st inv bΩ pΩ =
  subscribeE-input-width Ω g i κ id now sched st inv pΩ

subscribeE-width {Γ = Γ} {u = u} Ω g (ofᵉ ts) κ id now sched st inv bΩ pΩ =
  inv ,
  ∧-intro
    (∧-intro refl
      (all-++-intro _ (map value (map (λ tm → evalTm tm) ts)) _
        (mapValue-Ω Ω u (map (λ tm → evalTm tm) ts)
          (ofVals-Ω Ω ts (≤-trans (m≤n⊔m (length ts) (ofWᵗˢ ts)) bΩ)))
        refl))
    refl

subscribeE-width Ω g emptyᵉ κ id now sched st inv bΩ pΩ = inv , refl

subscribeE-width Ω g (mapᵉ f b) κ id now sched st inv bΩ pΩ =
  pushBurst-width Ω g id now (map-f f) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) fΩ pΩ (proj₂ IH)
  where
  ofwf = ≤-trans (m≤m⊔n (ofWᵗ f) (ofWᵉ b)) bΩ
  ofwb = ≤-trans (m≤n⊔m (ofWᵗ f) (ofWᵉ b)) bΩ
  fΩ : frameΩ? Ω (map-f f) ≡ true
  fΩ = T⇒≡true _ (≤⇒≤ᵇ ofwf)
  sE = subscribeE g b (map-f f ↠ κ) id now sched st
  IH = subscribeE-width Ω g b (map-f f ↠ κ) id now sched st inv ofwb
         (∧-intro fΩ pΩ)

subscribeE-width Ω g (takeᵉ count b) κ id now sched st inv bΩ pΩ
  with evalTm count
... | zero  = inv , refl
... | suc k =
  pushBurst-width Ω g id now (take-f nid) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) refl pΩ (proj₂ IH)
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  ofwb   = ≤-trans (m≤n⊔m (ofWᵗ count) (ofWᵉ b)) bΩ
  sE     = subscribeE g b (take-f nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-width Ω g b (take-f nid ↠ κ) id now sched₁ st₀
             (install-width Ω sched₁ st nid (take-st (suc k)) refl inv)
             ofwb (∧-intro refl pΩ)

subscribeE-width {Γ = Γ} {u = u} Ω g (scanᵉ f z b) κ id now sched st inv bΩ pΩ =
  pushBurst-width Ω g id now (scan-f f nid) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) fΩ pΩ (proj₂ IH)
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  -- ofWᵉ (scanᵉ f z b) = ofWᵗ f ⊔ (ofWᵗ z ⊔ ofWᵉ b)
  ofwf = ≤-trans (m≤m⊔n (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ b)) bΩ
  ofwz = ≤-trans (m≤m⊔n (ofWᵗ z) (ofWᵉ b))
           (≤-trans (m≤n⊔m (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ b)) bΩ)
  ofwb = ≤-trans (m≤n⊔m (ofWᵗ z) (ofWᵉ b))
           (≤-trans (m≤n⊔m (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ b)) bΩ)
  fΩ : frameΩ? Ω (scan-f f nid) ≡ true
  fΩ = T⇒≡true _ (≤⇒≤ᵇ ofwf)
  st₀  = installNode nid (scan-st (evalTm z)) st
  seed = ofW-evalWith Ω z []ᵃ tt ofwz
  sE   = subscribeE g b (scan-f f nid ↠ κ) id now sched₁ st₀
  IH   = subscribeE-width Ω g b (scan-f f nid ↠ κ) id now sched₁ st₀
           (install-width Ω sched₁ st nid (scan-st (evalTm z))
             (T⇒≡true _ (≤⇒≤ᵇ seed)) inv)
           ofwb (∧-intro fΩ pΩ)

subscribeE-width Ω g (mergeAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g mergeᵒ (merge-st 0 false) b κ id now sched st
    inv refl bΩ pΩ
subscribeE-width {u = u} Ω g (concatAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g concatᵒ (concat-st {t = u} [] false false) b κ id now
    sched st inv refl bΩ pΩ
subscribeE-width Ω g (switchAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g switchᵒ (switch-st nothing false) b κ id now sched st
    inv refl bΩ pΩ
subscribeE-width Ω g (exhaustAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g exhaustᵒ (exhaust-st false false) b κ id now sched st
    inv refl bΩ pΩ

subscribeE-width Ω g0 (μᵉ body) κ id now sched st inv bΩ pΩ = inv , refl
subscribeE-width Ω (gs fuel) (μᵉ body) κ id now sched st inv bΩ pΩ =
  subscribeE-width Ω fuel (unfoldμ body) κ id now sched st inv ofwU pΩ
  where
  ofwU : ofWᵉ (unfoldμ body) ≤ Ω
  ofwU = ≤-trans (ofW-elimG (here refl) (μᵉ body) body) (⊔-lub bΩ bΩ)

subscribeE-width Ω g (varᵉ ()) κ id now sched st inv bΩ pΩ

subscribeE-width Ω g (deferᵉ body) κ id now sched st inv bΩ pΩ =
  subscribeE-defer-width Ω g body κ id now sched st inv bΩ pΩ
