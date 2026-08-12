-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY, part 5 of 6.
--
-- foldPath-width's 5-member block (one genuine cycle of 3).
--
-- Split from Verify-Budget-Sufficient.Wet on 2026-08-12.  The three
-- multi-member blocks (36/13/5 members, genuine cycles) each get their
-- own module so an edit re-checks one part instead of 4.7k lines.
-- Consumers import the Wet umbrella and are unaffected.

module Verify-Budget-Sufficient.Wet.Part5 where


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
open import Data.List.Properties using (length-++)
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
                                complete; exhausted;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                subΘExp; subΘTm; subΘTms;
                                plugsᵉ; plugsᵗ; plugsᵗˢ;
                                occsᵉ; occsᵗ; occsᵗˢ; varIx;
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
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ;
                                 pm-elimGᵉ; pm-elimGᵗ; pm-elimGᵗˢ;
                                 hopD-elimGᵉ; hopD-elimGᵗ; hopD-elimGᵗˢ;
                                 hopD-unfoldμ)
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


open import Verify-Budget-Sufficient.Wet.Part4 public

------------------------------------------------------------------
-- (W11-C) THE DELIVERY CLIQUE, width face.  Same lexicographic
-- recursion as the wet clique — (dispatch gas, path), frame hops
-- shrinking the path at constant gas and the share hop peeling one
-- gas — but with Ω flat there is no receipt to thread and no
-- widening at the joins, so each clause is its wet twin with the
-- ledger bookkeeping struck out.
------------------------------------------------------------------

foldPath-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  pathΩ? Ω path ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vals ≡ true →
  all (eventΩ? Ω) evs ≡ true →
  let r = foldPath sf gas id now envSrc path vals evs fin sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

dispatchShare-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ (lookup Γ i) v ≤ᵇ Ω) vals ≡ true →
  let r = dispatchShare sf gas id now i vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

shareGo-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ rp → pathΩ? Ω (proj₂ rp)) ps ≡ true →
  all (λ v → ofWᵛ (lookup Γ i) v ≤ᵇ Ω) vals ≡ true →
  let r = shareGo sf gas id now i vals fin ps sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

chainStep-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  pathΩ? Ω path ≡ true →
  (ofWᵛ (arrTy a) (arrVal a) ≤ᵇ Ω) ≡ true →
  let r = chainStep id a path sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

cascadeGo-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  (ofWᵛ (arrTy a) (arrVal a) ≤ᵇ Ω) ≡ true →
  all (λ rc → pathΩ? Ω (proj₂ rc)) chains ≡ true →
  let r = cascadeGo a id chains sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

-- the root: assemble the envelope
foldPath-width {u = u} Ω sf gas id now envSrc root vals evs fin sched st
               inv pΩ vΩ eΩ =
  inv ,
  ∧-intro
    (all-++-intro _ evs _ eΩ
      (all-++-intro _ (map value vals) _
        (mapValue-Ω Ω u vals vΩ)
        (finList-Ω Ω fin)))
    refl

-- the share boundary: valueless handoff emit, then the fan-out
foldPath-width Ω sf gas id now envSrc (share-sink i) vals evs fin sched st
               inv pΩ vΩ eΩ =
  proj₁ DS , ∧-intro (all-++-intro _ evs _ eΩ refl) (proj₂ DS)
  where
  DS = dispatchShare-width Ω sf gas id now i vals fin sched st inv vΩ

-- a frame hop: step it, then keep folding down the shorter path
foldPath-width Ω sf gas id now envSrc (f ↠ path′) vals evs fin sched st
               inv pΩ vΩ eΩ = IH
  where
  fΩ   = proj₁ (∧-true (frameΩ? Ω f) _ pΩ)
  pΩ′  = proj₂ (∧-true (frameΩ? Ω f) _ pΩ)
  SF   = stepFrame-width Ω sf id now f path′ vals fin sched st inv fΩ pΩ′ vΩ
  step = stepFrame sf id now f path′ vals fin sched st
  IH   = foldPath-width Ω sf gas id now envSrc path′ (proj₁ step)
           (evs ++ proj₁ (proj₂ step)) (proj₁ (proj₂ (proj₂ step)))
           (proj₁ (proj₂ (proj₂ (proj₂ step))))
           (proj₂ (proj₂ (proj₂ (proj₂ step))))
           (proj₁ SF) pΩ′ (proj₁ (proj₂ SF))
           (all-++-intro _ evs _ eΩ (proj₂ (proj₂ SF)))

-- out of dispatch gas: unreachable in a real run, free when it fires
dispatchShare-width Ω sf zero id now i vals fin sched st inv vΩ = inv , refl
dispatchShare-width Ω sf (suc gas) id now i vals fin sched st inv vΩ =
  shareFinish-width Ω i fin (proj₁ GOr)
    (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr)) (proj₁ GO) ,
  subst (λ b → burstΩ? Ω b ≡ true)
        (sym (shareFinish-burst i fin (proj₁ GOr)
               (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))))
        (proj₂ GO)
  where
  st₀  = shareLatch i fin st
  adm  = shareAdmit i (EvalSt.registry st)
  admΩ = shareAdmit-Ω Ω i (EvalSt.registry st)
           (proj₁ (proj₂ (proj₂ (WOK-parts Ω sched st inv))))
  GO   = shareGo-width Ω sf gas id now i vals fin adm sched st₀
           (shareLatch-width Ω i fin sched st inv) admΩ vΩ
  GOr  = shareGo sf gas id now i vals fin adm sched st₀

shareGo-width Ω sf gas id now i vals fin [] sched st inv pΩ vΩ = inv , refl
shareGo-width {Γ = Γ} Ω sf gas id now i vals fin ((rid , q) ∷ ps) sched st
              inv pΩ vΩ
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
-- cut earlier this cascade: its close already rode the cutting emit
... | true  = shareGo-width Ω sf gas id now i vals fin ps sched st inv
                (proj₂ (∧-true (pathΩ? Ω q) _ pΩ)) vΩ
... | false = proj₁ IH ,
              all-++-intro _ (proj₁ FPr) _ (proj₂ FP) (proj₂ IH)
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  FP  = foldPath-width Ω sf gas id now (toℕ i) q vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
          (delivered-width Ω rid sched st inv)
          (proj₁ (∧-true (pathΩ? Ω q) _ pΩ)) vΩ
          (closeList-Ω Ω (toℕ i) fin)
  FPr = foldPath sf gas id now (toℕ i) q vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
  IH  = shareGo-width Ω sf gas id now i vals fin ps
          (proj₁ (proj₂ FPr)) (proj₂ (proj₂ FPr)) (proj₁ FP)
          (proj₂ (∧-true (pathΩ? Ω q) _ pΩ)) vΩ

chainStep-width {n = n} {e = e} Ω id a path sched st inv pΩ vΩ =
  foldPath-width Ω (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st inv pΩ (∧-intro vΩ refl)
    (closeList-Ω Ω (arrSource a) (Arrival.isLast a))

-- the cascade fold: one emit per surviving registration, in
-- subscription order
cascadeGo-width Ω a id []                   sched st inv vΩ pΩ = inv , refl
cascadeGo-width Ω a id ((rid , c) ∷ chains) sched st inv vΩ pΩ
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-width Ω a id chains sched st inv vΩ
                (proj₂ (∧-true (pathΩ? Ω c) _ pΩ))
... | false = proj₁ IH , all-++-intro _ (proj₁ CSr) _ (proj₂ CS) (proj₂ IH)
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  CS  = chainStep-width Ω id a c sched st₀
          (delivered-width Ω rid sched st inv)
          (proj₁ (∧-true (pathΩ? Ω c) _ pΩ)) vΩ
  CSr = chainStep id a c sched st₀
  IH  = cascadeGo-width Ω a id chains
          (proj₁ (proj₂ CSr)) (proj₂ (proj₂ CSr)) (proj₁ CS) vΩ
          (proj₂ (∧-true (pathΩ? Ω c) _ pΩ))
