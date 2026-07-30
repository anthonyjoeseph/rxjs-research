-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY, and the theorem.
--
-- The half that steps the evaluator.  The Keeps ring (slot/share
-- monotonicity), the size-elim laws, the ledger arithmetic, the wet
-- lemmas for every evaluator entry point, subscribeE-walkS and
-- subscribeAll-wet, cascadeGo-walk, the width family, and then the four
-- results that compose them: burst-wet, cascade-dry, drain-dry, and
-- budget-sufficient.
--
-- budget-sufficient IS the export Verify-Well-Formed consumes, and it
-- lives here rather than at the top so that grinding the caps face does
-- not re-check Verify-Well-Formed.
--
-- This module is a SIBLING of .Caps-Face: it never mentions Caps.
module Verify-Budget-Sufficient.Wet where

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
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; all; any; length;
                                sum; tabulate; concat; map)
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
                                shellsᵉ; shellsᵛ;
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
                                dropSource; arrSource; chainsOf; cascadeGo;
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
                                budgetAt; slotsSize)

open import Verify-Budget-Sufficient.Keeps-Ring public

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

-- the node-install ring's fnCap face (mirror of setNode-bounded /
-- install-bounded: setNode either replaces the hit key or recurses
-- past a survivor, and the live half is untouched)
setNode-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  fnCapNode Ψ ns ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-fnCap Ψ nid ns []             bn h = ∧-intro bn refl
setNode-fnCap Ψ nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-fnCap Ψ nid ns r bn (proj₂ (∧-true _ _ h)))

install-fnCap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  fnCapNode Ψ ns ≡ true → fnCapBounded? Ψ sched st ≡ true →
  fnCapBounded? Ψ sched (installNode nid ns st) ≡ true
install-fnCap Ψ sched st nid ns bn h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (setNode-fnCap Ψ nid ns (EvalSt.nodes st) bn (proj₂ (∧-true _ _ h)))


lift1 : ∀ {M} → 1 ≤ M → 1 ≤ 1 * M
lift1 {M} h = ≤-trans h (≤-reflexive (sym (+-identityʳ M)))

-- subst on the Δ-index of Exp is transparent to sizeᵉ
size-substᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Δ′ Θ t} (p : Δ ≡ Δ′) (e : Exp Γ Δᵍ Δ Θ t) →
  sizeᵉ (subst (λ ζ → Exp Γ Δᵍ ζ Θ t) p e) ≡ sizeᵉ e
size-substᴱ refl e = refl

-- elimination copies the closure at ≤ one var position per node, so
-- size grows by at most the closure's own size.  Same sucmul/sum
-- skeleton as size-subΘᵉ; only elimD's hit clause plants the copy.
mutual
  size-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    sizeᵉ (elimGExp x cl e) ≤ sizeᵉ e * sizeᵉ cl
  size-elimGᵉ x cl (input i)       = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (ofᵉ ts)        =
    sucmul (sizeᵗˢ ts) (sizeᵉ cl) (size-elimGᵗˢ x cl ts) (sizeᵉ-pos cl)
  size-elimGᵉ x cl emptyᵉ          = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (mapᵉ f e)      =
    sucmul (sizeᵗ f + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ f) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl f) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (takeᵉ c e)     =
    sucmul (sizeᵗ c + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ c) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl c) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (scanᵉ f z e)   =
    sucmul ((sizeᵗ f + sizeᵗ z) + sizeᵉ e) (sizeᵉ cl)
      (sum3 (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl f) (size-elimGᵗ x cl z) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (mergeAllᵉ e)   =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (concatAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (switchAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (exhaustAllᵉ e) =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (μᵉ e)          =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ (there x) cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (varᵉ y)        = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (deferᵉ e)      =
    sucmul (sizeᵉ e) (sizeᵉ cl)
      (≤-trans (≤-reflexive (size-substᴱ (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e)))
               (size-elimDᵉ (∈-++⁺ˡ x) cl e))
      (sizeᵉ-pos cl)

  size-elimDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    sizeᵉ (elimDExp x cl e) ≤ sizeᵉ e * sizeᵉ cl
  size-elimDᵉ x cl (input i)       = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (ofᵉ ts)        =
    sucmul (sizeᵗˢ ts) (sizeᵉ cl) (size-elimDᵗˢ x cl ts) (sizeᵉ-pos cl)
  size-elimDᵉ x cl emptyᵉ          = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (mapᵉ f e)      =
    sucmul (sizeᵗ f + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ f) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl f) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (takeᵉ c e)     =
    sucmul (sizeᵗ c + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ c) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl c) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (scanᵉ f z e)   =
    sucmul ((sizeᵗ f + sizeᵗ z) + sizeᵉ e) (sizeᵉ cl)
      (sum3 (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl f) (size-elimDᵗ x cl z) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (mergeAllᵉ e)   =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (concatAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (switchAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (exhaustAllᵉ e) =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (μᵉ e)          =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (varᵉ y)        with compare∈ x y
  ... | inj₁ refl =
    ≤-trans (≤-reflexive (size-renᵉ (λ ()) (λ ()) (λ ()) cl))
            (≤-reflexive (sym (+-identityʳ (sizeᵉ cl))))
  ... | inj₂ y′   = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (deferᵉ e)      =
    sucmul (sizeᵉ e) (sizeᵉ cl)
      (≤-trans (≤-reflexive (size-substᴱ (⊟-++ʳ x) (elimDExp (∈-++⁺ʳ _ x) cl e)))
               (size-elimDᵉ (∈-++⁺ʳ _ x) cl e))
      (sizeᵉ-pos cl)

  size-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    sizeᵗ (elimGTm x cl tm) ≤ sizeᵗ tm * sizeᵉ cl
  size-elimGᵗ x cl (varᵗ y)      = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl unit̂          = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (bool̂ _)      = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (nat̂ _)       = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (pairᵗ a b)   =
    sucmul (sizeᵗ a + sizeᵗ b) (sizeᵉ cl)
      (sum2 (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimGᵗ x cl a) (size-elimGᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (fstᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimGᵗ x cl p) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (sndᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimGᵗ x cl p) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (inlᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (inrᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (caseᵗ s l r) =
    sucmul ((sizeᵗ s + sizeᵗ l) + sizeᵗ r) (sizeᵉ cl)
      (sum3 (sizeᵗ s) (sizeᵗ l) (sizeᵗ r) (sizeᵉ cl)
            (size-elimGᵗ x cl s) (size-elimGᵗ x cl l) (size-elimGᵗ x cl r))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (ifᵗ c a b)   =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (sizeᵉ cl)
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimGᵗ x cl c) (size-elimGᵗ x cl a) (size-elimGᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (primᵗ _ a)   =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (strmᵗ e)     =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)

  size-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    sizeᵗ (elimDTm x cl tm) ≤ sizeᵗ tm * sizeᵉ cl
  size-elimDᵗ x cl (varᵗ y)      = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl unit̂          = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (bool̂ _)      = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (nat̂ _)       = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (pairᵗ a b)   =
    sucmul (sizeᵗ a + sizeᵗ b) (sizeᵉ cl)
      (sum2 (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimDᵗ x cl a) (size-elimDᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (fstᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimDᵗ x cl p) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (sndᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimDᵗ x cl p) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (inlᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (inrᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (caseᵗ s l r) =
    sucmul ((sizeᵗ s + sizeᵗ l) + sizeᵗ r) (sizeᵉ cl)
      (sum3 (sizeᵗ s) (sizeᵗ l) (sizeᵗ r) (sizeᵉ cl)
            (size-elimDᵗ x cl s) (size-elimDᵗ x cl l) (size-elimDᵗ x cl r))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (ifᵗ c a b)   =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (sizeᵉ cl)
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimDᵗ x cl c) (size-elimDᵗ x cl a) (size-elimDᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (primᵗ _ a)   =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (strmᵗ e)     =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)

  size-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    sizeᵗˢ (elimGTms x cl ts) ≤ sizeᵗˢ ts * sizeᵉ cl
  size-elimGᵗˢ x cl []       = lift1 (sizeᵉ-pos cl)
  size-elimGᵗˢ x cl (y ∷ ys) =
    sum2 (sizeᵗ y) (sizeᵗˢ ys) (sizeᵉ cl)
         (size-elimGᵗ x cl y) (size-elimGᵗˢ x cl ys)

  size-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    sizeᵗˢ (elimDTms x cl ts) ≤ sizeᵗˢ ts * sizeᵉ cl
  size-elimDᵗˢ x cl []       = lift1 (sizeᵉ-pos cl)
  size-elimDᵗˢ x cl (y ∷ ys) =
    sum2 (sizeᵗ y) (sizeᵗˢ ys) (sizeᵉ cl)
         (size-elimDᵗ x cl y) (size-elimDᵗˢ x cl ys)

-- the μ-copy size bound: unfolding plants (μᵉ body) at the body's
-- global-var positions, so the copy is at most sizeᵉ (μᵉ body) squared
size-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  sizeᵉ (unfoldμ body) ≤ sizeᵉ (μᵉ body) * sizeᵉ (μᵉ body)
size-unfoldμ body =
  ≤-trans (size-elimGᵉ (here refl) (μᵉ body) body)
          (*-monoˡ-≤ (sizeᵉ (μᵉ body)) (n≤1+n (sizeᵉ body)))


------------------------------------------------------------------
-- THE LEDGER RULE, PROVEN — memo (2)'s one uniform step: an eval
-- edge at position E ≥ 2 lands within E · 3^(suc Ψ).  This is the
-- design's load-bearing arithmetic, machine-checked: grow-pow
-- re-bases the grown store, the exponents collapse by
-- ^-*-assoc/^-distrib, and ledger-step is the ℕ inequality
-- E + (E+2)·3^w ≤ E·3^(suc Ψ).
------------------------------------------------------------------

ledger-step : ∀ (E w Ψ : ℕ) → 2 ≤ E → w ≤ Ψ →
  E + (E + 2) * 3 ^ w ≤ E * 3 ^ suc Ψ
ledger-step E w Ψ 2≤E w≤Ψ =
  ≤-trans (+-mono-≤ E≤E3w (*-monoˡ-≤ (3 ^ w) E+2≤2E))
  (≤-trans (≤-reflexive shuffle)
           (*-monoʳ-≤ E (^-monoʳ-≤ 3 (s≤s w≤Ψ))))
  where
  E+2≤2E : E + 2 ≤ 2 * E
  E+2≤2E = ≤-trans (+-monoʳ-≤ E 2≤E)
                   (≤-reflexive (cong (E +_) (sym (+-identityʳ E))))
  E≤E3w : E ≤ E * 3 ^ w
  E≤E3w = ≤-trans (≤-reflexive (sym (*-identityʳ E)))
                  (*-monoʳ-≤ E (one≤3^ w))
  shuffle : E * 3 ^ w + 2 * E * 3 ^ w ≡ E * (3 * 3 ^ w)
  shuffle = solve 2
    (λ e x → e :* x :+ con 2 :* e :* x := e :* (con 3 :* x)) refl
    E (3 ^ w)

-- one eval edge, end to end: everything within the current cap in,
-- result within the cap at E · 3^(suc Ψ) out
evalStep-cap : ∀ {n} {Γ : Ctx n} {s t} (Ψ W E : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  2 ≤ E → caseWᵗ fn ≤ Ψ →
  sizeᵗ fn ≤ capᴱ W E → sizeᵛ s v ≤ capᴱ W E →
  sizeᵛ t (applyFn fn v) ≤ capᴱ W (E * 3 ^ suc Ψ)
evalStep-cap Ψ W E fn v 2≤E w≤Ψ hf hv =
  ≤-trans (applyFn-sharp (capᴱ W E) fn v hv hf)
  (≤-trans (*-mono-≤ hf (^-monoˡ-≤ (3 ^ caseWᵗ fn) (grow-pow W E)))
  (≤-trans (≤-reflexive collapse)
           (capᴱ-mono W (ledger-step E (caseWᵗ fn) Ψ 2≤E w≤Ψ))))
  where
  collapse : capᴱ W E * ((2 + 2 * W) ^ (E + 2)) ^ (3 ^ caseWᵗ fn)
           ≡ capᴱ W (E + (E + 2) * 3 ^ caseWᵗ fn)
  collapse =
    trans (cong (capᴱ W E *_)
            (^-*-assoc (2 + 2 * W) (E + 2) (3 ^ caseWᵗ fn)))
          (sym (^-distribˡ-+-* (2 + 2 * W) E ((E + 2) * 3 ^ caseWᵗ fn)))

-- the fn-cap face of one eval edge
applyFn-fnCap : ∀ {n} {Γ : Ctx n} {s t} (Ψ : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  fnCapᵛ s v ≤ Ψ → caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ →
  fnCapᵛ t (applyFn fn v) ≤ Ψ
applyFn-fnCap Ψ fn v hv hfn = fnCap-evalWith Ψ fn (v ∷ᵃ []ᵃ) (hv , tt) hfn

-- the closed-eval face of the ledger rule (of-elements, scan seeds,
-- take counts): same collapse as evalStep-cap over the empty env
evalTm-cap : ∀ {n} {Γ : Ctx n} {t} (Ψ W E : ℕ) (tm : Tm Γ [] [] [] t) →
  2 ≤ E → caseWᵗ tm ≤ Ψ → sizeᵗ tm ≤ capᴱ W E →
  sizeᵛ t (evalTm tm) ≤ capᴱ W (E * 3 ^ suc Ψ)
evalTm-cap Ψ W E tm 2≤E w≤Ψ hsz =
  ≤-trans (evalWith-sharp (capᴱ W E) tm []ᵃ tt hsz)
  (≤-trans (*-mono-≤ hsz (^-monoˡ-≤ (3 ^ caseWᵗ tm) (grow-pow W E)))
  (≤-trans (≤-reflexive collapse)
           (capᴱ-mono W (ledger-step E (caseWᵗ tm) Ψ 2≤E w≤Ψ))))
  where
  collapse : capᴱ W E * ((2 + 2 * W) ^ (E + 2)) ^ (3 ^ caseWᵗ tm)
           ≡ capᴱ W (E + (E + 2) * 3 ^ caseWᵗ tm)
  collapse =
    trans (cong (capᴱ W E *_)
            (^-*-assoc (2 + 2 * W) (E + 2) (3 ^ caseWᵗ tm)))
          (sym (^-distribˡ-+-* (2 + 2 * W) E ((E + 2) * 3 ^ caseWᵗ tm)))

2≤capᴱ : ∀ (W : ℕ) {E : ℕ} → 1 ≤ E → 2 ≤ capᴱ W E
2≤capᴱ W h = ≤-trans (2≤C W) (pow1 W h)

capᴱ-square : ∀ (W E : ℕ) → capᴱ W (2 * E) ≡ capᴱ W E * capᴱ W E
capᴱ-square W E =
  trans (cong ((2 + 2 * W) ^_) (cong (E +_) (+-identityʳ E)))
        (^-distribˡ-+-* (2 + 2 * W) E E)

-- the invariant only ever needs widening upward in B (Ψ is fixed):
-- proven legs (stBounded-widen, ≤ᵇ-widen) + the regsB? leg (W7)
INV?-widen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {Ψ B B′ : ℕ}
  (sched : Sched Γ) (st : EvalSt e) → B ≤ B′ →
  INV? Ψ B sched st ≡ true → INV? Ψ B′ sched st ≡ true
INV?-widen {Ψ = Ψ} {B} {B′} sched st le inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | ss , sf =
  ∧-intro (stBounded-widen le sched st sb)
  (∧-intro fc
  (∧-intro (≤ᵇ-widen (length (EvalSt.registry st)) le rl)
  (∧-intro (regsB?-widen (EvalSt.registry st) le rb)
  (∧-intro (≤ᵇ-widen (slotsSize (Sched.slots sched)) le ss) sf))))

-- map's whole value list through one eval edge
map-applyFn-B : ∀ {n} {Γ : Ctx n} {s u} (Ψ W E : ℕ)
  (fn : Fn Γ [] [] [] s u) → 2 ≤ E →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ → sizeᵗ fn ≤ capᴱ W E →
  (vs : List (Val Γ s)) → all (valB? (capᴱ W E) Ψ s) vs ≡ true →
  all (valB? (capᴱ W (E * 3 ^ suc Ψ)) Ψ u) (map (applyFn fn) vs) ≡ true
map-applyFn-B Ψ W E fn 2≤E cap sz [] h = refl
map-applyFn-B {s = s} {u = u} Ψ W E fn 2≤E cap sz (v ∷ vs) h
  with ∧-true (valB? (capᴱ W E) Ψ s v) _ h
... | hv , hvs with ∧-true (sizeᵛ s v ≤ᵇ capᴱ W E) _ hv
... | hsz , hcap =
  ∧-intro
    (∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ (evalStep-cap Ψ W E fn v 2≤E
        (≤-trans (m≤m⊔n (caseWᵗ fn) (fnCapᵗ fn)) cap) sz
        (≤ᵇ⇒≤ _ _ (T-to hsz)))))
      (T⇒≡true _ (≤⇒≤ᵇ (applyFn-fnCap Ψ fn v
        (≤ᵇ⇒≤ _ _ (T-to hcap)) cap))))
    (map-applyFn-B Ψ W E fn 2≤E cap sz vs hvs)

-- installing a node whose state is bounded on both faces preserves
-- the whole invariant (only the nodes field changes)
install-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  boundedNode B ns ≡ true → fnCapNode Ψ ns ≡ true →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched (installNode nid ns st) ≡ true
install-INV {Γ = Γ} Ψ B sched st nid ns bn fnn inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 =
  ∧-intro (install-bounded B sched st nid ns bn sb)
  (∧-intro (install-fnCap Ψ sched st nid ns fnn fc)
  (∧-intro rl (∧-intro rb r4)))

-- registering a chain: the registry grows by ONE entry — the length
-- rider pays one ×2 ledger edge (B+1 ≤ B·B = capᴱ (2E)), the new
-- path is bounded by hypothesis, everything else is untouched
register-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W E : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) → 1 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  INV? Ψ (capᴱ W (2 * E)) sched (register src κ st) ≡ true
register-INV {u = u} Ψ W E src κ sched st 1≤E inv pκ
  with ∧-true (stBounded? (capᴱ W E) sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ capᴱ W E) _ r2
... | rl , r3 with ∧-true (regsB? (capᴱ W E) Ψ (EvalSt.registry st)) _ r3
... | rb , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ capᴱ W E) _ r4
... | ss , sf =
  ∧-intro (stBounded-widen cap≤ sched st sb)
  (∧-intro fc
  (∧-intro lenOK
  (∧-intro regOK
  (∧-intro (≤ᵇ-widen (slotsSize (Sched.slots sched)) cap≤ ss) sf))))
  where
  E≤2E = m≤m+n E (E + 0)
  cap≤ = capᴱ-mono W E≤2E
  1≤B  = ≤-trans (s≤s z≤n) (2≤capᴱ W 1≤E)
  lenOK : (length (EvalSt.registry st
                   ++ (EvalSt.nextReg st , src , u , κ) ∷ [])
           ≤ᵇ capᴱ W (2 * E)) ≡ true
  lenOK = T⇒≡true _ (≤⇒≤ᵇ (
    ≤-trans (≤-reflexive (length-++ (EvalSt.registry st)))
    (≤-trans (+-monoˡ-≤ 1 (≤ᵇ⇒≤ _ _ (T-to rl)))
    (≤-trans (+-monoʳ-≤ (capᴱ W E) 1≤B)
    (≤-trans (m+n≤m*n (2≤capᴱ W 1≤E) (2≤capᴱ W 1≤E))
             (≤-reflexive (sym (capᴱ-square W E))))))))
  regOK : regsB? (capᴱ W (2 * E)) Ψ
            (EvalSt.registry st
             ++ (EvalSt.nextReg st , src , u , κ) ∷ []) ≡ true
  regOK = all-++-intro _ (EvalSt.registry st) _
            (regsB?-widen (EvalSt.registry st) cap≤ rb)
            (∧-intro (pathB?-widen κ cap≤ pκ) refl)

-- of-list literals through the closed-eval ledger edge, elementwise
ofVals-B : ∀ {n} {Γ : Ctx n} {u} (Ψ W E : ℕ) → 2 ≤ E →
  (ts : List (Tm Γ [] [] [] u)) →
  sizeᵗˢ ts ≤ capᴱ W E → fnCapᵗˢ ts ≤ Ψ →
  all (valB? (capᴱ W (E * 3 ^ suc Ψ)) Ψ u) (map (λ tm → evalTm tm) ts) ≡ true
ofVals-B Ψ W E 2≤E [] hsz hfc = refl
ofVals-B {u = u} Ψ W E 2≤E (y ∷ ys) hsz hfc =
  ∧-intro
    (∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ (evalTm-cap Ψ W E y 2≤E
        (≤-trans (m≤m⊔n (caseWᵗ y) (fnCapᵗ y))
                 (≤-trans (m≤m⊔n _ (fnCapᵗˢ ys)) hfc))
        (≤-trans (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)) hsz))))
      (T⇒≡true _ (≤⇒≤ᵇ (fnCap-evalWith Ψ y []ᵃ tt
        (≤-trans (m≤m⊔n _ (fnCapᵗˢ ys)) hfc)))))
    (ofVals-B Ψ W E 2≤E ys
      (≤-trans (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)) hsz)
      (≤-trans (m≤n⊔m _ (fnCapᵗˢ ys)) hfc))

------------------------------------------------------------------
-- (W6 face) THE SCAN FRAME, PROVEN.  A scan step is a node lookup,
-- one fold run, and a re-install: no recursion, no burst.  The size
-- side is scanVals-sharp's closed form (cap grown by
-- 3^(suc caseW · |vals|)); the fn-cap side is the pointwise
-- applyFn-fnCap run; the state side is install-INV over the widened
-- invariant.  The three stuck shapes (no node, wrong node, type
-- mismatch) emit nothing and move no ledger.
------------------------------------------------------------------

-- valB? unzips into its two faces and zips back
allB-size : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (valB? B Ψ u) vs ≡ true → All (λ v → sizeᵛ u v ≤ B) vs
allB-size B Ψ u []       h = []ᵃ
allB-size B Ψ u (v ∷ vs) h =
  valB-sz B Ψ u v (allB-head B Ψ u v vs h)
    ∷ᵃ allB-size B Ψ u vs (allB-tail B Ψ u v vs h)

allB-fnCap : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (valB? B Ψ u) vs ≡ true → All (λ v → fnCapᵛ u v ≤ Ψ) vs
allB-fnCap B Ψ u []       h = []ᵃ
allB-fnCap B Ψ u (v ∷ vs) h =
  valB-fc B Ψ u v (allB-head B Ψ u v vs h)
    ∷ᵃ allB-fnCap B Ψ u vs (allB-tail B Ψ u v vs h)

allB-zip : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  All (λ v → sizeᵛ u v ≤ B) vs → All (λ v → fnCapᵛ u v ≤ Ψ) vs →
  all (valB? B Ψ u) vs ≡ true
allB-zip B Ψ u []       _           _           = refl
allB-zip B Ψ u (v ∷ vs) (hsz ∷ᵃ hss) (hf ∷ᵃ hfs) =
  ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ hsz)) (T⇒≡true _ (≤⇒≤ᵇ hf)))
          (allB-zip B Ψ u vs hss hfs)

-- a node lookup carries both bounded faces of whatever it finds
NodeB : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Maybe (NodeState Γ) → Set
NodeB B Ψ nothing   = ⊤
NodeB B Ψ (just ns) = (boundedNode B ns ≡ true) × (fnCapNode Ψ ns ≡ true)

lookupNode-B : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) nodes ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  NodeB B Ψ (lookupNode nid nodes)
lookupNode-B B Ψ nid []            hb hf = tt
lookupNode-B B Ψ nid ((k , s) ∷ r) hb hf with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ hb) , proj₁ (∧-true _ _ hf)
... | false = lookupNode-B B Ψ nid r (proj₂ (∧-true _ _ hb)) (proj₂ (∧-true _ _ hf))

-- the fn-cap face of one fold run: no applyFn ever mints a new fn
scanVals-fnCap : ∀ {n} {Γ : Ctx n} {s u} (Ψ : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ → fnCapᵛ u ac ≤ Ψ →
  All (λ v → fnCapᵛ s v ≤ Ψ) vs →
  (fnCapᵛ u (proj₂ (scanVals fn ac vs)) ≤ Ψ)
  × All (λ o → fnCapᵛ u o ≤ Ψ) (proj₁ (scanVals fn ac vs))
scanVals-fnCap Ψ fn ac []       hfn hacc _            = hacc , []ᵃ
scanVals-fnCap Ψ fn ac (v ∷ vs) hfn hacc (hv ∷ᵃ hvs) =
  proj₁ IH , acc′OK ∷ᵃ proj₂ IH
  where
  acc′OK = applyFn-fnCap Ψ fn (ac , v) (⊔-lub hacc hv) hfn
  IH     = scanVals-fnCap Ψ fn (applyFn fn (ac , v)) vs hfn acc′OK hvs

stepFrame-scan-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ (scan-f fn nid) ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-scan-wet {s = s} {u = u} Ψ W g id now fn nid κ vals fin sched st E
                   3≤E inv fB pB vB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ nid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | nothing            | _ = E , ≤-refl , inv , refl , refl
... | just (take-st _)   | _ = E , ≤-refl , inv , refl , refl
... | just (merge-st _ _)   | _ = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) | _ = E , ≤-refl , inv , refl , refl
... | just (switch-st _ _)  | _ = E , ≤-refl , inv , refl , refl
... | just (exhaust-st _ _) | _ = E , ≤-refl , inv , refl , refl
... | just (scan-st {w} ac) | nb with w ≟ᵗ u
...   | no _    = E , ≤-refl , inv , refl , refl
...   | yes refl =
  E′ , E≤E′ ,
  install-INV Ψ (capᴱ W E′) sched st nid (scan-st (proj₂ run))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ szRun)))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ fcRun)))
    (INV?-widen sched st (capᴱ-mono W E≤E′) inv) ,
  allB-zip (capᴱ W E′) Ψ u (proj₁ run) (proj₂ szRun) (proj₂ fcRun) ,
  refl
  where
  E′    = E * 3 ^ (suc (caseWᵗ fn) * length vals)
  E≤E′  = E≤E*3^ E (suc (caseWᵗ fn) * length vals)
  run   = scanVals fn ac vals
  szfn  : sizeᵗ fn ≤ capᴱ W E
  szfn  = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (sizeᵗ fn ≤ᵇ capᴱ W E) _ fB)))
  capfn : caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ
  capfn = ≤ᵇ⇒≤ _ _ (T-to (proj₂ (∧-true (sizeᵗ fn ≤ᵇ capᴱ W E) _ fB)))
  szRun = scanVals-sharp W E fn ac vals 3≤E szfn
            (≤ᵇ⇒≤ _ _ (T-to (proj₁ nb)))
            (allB-size (capᴱ W E) Ψ s vals vB)
  fcRun = scanVals-fnCap Ψ fn ac vals capfn
            (≤ᵇ⇒≤ _ _ (T-to (proj₂ nb)))
            (allB-fnCap (capᴱ W E) Ψ s vals vB)

------------------------------------------------------------------
-- THE TAKE FRAME, PROVEN.  take emits a prefix of its input (so its
-- values ride the caller's bound), and on the cutting emit it runs
-- cutThrough: a filter on the registry whose closes are value-free
-- and whose survivors keep their frame bounds and can only shrink in
-- count.  sweepLive then filters the live schedule.  No eval edge:
-- E′ = E on both branches.
------------------------------------------------------------------

takeVals-B : ∀ {n} {Γ : Ctx n} {s} (B Ψ : ℕ) (k : ℕ) (vals : List (Val Γ s)) →
  all (valB? B Ψ s) vals ≡ true →
  all (valB? B Ψ s) (proj₁ (takeVals k vals)) ≡ true
takeVals-B B Ψ zero          _        h = refl
takeVals-B B Ψ (suc k)       []       h = refl
takeVals-B B Ψ (suc zero)    (v ∷ vs) h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-B B Ψ (suc (suc k)) (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-B B Ψ (suc k) vs (proj₂ (∧-true _ _ h)))

-- the sweep is a filter on the fn-cap face too (mirror of
-- sweepLive-bounded)
sweepLive-fnCap : ∀ {n} {Γ : Ctx n} {t} (Ψ : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (fnCapLive Ψ) ls ≡ true →
  all (fnCapLive Ψ) (sweepLive reg ls) ≡ true
sweepLive-fnCap Ψ reg []       h = refl
sweepLive-fnCap {n = n} Ψ reg (l ∷ ls) h
  with ∧-true (fnCapLive Ψ l) (all (fnCapLive Ψ) ls) h
... | bl , bls
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ∧-intro bl (sweepLive-fnCap Ψ reg ls bls)
... | false = sweepLive-fnCap Ψ reg ls bls

-- the cut is a filter on the registry: the count only drops, the
-- survivors keep their frame bounds, and every close it mints is
-- value-free
cutThrough-len : ∀ {n} {Γ : Ctx n} {t} (nid : NodeId) (d : List RegId)
  (wm : RegId) (dy : List Source) (reg : List (RegId × Source × Chain Γ t)) →
  length (proj₁ (cutThrough nid d wm dy reg)) ≤ length reg
cutThrough-len nid d wm dy []                    = z≤n
cutThrough-len nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-len nid d wm dy r
... | true  | kept , closes , rids | ih = ≤-trans ih (n≤1+n _)
... | false | kept , closes , rids | ih = s≤s ih

cutThrough-regs : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ reg ≡ true → regsB? B Ψ (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regs B Ψ nid d wm dy []                    h = refl
cutThrough-regs B Ψ nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regs B Ψ nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | kept , closes , rids | ih = ih
... | false | kept , closes , rids | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closes : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventB? B Ψ) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closes B Ψ nid d wm dy []                    = refl
cutThrough-closes B Ψ nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-closes B Ψ nid d wm dy r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih
      with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

stepFrame-take-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now (take-f nid) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-take-wet {s = s} Ψ W g id now nid κ vals fin sched st E 3≤E inv pB vB
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = E , ≤-refl , inv , refl , refl
... | just (scan-st _)       = E , ≤-refl , inv , refl , refl
... | just (merge-st _ _)    = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , refl , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , refl , refl
... | just (exhaust-st _ _)  = E , ≤-refl , inv , refl , refl
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st nid
    (take-st (proj₁ (proj₂ (takeVals k vals)))) refl refl inv ,
  takeVals-B (capᴱ W E) Ψ k vals vB , refl
...   | true =
  E , ≤-refl ,
  ∧-intro
    (∧-intro (sweepLive-bounded B kept (Sched.live sched) bls)
             (setNode-bounded B nid (take-st zero) (EvalSt.nodes st) refl bns))
  (∧-intro
    (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched) fls)
             (setNode-fnCap Ψ nid (take-st zero) (EvalSt.nodes st) refl fns))
  (∧-intro lenOK
  (∧-intro (cutThrough-regs B Ψ nid del wm dy (EvalSt.registry st) rb) r4))) ,
  takeVals-B B Ψ k vals vB ,
  cutThrough-closes B Ψ nid del wm dy (EvalSt.registry st)
  where
  B    = capᴱ W E
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough nid del wm dy (EvalSt.registry st))
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  r4   = ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  bls  = stB-live B sched st sb
  bns  = stB-nodes B sched st sb
  fls  = fcB-live Ψ sched st fc
  fns  = fcB-nodes Ψ sched st fc
  lenOK : (length kept ≤ᵇ B) ≡ true
  lenOK = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (cutThrough-len nid del wm dy (EvalSt.registry st))
             (≤ᵇ⇒≤ _ _ (T-to rl))))

------------------------------------------------------------------
-- THE OUTER *All FRAME.  thruWalk folds the emitted inners; each
-- step subscribes one inner inside the current instant and rewrites
-- the *All node.  Only the per-emit step moves the ledger (it is a
-- subscribeE re-entry); the wrap and the node rewrites are free.
------------------------------------------------------------------

eventsB?-widen : ∀ {n} {Γ : Ctx n} {u} {B B′ Ψ : ℕ}
  (es : List (InstEvent (Val Γ u))) → B ≤ B′ →
  all (eventB? B Ψ) es ≡ true → all (eventB? B′ Ψ) es ≡ true
eventsB?-widen es B≤ h = all-impl _ _ (λ ev → eventB?-widen ev B≤) es h

-- splitting a whole burst: same two faces as splitEvents, concatenated
splitBurst-vals-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ) (str : Stream Γ s) →
  burstB? B Ψ str ≡ true →
  all (valB? B Ψ s) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-B B Ψ []               h = refl
splitBurst-vals-B {Γ = Γ} {u = u} B Ψ (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-B B Ψ (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-B {u = u} B Ψ ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ) (str : Stream Γ s) →
  all (eventB? B Ψ) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-B B Ψ []               = refl
splitBurst-bk-B {Γ = Γ} {u = u} B Ψ (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-B {u = u} B Ψ (InstEmit.events em))
    (splitBurst-bk-B {u = u} B Ψ ems)

-- mergeAll's counter bump: whatever the lookup finds, the invariant
-- survives (merge-st is value-free, every other shape is a no-op)
mergeBump-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (nid : NodeId) (d : Bool) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched (record st { nodes = mergeBump nid d (EvalSt.nodes st) }) ≡ true
mergeBump-INV Ψ B nid d sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od)   = install-INV Ψ B sched st nid
                                 (merge-st (if d then k else suc k) od) refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

-- switchAll's cut: the same registry filter the take frame runs
switchKill-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ W E : ℕ)
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  let r = switchKill cur sched st
  in (INV? Ψ (capᴱ W E) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (all (eventB? (capᴱ W E) Ψ) (proj₁ r) ≡ true)
switchKill-INV Ψ W E nothing  sched st inv = inv , refl
switchKill-INV Ψ W E (just v) sched st inv =
  ∧-intro
    (∧-intro (sweepLive-bounded B kept (Sched.live sched) bls) bns)
  (∧-intro
    (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched) fls) fns)
  (∧-intro lenOK
  (∧-intro (cutThrough-regs B Ψ v del wm dy (EvalSt.registry st) rb) r4))) ,
  cutThrough-closes B Ψ v del wm dy (EvalSt.registry st)
  where
  B    = capᴱ W E
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough v del wm dy (EvalSt.registry st))
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  r4   = ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  bls  = stB-live B sched st sb
  bns  = stB-nodes B sched st sb
  fls  = fcB-live Ψ sched st fc
  fns  = fcB-nodes Ψ sched st fc
  lenOK : (length kept ≤ᵇ B) ≡ true
  lenOK = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (cutThrough-len v del wm dy (EvalSt.registry st))
             (≤ᵇ⇒≤ _ _ (T-to rl))))

-- the wrap: values and events pass through, only the *All node's
-- done-flag is written back (and concat's queue is re-installed as-is)
thruWrap-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ B : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  all (valB? B Ψ u) vs ≡ true →
  all (eventB? B Ψ) bs ≡ true →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in (INV? Ψ B (proj₁ (proj₂ (proj₂ (proj₂ r))))
               (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? B Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? B Ψ) (proj₁ (proj₂ r)) ≡ true)
thruWrap-wet Ψ B op nid false vs bs sched st inv vB bB = inv , vB , bB
thruWrap-wet Ψ B mergeᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)    =
      install-INV Ψ B sched st nid (merge-st k true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (concat-st _ _ _) = inv , vB , bB
... | just (switch-st _ _)   = inv , vB , bB
... | just (exhaust-st _ _)  = inv , vB , bB
thruWrap-wet Ψ B concatᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B B Ψ nid (EvalSt.nodes st)
         (stB-nodes B sched st (proj₁ (INV-parts Ψ B sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ B sched st inv))))
... | just (concat-st q act _) | nb =
      install-INV Ψ B sched st nid (concat-st q act true)
        (proj₁ nb) (proj₂ nb) inv , vB , bB
... | nothing                | _ = inv , vB , bB
... | just (scan-st _)       | _ = inv , vB , bB
... | just (take-st _)       | _ = inv , vB , bB
... | just (merge-st _ _)    | _ = inv , vB , bB
... | just (switch-st _ _)   | _ = inv , vB , bB
... | just (exhaust-st _ _)  | _ = inv , vB , bB
thruWrap-wet Ψ B switchᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      install-INV Ψ B sched st nid (switch-st cur true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (merge-st _ _)    = inv , vB , bB
... | just (concat-st _ _ _) = inv , vB , bB
... | just (exhaust-st _ _)  = inv , vB , bB
thruWrap-wet Ψ B exhaustᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      install-INV Ψ B sched st nid (exhaust-st act true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (merge-st _ _)    = inv , vB , bB
... | just (concat-st _ _ _) = inv , vB , bB
... | just (switch-st _ _)   = inv , vB , bB

-- forward declarations: these join subscribeE-walkS's clique
-- (thruConsume re-enters subscribeE through subscribeInner; the input
-- clause re-enters it through a share's connect), so their definitions
-- live after the walk's own signature
subscribeE-input-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeE g (input i) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

-- the DELIVERY clique: foldPath walks one chain sinkward, and at a
-- share boundary hands off to dispatchShare, which folds every
-- admitted registration back through foldPath.  Lexicographic on
-- (dispatch gas, path) exactly as the machine recurses: the frame
-- hops shrink the path at constant gas, the share hop peels one gas
foldPath-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ path ≡ true →
  all (valB? (capᴱ W E) Ψ u) vals ≡ true →
  all (eventB? (capᴱ W E) Ψ) evs ≡ true →
  let r = foldPath sf gas id now envSrc path vals evs fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

dispatchShare-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (valB? (capᴱ W E) Ψ (lookup Γ i)) vals ≡ true →
  let r = dispatchShare sf gas id now i vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

shareGo-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (λ rp → pathB? (capᴱ W E) Ψ (proj₂ rp)) ps ≡ true →
  all (valB? (capᴱ W E) Ψ (lookup Γ i)) vals ≡ true →
  let r = shareGo sf gas id now i vals fin ps sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

chainStep-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (id : Id) (a : Arrival Γ)
  (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ path ≡ true →
  valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
  let r = chainStep id a path sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

sharedSlot-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ d ≤ capᴱ W E → fnCapᵉ d ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

sharedConnect-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ d ≤ capᴱ W E → fnCapᵉ d ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = sharedConnect g i d κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

subscribeInner-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  valB? (capᴱ W E) Ψ (obs u) o ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeInner g op allNid κ id now o sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ (proj₂ r)) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ (proj₂ r))) ≡ true)

thruConsume-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  valB? (capᴱ W E) Ψ (obs u) o ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = thruConsume g op nid κ id now o sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ r)))
                           (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

thruWalk-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ (obs u)) vals ≡ true →
  let r = thruWalk g op nid κ id now vals sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ r)))
                           (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

stepFrame-thruOuter-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ (obs u)) vals ≡ true →
  let r = stepFrame g id now (thru-outer op nid) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
concatDrain-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ capᴱ W E) q ≡ true →
  all (λ o → fnCapᵉ o ≤ᵇ Ψ) q ≡ true →
  let r = concatDrain g allNid κ id now q sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
     × (all (λ o → sizeᵉ o ≤ᵇ capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ o → fnCapᵉ o ≤ᵇ Ψ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)

innerFinish-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

-- the inner *All frame: a fin is either absorbed (a sibling
-- registration still lives) or finishes the *All node.  Only
-- concatAll's drain moves the ledger
stepFrame-fromInner-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now (from-inner op allNid inst) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-fromInner-wet Ψ W g id now op allNid inst κ vals false sched st E
                        3≤E inv pB vB = E , ≤-refl , inv , vB , refl
stepFrame-fromInner-wet Ψ W g id now op allNid inst κ vals true sched st E
                        3≤E inv pB vB
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = E , ≤-refl , inv , vB , refl
... | false = innerFinish-wet Ψ W g op allNid inst κ id now vals sched st E
                3≤E inv pB vB

-- the concat queue's stored outers only ever need widening upward
allsz-widen : ∀ {n} {Γ : Ctx n} {s} {B B′ : ℕ} (q : List (Closed Γ s)) → B ≤ B′ →
  all (λ o → sizeᵉ o ≤ᵇ B) q ≡ true → all (λ o → sizeᵉ o ≤ᵇ B′) q ≡ true
allsz-widen q B≤ h = all-impl _ _ (λ o → ≤ᵇ-widen (sizeᵉ o) B≤) q h

stepFrame-thruOuter-wet Ψ W g id now op nid κ vals fin sched st E 3≤E inv pB vB =
  E′ , E≤E′ , proj₁ WR , proj₁ (proj₂ WR) , proj₂ (proj₂ WR)
  where
  WK   = thruWalk-wet Ψ W g op nid κ id now vals sched st E 3≤E inv pB vB
  E′   = proj₁ WK
  E≤E′ = proj₁ (proj₂ WK)
  wr   = thruWalk g op nid κ id now vals sched st
  WR   = thruWrap-wet Ψ (capᴱ W E′) op nid fin (proj₁ wr) (proj₁ (proj₂ wr))
           (proj₁ (proj₂ (proj₂ wr))) (proj₂ (proj₂ (proj₂ wr)))
           (proj₁ (proj₂ (proj₂ WK)))
           (proj₁ (proj₂ (proj₂ (proj₂ WK))))
           (proj₂ (proj₂ (proj₂ (proj₂ WK))))

------------------------------------------------------------------
-- stepFrame-wet, now a REAL dispatch: the map clause proven end to
-- end on the ledger rule; the other frames delegate to their named
-- cores above
------------------------------------------------------------------

stepFrame-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ f ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-wet Ψ W g id now (map-f fn) κ vals fin sched st E 3≤E inv fB pB vB =
  E * 3 ^ suc Ψ , E≤E*3^ E (suc Ψ) ,
  INV?-widen sched st (capᴱ-mono W (E≤E*3^ E (suc Ψ))) inv ,
  map-applyFn-B Ψ W E fn (≤-trans (n≤1+n 2) 3≤E) capsOK szOK vals vB ,
  refl
  where
  fB2   = ∧-true (sizeᵗ fn ≤ᵇ capᴱ W E) _ fB
  szOK  : sizeᵗ fn ≤ capᴱ W E
  szOK  = ≤ᵇ⇒≤ _ _ (T-to (proj₁ fB2))
  capsOK : caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ
  capsOK = ≤ᵇ⇒≤ _ _ (T-to (proj₂ fB2))
stepFrame-wet Ψ W g id now (scan-f fn nid) κ vals fin sched st E h inv fB pB vB =
  stepFrame-scan-wet Ψ W g id now fn nid κ vals fin sched st E h inv fB pB vB
stepFrame-wet Ψ W g id now (take-f nid) κ vals fin sched st E h inv fB pB vB =
  stepFrame-take-wet Ψ W g id now nid κ vals fin sched st E h inv pB vB
stepFrame-wet Ψ W g id now (from-inner op allNid inst) κ vals fin sched st E h inv fB pB vB =
  stepFrame-fromInner-wet Ψ W g id now op allNid inst κ vals fin sched st E h inv pB vB
stepFrame-wet Ψ W g id now (thru-outer op nid) κ vals fin sched st E h inv fB pB vB =
  stepFrame-thruOuter-wet Ψ W g id now op nid κ vals fin sched st E h inv pB vB

-- the fin marker's event list is value-free either way
finList-B : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (b : Bool) →
  all (eventB? {n = n} {Γ = Γ} {u = u} B Ψ)
      (if b then complete ∷ [] else []) ≡ true
finList-B B Ψ true  = refl
finList-B B Ψ false = refl

------------------------------------------------------------------
-- pushBurst-wet, PROVEN: the burst re-entry threads the walk
-- invariant emit by emit over stepFrame-wet — the first of the
-- mutual block's contracts discharged as a real induction (list
-- induction on the burst; each emit splits, steps its frame at the
-- current ledger position, and reassembles under widened bounds)
------------------------------------------------------------------

pushBurst-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (ems : Stream Γ s)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ f ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  burstB? (capᴱ W E) Ψ ems ≡ true →
  let r = pushBurst g id now f κ ems sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
pushBurst-wet Ψ W g id now f κ [] sched st E 3≤E inv fB pB bB =
  E , ≤-refl , inv , refl
pushBurst-wet {Γ = Γ} {s = s} {u = u} Ψ W g id now f κ (em ∷ ems)
              sched st E 3≤E inv fB pB bB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , outAll
  where
  B₀    = capᴱ W E
  sp    : List (Val Γ s) × List (InstEvent (Val Γ u)) × Bool
  sp    = splitEvents (InstEmit.events em)
  vals  = proj₁ sp
  emB   = proj₁ (∧-true (all (eventB? B₀ Ψ) (InstEmit.events em)) _ bB)
  emsB  = proj₂ (∧-true (all (eventB? B₀ Ψ) (InstEmit.events em)) _ bB)

  step  = stepFrame g id now f κ vals (proj₂ (proj₂ sp)) sched st
  W1    = stepFrame-wet Ψ W g id now f κ vals (proj₂ (proj₂ sp))
            sched st E 3≤E inv fB pB
            (splitEvents-vals-B B₀ Ψ (InstEmit.events em) emB)
  E₁    = proj₁ W1
  E≤E₁  = proj₁ (proj₂ W1)
  inv₁  = proj₁ (proj₂ (proj₂ W1))
  outB  = proj₁ (proj₂ (proj₂ (proj₂ W1)))
  cap₁  = capᴱ-mono W E≤E₁

  rec   = pushBurst-wet Ψ W g id now f κ ems
            (proj₁ (proj₂ (proj₂ (proj₂ step))))
            (proj₂ (proj₂ (proj₂ (proj₂ step))))
            E₁ (≤-trans 3≤E E≤E₁) inv₁
            (frameB?-widen f cap₁ fB) (pathB?-widen κ cap₁ pB)
            (burstB?-widen ems cap₁ emsB)
  E₂    = proj₁ rec
  E₁≤E₂ = proj₁ (proj₂ rec)
  inv₂  = proj₁ (proj₂ (proj₂ rec))
  restB = proj₂ (proj₂ (proj₂ rec))
  cap₂  = capᴱ-mono W E₁≤E₂

  headOK : all (eventB? (capᴱ W E₂) Ψ)
             (proj₁ (proj₂ sp)
              ++ retagEvents (proj₁ (proj₂ step))
              ++ map value (proj₁ step)
              ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           ≡ true
  headOK =
    all-++-intro _ (proj₁ (proj₂ sp)) _
      (splitEvents-bk-B (capᴱ W E₂) Ψ (InstEmit.events em))
      (all-++-intro _ (retagEvents (proj₁ (proj₂ step))) _
        (retag-B (capᴱ W E₂) Ψ (proj₁ (proj₂ step)))
        (all-++-intro _ (map value (proj₁ step)) _
          (mapValue-B (capᴱ W E₂) Ψ u (proj₁ step)
            (valsB?-widen u (proj₁ step) cap₂ outB))
          (finList-B (capᴱ W E₂) Ψ (proj₁ (proj₂ (proj₂ step))))))

  outAll = ∧-intro headOK restB

------------------------------------------------------------------
-- (W9, deferᵉ) THE DEFER HOP, PROVEN.  deferᵉ is the one walk clause
-- that mints machinery without recursing: a node, a source and an
-- ordinal are minted, the merge node installed, the BODY itself
-- parked as the single pending value of a fresh live source, and the
-- outer chain registered.  The only ledger cost is register-INV's ×2
-- length edge; the burst is a lone `init`, so it is bounded by refl.
------------------------------------------------------------------

-- adding a live hop: only the live conjuncts move, and both faces of
-- the new entry come from the caller
addLive-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (l : LiveSource Γ) →
  boundedLive B l ≡ true → fnCapLive Ψ l ≡ true →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (record sched { live = l ∷ Sched.live sched }) st ≡ true
addLive-INV Ψ B sched st l bl fl inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 =
  ∧-intro (∧-intro (∧-intro bl (proj₁ (∧-true _ _ sb))) (proj₂ (∧-true _ _ sb)))
  (∧-intro (∧-intro (∧-intro fl (proj₁ (∧-true _ _ fc))) (proj₂ (∧-true _ _ fc)))
           r2)

------------------------------------------------------------------
-- (W9 face) THE SLOTS, READ ONE AT A TIME.  INV? carries the whole
-- slot vector's size and weight as two sums; a single slot is one
-- summand, so fᵢ≤sum-tab projects the per-slot bound the input
-- clause needs.  The slots themselves never change, so these are
-- the ONLY facts the input clause has about what it is subscribing.
------------------------------------------------------------------

slotSize-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → slotSize (Sched.slots sched i) ≤ B
slotSize-at {Γ = Γ} Ψ B i sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | _ , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | _ , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | _ , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | _ , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | ss , _ =
  ≤-trans (fᵢ≤sum-tab (λ j → slotSize (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to ss))

slotFnCap-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → slotFnCap (Sched.slots sched i) ≤ Ψ
slotFnCap-at {Γ = Γ} Ψ B i sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | _ , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | _ , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | _ , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | _ , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | _ , sf =
  ≤-trans (fᵢ≤sum-tab (λ j → slotFnCap (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to sf))

-- a script's sync prefix, elementwise, off the slot's two sums
sumVals-B : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  sum (map (sizeᵛ u) vs) ≤ B → sum (map (fnCapᵛ u) vs) ≤ Ψ →
  all (valB? B Ψ u) vs ≡ true
sumVals-B B Ψ u []       hsz hf = refl
sumVals-B B Ψ u (v ∷ vs) hsz hf =
  ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (sizeᵛ u v) _) hsz)))
                   (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (fnCapᵛ u v) _) hf))))
          (sumVals-B B Ψ u vs (≤-trans (m≤n+m _ (sizeᵛ u v)) hsz)
                              (≤-trans (m≤n+m _ (fnCapᵛ u v)) hf))

-- retagging an emit's kind leaves its EVENTS alone, so the share's
-- plumbing relabel is invisible to every in-flight bound
sharedPlumb-B : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (str : Stream Γ u) →
  burstB? B Ψ str ≡ true → burstB? B Ψ (sharedPlumb str) ≡ true
sharedPlumb-B B Ψ []         h = refl
sharedPlumb-B B Ψ (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-B B Ψ ems (proj₂ (∧-true _ _ h)))

-- the completion latch: dropping a source SHRINKS the registry on
-- both riders, and completedSources / connectedShares are read by no
-- conjunct at all
dropSource-len : ∀ {n} {Γ : Ctx n} {t} (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  length (dropSource src reg) ≤ length reg
dropSource-len src []                  = z≤n
dropSource-len src ((rid , s , c) ∷ r) with sameSource src s
... | true  = ≤-trans (dropSource-len src r) (n≤1+n _)
... | false = s≤s (dropSource-len src r)

dropSource-regs : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ reg ≡ true → regsB? B Ψ (dropSource src reg) ≡ true
dropSource-regs B Ψ src []                  h = refl
dropSource-regs B Ψ src ((rid , s , c) ∷ r) h with sameSource src s
... | true  = dropSource-regs B Ψ src r (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (dropSource-regs B Ψ src r (proj₂ (∧-true _ _ h)))

latch-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched
    (record st { registry = dropSource src (EvalSt.registry st)
               ; completedSources = src ∷ EvalSt.completedSources st })
    ≡ true
latch-INV Ψ B src sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 =
  ∧-intro sb
  (∧-intro fc
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len src (EvalSt.registry st))
                                     (≤ᵇ⇒≤ _ _ (T-to rl)))))
  (∧-intro (dropSource-regs B Ψ src (EvalSt.registry st) rb) r4)))

-- a share's close list, the dual of finList-B
closeList-B : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (src : Source) (b : Bool) →
  all (eventB? {n = n} {Γ = Γ} {u = u} B Ψ)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-B B Ψ src true  = refl
closeList-B B Ψ src false = refl

-- completedSources / dying / delivered are read by no conjunct
shareLatch-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched (shareLatch i b st) ≡ true
shareLatch-INV Ψ B i false sched st inv = inv
shareLatch-INV Ψ B i true  sched st inv = inv

delivered-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true
delivered-INV Ψ B rid sched st inv = inv

-- the admitted fan-out chains inherit their bounds from the registry
shareAdmit-B : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (i : Fin n)
  (reg : List (RegId × Source × Chain Γ t)) → regsB? B Ψ reg ≡ true →
  all (λ rp → pathB? B Ψ (proj₂ rp)) (shareAdmit i reg) ≡ true
shareAdmit-B B Ψ i []                      h = refl
shareAdmit-B {Γ = Γ} B Ψ i ((rid , src , (u , q)) ∷ r) h
  with sameSource (toℕ i) src | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-B B Ψ i r (proj₂ (∧-true (pathB? B Ψ q) _ h))
... | true  | no  _    = shareAdmit-B B Ψ i r (proj₂ (∧-true (pathB? B Ψ q) _ h))
... | true  | yes refl =
      ∧-intro (proj₁ (∧-true (pathB? B Ψ q) _ h))
              (shareAdmit-B B Ψ i r (proj₂ (∧-true (pathB? B Ψ q) _ h)))

-- the share's completion sweep: the registry SHRINKS on both riders
-- and the live list is filtered, so every conjunct only improves
shareFinish-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (proj₁ (proj₂ (shareFinish i b (emits , sched , st))))
           (proj₂ (proj₂ (shareFinish i b (emits , sched , st)))) ≡ true
shareFinish-INV Ψ B i false emits sched st inv = inv
shareFinish-INV Ψ B i true  emits sched st inv =
  ∧-intro (∧-intro (sweepLive-bounded B kept (Sched.live sched)
                     (stB-live B sched st sb))
                   (stB-nodes B sched st sb))
  (∧-intro (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched)
                      (fcB-live Ψ sched st fc))
                    (fcB-nodes Ψ sched st fc))
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len (toℕ i) (EvalSt.registry st))
                                     (≤ᵇ⇒≤ _ _ (T-to rl)))))
  (∧-intro (dropSource-regs B Ψ (toℕ i) (EvalSt.registry st) rb)
  (∧-intro ss sf))))
  where
  kept = dropSource (toℕ i) (EvalSt.registry st)
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  ss   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P))))
  sf   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P))))

-- shareFinish never touches the emits it is handed
shareFinish-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  proj₁ (shareFinish i b (emits , sched , st)) ≡ emits
shareFinish-burst i false emits sched st = refl
shareFinish-burst i true  emits sched st = refl

-- connectedShares is read by no conjunct of INV?, so latching a
-- connect is invisible to the invariant (record eta does the work)
connectShare-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched
    (record st { connectedShares = src ∷ EvalSt.connectedShares st }) ≡ true
connectShare-INV Ψ B src sched st inv = inv

-- the connect's two landings, factored out of sharedConnect's `if` so
-- the caller can keep one where-block across both
connectWrap-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (i : Fin n) (id : Id) (c : Bool)
  (burst : Stream Γ (lookup Γ i)) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → burstB? B Ψ burst ≡ true →
  let r = if c
          then (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                  at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched
               , record st { registry = dropSource (toℕ i) (EvalSt.registry st)
                           ; completedSources = toℕ i ∷ EvalSt.completedSources st }
          else ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst
               , sched , st
  in (INV? Ψ B (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? B Ψ (proj₁ r) ≡ true)
connectWrap-wet Ψ B i id true  burst sched st inv bB =
  latch-INV Ψ B (toℕ i) sched st inv ,
  ∧-intro refl (sharedPlumb-B B Ψ burst bB)
connectWrap-wet Ψ B i id false burst sched st inv bB =
  inv , ∧-intro refl (sharedPlumb-B B Ψ burst bB)

subscribeE-defer-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (body : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ body ≤ capᴱ W E → fnCapᵉ body ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeE g (deferᵉ body) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
subscribeE-defer-wet {Γ = Γ} {u = u} Ψ W g body κ id now sched st E
                     3≤E inv szB fcB pB =
  2 * E , m≤m+n E (E + 0) ,
  register-INV Ψ W E src (thru-outer mergeᵒ nid ↠ κ) sched₄ st₀
    (≤-trans (s≤s z≤n) 3≤E) inv₂ (∧-intro refl pB) ,
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
  inv₁   = install-INV Ψ (capᴱ W E) sched₃ st nid (merge-st 0 false)
             refl refl inv
  inv₂   = addLive-INV Ψ (capᴱ W E) sched₃ st₀ hop
             (∧-intro (T⇒≡true _ (≤⇒≤ᵇ szB)) refl)
             (∧-intro (T⇒≡true _ (≤⇒≤ᵇ fcB)) refl)
             inv₁

------------------------------------------------------------------
-- subscribeE-walkS, THE REAL INDUCTION: the store half of the wet
-- contract ground through the machine's clauses, lexicographic on
-- (gas, expression) exactly as the machine recurses.  Eleven of the
-- thirteen clauses are proven here (of/empty one-shots pay one eval
-- edge; map/take/scan/the four *Alls thread install-INV/register
-- rings, the IH and pushBurst-wet; μ pays the ×2 copy edge against
-- size-unfoldμ with shells/caps carried by elimG-invariance; varᵉ
-- is absurd); input and deferᵉ delegate to their named W9 cores.
------------------------------------------------------------------

subscribeE-walkS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeE g b κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

-- the shared *All shape: mint, install (bounded on both faces),
-- subscribe under the thru-outer frame, push the burst — proven
-- once, consumed by all four *All clauses
subscribeAll-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  boundedNode (capᴱ W E) ns ≡ true → fnCapNode Ψ ns ≡ true →
  sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeAll g op ns b κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
subscribeAll-wet Ψ W g op ns b κ id now sched st E 3≤E inv bn fnn szB fcB pB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  inv₀   = install-INV Ψ (capᴱ W E) sched₁ st nid ns bn fnn inv
  sE      = subscribeE g b (thru-outer op nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-walkS Ψ W g b (thru-outer op nid ↠ κ) id now
             sched₁ st₀ E 3≤E inv₀ szB fcB (∧-intro refl pB)
  E₁     = proj₁ IH
  E≤E₁   = proj₁ (proj₂ IH)
  inv₁   = proj₁ (proj₂ (proj₂ IH))
  bB₁    = proj₂ (proj₂ (proj₂ IH))
  cap₁   = capᴱ-mono W E≤E₁
  PB     = pushBurst-wet Ψ W g id now (thru-outer op nid) κ (proj₁ sE)
             (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁
             (≤-trans 3≤E E≤E₁) inv₁ refl (pathB?-widen κ cap₁ pB) bB₁
  E₂     = proj₁ PB
  E₁≤E₂  = proj₁ (proj₂ PB)
  inv₂   = proj₁ (proj₂ (proj₂ PB))
  b₂     = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (input i) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeE-input-wet Ψ W g i κ id now sched st E 3≤E inv pB

subscribeE-walkS {Γ = Γ} {u = u} Ψ W g (ofᵉ ts) κ id now sched st E 3≤E inv szB fcB pB =
  E * 3 ^ suc Ψ , E≤E*3^ E (suc Ψ) ,
  INV?-widen (record sched { nextSource = suc (Sched.nextSource sched) }) st
    (capᴱ-mono W (E≤E*3^ E (suc Ψ))) inv ,
  ∧-intro
    (∧-intro refl
      (all-++-intro _ (map value (map (λ tm → evalTm tm) ts)) _
        (mapValue-B (capᴱ W (E * 3 ^ suc Ψ)) Ψ u (map (λ tm → evalTm tm) ts)
          (ofVals-B Ψ W E (≤-trans (n≤1+n 2) 3≤E) ts (≤-trans (n≤1+n (sizeᵗˢ ts)) szB) fcB))
        refl))
    refl

subscribeE-walkS Ψ W g emptyᵉ κ id now sched st E 3≤E inv szB fcB pB =
  E , ≤-refl , inv , refl

subscribeE-walkS Ψ W g (mapᵉ f b) κ id now sched st E 3≤E inv szB fcB pB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  szf  = ≤-trans (≤-trans (m≤m+n (sizeᵗ f) (sizeᵉ b)) (n≤1+n _)) szB
  szb  = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) (n≤1+n _)) szB
  capf = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fcB
  fcb  = ≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fcB
  fB   : frameB? (capᴱ W E) Ψ (map-f f) ≡ true
  fB   = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ szf)) (T⇒≡true _ (≤⇒≤ᵇ capf))
  sE    = subscribeE g b (map-f f ↠ κ) id now sched st
  IH   = subscribeE-walkS Ψ W g b (map-f f ↠ κ) id now sched st E 3≤E inv
           szb fcb (∧-intro fB pB)
  E₁   = proj₁ IH
  E≤E₁ = proj₁ (proj₂ IH)
  inv₁ = proj₁ (proj₂ (proj₂ IH))
  bB₁  = proj₂ (proj₂ (proj₂ IH))
  cap₁ = capᴱ-mono W E≤E₁
  PB   = pushBurst-wet Ψ W g id now (map-f f) κ (proj₁ sE)
           (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁ (≤-trans 3≤E E≤E₁)
           inv₁ (frameB?-widen (map-f f) cap₁ fB) (pathB?-widen κ cap₁ pB) bB₁
  E₂   = proj₁ PB
  E₁≤E₂ = proj₁ (proj₂ PB)
  inv₂ = proj₁ (proj₂ (proj₂ PB))
  b₂   = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (takeᵉ count b) κ id now sched st E 3≤E inv szB fcB pB
  with evalTm count
... | zero  = E , ≤-refl , inv , refl
... | suc k = E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  szb    = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ count)) (n≤1+n _)) szB
  fcb    = ≤-trans (m≤n⊔m (caseWᵗ count ⊔ fnCapᵗ count) (fnCapᵉ b)) fcB
  inv₀   = install-INV Ψ (capᴱ W E) sched₁ st nid (take-st (suc k)) refl refl inv
  sE      = subscribeE g b (take-f nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-walkS Ψ W g b (take-f nid ↠ κ) id now sched₁ st₀ E 3≤E
             inv₀ szb fcb (∧-intro refl pB)
  E₁     = proj₁ IH
  E≤E₁   = proj₁ (proj₂ IH)
  inv₁   = proj₁ (proj₂ (proj₂ IH))
  bB₁    = proj₂ (proj₂ (proj₂ IH))
  cap₁   = capᴱ-mono W E≤E₁
  PB     = pushBurst-wet Ψ W g id now (take-f nid) κ (proj₁ sE)
             (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁
             (≤-trans 3≤E E≤E₁) inv₁ refl (pathB?-widen κ cap₁ pB) bB₁
  E₂     = proj₁ PB
  E₁≤E₂  = proj₁ (proj₂ PB)
  inv₂   = proj₁ (proj₂ (proj₂ PB))
  b₂     = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS {Γ = Γ} {u = u} Ψ W g (scanᵉ f z b) κ id now sched st E 3≤E inv szB fcB pB =
  E₃ , ≤-trans E≤E₁ (≤-trans E₁≤E₂ E₂≤E₃) , inv₃ , b₃
  where
  E₁    = E * 3 ^ suc Ψ
  E≤E₁  = E≤E*3^ E (suc Ψ)
  3≤E₁  = ≤-trans 3≤E E≤E₁
  cap₁  = capᴱ-mono W E≤E₁
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  -- caps out of fnCapᵉ (scanᵉ f z b) = F ⊔ (Z ⊔ R)
  capf  = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) _) fcB
  capz  : caseWᵗ z ⊔ fnCapᵗ z ≤ Ψ
  capz  = ≤-trans (m≤m⊔n (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ b))
            (≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) _) fcB)
  fcb   = ≤-trans (m≤n⊔m (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ b))
            (≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) _) fcB)
  -- sizes out of sizeᵉ (scanᵉ f z b) = suc (sizeᵗ f + sizeᵗ z + sizeᵉ b)
  szf   = ≤-trans (≤-trans (m≤m+n (sizeᵗ f) (sizeᵗ z))
                   (≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ b)) (n≤1+n _))) szB
  szz   = ≤-trans (≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f))
                   (≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ b)) (n≤1+n _))) szB
  szb   = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f + sizeᵗ z)) (n≤1+n _)) szB
  -- the seed's install pays one eval edge
  seedB = evalTm-cap Ψ W E z (≤-trans (n≤1+n 2) 3≤E)
            (≤-trans (m≤m⊔n (caseWᵗ z) (fnCapᵗ z)) capz) szz
  seedF = fnCap-evalWith Ψ z []ᵃ tt capz
  st₀   = installNode nid (scan-st (evalTm z)) st
  inv₀  = install-INV Ψ (capᴱ W E₁) sched₁ st nid (scan-st (evalTm z))
            (T⇒≡true _ (≤⇒≤ᵇ seedB)) (T⇒≡true _ (≤⇒≤ᵇ seedF))
            (INV?-widen sched₁ st cap₁ inv)
  fB₁   : frameB? (capᴱ W E₁) Ψ (scan-f f nid) ≡ true
  fB₁   = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans szf cap₁)))
                  (T⇒≡true _ (≤⇒≤ᵇ capf))
  sE     = subscribeE g b (scan-f f nid ↠ κ) id now sched₁ st₀
  IH    = subscribeE-walkS Ψ W g b (scan-f f nid ↠ κ) id now sched₁ st₀ E₁
            3≤E₁ inv₀ (≤-trans szb cap₁) fcb
            (∧-intro fB₁ (pathB?-widen κ cap₁ pB))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  cap₂  = capᴱ-mono W E₁≤E₂
  PB    = pushBurst-wet Ψ W g id now (scan-f f nid) κ (proj₁ sE)
            (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₂
            (≤-trans 3≤E₁ E₁≤E₂) inv₂ (frameB?-widen (scan-f f nid) cap₂ fB₁)
            (pathB?-widen κ (capᴱ-mono W (≤-trans E≤E₁ E₁≤E₂)) pB) bB₂
  E₃    = proj₁ PB
  E₂≤E₃ = proj₁ (proj₂ PB)
  inv₃  = proj₁ (proj₂ (proj₂ PB))
  b₃    = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (mergeAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g mergeᵒ (merge-st 0 false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS {u = u} Ψ W g (concatAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g concatᵒ (concat-st {t = u} [] false false) b κ id now
    sched st E 3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS Ψ W g (switchAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g switchᵒ (switch-st nothing false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS Ψ W g (exhaustAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g exhaustᵒ (exhaust-st false false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB

subscribeE-walkS Ψ W g0 (μᵉ body) κ id now sched st E 3≤E inv szB fcB pB =
  E , ≤-refl , inv , refl
subscribeE-walkS Ψ W (gs fuel) (μᵉ body) κ id now sched st E 3≤E inv szB fcB pB =
  proj₁ IH , ≤-trans E≤2E (proj₁ (proj₂ IH)) ,
  proj₁ (proj₂ (proj₂ IH)) , proj₂ (proj₂ (proj₂ IH))
  where
  E≤2E = m≤m+n E (E + 0)
  cap2 = capᴱ-mono W E≤2E
  szU  : sizeᵉ (unfoldμ body) ≤ capᴱ W (2 * E)
  szU  = ≤-trans (size-unfoldμ body)
         (≤-trans (*-mono-≤ szB szB) (≤-reflexive (sym (capᴱ-square W E))))
  fcU  : fnCapᵉ (unfoldμ body) ≤ Ψ
  fcU  = ≤-trans (fnCap-elimG (here refl) (μᵉ body) body) (⊔-lub fcB fcB)
  IH   = subscribeE-walkS Ψ W fuel (unfoldμ body) κ id now sched st (2 * E)
           (≤-trans 3≤E E≤2E) (INV?-widen sched st cap2 inv) szU fcU
           (pathB?-widen κ cap2 pB)

subscribeE-walkS Ψ W g (varᵉ ()) κ id now sched st E 3≤E inv szB fcB pB

subscribeE-walkS Ψ W g (deferᵉ body) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeE-defer-wet Ψ W g body κ id now sched st E 3≤E inv
    (≤-trans (n≤1+n (sizeᵉ body)) szB) fcB pB

------------------------------------------------------------------
-- (W9) THE INPUT CLAUSE.  Five shapes over ONE slot.  INV? carries
-- the slot VECTOR's size and weight as two sums; slotSize-at and
-- slotFnCap-at cut out the single summand this subscription reads,
-- and that is everything the clause knows about what it subscribes.
-- Four shapes are pure state motion — a registration ring, a
-- one-shot, a fresh cold anchor.  `shared` is the one that recurses:
-- its connect walks the stored def, and THAT is the gas edge, so
-- sharedSlot/sharedConnect join the walk's clique.
------------------------------------------------------------------

sharedSlot-wet Ψ W g i d κ id now sched st E 3≤E inv szd fcd pB
  with memberSource (toℕ i) (EvalSt.completedSources st)
-- a share that already completed: completion is re-observable, values
-- are not, so a late subscriber gets close/complete and registers nothing
... | true  = E , ≤-refl , inv , refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
-- already connected: join mid-flight, one registration, no ledger walk
...   | true  = 2 * E , m≤m+n E (E + 0) ,
                register-INV Ψ W E (toℕ i) κ sched st
                  (≤-trans (s≤s z≤n) 3≤E) inv pB ,
                refl
...   | false = sharedConnect-wet Ψ W g i d κ id now sched st E
                  3≤E inv szd fcd pB

-- out of fuel: the dry stub carries a lone close and moves nothing
sharedConnect-wet Ψ W g0 i d κ id now sched st E 3≤E inv szd fcd pB =
  E , ≤-refl , inv , refl
sharedConnect-wet Ψ W (gs fuel) i d κ id now sched st E 3≤E inv szd fcd pB =
  E₂ , E≤E₂ , proj₁ WR , proj₂ WR
  where
  E≤2E  = m≤m+n E (E + 0)
  cap2  = capᴱ-mono W E≤2E
  -- the share owns its registration: it is planted at share-sink
  -- BEFORE the def is walked, so the def's own connect burst sees it
  st₀   = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁   = register (toℕ i) κ st₀
  inv₁  = register-INV Ψ W E (toℕ i) κ sched st₀ (≤-trans (s≤s z≤n) 3≤E)
            (connectShare-INV Ψ (capᴱ W E) (toℕ i) sched st inv) pB
  -- the gas edge: d is a STORED expression, structurally unrelated to
  -- the `input i` being subscribed, so only the fuel decreases here
  IH    = subscribeE-walkS Ψ W fuel d (share-sink i) id now sched st₁ (2 * E)
            (≤-trans 3≤E E≤2E) inv₁ (≤-trans szd cap2) fcd refl
  E₂    = proj₁ IH
  E≤E₂  = ≤-trans E≤2E (proj₁ (proj₂ IH))
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  SE    = subscribeE fuel d (share-sink i) id now sched st₁
  WR    = connectWrap-wet Ψ (capᴱ W E₂) i id (burstCompleted (proj₁ SE))
            (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)) inv₂ bB₂

subscribeE-input-wet {Γ = Γ} Ψ W g i κ id now sched st E 3≤E inv pB
  with Sched.slots sched i
     | slotSize-at Ψ (capᴱ W E) i sched st inv
     | slotFnCap-at Ψ (capᴱ W E) i sched st inv

-- a shared def: connect once, ever; then join
... | shared d | szd | fcd =
      sharedSlot-wet Ψ W g i d κ id now sched st E 3≤E inv szd fcd pB

-- a cold with no async tail: born and spent inside its own burst —
-- nothing registered, nothing scheduled, one ledger-free one-shot
... | scripted (cold sy []) | szs | fcs =
      E , ≤-refl , inv ,
      ∧-intro
        (all-++-intro _ (map value sy) _
          (mapValue-B (capᴱ W E) Ψ (lookup Γ i) sy
            (sumVals-B (capᴱ W E) Ψ (lookup Γ i) sy
              (≤-trans (≤-trans (m≤m+n _ 0) (n≤1+n _)) szs)
              (≤-trans (m≤m+n _ 0) fcs)))
          refl)
        refl

-- a cold WITH a tail: per-subscription anchoring — a fresh source and
-- ordinal, the tail resolved against this subscription's tick, one
-- registration.  resolve only RETIMES, so both slot bounds ride through
... | scripted (cold sy (tv ∷ tvs)) | szs | fcs =
      2 * E , E≤2E ,
      register-INV Ψ W E src κ sched₃ st (≤-trans (s≤s z≤n) 3≤E) inv₃ pB ,
      ∧-intro
        (mapValue-B (capᴱ W (2 * E)) Ψ (lookup Γ i) sy
          (valsB?-widen (lookup Γ i) sy cap2 syB))
        refl
      where
      E≤2E   = m≤m+n E (E + 0)
      cap2   = capᴱ-mono W E≤2E
      src    = Sched.nextSource sched
      sched₁ = proj₂ (mintSource sched)
      ord    = Sched.nextOrdinal sched₁
      sched₂ = proj₂ (mintOrdinal sched₁)
      anchored : LiveSource Γ
      anchored = record { source = src ; ordinal = ord ; elemTy = lookup Γ i
                        ; pending = resolve now (tv ∷ tvs) }
      sched₃ = record sched₂ { live = anchored ∷ Sched.live sched₂ }
      -- the tail's own two sums, split off the slot's.  Both summands
      -- are given: the goal pins only the tail, and nothing can recover
      -- the sync side by inverting _+_
      syncSz = sum (map (sizeᵛ (lookup Γ i)) sy)
      tailSum = sum (map (λ p → sizeᵛ (lookup Γ i) (Timed.val p)) (tv ∷ tvs))
      syncFc = sum (map (fnCapᵛ (lookup Γ i)) sy)
      tailFcSum = sum (map (λ p → fnCapᵛ (lookup Γ i) (Timed.val p)) (tv ∷ tvs))
      tailSz = ≤-trans (m≤n+m tailSum syncSz)
                       (≤-trans (n≤1+n (syncSz + tailSum)) szs)
      tailFc = ≤-trans (m≤n+m tailFcSum syncFc) fcs
      inv₃ = addLive-INV Ψ (capᴱ W E) sched₂ st anchored
               (resolve-bounded (capᴱ W E) now (tv ∷ tvs) tailSz)
               (resolve-measure (fnCapᵛ (lookup Γ i)) Ψ now (tv ∷ tvs) tailFc)
               inv
      syB = sumVals-B (capᴱ W E) Ψ (lookup Γ i) sy
              (≤-trans (≤-trans (m≤m+n _ _) (n≤1+n _)) szs)
              (≤-trans (m≤m+n _ _) fcs)

-- a hot: already live at the slot's own source/ordinal.  Either it is
-- spent (immediate close/complete, nothing registered) or this is just
-- one more registration — fan-out IS that multiplicity
... | scripted (hot _) | szs | fcs
      with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = E , ≤-refl , inv , refl
...   | false = 2 * E , m≤m+n E (E + 0) ,
                register-INV Ψ W E (toℕ i) κ sched st
                  (≤-trans (s≤s z≤n) 3≤E) inv pB ,
                refl

------------------------------------------------------------------
-- THE DELIVERY CLIQUE.  One arrival, one chain: fold the value list
-- sinkward through the frames (stepFrame-wet at every hop, which is
-- where the ledger actually moves), and at a share boundary hand off
-- to the fan-out — one emit per registration the share owes, each
-- folded back through foldPath.  Nothing here mints values: the
-- frames do, and they are already accounted for.
------------------------------------------------------------------

-- the root: assemble the envelope.  evs, then the values, then the
-- completion if this emit carries one
foldPath-wet {u = u} Ψ W sf gas id now envSrc root vals evs fin sched st E
             3≤E inv pB vB eB =
  E , ≤-refl , inv ,
  ∧-intro
    (all-++-intro _ evs _ eB
      (all-++-intro _ (map value vals) _
        (mapValue-B (capᴱ W E) Ψ u vals vB)
        (finList-B (capᴱ W E) Ψ fin)))
    refl

-- the share boundary: the chain's own valueless emit announces the
-- handoff, then the share fans the SAME values out to its own
-- registrations — the diamond, batched by construction
foldPath-wet Ψ W sf gas id now envSrc (share-sink i) vals evs fin sched st E
             3≤E inv pB vB eB =
  E′ , E≤E′ , inv′ ,
  ∧-intro (all-++-intro _ evs _ (eventsB?-widen evs cap′ eB) refl) bB′
  where
  DS   = dispatchShare-wet Ψ W sf gas id now i vals fin sched st E 3≤E inv vB
  E′   = proj₁ DS
  E≤E′ = proj₁ (proj₂ DS)
  inv′ = proj₁ (proj₂ (proj₂ DS))
  bB′  = proj₂ (proj₂ (proj₂ DS))
  cap′ = capᴱ-mono W E≤E′

-- a frame hop: step it, then keep folding down the shorter path
foldPath-wet Ψ W sf gas id now envSrc (f ↠ path′) vals evs fin sched st E
             3≤E inv pB vB eB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , bB₂
  where
  SF   = stepFrame-wet Ψ W sf id now f path′ vals fin sched st E 3≤E inv
           (proj₁ (∧-true (frameB? (capᴱ W E) Ψ f) _ pB))
           (proj₂ (∧-true (frameB? (capᴱ W E) Ψ f) _ pB)) vB
  E₁    = proj₁ SF
  E≤E₁  = proj₁ (proj₂ SF)
  inv₁  = proj₁ (proj₂ (proj₂ SF))
  vB₁   = proj₁ (proj₂ (proj₂ (proj₂ SF)))
  eB₁   = proj₂ (proj₂ (proj₂ (proj₂ SF)))
  cap₁  = capᴱ-mono W E≤E₁
  step  = stepFrame sf id now f path′ vals fin sched st
  IH    = foldPath-wet Ψ W sf gas id now envSrc path′ (proj₁ step)
            (evs ++ proj₁ (proj₂ step)) (proj₁ (proj₂ (proj₂ step)))
            (proj₁ (proj₂ (proj₂ (proj₂ step))))
            (proj₂ (proj₂ (proj₂ (proj₂ step)))) E₁
            (≤-trans 3≤E E≤E₁) inv₁
            (pathB?-widen path′ cap₁
              (proj₂ (∧-true (frameB? (capᴱ W E) Ψ f) _ pB)))
            vB₁
            (all-++-intro _ evs _ (eventsB?-widen evs cap₁ eB) eB₁)
  E₁≤E₂ = proj₁ (proj₂ IH)
  E₂    = proj₁ IH
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))

-- out of dispatch gas: unreachable in a real run (the telescope bound
-- is the context size), and free when it does fire
dispatchShare-wet Ψ W sf zero id now i vals fin sched st E 3≤E inv vB =
  E , ≤-refl , inv , refl
dispatchShare-wet {Γ = Γ} Ψ W sf (suc gas) id now i vals fin sched st E
                  3≤E inv vB =
  E′ , E≤E′ ,
  shareFinish-INV Ψ (capᴱ W E′) i fin (proj₁ GOr)
    (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr)) inv′ ,
  subst (λ b → burstB? (capᴱ W E′) Ψ b ≡ true)
        (sym (shareFinish-burst i fin (proj₁ GOr)
               (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))))
        bB′
  where
  st₀  = shareLatch i fin st
  inv₀ = shareLatch-INV Ψ (capᴱ W E) i fin sched st inv
  adm  = shareAdmit i (EvalSt.registry st)
  admB = shareAdmit-B (capᴱ W E) Ψ i (EvalSt.registry st)
           (proj₁ (proj₂ (proj₂ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv)))))
  GO   = shareGo-wet Ψ W sf gas id now i vals fin adm sched st₀ E 3≤E inv₀ admB vB
  GOr  = shareGo sf gas id now i vals fin adm sched st₀
  E′   = proj₁ GO
  E≤E′ = proj₁ (proj₂ GO)
  inv′ = proj₁ (proj₂ (proj₂ GO))
  bB′  = proj₂ (proj₂ (proj₂ GO))

shareGo-wet Ψ W sf gas id now i vals fin [] sched st E 3≤E inv pB vB =
  E , ≤-refl , inv , refl
shareGo-wet {Γ = Γ} Ψ W sf gas id now i vals fin ((rid , q) ∷ ps) sched st E
            3≤E inv pB vB
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
-- cut earlier this cascade: its close already rode the cutting emit
... | true  = shareGo-wet Ψ W sf gas id now i vals fin ps sched st E 3≤E inv
                (proj₂ (∧-true (pathB? (capᴱ W E) Ψ q) _ pB)) vB
... | false = E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
              all-++-intro _ (proj₁ FPr) _
                (burstB?-widen (proj₁ FPr) cap₂ bB₁) bB₂
  where
  st₀  = record st { delivered = rid ∷ EvalSt.delivered st }
  FP   = foldPath-wet Ψ W sf gas id now (toℕ i) q vals
           (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀ E
           3≤E (delivered-INV Ψ (capᴱ W E) rid sched st inv)
           (proj₁ (∧-true (pathB? (capᴱ W E) Ψ q) _ pB)) vB
           (closeList-B (capᴱ W E) Ψ (toℕ i) fin)
  FPr  = foldPath sf gas id now (toℕ i) q vals
           (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
  E₁   = proj₁ FP
  E≤E₁ = proj₁ (proj₂ FP)
  inv₁ = proj₁ (proj₂ (proj₂ FP))
  bB₁  = proj₂ (proj₂ (proj₂ FP))
  cap₁ = capᴱ-mono W E≤E₁
  IH   = shareGo-wet Ψ W sf gas id now i vals fin ps
           (proj₁ (proj₂ FPr)) (proj₂ (proj₂ FPr)) E₁
           (≤-trans 3≤E E≤E₁) inv₁
           (allPathB-widen ps cap₁
             (proj₂ (∧-true (pathB? (capᴱ W E) Ψ q) _ pB)))
           (valsB?-widen (lookup Γ i) vals cap₁ vB)
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  cap₂  = capᴱ-mono W E₁≤E₂

-- one arrival seeded into one chain: chainStep is foldPath with the
-- arrival's value, its tick, and (when the source is spent) this
-- registration's own exhausted close
chainStep-wet {n = n} {e = e} Ψ W id a path sched st E 3≤E inv pB vB =
  foldPath-wet Ψ W (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st E 3≤E inv pB (∧-intro vB refl)
    (closeList-B (capᴱ W E) Ψ (arrSource a) (Arrival.isLast a))

------------------------------------------------------------------
-- the *All re-entry, the clique's last link: one inner subscription
-- per emitted outer value.  g0 is the dry stub (a lone close, no
-- ledger); gs peels one fuel unit and re-enters subscribeE-walkS on
-- the inner — a runtime VALUE, so the gas is what decreases.
------------------------------------------------------------------

subscribeInner-wet Ψ W g0 op allNid κ id now o sched st E 3≤E inv oB pB =
  E , ≤-refl , inv , refl , refl
subscribeInner-wet {t = t} {u = u} Ψ W (gs fuel) op allNid κ id now o sched st E
                   3≤E inv oB pB =
  E′ , E≤E′ , inv′ ,
  -- s is the burst's element type (u); the phantom A is the ROOT's
  -- (Val Γ t) — that is what subscribeInner's back-channel carries
  splitBurst-vals-B {s = u} {u = t} (capᴱ W E′) Ψ (proj₁ sE) bB ,
  splitBurst-bk-B {s = u} {u = t} (capᴱ W E′) Ψ (proj₁ sE)
  where
  inst   = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc inst }
  sE     = subscribeE fuel o (from-inner op allNid inst ↠ κ) id now sched₀ st
  IH     = subscribeE-walkS Ψ W fuel o (from-inner op allNid inst ↠ κ) id now
             sched₀ st E 3≤E inv
             (≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true _ _ oB))))
             (≤ᵇ⇒≤ _ _ (T-to (proj₂ (∧-true _ _ oB))))
             (∧-intro refl pB)
  E′     = proj₁ IH
  E≤E′   = proj₁ (proj₂ IH)
  inv′   = proj₁ (proj₂ (proj₂ IH))
  bB     = proj₂ (proj₂ (proj₂ IH))

thruConsume-wet Ψ W g mergeᵒ nid κ id now o sched st E 3≤E inv oB pB =
  E₁ , E≤E₁ , mergeBump-INV Ψ (capᴱ W E₁) nid done sched₁ st₁ inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g mergeᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g mergeᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
thruConsume-wet {u = u} Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ nid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | just (concat-st {w} q true od) | nb with w ≟ᵗ u
...   | yes refl =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st nid (concat-st (q ++ o ∷ []) true od)
    (all-++-intro _ q _ (proj₁ nb)
      (∧-intro (proj₁ (∧-true _ _ oB)) refl))
    (all-++-intro _ q _ (proj₂ nb)
      (∧-intro (proj₂ (∧-true _ _ oB)) refl))
    inv ,
  refl , refl
...   | no _ = E , ≤-refl , inv , refl , refl
thruConsume-wet {u = u} Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (concat-st q false od) | nb =
  E₁ , E≤E₁ ,
  install-INV Ψ (capᴱ W E₁) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (concat-st {t = u} [] (not done) od) refl refl inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g concatᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | nothing | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (scan-st _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (take-st _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (merge-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (switch-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (exhaust-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g switchᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
  E₁ , E≤E₁ ,
  install-INV Ψ (capᴱ W E₁) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₂ nid
    (switch-st (if done then nothing else just inst) od) refl refl inv₁ ,
  vsB ,
  all-++-intro _ closes _
    (eventsB?-widen closes (capᴱ-mono W E≤E₁) (proj₂ KL)) bsB
  where
  KL     = switchKill-INV Ψ W E cur sched st inv
  closes = proj₁ (switchKill cur sched st)
  sched₁ = proj₁ (proj₂ (switchKill cur sched st))
  st₁    = proj₂ (proj₂ (switchKill cur sched st))
  SI     = subscribeInner-wet Ψ W g switchᵒ nid κ id now o sched₁ st₁ E 3≤E
             (proj₁ KL) oB pB
  SI₄    = subscribeInner g switchᵒ nid κ id now o sched₁ st₁
  inst   = proj₁ SI₄
  done   = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁     = proj₁ SI
  E≤E₁   = proj₁ (proj₂ SI)
  inv₁   = proj₁ (proj₂ (proj₂ SI))
  vsB    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
... | nothing                = E , ≤-refl , inv , refl , refl
... | just (scan-st _)       = E , ≤-refl , inv , refl , refl
... | just (take-st _)       = E , ≤-refl , inv , refl , refl
... | just (merge-st _ _)    = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , refl , refl
... | just (exhaust-st _ _)  = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g exhaustᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = E , ≤-refl , inv , refl , refl
... | just (exhaust-st false od) =
  E₁ , E≤E₁ ,
  install-INV Ψ (capᴱ W E₁) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (exhaust-st (not done) od) refl refl inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g exhaustᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g exhaustᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
... | nothing                = E , ≤-refl , inv , refl , refl
... | just (scan-st _)       = E , ≤-refl , inv , refl , refl
... | just (take-st _)       = E , ≤-refl , inv , refl , refl
... | just (merge-st _ _)    = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , refl , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , refl , refl

thruWalk-wet Ψ W g op nid κ id now [] sched st E 3≤E inv pB vB =
  E , ≤-refl , inv , refl , refl
thruWalk-wet {u = u} Ψ W g op nid κ id now (o ∷ os) sched st E 3≤E inv pB vB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
  all-++-intro _ vs _ (valsB?-widen u vs cap₁₂ vsB) vs′B ,
  all-++-intro _ bs _ (eventsB?-widen bs cap₁₂ bsB) bs′B
  where
  CS   = thruConsume-wet Ψ W g op nid κ id now o sched st E 3≤E inv
           (proj₁ (∧-true _ _ vB)) pB
  cr   = thruConsume g op nid κ id now o sched st
  vs   = proj₁ cr
  bs   = proj₁ (proj₂ cr)
  E₁   = proj₁ CS
  E≤E₁ = proj₁ (proj₂ CS)
  inv₁ = proj₁ (proj₂ (proj₂ CS))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ CS)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ CS)))
  cap₁ = capᴱ-mono W E≤E₁
  IH   = thruWalk-wet Ψ W g op nid κ id now os
           (proj₁ (proj₂ (proj₂ cr))) (proj₂ (proj₂ (proj₂ cr))) E₁
           (≤-trans 3≤E E≤E₁) inv₁ (pathB?-widen κ cap₁ pB)
           (valsB?-widen (obs u) os cap₁ (proj₂ (∧-true _ _ vB)))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  vs′B  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  bs′B  = proj₂ (proj₂ (proj₂ (proj₂ IH)))
  cap₁₂ = capᴱ-mono W E₁≤E₂

------------------------------------------------------------------
-- the inner *All frame's drain and finish.  concatAll is the only
-- op whose completion does more than flip a flag: it walks its
-- parked queue, subscribing each stored outer until one stays open.
------------------------------------------------------------------

concatDrain-wet Ψ W g allNid κ id now [] sched st E 3≤E inv pB qz qf =
  E , ≤-refl , inv , refl , refl , refl , refl
concatDrain-wet {s = s} Ψ W g allNid κ id now (o ∷ q) sched st E 3≤E inv pB qz qf
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-wet Ψ W g concatᵒ allNid κ id now o sched st E 3≤E inv
         (∧-intro (proj₁ (∧-true (sizeᵉ o ≤ᵇ capᴱ W E) _ qz))
                  (proj₁ (∧-true (fnCapᵉ o ≤ᵇ Ψ) _ qf))) pB
... | (_ , vs , bs , false , sched₁ , st₁) | (E₁ , E≤E₁ , inv₁ , vsB , bsB) =
  E₁ , E≤E₁ , inv₁ , vsB , bsB ,
  allsz-widen q (capᴱ-mono W E≤E₁) (proj₂ (∧-true _ _ qz)) ,
  proj₂ (∧-true _ _ qf)
... | (_ , vs , bs , true , sched₁ , st₁) | (E₁ , E≤E₁ , inv₁ , vsB , bsB) =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
  all-++-intro _ vs _ (valsB?-widen s vs cap₁₂ vsB) vs′B ,
  all-++-intro _ bs _ (eventsB?-widen bs cap₁₂ bsB) bs′B ,
  q′z , q′f
  where
  IH    = concatDrain-wet Ψ W g allNid κ id now q sched₁ st₁ E₁
            (≤-trans 3≤E E≤E₁) inv₁ (pathB?-widen κ (capᴱ-mono W E≤E₁) pB)
            (allsz-widen q (capᴱ-mono W E≤E₁) (proj₂ (∧-true _ _ qz)))
            (proj₂ (∧-true _ _ qf))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  vs′B  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  bs′B  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  q′z   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  q′f   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  cap₁₂ = capᴱ-mono W E₁≤E₂

innerFinish-wet Ψ W g mergeᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od)   =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st allNid (merge-st (pred k) od) refl refl inv ,
  vB , refl
... | nothing                = E , ≤-refl , inv , vB , refl
... | just (scan-st _)       = E , ≤-refl , inv , vB , refl
... | just (take-st _)       = E , ≤-refl , inv , vB , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , vB , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , vB , refl
... | just (exhaust-st _ _)  = E , ≤-refl , inv , vB , refl
innerFinish-wet {s = s} Ψ W g concatᵒ allNid inst κ id now vals sched st E
                3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ allNid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | just (concat-st {w} q act od) | nb with w ≟ᵗ s
...   | yes refl =
  E′ , E≤E′ ,
  install-INV Ψ (capᴱ W E′) sched′ st′ allNid (concat-st q′ act′ od)
    q′z q′f inv′ ,
  all-++-intro _ vals _ (valsB?-widen s vals (capᴱ-mono W E≤E′) vB) vsB ,
  bsB
  where
  DR    = concatDrain-wet Ψ W g allNid κ id now q sched st E 3≤E inv pB
            (proj₁ nb) (proj₂ nb)
  dr    = concatDrain g allNid κ id now q sched st
  act′  = proj₁ (proj₂ (proj₂ dr))
  q′    = proj₁ (proj₂ (proj₂ (proj₂ dr)))
  sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
  st′   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
  E′    = proj₁ DR
  E≤E′  = proj₁ (proj₂ DR)
  inv′  = proj₁ (proj₂ (proj₂ DR))
  vsB   = proj₁ (proj₂ (proj₂ (proj₂ DR)))
  bsB   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  q′z   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR)))))
  q′f   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR)))))
...   | no _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | nothing               | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (scan-st _)      | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (take-st _)      | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (merge-st _ _)   | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (switch-st _ _)  | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (exhaust-st _ _) | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
... | just (switch-st (just c) od) with c ≡ᵇ inst
...   | true  =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st allNid (switch-st nothing od) refl refl inv ,
  vB , refl
...   | false = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (switch-st nothing od) = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | nothing                = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (scan-st _)       = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (take-st _)       = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (merge-st _ _)    = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (concat-st _ _ _) = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (exhaust-st _ _)  = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g exhaustᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
... | just (exhaust-st act od) =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st allNid (exhaust-st false od) refl refl inv ,
  vB , refl
... | nothing                = E , ≤-refl , inv , vB , refl
... | just (scan-st _)       = E , ≤-refl , inv , vB , refl
... | just (take-st _)       = E , ≤-refl , inv , vB , refl
... | just (merge-st _ _)    = E , ≤-refl , inv , vB , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , vB , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , vB , refl

------------------------------------------------------------------
-- THE FOLD DECOMPOSITION, PROVEN: cascadeGo threads the walk
-- invariant chain by chain over chainStep-wet.  This is the
-- structure the cascadeGo-wet memo demanded — per-cascade growth
-- threads through the fold at a moving ledger position, with the
-- registry cardinality rider (INV?'s length conjunct) available at
-- the latch for the eventual receipt arithmetic.  Not consumed yet:
-- cascade-dry keeps riding the landing core below until the
-- quantitative debt (memo (3)) closes.
------------------------------------------------------------------

cascadeGo-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (λ rc → pathB? (capᴱ W E) Ψ (proj₂ rc)) chains ≡ true →
  valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
cascadeGo-walk Ψ W a id [] sched st E 3≤E inv chB vB =
  E , ≤-refl , inv , refl
cascadeGo-walk Ψ W a id ((rid , c) ∷ chains) sched st E 3≤E inv chB vB
  with ∧-true (pathB? (capᴱ W E) Ψ c) _ chB
... | pc , pchains with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-walk Ψ W a id chains sched st E 3≤E inv pchains vB
... | false =
  let st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
      (E₁ , E≤E₁ , inv₁ , em₁) =
        chainStep-wet Ψ W id a c sched st₀ E 3≤E inv pc vB
      cap≤ = capᴱ-mono W E≤E₁
      (E₂ , E₁≤E₂ , inv₂ , em₂) =
        cascadeGo-walk Ψ W a id chains
          (proj₁ (proj₂ (chainStep id a c sched st₀)))
          (proj₂ (proj₂ (chainStep id a c sched st₀)))
          E₁ (≤-trans 3≤E E≤E₁) inv₁
          (chainsB?-widen chains cap≤ pchains)
          (valB?-widen (arrTy a) (arrVal a) cap≤ vB)
  in E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
     all-++-intro _ (proj₁ (chainStep id a c sched st₀)) _
       (burstB?-widen (proj₁ (chainStep id a c sched st₀))
                      (capᴱ-mono W E₁≤E₂) em₁)
       em₂

------------------------------------------------------------------
-- the three cores
------------------------------------------------------------------

------------------------------------------------------------------
-- THE PROOF DESIGN for the three cores (2026-07-19, after the tower
-- attack).  The wet contract for the mutual subscription block is one
-- strengthened induction, consumed through `hasAtLeast`:
--
--   fuel hasAtLeast need(args) → no dry × stores land bounded
--
-- and the induction that defines/bounds `need` is LEXICOGRAPHIC over
-- the three decrement edges:
--
--   1. share connect — decreases the UNCONNECTED-SLOT COUNT
--      (connectedShares latches; a def's walk can only shrink it).
--   2. μ-unfold — decreases SYNC-REACHABLE SIZE (syncSizeᵉ, deferᵉ
--      a leaf): unfoldμ substitutes `μᵉ body` only at var positions,
--      and vars are TYPE-GUARANTEED defer-gated (Δᵍ→Δ moves only at
--      deferᵉ), so the substituted copies are invisible to the
--      synchronous walk.  DISCHARGED above: syncSize-unfoldμ /
--      unfoldμ-shrinks, machine-checked.
--   3. subscribeInner — decreases the DERSHOWITZ–MANNA MULTISET of
--      SHELL sizes (2026-07-20: the SHELL DESIGN, adopted with
--      Anthony's approval, replacing the layer-derivation reading).
--      A runtime obs value IS a closed expression; its measure is
--      measureE = counts B ∘ shellsᵉ — the multiset of operator-
--      skeleton sizes of the value and every sync-reachable
--      embedded observable (Rx.Exp.shellsᵉ), a pure function of
--      syntax.  Shells count Exp constructors ONLY (Tm material
--      weightless, strmᵗ/deferᵉ leaves), which buys the design's
--      two load-bearing facts, both PROVEN above:
--        · substitution invariance (shellSize-subΘ): subΘ rewrites
--          only Tm material, so instantiation preserves every
--          shell size EXACTLY.  No inflation — an instantiated
--          template's multiset is a class-preserved copy of the
--          template's plus the plugged obs values' own shells
--          (reify-inner: a plug's footprint is void, its shells
--          join the inner multiset verbatim).
--        · free side conditions: every shell of e is ≤ sizeᵉ e
--          (shells-≤/shellsᵛ-≤) and shells number ≤ sizeᵉ e
--          (shells-len) — so stBounded?'s sizeᵛ cap bounds both
--          the classes (≤ B) and the entry sum (≤ V, the rank
--          bridge's side condition).  NO new invariant; the whole
--          Layered derivation apparatus is deleted (git: 1fbc59c).
--      The hops:
--        · embedded-value hop (subscribing a value that sits as a
--          strmᵗ subtree of the carrier — of-list literals under
--          closed evaluation, evalWith (strmᵗ e) []ᵃ = e): its
--          shellsᵉ is a CONTIGUOUS sublist of the carrier's inner
--          (innerᵗ (strmᵗ e) = shellsᵉ e), and the carrier's own
--          shell rides on top — strict sub-multiset, ≺-embed.
--        · eval/scan-produced hop (applyFn/evalWith instantiates a
--          template): by shellSize-subΘ the produced multiset =
--          the fn-body strmᵗ subtree's sub-multiset, classes on
--          the nose, ⊎ the plugged obs values' shells.  The first
--          part is the embed shape again; the plugged part is
--          where the LEDGER lives — the plugs are prior stored
--          values whose shells the global multiset already owns
--          (deliveries ≤ syntactic occurrences because subΘ
--          COPIES trees — SYNC-LINEARITY, PROVEN above:
--          plugs-lenᵉ bounds the plug cardinality by occsᵉ · V,
--          occs≤syncᵉ caps occurrences syntactically, and
--          inner-len-subΘ is the exact length bookkeeping).  The
--          multiset-level input is the subΘ multiset equation
--          (subΘ-countsᵉ, proven); subΘ-capᵉ is its All-cap
--          shadow and subΘ-shells-len its entry-sum package.
--        · share-crossing hop (a template's `input` hits a slot):
--          exits the per-value measure — it anchors against the
--          slot's own element of the GLOBAL multiset {program} ⊎
--          {slots}; that re-anchoring is the ownership half of the
--          ledger (cascadeGo-wet), not the per-value order.
--      (The 2026-07-19 layer-derivation design worked but carried
--      an unfixable wart: unused env entries gave layers with no
--      syntactic footprint, so the entry-sum side condition needed
--      its own invariant.  The design before THAT — lex (skeleton,
--      value size), subterm-ordered — is REFUTED: chain two
--      obs-typed scans directly, second fn λ(b,v). mergeAll(of[snd
--      x]), and the embedded-value hop lands on a first-scan ac
--      whose template is subterm-incomparable with the carrier's
--      and can dwarf it.)
--
-- THE DEMAND, closed-form and PROVEN (dBound above).  Fuel is
-- depth-consumed, so the contract carries
--
--   fuel hasAtLeast suc (dBound V R U r s)
--
-- with V the store size bound, R = (suc V)^(suc B) the store rank
-- cap (rank-lt-pow), U = unconn, r = the current value's rank, s =
-- the current expression's syncSize.  Each decrement edge consumes
-- one gs against a strictly smaller demand: dBound-μ
-- (unfoldμ-shrinks drops s), dBound-hop (rank-mono-≺ over
-- ≺-embed/≺-replace drops r, s resets ≤ V), dBound-connect
-- (unconn-insert drops U, r resets ≤ R) — all three proven, so the
-- clause proofs only apply them.  dBound < (suc V)^(B+3)·suc U:
-- one exponential story above the store bound, while the seeded
-- budget's tower gains (suc sz) stories per instant —
-- budget-hasAtLeast's tower summand dominates with room to spare,
-- and every literal-headed demand (no chained scans) is already
-- covered by the 2^(sz·(id+1)²) summand alone.
--
-- The cores below are the contract instantiated at
-- the root burst (burst-dry/-bounded) and at the chain fold
-- (cascadeGo-wet); the disjointness argument (each registration's
-- path owns its minted nodes, so per-cascade store traffic is
-- structure-bounded) supplies the store-boundedness half.
--
-- THE WALK INVARIANT (2026-07-20, the clause-grind session).  The
-- stated subscribeE-wet is the contract's OUTER FACE only — its
-- `sizeᵉ b ≤ V` hypothesis holds at both instantiation sites (root
-- program; stored values) but does NOT self-apply down the walk,
-- and the induction must generalize internally:
--   · μ edge: unfoldμ COPIES the closed μ, so sizeᵉ grows past any
--     fixed cap along iterated unfolds.  Thread the SHELL caps
--     instead — every shell preserved-or-stepped-down and the
--     count exactly preserved (shells-unfoldμ-cap/-len above);
--     sizeᵉ is only needed for STORABILITY, against the (tower)
--     landing budget, not against V.
--   · no fixed (V, R) survives the walk: a scan frame folds each
--     value with NO fuel peel (fuel is depth-consumed; breadth is
--     free), and each fold is one base swap (applyFn-size), so
--     mid-walk stores legitimately outgrow the entry cap V and
--     later inner subscriptions carry ranks past R.  A cap indexed
--     by REMAINING GAS fails for the same reason (folds do not
--     peel gas).
--   · the missing accounting is a per-instant BREADTH LEDGER: the
--     value-list lengths threading stepFrame/pushBurst.  SETTLED
--     2026-07-24 — see THE WALK LEDGER section above: the sharp
--     eval bound (caseW, substitution-invariant exponent) replaces
--     applyFn-size's self-inflating one, the ledger is the
--     multiplicative exponent capᴱ W₀ E with one uniform ×3^(suc Ψ)
--     rule per eval edge and ×2 per cheap edge, fold-runs cost
--     3^(suc Ψ · m) by scanVals-sharp, and INV? (store bounds +
--     fn caps + registry cardinality + chain frames) is the
--     invariant the walk contracts thread.  The count cap's DESIGN
--     closed 2026-07-24 (memo (5), THE WIDTH LEDGER, corrected to
--     the recurrence-closed walkCap form): widths are
--     substitution-invariant, so run lengths and the per-lineage
--     fold count 𝔉 anchor at walkCap — all entry-frozen.  The
--     JOINT FACE (subscribeE-walk above) states wet + dry + ledger
--     together; what remains is its clause grind and the landing
--     composition; until THAT lands, the landing halves live in
--     these two cores and nowhere else.
------------------------------------------------------------------

------------------------------------------------------------------
-- (W11-A) THE FLAT STATE LEMMAS.  Ω never moves, so each of these
-- is "invariant in, invariant out": the size side's ledger edges
-- (register-INV's ×2 length rider, the widening chains) all vanish,
-- and widthOK? has no length conjunct to pay them with.  Every
-- proof below is its fnCap counterpart with the arithmetic deleted.
------------------------------------------------------------------

-- widthOK? is a FLAT four-way ∧ (no nested stBounded?/fnCapBounded?
-- pair), so one projector serves the whole block — same reason
-- INV-parts exists: `∧-true _ _` alone leaves a stuck metavariable
WOK-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → widthOK? Ω sched st ≡ true →
  (all (ofWLive Ω) (Sched.live sched) ≡ true)
  × (all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st) ≡ true)
  × (regsΩ? Ω (EvalSt.registry st) ≡ true)
  × ((slotsOfW (Sched.slots sched) ≤ᵇ Ω) ≡ true)
WOK-parts Ω sched st h
  with ∧-true (all (ofWLive Ω) (Sched.live sched)) _ h
... | lv , r1
  with ∧-true (all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st)) _ r1
... | nd , r2 with ∧-true (regsΩ? Ω (EvalSt.registry st)) _ r2
... | rg , sl = lv , nd , rg , sl

-- the node-install ring (mirror of setNode-bounded / setNode-fnCap)
setNode-ofW : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  ofWNode Ω ns ≡ true →
  all (λ kv → ofWNode Ω (proj₂ kv)) nodes ≡ true →
  all (λ kv → ofWNode Ω (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-ofW Ω nid ns []             bn h = ∧-intro bn refl
setNode-ofW Ω nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-ofW Ω nid ns r bn (proj₂ (∧-true _ _ h)))

install-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  ofWNode Ω ns ≡ true → widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (installNode nid ns st) ≡ true
install-width Ω sched st nid ns bn h =
  ∧-intro (proj₁ P)
  (∧-intro (setNode-ofW Ω nid ns (EvalSt.nodes st) bn (proj₁ (proj₂ P)))
  (∧-intro (proj₁ (proj₂ (proj₂ P))) (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- registering a chain: one entry appended, its frames bounded by
-- hypothesis.  No length rider means no ledger edge at all — the
-- single place where the width walk is strictly cheaper than the
-- size walk rather than merely equal
register-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  widthOK? Ω sched (register src κ st) ≡ true
register-width {u = u} Ω src κ sched st h pκ =
  ∧-intro (proj₁ P)
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (all-++-intro _ (EvalSt.registry st) _
              (proj₁ (proj₂ (proj₂ P))) (∧-intro pκ refl))
           (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

addLive-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (l : LiveSource Γ) →
  ofWLive Ω l ≡ true → widthOK? Ω sched st ≡ true →
  widthOK? Ω (record sched { live = l ∷ Sched.live sched }) st ≡ true
addLive-width Ω sched st l bl h =
  ∧-intro (∧-intro bl (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (proj₁ (proj₂ (proj₂ P))) (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- the live sweep, width face (mirror of sweepLive-bounded/-fnCap)
sweepLive-ofW : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (ofWLive Ω) ls ≡ true →
  all (ofWLive Ω) (sweepLive reg ls) ≡ true
sweepLive-ofW Ω reg []       h = refl
sweepLive-ofW {n = n} Ω reg (l ∷ ls) h
  with ∧-true (ofWLive Ω l) (all (ofWLive Ω) ls) h
... | bl , bls
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ∧-intro bl (sweepLive-ofW Ω reg ls bls)
... | false = sweepLive-ofW Ω reg ls bls

-- dropping a source only shrinks the registry
dropSource-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (dropSource src reg) ≡ true
dropSource-regsΩ Ω src []                  h = refl
dropSource-regsΩ Ω src ((rid , s , c) ∷ r) h with sameSource src s
... | true  = dropSource-regsΩ Ω src r (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (dropSource-regsΩ Ω src r (proj₂ (∧-true _ _ h)))

latch-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched
    (record st { registry = dropSource src (EvalSt.registry st)
               ; completedSources = src ∷ EvalSt.completedSources st })
    ≡ true
latch-width Ω src sched st h =
  ∧-intro (proj₁ P)
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (dropSource-regsΩ Ω src (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- completedSources / dying / delivered / connectedShares are read
-- by no conjunct of widthOK? either
shareLatch-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → widthOK? Ω sched (shareLatch i b st) ≡ true
shareLatch-width Ω i false sched st h = h
shareLatch-width Ω i true  sched st h = h

delivered-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (record st { delivered = rid ∷ EvalSt.delivered st })
    ≡ true
delivered-width Ω rid sched st h = h

connectShare-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched
    (record st { connectedShares = src ∷ EvalSt.connectedShares st }) ≡ true
connectShare-width Ω src sched st h = h

-- the admitted fan-out chains inherit their frame widths
shareAdmit-Ω : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (i : Fin n)
  (reg : List (RegId × Source × Chain Γ t)) → regsΩ? Ω reg ≡ true →
  all (λ rp → pathΩ? Ω (proj₂ rp)) (shareAdmit i reg) ≡ true
shareAdmit-Ω Ω i []                      h = refl
shareAdmit-Ω {Γ = Γ} Ω i ((rid , src , (u , q)) ∷ r) h
  with sameSource (toℕ i) src | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h))
... | true  | no  _    = shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h))
... | true  | yes refl =
      ∧-intro (proj₁ (∧-true (pathΩ? Ω q) _ h))
              (shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h)))

shareFinish-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω (proj₁ (proj₂ (shareFinish i b (emits , sched , st))))
             (proj₂ (proj₂ (shareFinish i b (emits , sched , st)))) ≡ true
shareFinish-width Ω i false emits sched st h = h
shareFinish-width Ω i true  emits sched st h =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (dropSource-regsΩ Ω (toℕ i) (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P)))))
  where
  kept = dropSource (toℕ i) (EvalSt.registry st)
  P    = WOK-parts Ω sched st h

------------------------------------------------------------------
-- (W11-A′) THE BURST HELPERS.  eventΩ? only constrains `value`, so
-- every marker list is refl and the real content is the value lists.
------------------------------------------------------------------

mapValue-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true →
  all (eventΩ? Ω) (map value vs) ≡ true
mapValue-Ω Ω u []       h = refl
mapValue-Ω Ω u (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (mapValue-Ω Ω u vs (proj₂ (∧-true _ _ h)))

finList-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (b : Bool) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω)
      (if b then complete ∷ [] else []) ≡ true
finList-Ω Ω true  = refl
finList-Ω Ω false = refl

closeList-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (src : Source) (b : Bool) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-Ω Ω src true  = refl
closeList-Ω Ω src false = refl

sharedPlumb-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (str : Stream Γ u) →
  burstΩ? Ω str ≡ true → burstΩ? Ω (sharedPlumb str) ≡ true
sharedPlumb-Ω Ω []         h = refl
sharedPlumb-Ω Ω (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-Ω Ω ems (proj₂ (∧-true _ _ h)))

-- a script's sync prefix, elementwise off the slot's ofW SUM (the
-- width seed is a sum dominating the max, exactly as ΨAt is)
sumVals-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  sum (map (ofWᵛ u) vs) ≤ Ω → all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true
sumVals-Ω Ω u []       hw = refl
sumVals-Ω Ω u (v ∷ vs) hw =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (ofWᵛ u v) _) hw)))
          (sumVals-Ω Ω u vs (≤-trans (m≤n+m _ (ofWᵛ u v)) hw))

-- one slot's width, projected out of widthOK?'s slots sum
slotOfW-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → slotOfW (Sched.slots sched i) ≤ Ω
slotOfW-at Ω i sched st h =
  ≤-trans (fᵢ≤sum-tab (λ j → slotOfW (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to (proj₂ (proj₂ (proj₂ (WOK-parts Ω sched st h))))))

------------------------------------------------------------------
-- (W11-B) THE FRAME ANALYTICS.  Every fact the frames need about
-- values, nodes and the registry, at the flat width.  These are the
-- W2/W4 mirrors with the ledger stripped: no caseW rider (widths
-- are substitution-invariant, so eval never widens), no capᴱ, no E.
------------------------------------------------------------------

applyFn-ofW : ∀ {n} {Γ : Ctx n} {s t} (Ω : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  ofWᵛ s v ≤ Ω → ofWᵗ fn ≤ Ω → ofWᵛ t (applyFn fn v) ≤ Ω
applyFn-ofW Ω fn v hv hfn = ofW-evalWith Ω fn (v ∷ᵃ []ᵃ) (hv , tt) hfn

map-applyFn-Ω : ∀ {n} {Γ : Ctx n} {s u} (Ω : ℕ)
  (fn : Fn Γ [] [] [] s u) → ofWᵗ fn ≤ Ω →
  (vs : List (Val Γ s)) → all (λ v → ofWᵛ s v ≤ᵇ Ω) vs ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) (map (applyFn fn) vs) ≡ true
map-applyFn-Ω Ω fn hfn []       h = refl
map-applyFn-Ω {s = s} Ω fn hfn (v ∷ vs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (applyFn-ofW Ω fn v
            (≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))) hfn)))
          (map-applyFn-Ω Ω fn hfn vs
            (proj₂ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))

-- one fold run: the accumulator and every output stay under Ω,
-- because applyFn never widens (ofW-evalWith)
scanVals-ofW : ∀ {n} {Γ : Ctx n} {s u} (Ω : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) →
  ofWᵗ fn ≤ Ω → ofWᵛ u ac ≤ Ω →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vs ≡ true →
  (ofWᵛ u (proj₂ (scanVals fn ac vs)) ≤ Ω)
  × (all (λ o → ofWᵛ u o ≤ᵇ Ω) (proj₁ (scanVals fn ac vs)) ≡ true)
scanVals-ofW Ω fn ac []       hfn hacc _ = hacc , refl
scanVals-ofW {s = s} Ω fn ac (v ∷ vs) hfn hacc h =
  proj₁ IH , ∧-intro (T⇒≡true _ (≤⇒≤ᵇ acc′OK)) (proj₂ IH)
  where
  hv     = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))
  acc′OK = applyFn-ofW Ω fn (ac , v) (⊔-lub hacc hv) hfn
  IH     = scanVals-ofW Ω fn (applyFn fn (ac , v)) vs hfn acc′OK
             (proj₂ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h))

takeVals-Ω : ∀ {n} {Γ : Ctx n} {s} (Ω : ℕ) (k : ℕ) (vals : List (Val Γ s)) →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (takeVals k vals)) ≡ true
takeVals-Ω Ω zero          _        h = refl
takeVals-Ω Ω (suc k)       []       h = refl
takeVals-Ω Ω (suc zero)    (v ∷ vs) h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-Ω Ω (suc (suc k)) (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-Ω Ω (suc k) vs (proj₂ (∧-true _ _ h)))

cutThrough-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regsΩ Ω nid d wm dy []                    h = refl
cutThrough-regsΩ Ω nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regsΩ Ω nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | kept , closes , rids | ih = ih
... | false | kept , closes , rids | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closesΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventΩ? Ω) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closesΩ Ω nid d wm dy []                    = refl
cutThrough-closesΩ Ω nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-closesΩ Ω nid d wm dy r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih
      with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

-- a node lookup carries the width face of whatever it finds
NodeΩ : ∀ {n} {Γ : Ctx n} → ℕ → Maybe (NodeState Γ) → Set
NodeΩ Ω nothing   = ⊤
NodeΩ Ω (just ns) = ofWNode Ω ns ≡ true

lookupNode-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → ofWNode Ω (proj₂ kv)) nodes ≡ true →
  NodeΩ Ω (lookupNode nid nodes)
lookupNode-Ω Ω nid []            h = tt
lookupNode-Ω Ω nid ((k , s) ∷ r) h with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ h)
... | false = lookupNode-Ω Ω nid r (proj₂ (∧-true _ _ h))

-- splitting an emit / a whole burst
splitEvents-vals-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? Ω) es ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-Ω Ω []              h = refl
splitEvents-vals-Ω Ω (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h)))
splitEvents-vals-Ω Ω (init _   ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (close _ _ ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (handoff _ ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (complete ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))

splitEvents-bk-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? Ω) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-Ω Ω []              = refl
splitEvents-bk-Ω {u = u} Ω (value v  ∷ es) = splitEvents-bk-Ω {u = u} Ω es
splitEvents-bk-Ω {u = u} Ω (init _   ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (close _ _ ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (handoff _ ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (complete ∷ es) = splitEvents-bk-Ω {u = u} Ω es

splitBurst-vals-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ) (str : Stream Γ s) →
  burstΩ? Ω str ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-Ω Ω []               h = refl
splitBurst-vals-Ω {Γ = Γ} {u = u} Ω (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-Ω Ω (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-Ω {u = u} Ω ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ) (str : Stream Γ s) →
  all (eventΩ? Ω) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-Ω Ω []               = refl
splitBurst-bk-Ω {Γ = Γ} {u = u} Ω (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-Ω {u = u} Ω (InstEmit.events em))
    (splitBurst-bk-Ω {u = u} Ω ems)

-- retagging drops values, so the result is unconditionally clean
retag-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω) (retagEvents es) ≡ true
retag-Ω Ω []              = refl
retag-Ω {u = u} Ω (init _   ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (close _ _ ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (handoff _ ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (complete ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (value _  ∷ es) = retag-Ω {u = u} Ω es

-- mergeAll's counter bump and switchAll's cut, width faces
mergeBump-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (nid : NodeId) (d : Bool) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (record st { nodes = mergeBump nid d (EvalSt.nodes st) })
    ≡ true
mergeBump-width Ω nid d sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od)   = install-width Ω sched st nid
                                 (merge-st (if d then k else suc k) od) refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

switchKill-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  let r = switchKill cur sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (all (eventΩ? Ω) (proj₁ r) ≡ true)
switchKill-width Ω nothing  sched st inv = inv , refl
switchKill-width Ω (just v) sched st inv =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (cutThrough-regsΩ Ω v del wm dy (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P))))) ,
  cutThrough-closesΩ Ω v del wm dy (EvalSt.registry st)
  where
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough v del wm dy (EvalSt.registry st))
  P    = WOK-parts Ω sched st inv

-- the wrap: values and events pass through, only the *All node's
-- done flag is written back
thruWrap-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true →
  all (eventΩ? Ω) bs ≡ true →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
thruWrap-width Ω op nid false vs bs sched st inv vΩ bΩ = inv , vΩ , bΩ
thruWrap-width Ω mergeᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)    =
      install-width Ω sched st nid (merge-st k true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (switch-st _ _)   = inv , vΩ , bΩ
... | just (exhaust-st _ _)  = inv , vΩ , bΩ
thruWrap-width Ω concatᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st q act _) | nb =
      install-width Ω sched st nid (concat-st q act true) nb inv , vΩ , bΩ
... | nothing                | _ = inv , vΩ , bΩ
... | just (scan-st _)       | _ = inv , vΩ , bΩ
... | just (take-st _)       | _ = inv , vΩ , bΩ
... | just (merge-st _ _)    | _ = inv , vΩ , bΩ
... | just (switch-st _ _)   | _ = inv , vΩ , bΩ
... | just (exhaust-st _ _)  | _ = inv , vΩ , bΩ
thruWrap-width Ω switchᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      install-width Ω sched st nid (switch-st cur true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (merge-st _ _)    = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (exhaust-st _ _)  = inv , vΩ , bΩ
thruWrap-width Ω exhaustᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      install-width Ω sched st nid (exhaust-st act true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (merge-st _ _)    = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (switch-st _ _)   = inv , vΩ , bΩ

------------------------------------------------------------------
-- the two SELF-CONTAINED frames: scan folds under Ω (applyFn never
-- widens), take passes a prefix through and, on the cutting emit,
-- runs cutThrough + sweepLive.  Neither re-enters subscribeE, so
-- both live outside the clique.
------------------------------------------------------------------

stepFrame-scan-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω (scan-f fn nid) ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
stepFrame-scan-width {s = s} {u = u} Ω g id now fn nid κ vals fin sched st
                     inv fΩ vΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | nothing                | _ = inv , refl , refl
... | just (take-st _)       | _ = inv , refl , refl
... | just (merge-st _ _)    | _ = inv , refl , refl
... | just (concat-st _ _ _) | _ = inv , refl , refl
... | just (switch-st _ _)   | _ = inv , refl , refl
... | just (exhaust-st _ _)  | _ = inv , refl , refl
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = inv , refl , refl
...   | yes refl =
  install-width Ω sched st nid (scan-st (proj₂ run))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ run-ok))) inv ,
  proj₂ run-ok , refl
  where
  run    = scanVals fn ac vals
  ofwfn  : ofWᵗ fn ≤ Ω
  ofwfn  = ≤ᵇ⇒≤ _ _ (T-to fΩ)
  run-ok = scanVals-ofW Ω fn ac vals ofwfn (≤ᵇ⇒≤ _ _ (T-to nb)) vΩ

stepFrame-take-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now (take-f nid) κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
stepFrame-take-width {s = s} Ω g id now nid κ vals fin sched st inv vΩ
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (switch-st _ _)   = inv , refl , refl
... | just (exhaust-st _ _)  = inv , refl , refl
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false =
  install-width Ω sched st nid
    (take-st (proj₁ (proj₂ (takeVals k vals)))) refl inv ,
  takeVals-Ω Ω k vals vΩ , refl
...   | true =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (setNode-ofW Ω nid (take-st zero) (EvalSt.nodes st) refl
              (proj₁ (proj₂ P)))
  (∧-intro (cutThrough-regsΩ Ω nid del wm dy (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P))))) ,
  takeVals-Ω Ω k vals vΩ ,
  cutThrough-closesΩ Ω nid del wm dy (EvalSt.registry st)
  where
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough nid del wm dy (EvalSt.registry st))
  P    = WOK-parts Ω sched st inv

-- the connect's two landings, factored out of sharedConnect's `if`
connectWrap-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (i : Fin n) (id : Id) (c : Bool)
  (burst : Stream Γ (lookup Γ i)) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → burstΩ? Ω burst ≡ true →
  let r : Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
      r = if c
          then (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                  at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched
               , record st { registry = dropSource (toℕ i) (EvalSt.registry st)
                           ; completedSources = toℕ i ∷ EvalSt.completedSources st }
          else (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched , st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)
connectWrap-width Ω i id true  burst sched st inv bΩ =
  latch-width Ω (toℕ i) sched st inv ,
  ∧-intro refl (sharedPlumb-Ω Ω burst bΩ)
connectWrap-width Ω i id false burst sched st inv bΩ =
  inv , ∧-intro refl (sharedPlumb-Ω Ω burst bΩ)

-- of-list literals: eval never widens, so each element rides the
-- list's own ofWᵗˢ max
ofVals-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (ts : List (Tm Γ [] [] [] u)) →
  ofWᵗˢ ts ≤ Ω →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) (map (λ tm → evalTm tm) ts) ≡ true
ofVals-Ω Ω []       h = refl
ofVals-Ω Ω (y ∷ ys) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (ofW-evalWith Ω y []ᵃ tt
            (≤-trans (m≤m⊔n (ofWᵗ y) (ofWᵗˢ ys)) h))))
          (ofVals-Ω Ω ys (≤-trans (m≤n⊔m (ofWᵗ y) (ofWᵗˢ ys)) h))


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

postulate
  -- THE WET CONTRACT, stated at the mutual block's entry point:
  -- from a store-bounded machine, subscribing any store-sized value
  -- with fuel for its demand neither dries nor escapes the next
  -- instant's budget.  This is the strengthened induction of the
  -- proof design above, to be ground clause by clause through the
  -- block (subscribeE / stepFrame / pushBurst / subscribeAll /
  -- subscribeInner / subscribeSharedSlot), each decrement edge
  -- consuming one hasAtLeast-peel against dBound-μ / dBound-hop /
  -- dBound-connect.  The internal walk threads a stronger invariant
  -- (mid-walk states at the SAME instant); only this outer face is
  -- fixed here.
  subscribeE-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    let V = sizeBudgetAt e (Sched.slots sched) id in
    stBounded? V sched st ≡ true →
    sizeᵉ b ≤ V →
    g hasAtLeast
      suc (dBound V (hopR V)
                  (unconn (Sched.slots sched) (EvalSt.connectedShares st))
                  (hopDᵉ V b) (syncSizeᵉ b)) →
    let r = subscribeE g b κ id now sched st
    in (hasDry (proj₁ r) ≡ false)
       × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                     (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

  -- the chain fold at instant id, from a latched state within id's
  -- size budget, stays wet and lands within suc id's.
  --
  -- FOLD-THREADING (2026-07-20, the ledger finding): this core does
  -- NOT decompose into an end-to-end per-chainStep contract at the
  -- two fixed bounds.  After chain k lands, chain k+1 starts from a
  -- mid-cascade state that only suc id's budget bounds — and a
  -- fixed-bound "start @ suc id → land @ suc id" step statement is
  -- FALSE over its full quantification (a store value near the
  -- bound grows past it under one more applyFn), so stating it
  -- would be a forbidden false postulate.  The honest decomposition
  -- threads per-cascade growth through the fold, and its exponent
  -- budget is |chains| · demand — but |chains| (the registry's
  -- cardinality at instant id) has NO syntactic bound: it needs its
  -- own cumulative invariant (registrations accrue ≤ demand per
  -- instant) formulated and proven BEFORE a chainStep-wet can be
  -- shaped truthfully.  Until then this stays one postulate (the
  -- FoldOut precedent: no half-stated leaf).  What IS proven of the
  -- ledger: connect-anchor (share crossings re-anchor against the
  -- global syntactic multiset {program} ⊎ {slots}), and the
  -- per-cascade delivered/cancelled ledger caps deliveries at one
  -- per registration (Verify-Well-Formed's cascadeGo-skip ring).
  cascadeGo-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
    let r = cascadeGo a id chains sched st
    in (hasDry (proj₁ r) ≡ false)
       × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                     (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- the burst cores — PROVEN: the contract instantiated at the root.
-- The root subscribes the program itself from the initial machine:
-- init-bounded seeds the store invariant, the program is its own
-- size witness, and the seeded budget covers the demand by
-- dBound-bound + seed-covers (U ≤ sz through the slot content,
-- r ≤ R through measureE-rank).
------------------------------------------------------------------

burst-wet : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in (hasDry (proj₁ r) ≡ false)
     × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) 1)
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
burst-wet e ins =
  subscribeE-wet (budgetAt e ins 0) e root 0 0
                 (sched-init e ins) (st-init e)
                 (init-bounded e ins 0) size≤V fuel-ok
  where
  sz = sizeᵉ e + slotsSize ins
  V  = sizeBudgetAt e ins 0

  size≤V : sizeᵉ e ≤ V
  size≤V = size≤budget e ins 0

  U≤sz : unconn ins [] ≤ sz
  U≤sz = ≤-trans (unconn≤slots ins []) (m≤n+m (slotsSize ins) (sizeᵉ e))

  fuel-ok : budgetAt e ins 0 hasAtLeast
    suc (dBound V (hopR V) (unconn ins [])
                (hopDᵉ V e) (syncSizeᵉ e))
  fuel-ok = hasAtLeast-mono
    (≤-trans (s≤s (dBound-bound (≤-trans (syncSize≤sizeᵉ e) size≤V)
                                (hopD-cap V e (2≤sizeBudget e ins 0) size≤V)))
             (seed-covers sz (unconn ins []) U≤sz))
    (budget-hasAtLeast sz 0)

burst-dry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false
burst-dry e ins = proj₁ (burst-wet e ins)

burst-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) 1)
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-bounded e ins = proj₂ (burst-wet e ins)


------------------------------------------------------------------
-- one cascade — PROVEN: latch, the postulated fold core, finish
------------------------------------------------------------------

cascade-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
  let r = cascade a id sched st
  in (hasDry (proj₁ r) ≡ false)
     × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascade-dry {e = e} a id sched st bnd
  with cascadeGo-wet a id (chainsOf a st) sched (cascadeLatch a st)
         (latch-bounded (sizeBudgetAt e (Sched.slots sched) id) sched a st bnd)
... | dry , bnd' = dry , final
  where
  sched' = proj₁ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  st'    = proj₂ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  final : stBounded?
            (sizeBudgetAt e (Sched.slots (proj₁ (cascadeFinish a sched' st')))
                      (suc id))
            (proj₁ (cascadeFinish a sched' st'))
            (proj₂ (cascadeFinish a sched' st')) ≡ true
  final = subst
            (λ sl → stBounded? (sizeBudgetAt e sl (suc id))
                      (proj₁ (cascadeFinish a sched' st'))
                      (proj₂ (cascadeFinish a sched' st')) ≡ true)
            (sym (finish-slots a sched' st'))
            (finish-bounded (sizeBudgetAt e (Sched.slots sched') (suc id))
                            a sched' st' bnd')

------------------------------------------------------------------
-- the fuel loop composes cascades — PROVEN
------------------------------------------------------------------

drain-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry zero    id sched st bnd = refl
drain-dry (suc k) id sched st bnd with sched-next sched in eq
... | inj₁ _            = refl
drain-dry {e = e} (suc k) id sched st bnd | inj₂ (a , sched′) =
  let bnd′ : stBounded? (sizeBudgetAt e (Sched.slots sched′) id) sched′ st ≡ true
      bnd′ = subst
               (λ sl → stBounded? (sizeBudgetAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-bounded (sizeBudgetAt e (Sched.slots sched) id) sched st eq bnd)
      (dry₁ , bnd″) = cascade-dry a id sched′ st bnd′
  in hasDry-append (proj₁ (cascade a id sched′ st)) _
       dry₁
       (drain-dry k (suc id)
         (proj₁ (proj₂ (cascade a id sched′ st)))
         (proj₂ (proj₂ (cascade a id sched′ st)))
         bnd″)

------------------------------------------------------------------
-- the theorem: same statement as Verify-Well-Formed's postulate;
-- the splice (coordinated, later) replaces that postulate with this
------------------------------------------------------------------

budget-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
budget-sufficient fuel e ins =
  hasDry-append
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)))
    _
    (burst-dry e ins)
    (drain-dry fuel 1
      (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e))))
      (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e))))
      (burst-bounded e ins))
