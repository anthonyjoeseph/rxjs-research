-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY.
--
-- The half that steps the evaluator.  The Keeps ring (slot/share
-- monotonicity), the size-elim laws, the ledger arithmetic, the wet
-- lemmas for every evaluator entry point, subscribeE-walkS and
-- subscribeAll-wet, cascadeGo-walk, the width family, and the burst
-- cores (burst-wet/burst-dry/burst-bounded) and pop ring (pop-INV/
-- pop-head-bounded) that compose them.
--
-- `cascade-dry`, `drain-dry`, and `budget-sufficient` — the theorem
-- Verify-Well-Formed consumes — MOVED to `.Caps-Bridge`
-- (PROOF-STATE.md § "RULING: Caps-Bridge was built UPSIDE DOWN"): a
-- module above `.Wet` can consume `.Caps-Bridge`'s `cascade-wet-via-caps`
-- in place of the postulated `cascadeGo-wet` below; `.Wet` itself
-- cannot, since `.Caps-Bridge` imports `.Wet`.
--
-- This module is a LAYER OVER .Caps as of 2026-08-01: the wet cores'
-- reset caps and per-instant store bound are read off `capsAt`, the caps
-- recurrence, which is the only entry-computable reach bound in the
-- machine (round3b-ledger-reset-absurd rules out the ledger).  The
-- recurrence sits in its own prerequisite module rather than in
-- .Caps-Face — the Keeps-Ring precedent, taken the same day the layering
-- landed — so this module and the caps FACE are still siblings and a
-- caps-face grind does not re-check twenty minutes of wet clauses.
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
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡;
                                       +-cancelʳ-≤)
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
sweepLive-fnCap Ψ = sweepLive-all (fnCapLive Ψ)

-- the cut is a filter on the registry: the count only drops (that half
-- is cutThrough-len, in .Measures, since the caps face needs it too),
-- the survivors keep their frame bounds, and every close it mints is
-- value-free
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
dropSource-regs : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ reg ≡ true → regsB? B Ψ (dropSource src reg) ≡ true
dropSource-regs B Ψ = dropSource-all (λ en → pathB? B Ψ (proj₂ (proj₂ (proj₂ en))))

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
sweepLive-ofW Ω = sweepLive-all (ofWLive Ω)

-- dropping a source only shrinks the registry
dropSource-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (dropSource src reg) ≡ true
dropSource-regsΩ Ω = dropSource-all (λ en → pathΩ? Ω (proj₂ (proj₂ (proj₂ en))))

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

------------------------------------------------------------------
-- THE WET CORES — THE ASSEMBLY, TRANSCRIBED (2026-08-01), AND THE
-- THREE STATEMENT-LEVEL GAPS IT FOUND.  Outside-in, at this joint:
-- the companion tree the wet induction would walk was written down
-- BEFORE any clause was ground — and writing it down is what found
-- the gaps.  They are cured below, in one pass, against the caps
-- recurrence.
--
-- THE COMPANION TREE.  The wet induction needs no new tree.  It is
-- subscribeE-walkS's, clause for clause, with the wet payload (hasDry
-- ≡ false, and one hasAtLeast peel per gas edge) carried alongside the
-- store payload each member already threads.  Transcribed, with what
-- each member threads and which of the three gas edges it owns:
--
--   subscribeE-walkS      THE WALK, thirteen clauses.  `input` →
--     -input-wet; of/empty are one-shots (one eval edge, no gas);
--     map/take/scan are install-INV + the IH + pushBurst-wet (no gas);
--     the four *Alls → subscribeAll-wet; μᵉ g0 is the dry stub and
--     μᵉ (gs fuel) is THE μ EDGE (re-enter on unfoldμ at the ×2 copy
--     edge); varᵉ is absurd; deferᵉ → -defer-wet (mint source +
--     ordinal, addLive-INV).
--   subscribeAll-wet      mint node, install-INV, the IH under
--     `thru-outer op nid ↠ κ`, pushBurst-wet.  Spends no gas itself —
--     a *All's gas is spent one level down, at subscribeInner.
--   subscribeE-input-wet  five shapes over ONE slot, cut out of the
--     telescope by slotSize-at / slotFnCap-at.  cold-without-tail is a
--     ledger-free one-shot; cold-with-tail and hot are register-INV
--     (the ×2 length edge); shared → sharedSlot-wet.
--   sharedSlot-wet        completed → nothing; already connected → one
--     register-INV; otherwise → sharedConnect-wet.
--   sharedConnect-wet     THE CONNECT EDGE.  g0 is the dry stub; gs
--     peels one, latches connectedShares (connectShare-INV), registers
--     (register-INV), walks the stored def at `share-sink i`, and
--     lands through connectWrap-wet.
--   pushBurst-wet         splitBurst, stepFrame-wet, retag.
--   stepFrame-wet         map-f is the ledger rule itself (×3^(suc Ψ));
--     scan-f → -scan-wet; take-f → -take-wet; from-inner →
--     -fromInner-wet (absorb, or innerFinish-wet); thru-outer →
--     -thruOuter-wet.
--   thruWalk-wet          one thruConsume-wet per emitted outer value.
--   thruConsume-wet       the per-op node bookkeeping around the hop:
--     merge's bump, concat's queue and drain, switch's kill, exhaust's
--     flag.
--   subscribeInner-wet    THE HOP EDGE.  g0 is the dry stub; gs peels
--     one and re-enters the walk on the inner observable VALUE under
--     `from-inner op allNid inst ↠ κ`.
--   concatDrain-wet / innerFinish-wet / thruWrap-wet   structural.
--
--   and one level out, the delivery clique: cascadeGo-walk →
--   chainStep-wet → foldPath-wet → (at share-sink) dispatchShare-wet →
--   shareGo-wet → foldPath-wet.  It spends NO gas at all: a burst
--   leaves subscribeE through a FRAME and is never re-entered through
--   a path (the Keeps memo's clique boundary, same reason).
--
-- So the structural half transcribes exactly.  What did NOT transcribe
-- was the two cores' own faces — and that is what is repaired here.
--
-- ================================================================
-- THE RESTATEMENT (2026-08-01): THE WET STACK ANCHORS AT capsAt
-- ================================================================
--
-- This is the convergence the caps campaign existed for.  Round 3b's
-- Ŝ / R̂ / F were always waiting for an ENTRY-COMPUTABLE reach bound —
-- round3b-ledger-reset-absurd is the proof that nothing ledger-shaped
-- can serve — and capsAt is it: a recurrence on the program syntax and
-- the slot telescope alone, with no reference to E, to capᴱ, or to any
-- quantity the walk's own work moves.
--
-- GAP 1 — THE INVARIANT WAS THE WRONG ONE, IN AND OUT.  Both cores
-- carried `stBounded? B`: two conjuncts, live pendings and node
-- stores.  Every member of the companion tree above, and the only face
-- anywhere that produces `hasDry ≡ false` (subscribeE-walk), carries
-- `INV? Ψ B` — SIX conjuncts: stBounded?, fnCapBounded?, registry
-- cardinality, regsB?, slotsSize, slotsFnCap.  Neither direction
-- closed: `stBounded? V` says nothing about a stored value's fn
-- weight, the registry's cardinality, or a registered chain's frames
-- (IN), and a stBounded?-only conclusion cannot re-seed an INV?-shaped
-- hypothesis (OUT), so drain-dry → cascade-dry → cascadeGo-wet did not
-- compose.  And subscribeE-wet's κ was completely unconstrained, where
-- every member needs `pathB? B Ψ κ` (register-INV consumes it to keep
-- regsB?).
--
--   CURED.  Both cores now carry INV? Ψ B in AND out, at
--   (Ψ, B) = (ΨAt e sl, sizeCapAt e sl ·) — a fn-cap seed that never
--   grows and a size cap that rides the caps recurrence per instant —
--   plus `pathB? B Ψ κ` on subscribeE-wet's continuation.
--   cascade-dry's conclusion is now LITERALLY drain-dry's next-instant
--   hypothesis, with no residue.
--
-- GAP 2 — THE DEMAND'S RESET CAPS WERE THE LEDGER.  subscribeE-wet
-- measured its demand at V = sizeBudgetAt e slots id — the instant's
-- STORE bound — in every cap role at once: dBound's V, R as hopR V,
-- hopD's index, and (through `sizeᵉ b ≤ V`) the entry size.  But the
-- hop child is drawn from a MID-walk burst, and mid-walk values
-- outgrow V (a scan frame folds every value with no fuel peel), so the
-- only stated bound on such a value was the walk's own ledger ceiling
-- capᴱ W E′ — whose permitted range grows with the walk's work, which
-- grows with the demand, which is ≥ suc V by sucV≤d.  That is exactly
-- the shape round3b-ledger-reset-absurd refutes.
--
--   CURED.  Ŝ is read off capsAt — `Caps.cSize (capsAt e sl ·)`,
--   abbreviated sizeCapAt below — and R̂ = hopR Ŝ, F = Ŝ.  The wiring
--   is reach-resets (.Caps-Face, PROVEN): from `sizeᵉ o ≤ C` at
--   `2 ≤ C` it yields BOTH `syncSizeᵉ o ≤ C` and `hopDᵉ C o ≤ hopR C`,
--   which is why F needs no separate justification — it IS Ŝ, and why
--   hop rank is not a Caps field (it is derivable from cSize; carrying
--   it would be a synonym).  The mid-walk growth objection dissolves
--   the same way it did on the caps side: the walk carries its own
--   progress index (the walk face's G, the caps face's j) while the
--   ANCHORS stay entry-fixed.
--
--   WHICH LEVEL, AND WHY — the hop edge picks it.  The entry
--   hypotheses (INV?, pathB?, sizeᵉ b) read level `id`; the reset caps
--   Ŝ / R̂ / F and the landing invariant read level `suc id`.
--   hop-step-needs (below, machine-checked) says an r-drop of one buys
--   EXACTLY `s + suc Ŝ` of syncSize headroom, so a hop child `o` owes
--
--       suc (syncSizeᵉ o) ≤ syncSizeᵉ b + suc Ŝ
--
--   and not one unit more.  `o` is drawn from a MID-instant burst, and
--   a mid-instant value is bounded by the instant's ENDPOINT caps
--   level, not by its entry level — caps-tick is exactly that shape
--   (capsAt id in, capsAt (suc id) out, every mid-cascade state at an
--   intermediate `frameStep j` between them).  So Ŝ := sizeCapAt e sl
--   (suc id), whence `sizeᵉ o ≤ Ŝ` gives `syncSizeᵉ o ≤ Ŝ` by
--   reach-resets and `suc Ŝ ≤ syncSizeᵉ b + suc Ŝ` closes the owed
--   inequality with the whole of syncSizeᵉ b as slack.  Reading Ŝ at
--   level `id` would NOT close it: the mid-instant inner is not
--   bounded there.  No pre-blowup base and no partial frameStep level
--   is needed — the two endpoints of one instant suffice.
--
-- GAP 3 — THE ARRIVAL WAS UNBOUNDED, AND THE POP RING COULD NOT BOUND
-- IT.  cascadeGo-wet quantified over `chains` and over `a` with no
-- bound on either.  cascadeGo-walk needs `all (λ rc → pathB? …)
-- chains` (which is INV?'s regsB? conjunct, so GAP 1 supplies it
-- through chainsOf-B below) and, separately, `valB? … (arrTy a)
-- (arrVal a)`.  Nothing bounded a POPPED arrival's value:
-- schedHeadOf-bounded and pop-bounded both keep the TAIL and drop the
-- popped element on the floor.
--
--   CURED at the statement.  cascadeGo-wet gains the arrival
--   hypothesis, and the companion that supplies it is NAMED:
--   pop-head-bounded, the head-KEEPING schedGo inversion (the popped
--   arrival was a pending of a live source, so stBounded?'s pendings
--   half bounds it).  Stated here, consumed by drain-dry; NOT proven
--   this leg.
--
-- WHAT THE WALK FACE'S PARAMETERS BECOME.  subscribeE-walk
-- (.Measures) is NOT restated: its eight caps are universally
-- quantified ℕs, so the capsAt instantiation is a choice of arguments
-- and nothing about the face resists it.  The map, recorded here so it
-- is not re-derived:
--
--   Ŝ  ←  Caps.cSize (capsAt e sl (suc id))            (= sizeCapAt)
--   R̂  ←  hopR Ŝ         — DERIVED from cSize by reach-resets, not a
--                          Caps field; hop rank is derivable, which is
--                          why there is no cHop
--   F  ←  Ŝ              — same object; reach-resets' second component
--                          is stated at index C = Ŝ
--   ℓ  ←  Caps.cSize (capsAt e sl (suc id))  — the caps face already
--                          reads path LENGTH at cSize: pathSz?'s
--                          `suc (pathLen p) ≤ᵇ B` conjunct is the ℓ
--                          ledger at ℓ := cSize (its own memo says so)
--   Ω  ←  NOT a Caps field.  ΩAt e sl.  cWid is the FRAME width
--                          (widLive / widNode); Ω is the per-NODE ofW
--                          width (widthOK?), and om-is-not-a-frame-
--                          budget is the counterexample to conflating
--                          them.  Ω needs no recurrence: the one width
--                          mint in the machine is ofᵉ and ΩAt already
--                          dominates it, which is why the width walk
--                          is proven with no running position.
--   Ψ  ←  NOT a Caps field.  ΨAt e sl.  Ψ never grows (caseW is
--                          substitution-invariant), so no recurrence.
--   W, E ← the walk's OWN ledger.  The joint this map left open —
--                            capᴱ W (E · 3^(suc Ψ · walkCap Ω ℓ G))
--                              ≤ sizeCapAt e sl (suc id)
--                          — was recorded here as "arithmetic, not
--                          statement-level".  IT IS NEITHER: it is
--                          REFUTED, by walk-hyps-absurd at V := Ŝ.  See
--                          GAP 4 below (wet-ceiling-absurd).  So the
--                          "two parallel accounting mechanisms for one
--                          growth is a smell" note at the end of
--                          .Caps-Face is not a smell but an
--                          obstruction, and collapsing E into j is not
--                          a follow-up but the only surviving route.
--
-- cascadeGo-level and cascadeGo-deliveries (.Caps-Face) are both
-- THEOREMS as of 2026-08-03, and design-owned.  Nothing restated here
-- consumes either of them.
------------------------------------------------------------------

-- THE EXACT SLACK AT A ONE-STEP HOP, so GAP 2's level choice is a
-- number and not a worry.  At a FIXED anchor Ŝ an r-drop of one buys
-- exactly `s + Ŝ` of syncSize headroom — necessary and sufficient,
-- both directions.  The whole content is *-suc: dBound's second
-- summand grows by exactly suc Ŝ per unit of r.
dBound-suc-r : ∀ (V R U r s : ℕ) →
  dBound V R U (suc r) s ≡ (s + suc V) + suc V * (r + suc R * U)
dBound-suc-r V R U r s =
  trans (cong (s +_) (*-suc (suc V) (r + suc R * U)))
        (sym (+-assoc s (suc V) (suc V * (r + suc R * U))))

hop-step-gives : ∀ (V R U r s s′ : ℕ) → suc s′ ≤ s + suc V →
  suc (dBound V R U r s′) ≤ dBound V R U (suc r) s
hop-step-gives V R U r s s′ h =
  ≤-trans (+-monoˡ-≤ (suc V * (r + suc R * U)) h)
          (≤-reflexive (sym (dBound-suc-r V R U r s)))

hop-step-needs : ∀ (V R U r s s′ : ℕ) →
  suc (dBound V R U r s′) ≤ dBound V R U (suc r) s → suc s′ ≤ s + suc V
hop-step-needs V R U r s s′ h =
  +-cancelʳ-≤ (suc V * (r + suc R * U)) (suc s′) (s + suc V)
    (≤-trans h (≤-reflexive (dBound-suc-r V R U r s)))

------------------------------------------------------------------
-- THE μ EDGE's r SIDE — hopD IS EQUAL ACROSS AN UNFOLD.  Asserted by
-- Rx.Hop-Depth's μ clause ("an unfold cannot change hopD") and by the
-- hop-descent memo in .Measures ("the UNFOLD step … is an equality
-- too"); proven here, because dBound-μ holds `r` FIXED and until this
-- is a theorem `hopDᵉ Ŝ (unfoldμ body)` and `hopDᵉ Ŝ (μᵉ body)` are
-- simply two different expressions and the edge cannot be taken.
--
-- The content is one line of typing: elimGExp rewrites Δᵍ-VARIABLE
-- positions only, and Δᵍ moves into Δ at deferᵉ and nowhere else, so
-- every plug lands under a deferᵉ — which hopD reads as 0.  The
-- coefficient mirror comes first, since hopD's mapᵉ and scanᵉ clauses
-- read pm for their slopes.
--
-- It lives HERE rather than in .Measures for sweepLive-fnCap's
-- reason: the wet face is its only consumer, and the size face has no
-- use for it.
------------------------------------------------------------------

mutual
  pm-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V k : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    pmᵉ V k (elimGExp x cl b) ≡ pmᵉ V k b
  pm-elimGᵉ V k x cl (input i)       = refl
  pm-elimGᵉ V k x cl (ofᵉ ts)        = pm-elimGᵗˢ V k x cl ts
  pm-elimGᵉ V k x cl emptyᵉ          = refl
  pm-elimGᵉ V k x cl (mapᵉ f b)      =
    cong₂ _+_ (pm-elimGᵗ V (suc k) x cl f)
              (cong₂ _*_ (cong (_⊔ 1) (pm-elimGᵗ V 0 x cl f))
                         (pm-elimGᵉ V k x cl b))
  pm-elimGᵉ V k x cl (takeᵉ c b)     = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (scanᵉ f z b)   =
    cong₂ _*_ (cong (λ y → (2 + y) ^ V) (pm-elimGᵗ V 0 x cl f))
              (cong₂ _+_ (cong₂ _+_ (pm-elimGᵗ V (suc k) x cl f)
                                    (pm-elimGᵗ V k x cl z))
                         (pm-elimGᵉ V k x cl b))
  pm-elimGᵉ V k x cl (mergeAllᵉ b)   = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (concatAllᵉ b)  = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (switchAllᵉ b)  = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (exhaustAllᵉ b) = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (μᵉ b)          = pm-elimGᵉ V k (there x) cl b
  pm-elimGᵉ V k x cl (varᵉ y)        = refl
  pm-elimGᵉ V k x cl (deferᵉ b)      = refl

  pm-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V k : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    pmᵗ V k (elimGTm x cl f) ≡ pmᵗ V k f
  pm-elimGᵗ V k x cl (varᵗ y)      = refl
  pm-elimGᵗ V k x cl unit̂          = refl
  pm-elimGᵗ V k x cl (bool̂ b)      = refl
  pm-elimGᵗ V k x cl (nat̂ m)       = refl
  pm-elimGᵗ V k x cl (pairᵗ a b)   =
    cong₂ _⊔_ (pm-elimGᵗ V k x cl a) (pm-elimGᵗ V k x cl b)
  pm-elimGᵗ V k x cl (fstᵗ p)      = pm-elimGᵗ V k x cl p
  pm-elimGᵗ V k x cl (sndᵗ p)      = pm-elimGᵗ V k x cl p
  pm-elimGᵗ V k x cl (inlᵗ a)      = pm-elimGᵗ V k x cl a
  pm-elimGᵗ V k x cl (inrᵗ a)      = pm-elimGᵗ V k x cl a
  pm-elimGᵗ V k x cl (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (pm-elimGᵗ V (suc k) x cl l)
                         (pm-elimGᵗ V (suc k) x cl r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_ (pm-elimGᵗ V 0 x cl l)
                                               (pm-elimGᵗ V 0 x cl r))
                                    refl)
                         (pm-elimGᵗ V k x cl s))
  pm-elimGᵗ V k x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (pm-elimGᵗ V k x cl a) (pm-elimGᵗ V k x cl b)
  pm-elimGᵗ V k x cl (primᵗ op a)  = refl
  pm-elimGᵗ V k x cl (strmᵗ b)     = pm-elimGᵉ V k x cl b

  pm-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V k : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    pmᵗˢ V k (elimGTms x cl ts) ≡ pmᵗˢ V k ts
  pm-elimGᵗˢ V k x cl []       = refl
  pm-elimGᵗˢ V k x cl (y ∷ ys) =
    cong₂ _⊔_ (pm-elimGᵗ V k x cl y) (pm-elimGᵗˢ V k x cl ys)

mutual
  hopD-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    hopDᵉ V (elimGExp x cl b) ≡ hopDᵉ V b
  hopD-elimGᵉ V x cl (input i)       = refl
  hopD-elimGᵉ V x cl (ofᵉ ts)        = hopD-elimGᵗˢ V x cl ts
  hopD-elimGᵉ V x cl emptyᵉ          = refl
  hopD-elimGᵉ V x cl (mapᵉ f b)      =
    cong₂ _+_ (hopD-elimGᵗ V x cl f)
              (cong₂ _*_ (cong (_⊔ 1) (pm-elimGᵗ V 0 x cl f))
                         (hopD-elimGᵉ V x cl b))
  hopD-elimGᵉ V x cl (takeᵉ c b)     = hopD-elimGᵉ V x cl b
  hopD-elimGᵉ V x cl (scanᵉ f z b)   =
    cong₂ _*_ (cong (λ y → (2 + y) ^ V) (pm-elimGᵗ V 0 x cl f))
              (cong₂ _+_ (cong₂ _+_ (hopD-elimGᵗ V x cl f)
                                    (hopD-elimGᵗ V x cl z))
                         (hopD-elimGᵉ V x cl b))
  hopD-elimGᵉ V x cl (mergeAllᵉ b)   = cong suc (hopD-elimGᵉ V x cl b)
  hopD-elimGᵉ V x cl (concatAllᵉ b)  = cong suc (hopD-elimGᵉ V x cl b)
  hopD-elimGᵉ V x cl (switchAllᵉ b)  = cong suc (hopD-elimGᵉ V x cl b)
  hopD-elimGᵉ V x cl (exhaustAllᵉ b) = cong suc (hopD-elimGᵉ V x cl b)
  hopD-elimGᵉ V x cl (μᵉ b)          = hopD-elimGᵉ V (there x) cl b
  hopD-elimGᵉ V x cl (varᵉ y)        = refl
  hopD-elimGᵉ V x cl (deferᵉ b)      = refl

  hopD-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    hopDᵗ V (elimGTm x cl f) ≡ hopDᵗ V f
  hopD-elimGᵗ V x cl (varᵗ y)      = refl
  hopD-elimGᵗ V x cl unit̂          = refl
  hopD-elimGᵗ V x cl (bool̂ b)      = refl
  hopD-elimGᵗ V x cl (nat̂ m)       = refl
  hopD-elimGᵗ V x cl (pairᵗ a b)   =
    cong₂ _⊔_ (hopD-elimGᵗ V x cl a) (hopD-elimGᵗ V x cl b)
  hopD-elimGᵗ V x cl (fstᵗ p)      = hopD-elimGᵗ V x cl p
  hopD-elimGᵗ V x cl (sndᵗ p)      = hopD-elimGᵗ V x cl p
  hopD-elimGᵗ V x cl (inlᵗ a)      = hopD-elimGᵗ V x cl a
  hopD-elimGᵗ V x cl (inrᵗ a)      = hopD-elimGᵗ V x cl a
  hopD-elimGᵗ V x cl (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (hopD-elimGᵗ V x cl l) (hopD-elimGᵗ V x cl r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_ (pm-elimGᵗ V 0 x cl l)
                                               (pm-elimGᵗ V 0 x cl r))
                                    refl)
                         (hopD-elimGᵗ V x cl s))
  hopD-elimGᵗ V x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (hopD-elimGᵗ V x cl a) (hopD-elimGᵗ V x cl b)
  hopD-elimGᵗ V x cl (primᵗ op a)  = refl
  hopD-elimGᵗ V x cl (strmᵗ b)     = hopD-elimGᵉ V x cl b

  hopD-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    hopDᵗˢ V (elimGTms x cl ts) ≡ hopDᵗˢ V ts
  hopD-elimGᵗˢ V x cl []       = refl
  hopD-elimGᵗˢ V x cl (y ∷ ys) =
    cong₂ _⊔_ (hopD-elimGᵗ V x cl y) (hopD-elimGᵗˢ V x cl ys)

-- the instance the μ clause takes
hopD-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (V : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
  hopDᵉ V (unfoldμ body) ≡ hopDᵉ V (μᵉ body)
hopD-unfoldμ V body = hopD-elimGᵉ V (here refl) (μᵉ body) body

------------------------------------------------------------------
-- THE THREE GAS EDGES, PACKAGED.  Each one is "the machine's own step
-- fact, the dBound descent lemma, and the reset supply" fused into the
-- single inequality a clause proof applies with nothing left to
-- compute.  Everything else in the wet induction is structural
-- threading; this is the termination content.
------------------------------------------------------------------

-- (1) THE μ EDGE.  r is fixed (hopD-unfoldμ), s strictly drops
-- (unfoldμ-shrinks), U is untouched — an unfold moves no state at all.
mu-edge : ∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
  suc (dBound Ŝ R̂ U (hopDᵉ Ŝ (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
    ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ (μᵉ body)) (syncSizeᵉ (μᵉ body))
mu-edge Ŝ R̂ U body
  rewrite hopD-unfoldμ Ŝ body =
  dBound-μ {Ŝ} {R̂} {U} {hopDᵉ Ŝ body}
           {syncSizeᵉ (unfoldμ body)} {syncSizeᵉ (μᵉ body)}
           (unfoldμ-shrinks body)

-- (2) THE HOP EDGE, at the entry-fixed anchor.  The r-drop is the
-- emitted-value invariant (burstHopD?) against the *All frame's
-- DEFINITIONAL `suc`; the s reset is `reach-reset`'s first component —
-- CALLED now, not inlined (.Measures, where the pair is stated once), so
-- this module still reads nothing from the caps FACE.  hop-step-needs
-- says the slack is exact: an r-drop of one buys `s + suc Ŝ`, and
-- `suc Ŝ` alone already covers it.
hop-edge : ∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) → 2 ≤ Ŝ →
  (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ (obs u) o < r →
  suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ (obs u) o) (syncSizeᵉ o))
    ≤ dBound Ŝ (hopR Ŝ) U r s
hop-edge Ŝ U r s 2≤Ŝ o szo r′<r =
  dBound-hop {Ŝ} {hopR Ŝ} {U} {hopDᵉ Ŝ o} {r} {syncSizeᵉ o} {s}
             r′<r (proj₁ (reach-reset Ŝ 2≤Ŝ o szo))

-- (3) THE CONNECT EDGE.  U strictly drops (unconn-insert, behind the
-- machine's own `memberSource … ≡ false` guard), and BOTH of the
-- child's measures reset at the anchor, because a shared slot's def is
-- cap-sized entry syntax — `reach-reset`'s two components, CALLED now
-- rather than inlined.  Its tuple is (sync , hop) and dBound-connect
-- wants hop first, hence the swap.
connect-edge : ∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
  (sl : Slots Γ) (cs : List Source) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
  suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs)) (hopDᵉ Ŝ d) (syncSizeᵉ d))
    ≤ dBound Ŝ (hopR Ŝ) (unconn sl cs) r s
connect-edge Ŝ r s 2≤Ŝ sl cs i {d} eqi fresh szd =
  dBound-connect {Ŝ} {hopR Ŝ} {unconn sl (toℕ i ∷ cs)} {unconn sl cs}
                 {hopDᵉ Ŝ d} {r} {syncSizeᵉ d} {s}
                 (unconn-insert sl cs i eqi fresh)
                 (proj₂ pair)
                 (proj₁ pair)
  where
  pair = reach-reset Ŝ 2≤Ŝ d szd

-- AND U NEVER RISES BETWEEN THE EDGES.  Every structural companion of
-- the subscribe clique threads the demand's U component past arbitrary
-- machine work, and this is the whole of what that costs: the Keeps
-- ring says the slots are literally unchanged and connectedShares only
-- grows, and unconn is antitone in the latter.  Instantiate at any
-- member of the clique's *-keeps family.
unconn-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (sched′ : Sched Γ) (st′ : EvalSt e) →
  Keeps sched st sched′ st′ →
  unconn (Sched.slots sched′) (EvalSt.connectedShares st′)
    ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st)
unconn-keeps sched st sched′ st′ K =
  subst (λ sl → unconn sl (EvalSt.connectedShares st′)
                  ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st))
        (sym (KeepsC.slotsEq K))
        (unconn-antitone (Sched.slots sched)
                         (EvalSt.connectedShares st)
                         (EvalSt.connectedShares st′)
                         (KeepsC.connMono K))

------------------------------------------------------------------
-- THE ONE ANCHOR.  Every cap the wet stack measures with is this
-- number at one of two instant levels: the store invariant's B, the
-- demand's s′ reset Ŝ, the r reset's base (R̂ = hopR Ŝ) and the hop
-- index F.  Entry-computable by construction — capsAt is a recurrence
-- on the syntax and the slot telescope alone.
------------------------------------------------------------------

sizeCapAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Id → ℕ
sizeCapAt e sl id = Caps.cSize (capsAt e sl id)

2≤sizeCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → 2 ≤ sizeCapAt e sl id
2≤sizeCapAt = 2≤capsAt-size

-- one instant is one frameBlowup, and a blowup never shrinks the size
-- cap: the two levels a core reads are ordered
sizeCapAt-mono : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → sizeCapAt e sl id ≤ sizeCapAt e sl (suc id)
sizeCapAt-mono e sl id =
  cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s z≤n) (2≤sizeCapAt e sl id))

-- the program's own size sits under the cap at every instant (capsAt's
-- base is `2 + sizeᵉ e + slotsSize sl`, one frameBlowup down)
size≤sizeCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → sizeᵉ e ≤ sizeCapAt e sl id
size≤sizeCapAt e sl id =
  ≤-trans (≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
          (capsAt-base-size e sl id)

------------------------------------------------------------------
-- GAP 4 (2026-08-01, found grinding the gas edges): THE LEDGER CANNOT
-- DELIVER subscribeE-wet's LANDING LEVEL, AND THAT IS NOT AN OPEN
-- ARITHMETIC DEBT — IT IS REFUTED.
--
-- The restatement's parameter map (above) leaves exactly one thing to
-- the follow-up, and calls it "arithmetic, not statement-level":
--
--     capᴱ W (E · 3^(suc Ψ · walkCap Ω ℓ G)) ≤ sizeCapAt e sl (suc id)
--
-- That inequality is the ONLY route from subscribeE-walk's conclusion
-- (INV? at the ledger position capᴱ W E′, with E′ bounded ABOVE by the
-- receipt and by nothing else) to subscribeE-wet's conclusion (INV? at
-- the caps level).  INV? weakens upward in B, so the core's landing
-- needs its ledger ceiling UNDER Ŝ, and the receipt's ceiling is the
-- only upper bound on E′ the face provides.
--
-- IT IS THE SAME THREE-EDGE LOOP the round-1 vacuity died of, and it
-- needs no new witness: walk-hyps-absurd (.Measures) IS the refutation,
-- at V := Ŝ, R := hopR Ŝ, d := G.  The edges, spelled out:
--
--   · suc Ŝ ≤ G          the demand is measured AT Ŝ, and one
--                        unconnected share or one remaining hop puts
--                        it past its own anchor  (sucV≤d)
--   · G ≤ X              walkCap's index dominates the demand it is
--                        indexed by                (d≤walkArg)
--   · X < capᴱ W X ≤ Ŝ   the ceiling, and capᴱ is exponential (n<2^n)
--
-- so Ŝ < Ŝ.  The side condition `1 ≤ r + suc R̂ · U` is not a
-- restriction worth caring about: it fails only when the call has NO
-- gas edge left at all (no unconnected share, no hop), i.e. exactly
-- when the wet contract has no content.
--
-- WHAT THIS DOES NOT SAY.  It does not refute subscribeE-wet, and it
-- does not refute subscribeE-walk.  It refutes the COMPOSITION: the
-- ledger receipt cannot be the supplier of the caps-level landing, for
-- any Ψ, W, Ω, ℓ, E, G.  Collapsing E into j is therefore not an
-- optimisation — it is the only surviving route, and the two
-- accounting mechanisms cannot be joined at the receipt.
--
-- WHAT IS LEFT, then, and it is where the next design ruling belongs.
-- The other candidate supplier is the caps face, which already lands a
-- whole cascade from capsAt id to capsAt (suc id) (caps-tick, ground).
-- Two things stand between it and this core:
--
--   (a) NO SUBSCRIBE-LEVEL CHARGE.  subscribeE-caps reports at
--       `frameStep (j + j′) c` with j′ existentially produced and
--       UNBOUNDED.  cascadeGo-level budgets a cascade's j (`lvls`, one
--       dLvl per delivery); nothing budgets a bare subscribe's, so
--       burst-wet's own landing (root subscribe, capsAt 0 → capsAt 1)
--       has no supplier either.  The missing companion is a
--       subscribeE-level analogue of `fLvl`, and it is NAMED here
--       rather than assumed.  It is the SAME hole the two *All frame
--       faces wait on (.Caps-Face, conjunct (a) there), seen from the
--       wet side — one companion would close both.
--       AND THE COMPANION IS NOT A CLOSED FORM (measured,
--       agda/probe/Sub-Charge-Probe.agda): a subscribe installs frames
--       and a frame subscribes one inner per payload, so the subscribe
--       charge and the frame charge are MUTUALLY RECURSIVE and no
--       function of (S, W, J) closes the loop — the same failure
--       `dCapᶜ` took on the delivery side, and the same repair, a
--       recursion on a nesting budget.  The gas escape that would have
--       killed any level reading (a synchronous μ fixpoint, re-entering
--       subscribeE once per unfolding against a `budgetAt` three tower
--       stories above `capsAt`) is closed BY TYPING: `deferᵉ` is the
--       sole gate moving Δᵍ into scope, so a μ's self-reference costs a
--       TICK.  The hierarchy is probed and gated; what it waits on is
--       the nesting budget's instantiation, which is a ruling.
--   (b) capsOK? IS NOT INV?.  They share stBounded? and nothing else:
--       INV? adds fnCapBounded?, regsB?, slotsFnCap and reads registry
--       cardinality at cSize where capsOK? reads it at cReg.  Four
--       conjuncts of the wet predicate have no caps-side counterpart.
--
-- Both are statement-level and both are face-level, so per the
-- outside-in rule the clause grind stops here rather than guessing at
-- them: the gas edges themselves are ground above and wait on this.
------------------------------------------------------------------

wet-ceiling-absurd : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) (Ψ W Ω ℓ E G U r s : ℕ) → 3 ≤ E →
  1 ≤ r + suc (hopR (sizeCapAt e sl (suc id))) * U →
  dBound (sizeCapAt e sl (suc id)) (hopR (sizeCapAt e sl (suc id))) U r s ≤ G →
  capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)) ≤ sizeCapAt e sl (suc id) →
  ⊥
wet-ceiling-absurd e sl id Ψ W Ω ℓ E G U r s 3≤E 1≤ dem ceil =
  walk-hyps-absurd Ψ W Ω (sizeCapAt e sl (suc id)) ℓ
                   (hopR (sizeCapAt e sl (suc id))) U r s G E 3≤E 1≤ dem ceil

------------------------------------------------------------------
-- THE CASCADE BOOKENDS ON THE INV? FACE — the caps face's
-- cascadeLatch-caps / cascadeFinish-caps, at the wet predicate.  The
-- latch touches only per-cascade scratch no conjunct reads; the finish
-- is the same drop-and-sweep shareFinish-INV already runs.
------------------------------------------------------------------

cascadeLatch-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched (cascadeLatch a st) ≡ true
cascadeLatch-INV Ψ B a sched st inv with Arrival.isLast a
... | true  = inv
... | false = inv

cascadeFinish-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (proj₁ (cascadeFinish a sched st))
           (proj₂ (cascadeFinish a sched st)) ≡ true
cascadeFinish-INV Ψ B a sched st inv with Arrival.isLast a
... | false = inv
... | true  =
  ∧-intro (∧-intro (sweepLive-bounded B kept (Sched.live sched)
                     (stB-live B sched st sb))
                   (stB-nodes B sched st sb))
  (∧-intro (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched)
                      (fcB-live Ψ sched st fc))
                    (fcB-nodes Ψ sched st fc))
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ
              (≤-trans (dropSource-len (arrSource a) (EvalSt.registry st))
                       (≤ᵇ⇒≤ _ _ (T-to rl)))))
  (∧-intro (dropSource-regs B Ψ (arrSource a) (EvalSt.registry st) rb)
  (∧-intro ss sf))))
  where
  kept = dropSource (arrSource a) (EvalSt.registry st)
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  ss   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P))))
  sf   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P))))

-- the chain snapshot inherits its bounds from the registry — GAP 3's
-- FIRST half, discharged from INV?'s regsB? conjunct rather than
-- postulated (the caps face's chainsGo-caps, at pathB?)
chainsGo-B : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ rs ≡ true →
  all (λ rc → pathB? B Ψ (proj₂ rc)) (chainsGo a rs) ≡ true
chainsGo-B B Ψ a [] h = refl
chainsGo-B B Ψ a ((rid , s , (u , p)) ∷ r) h
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = chainsGo-B B Ψ a r (proj₂ (∧-true _ _ h))
... | true  | no  _    = chainsGo-B B Ψ a r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (chainsGo-B B Ψ a r (proj₂ (∧-true _ _ h)))

chainsOf-B : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B Ψ : ℕ)
  (a : Arrival Γ) (st : EvalSt e) →
  regsB? B Ψ (EvalSt.registry st) ≡ true →
  all (λ rc → pathB? B Ψ (proj₂ rc)) (chainsOf a st) ≡ true
chainsOf-B B Ψ a st = chainsGo-B B Ψ a (EvalSt.registry st)

postulate
  -- THE WET CONTRACT, restated 2026-08-01 against the caps recurrence
  -- (GAP 1 + GAP 2 above).  From a machine within instant `id`'s caps
  -- level, subscribing a cap-sized value under a cap-bounded
  -- continuation with fuel for its demand — the demand measured at the
  -- ENTRY-COMPUTABLE reset caps Ŝ = sizeCapAt e sl (suc id),
  -- R̂ = hopR Ŝ, F = Ŝ, never at the ledger — neither dries nor escapes
  -- instant (suc id)'s caps level.
  --
  -- To be ground clause by clause through the mutual block
  -- (subscribeE / stepFrame / pushBurst / subscribeAll /
  -- subscribeInner / subscribeSharedSlot), each decrement edge
  -- consuming one hasAtLeast peel against dBound-μ / dBound-hop /
  -- dBound-connect, with hop-step-gives supplying the hop edge's
  -- syncSize headroom from reach-resets at Ŝ.  The internal walk
  -- threads the stronger mid-instant invariant (subscribeE-walk, at
  -- the parameter map recorded above); only this outer face is fixed
  -- here.
  --
  -- ASSEMBLY (2026-08-06): narrowed over exactly the facts this
  -- postulate's own header says it is to be ground from — the three
  -- packaged gas edges, the hasAtLeast peel, hop-step-gives' syncSize
  -- headroom, and the internal walk (subscribeE-walk) the header names
  -- as threading the mid-instant invariant — plus the Keeps-Ring share
  -- boundary facts and the .Measures budget/size faces the clause grind
  -- consumes.  Every hypothesis is already proven, so this is neither
  -- stronger nor weaker than the postulate it replaces.
  subscribeE-wet-core :
    -- subscribeE-walk  (Verify-Budget-Sufficient/Measures.agda:6125)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
      (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
      3 ≤ E →
      INV? Ψ (capᴱ W E) sched st ≡ true →
      sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
      pathB? (capᴱ W E) Ψ κ ≡ true →
      widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
      dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
             (hopDᵉ F b) (syncSizeᵉ b) ≤ G →
      g hasAtLeast suc G →
      pathLen κ + G ≤ ℓ →
      regsLen? ℓ (EvalSt.registry st) ≡ true →
      let r = subscribeE g b κ id now sched st
      in Σ ℕ λ E′ → (E ≤ E′)
         × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
         × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
         × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
         × (burstHopD? F (hopDᵉ F b) (proj₁ r) ≡ true)
         × (hasDry (proj₁ r) ≡ false)
         × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
              ≤ mintCount sched st + walkCap Ω ℓ G)
         × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
         × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
     ) →
    -- mu-edge  (Verify-Budget-Sufficient/Wet.agda:4036)
    (∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
      suc (dBound Ŝ R̂ U (hopDᵉ Ŝ (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
        ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ (μᵉ body)) (syncSizeᵉ (μᵉ body))
     ) →
    -- hop-edge  (Verify-Budget-Sufficient/Wet.agda:4052)
    (∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) → 2 ≤ Ŝ →
      (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ (obs u) o < r →
      suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ (obs u) o) (syncSizeᵉ o))
        ≤ dBound Ŝ (hopR Ŝ) U r s
     ) →
    -- connect-edge  (Verify-Budget-Sufficient/Wet.agda:4066)
    (∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
      (sl : Slots Γ) (cs : List Source) (i : Fin n)
      {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
      memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
      suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs)) (hopDᵉ Ŝ d) (syncSizeᵉ d))
        ≤ dBound Ŝ (hopR Ŝ) (unconn sl cs) r s
     ) →
    -- hop-step-gives  (Verify-Budget-Sufficient/Wet.agda:3877)
    (∀ (V R U r s s′ : ℕ) → suc s′ ≤ s + suc V →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s
     ) →
    -- hop-step-needs  (Verify-Budget-Sufficient/Wet.agda:3883)
    (∀ (V R U r s s′ : ℕ) →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s → suc s′ ≤ s + suc V
     ) →
    -- unconn-keeps  (Verify-Budget-Sufficient/Wet.agda:4087)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (sched : Sched Γ) (st : EvalSt e) (sched′ : Sched Γ) (st′ : EvalSt e) →
      Keeps sched st sched′ st′ →
      unconn (Sched.slots sched′) (EvalSt.connectedShares st′)
        ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- sharedConnect-unconn  (Verify-Budget-Sufficient/Keeps-Ring.agda:1016)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
      (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)} →
      Sched.slots sched i ≡ shared dd →
      memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
      unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
             (EvalSt.connectedShares
               (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
      < unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- obs-slot-shared  (Verify-Budget-Sufficient/Keeps-Ring.agda:464)
    (∀ {n} {Γ : Ctx n} {u} (s : Slot Γ (obs u)) →
      Σ (Closed Γ (obs u)) λ d → s ≡ shared d
     ) →
    -- share-live-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda:473)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ []) at id from s as subscribe) ∷ [])) ≡ []
     ) →
    -- share-spent-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda:478)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ close s exhausted ∷ complete ∷ []) at id from s as subscribe) ∷ []))
        ≡ []
     ) →
    -- hasAtLeast-pad  (Verify-Budget-Sufficient/Measures.agda:222)
    (∀ (m : ℕ) (g : Gas) {n} → n ≤ m → gasPad m g hasAtLeast n
     ) →
    -- hasAtLeast-peel  (Verify-Budget-Sufficient/Measures.agda:268)
    (∀ {g : Gas} {m : ℕ} → g hasAtLeast suc m →
      Σ Gas (λ g′ → (g ≡ gs g′) × (g′ hasAtLeast m))
     ) →
    -- seed-covers  (Verify-Budget-Sufficient/Measures.agda:3113)
    (∀ (sz U : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * 1) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * 1 * 1) + towerℕ ((7 + sz) * 2)
     ) →
    -- budget-covers  (Verify-Budget-Sufficient/Measures.agda:3400)
    (∀ (sz U id : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * suc (suc id)) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))
     ) →
    -- oneShot-tail-dry  (Verify-Budget-Sufficient/Measures.agda:3367)
    (∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (src : Source) →
      any dryEvent (map value vals ++ close src exhausted ∷ complete ∷ []) ≡ false
     ) →
    -- connect-anchor  (Verify-Budget-Sufficient/Measures.agda:1847)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
      let V = sizeBudgetAt e sl id in
      (hopDᵉ V d ≤ hopR V) × (syncSizeᵉ d ≤ V)
     ) →
    -- hopD-map-emit  (Verify-Budget-Sufficient/Measures.agda:2780)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ)
      (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) (v : Val Γ s) →
      (f₀ : Fn Γ [] [] [] s u) → hopDᵗ V f₀ ≤ hopDᵗ V f → pmᵗ V 0 f₀ ≤ pmᵗ V 0 f →
      hopDᵛ V s v ≤ hopDᵉ V b →
      hopDᵛ V u (applyFn f₀ v) ≤ hopDᵉ V (mapᵉ f b)
     ) →
    -- applyFn-size  (Verify-Budget-Sufficient/Measures.agda:3647)
    (∀ {n} {Γ : Ctx n} {s t} (V : ℕ)
      (fn : Fn Γ [] [] [] s t) (v : Val Γ s) → sizeᵛ s v ≤ V →
      sizeᵛ t (applyFn fn v) ≤ (2 + 2 * V) ^ (3 ^ sizeᵗ fn)
     ) →
    -- unconn-cons-≤  (Verify-Budget-Sufficient/Measures.agda:1217)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
      (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
     ) →
    -- shellSize-unfoldμ  (Verify-Budget-Sufficient/Measures.agda:1100)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      shellSizeᵉ (unfoldμ body) ≡ shellSizeᵉ body
     ) →
    -- inner-unfoldμ  (Verify-Budget-Sufficient/Measures.agda:1104)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      innerᵉ (unfoldμ body) ≡ innerᵉ body
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        Ŝ  = sizeCapAt e sl (suc id)
    in INV? Ψ B sched st ≡ true →
       pathB? B Ψ κ ≡ true →
       sizeᵉ b ≤ B →
       fnCapᵉ b ≤ Ψ →
       g hasAtLeast
         suc (dBound Ŝ (hopR Ŝ)
                     (unconn sl (EvalSt.connectedShares st))
                     (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
       let r = subscribeE g b κ id now sched st
       in (hasDry (proj₁ r) ≡ false)
          × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                  (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

  -- the chain fold at instant id, restated on the same two faces
  -- (GAP 1) and with GAP 3's arrival hypothesis.  Its decomposition
  -- (cascadeGo-walk, PROVEN) consumes exactly these three: INV? in and
  -- out, a bound on the arrival's value, and a bound on every snapshot
  -- chain — the last of which chainsOf-B above now supplies from
  -- INV?'s own regsB? conjunct.
  --
  -- FOLD-THREADING (2026-07-20, the ledger finding) — still standing,
  -- and orthogonal to all three gaps: this core does NOT decompose
  -- into an end-to-end per-chainStep contract at two fixed bounds.
  -- After chain k lands, chain k+1 starts from a mid-cascade state,
  -- and a fixed-bound "start @ level L → land @ level L" step
  -- statement is FALSE over its full quantification (a store value
  -- near the bound grows past it under one more applyFn) — that is
  -- caps-frame-boundary-absurd, uniform in the cap.  The honest
  -- decomposition threads per-cascade growth through the fold, which
  -- is what the caps face's `j` index does and what an eventual
  -- chainStep-wet must mirror.  Until the two accounting mechanisms
  -- are collapsed this stays one postulate (the FoldOut precedent: no
  -- half-stated leaf).
  --
  -- ASSEMBLY (2026-08-06): narrowed over the two state-bound facts a
  -- cascade's own bookkeeping steps need — the latch touches only the
  -- per-cascade ledger fields and the finish only drops registry
  -- entries, so neither disturbs stBounded?.
  cascadeGo-wet-core :
    -- latch-bounded  (Verify-Budget-Sufficient/Measures.agda:408)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (B : ℕ) (sched : Sched Γ) (a : Arrival Γ) (st : EvalSt e) →
      stBounded? B sched st ≡ true →
      stBounded? B sched (cascadeLatch a st) ≡ true
     ) →
    -- finish-bounded  (Verify-Budget-Sufficient/Measures.agda:475)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (B : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
      stBounded? B sched st ≡ true →
      stBounded? B (proj₁ (cascadeFinish a sched st))
                   (proj₂ (cascadeFinish a sched st)) ≡ true
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
    in INV? Ψ B sched st ≡ true →
       valB? B Ψ (arrTy a) (arrVal a) ≡ true →
       all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true →
       let r = cascadeGo a id chains sched st
       in (hasDry (proj₁ r) ≡ false)
          × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                  (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

-- the two wet faces, assembled over their cores
subscribeE-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
     let r = subscribeE g b κ id now sched st
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
subscribeE-wet =
  subscribeE-wet-core subscribeE-walk
    mu-edge hop-edge connect-edge hop-step-gives hop-step-needs unconn-keeps
    sharedConnect-unconn obs-slot-shared
    -- these two must be instantiated EXPLICITLY: `splitBurst` computes on
    -- the literal event list, so the reduced statement no longer mentions
    -- Γ or u and Agda cannot solve those implicits from the expected type.
    (λ {n} {Γ} {u} {A} → share-live-novals {n} {Γ} {u} {A})
    (λ {n} {Γ} {u} {A} → share-spent-novals {n} {Γ} {u} {A})
    hasAtLeast-pad hasAtLeast-peel seed-covers budget-covers oneShot-tail-dry
    connect-anchor hopD-map-emit applyFn-size unconn-cons-≤
    shellSize-unfoldμ inner-unfoldμ

cascadeGo-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
  in INV? Ψ B sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true →
     let r = cascadeGo a id chains sched st
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-wet = cascadeGo-wet-core latch-bounded finish-bounded

------------------------------------------------------------------
-- THE POP RING ON THE SIX-CONJUNCT FACE — PROVEN.  .Measures has the
-- stBounded? projections (schedHeadOf-bounded / schedGo-bounded /
-- pop-bounded); what the wet predicate needs on top is the SAME
-- induction at fnCapLive, and the head-KEEPING variant, which nothing
-- had: every existing inversion keeps the TAIL and drops the popped
-- element on the floor, so none of them bounds the arrival drain-dry
-- hands to cascade-dry.
--
-- The fnCap mirrors sit here rather than in .Measures for the reason
-- sweepLive-fnCap does: they exist for the wet face only, and the size
-- face has no use for them.
------------------------------------------------------------------

schedHeadOf-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  fnCapLive Ψ l ≡ true → fnCapLive Ψ l′ ≡ true
schedHeadOf-fnCap Ψ l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (fnCapLive Ψ) ls ≡ true → all (fnCapLive Ψ) ls′ ≡ true
schedGo-fnCap Ψ (l ∷ ls) eq bnd
  with ∧-true (fnCapLive Ψ l) (all (fnCapLive Ψ) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-fnCap Ψ (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-fnCap Ψ ls eqR bls)
schedGo-fnCap Ψ (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-fnCap Ψ l eqH bl) bls
schedGo-fnCap Ψ (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-fnCap Ψ l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-fnCap Ψ ls eqR bls)

pop-fnCap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  fnCapBounded? Ψ sched st ≡ true → fnCapBounded? Ψ sched′ st ≡ true
pop-fnCap Ψ sched st eq bnd
  with ∧-true (all (fnCapLive Ψ) (Sched.live sched)) _ bnd
... | bls , bns with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      ∧-intro (schedGo-fnCap Ψ (Sched.live sched) eqL bls) bns

-- the TAIL half, whole: the two store faces by their own inversions,
-- the two registry conjuncts untouched (the pop writes only `live`),
-- and the two slot conjuncts transported along pop-slots
pop-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched′ st ≡ true
pop-INV Ψ B sched st eq inv with INV-parts Ψ B sched st inv
... | sb , fc , rl , rb , ss , sf =
  ∧-intro (pop-bounded B sched st eq sb)
  (∧-intro (pop-fnCap Ψ sched st eq fc)
  (∧-intro rl
  (∧-intro rb
  (∧-intro (subst (λ sl → (slotsSize sl ≤ᵇ B) ≡ true)
                  (sym (pop-slots sched eq)) ss)
           (subst (λ sl → (slotsFnCap sl ≤ᵇ Ψ) ≡ true)
                  (sym (pop-slots sched eq)) sf)))))

-- GAP 3's NAMED COMPANION, PROVEN.  The popped arrival IS the head of
-- some live source's pending list, so stBounded?'s pendings half and
-- fnCapBounded?'s live half bound it between them — one induction over
-- schedGo carrying BOTH faces at once, since valB? is their conjunction
-- and a second pass would repeat the same case tree
schedHeadOf-head : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  boundedLive B l ≡ true → fnCapLive Ψ l ≡ true →
  valB? B Ψ (arrTy a) (arrVal a) ≡ true
schedHeadOf-head B Ψ l eq bs bf with LiveSource.pending l | eq | bs | bf
... | (t , v) ∷ ps | refl | bs′ | bf′ =
  ∧-intro (proj₁ (∧-true (sizeᵛ (LiveSource.elemTy l) v ≤ᵇ B) _ bs′))
          (proj₁ (∧-true (fnCapᵛ (LiveSource.elemTy l) v ≤ᵇ Ψ) _ bf′))

schedGo-head : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (boundedLive B) ls ≡ true → all (fnCapLive Ψ) ls ≡ true →
  valB? B Ψ (arrTy a) (arrVal a) ≡ true
schedGo-head B Ψ (l ∷ ls) eq bs bf
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) bs
     | ∧-true (fnCapLive Ψ l) (all (fnCapLive Ψ) ls) bf
... | bl , bls | fl , fls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-head B Ψ (l ∷ ls) refl bs bf
  | bl , bls | fl , fls | inj₁ _ | inj₂ (a′ , ls″) =
  schedGo-head B Ψ ls eqR bls fls
schedGo-head B Ψ (l ∷ ls) refl bs bf
  | bl , bls | fl , fls | inj₂ (a″ , l′) | inj₁ _ =
  schedHeadOf-head B Ψ l eqH bl fl
schedGo-head B Ψ (l ∷ ls) eq bs bf
  | bl , bls | fl , fls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = schedHeadOf-head B Ψ l eqH bl fl
... | false | refl = schedGo-head B Ψ ls eqR bls fls

pop-head-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? Ψ B sched st ≡ true →
  valB? B Ψ (arrTy a) (arrVal a) ≡ true
pop-head-bounded Ψ B sched st eq inv with INV-parts Ψ B sched st inv
... | sb , fc , _ with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      schedGo-head B Ψ (Sched.live sched) eqL
        (stB-live B sched st sb) (fcB-live Ψ sched st fc)

------------------------------------------------------------------
-- THE SEED ON THE SIX-CONJUNCT FACE AT THE CAPS LEVEL — PROVEN.
-- the stBounded? projection used to live here as `init-bounded`, read
-- against sizeBudgetAt; it was DELETED 2026-08-09 with the rest of #7's
-- superseded scaffold (git is the archive) because
-- capsAt-base-size relocates the same mkHot argument to
-- `Caps.cSize (capsAt …)`, the registry conjuncts are refl at st-init
-- (the registry is []), and the two slot conjuncts come from
-- capsAt-base-size and from ΨAt's own definition (`fnCapᵉ e + slotsFnCap`
-- dominates its second summand).
------------------------------------------------------------------

-- the fnCap face of one hot slot's initial pendings, off resolve-measure
-- at fnCapᵛ.  No `n≤1+n` here: inputFnCap has no `suc` to pay for,
-- because a script's own syntax carries no fn weight of its own
mkHot-fnCap : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (Ψ : ℕ) (i : Fin n) →
  slotFnCap (ins i) ≤ Ψ → all (fnCapLive Ψ) (mkHot ins i) ≡ true
mkHot-fnCap {Γ = Γ} ins Ψ i h with ins i | h
... | scripted (hot async) | h′ =
      ∧-intro (resolve-measure (fnCapᵛ (lookup Γ i)) Ψ 0 async h′) refl
... | scripted (cold _ _)  | _ = refl
... | shared _             | _ = refl

init-INV : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (id : Id) →
  INV? (ΨAt e ins) (sizeCapAt e ins id)
       (sched-init e ins) (st-init e) ≡ true
init-INV {n = n} e ins id =
  ∧-intro (∧-intro (all-concat-tab (boundedLive B) (mkHot ins) perSlotSz) refl)
  (∧-intro (∧-intro (all-concat-tab (fnCapLive Ψ) (mkHot ins) perSlotFc) refl)
  (∧-intro refl
  (∧-intro refl
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ slotsOK))
           (T⇒≡true _ (≤⇒≤ᵇ (m≤n+m (slotsFnCap ins) (fnCapᵉ e))))))))
  where
  B = sizeCapAt e ins id
  Ψ = ΨAt e ins
  slotsOK : slotsSize ins ≤ B
  slotsOK = ≤-trans (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
                    (capsAt-base-size e ins id)
  perSlotSz : ∀ i → all (boundedLive B) (mkHot ins i) ≡ true
  perSlotSz i = mkHot-bounded ins B i
                  (≤-trans (fᵢ≤sum-tab (λ j → slotSize (ins j)) i) slotsOK)
  perSlotFc : ∀ i → all (fnCapLive Ψ) (mkHot ins i) ≡ true
  perSlotFc i = mkHot-fnCap ins Ψ i
                  (≤-trans (fᵢ≤sum-tab (λ j → slotFnCap (ins j)) i)
                           (m≤n+m (slotsFnCap ins) (fnCapᵉ e)))

------------------------------------------------------------------
-- THE ROOT'S FUEL, at the moved anchor — PROVEN, and it is now an
-- IDENTITY rather than a height comparison.  `capsAt-tower` (.Caps)
-- lands `sizeCapAt e ins 1` under `towerℕ (capsH e ins 1)`; `prod≤3pow`
-- costs exactly THREE more stories (the (1+V)(1+R)(1+U) product with
-- R = hopR V); and `budgetAt`'s gas tower is DEFINED at height
-- `3 + capsHt sz 1` — the same recurrence, plus those same three.  That
-- is the point of a recurrence-defined budget: domination is by
-- construction, and the only arithmetic left is the ≤ that says the pad
-- summand does not get in the way.
------------------------------------------------------------------

-- ABSTRACT, and deliberately: this is the ONE member of the burst
-- chain that went from postulate to definition, and an unfoldable
-- body here is a body Verify-Well-Formed's `with` on
-- budget-sufficient can be asked to reduce.  Nothing needs to see
-- through it — every consumer wants the hasAtLeast, never its proof.
abstract
  caps-fuel-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    budgetAt e ins 0 hasAtLeast
      suc (dBound (sizeCapAt e ins 1) (hopR (sizeCapAt e ins 1))
                  (unconn ins []) (hopDᵉ (sizeCapAt e ins 1) e)
                  (syncSizeᵉ e))
  caps-fuel-root e ins =
    hasAtLeast-mono demand (budget-hasAtLeast sz (capsBase e ins) 0)
    where
    sz : ℕ
    sz = sizeᵉ e + slotsSize ins
    V  : ℕ
    V  = sizeCapAt e ins 1
    U  : ℕ
    U  = unconn ins []
    6≤V : 6 ≤ V
    6≤V = 6≤capsAt-size e ins 0
    sz≤V : sizeᵉ e ≤ V
    sz≤V = size≤sizeCapAt e ins 1
    U≤V : U ≤ V
    U≤V = ≤-trans (unconn≤slots ins [])
                  (≤-trans (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
                           (capsAt-base-size e ins 1))
    s≤V : syncSizeᵉ e ≤ V
    s≤V = ≤-trans (syncSize≤sizeᵉ e) sz≤V
    r≤R : hopDᵉ V e ≤ hopR V
    r≤R = hopD-cap V e (≤-trans (≤ᵇ⇒≤ 2 6 _) 6≤V) sz≤V
    demand : suc (dBound V (hopR V) U (hopDᵉ V e) (syncSizeᵉ e))
               ≤ 2 ^ (sz * 1 * 1) + towerℕ (3 + capsHgo (capsBase e ins) 1)
    demand =
      ≤-trans (s≤s (dBound-bound s≤V r≤R))
      (≤-trans (prod≤3pow V U 6≤V U≤V)
      (≤-trans (tower-3 (capsH e ins 1) V (proj₁ (capsAt-tower e ins 1)))
               (m≤n+m (towerℕ (3 + capsHgo (capsBase e ins) 1)) (2 ^ (sz * 1 * 1)))))

------------------------------------------------------------------
-- the burst cores — the contract instantiated at the root.  The root
-- subscribes the program itself from the initial machine: init-INV
-- seeds the six-conjunct invariant at the caps level, root is a
-- bounded continuation for free, the program is its own size witness
-- through capsAt's base, and caps-fuel-root covers the demand.
------------------------------------------------------------------

burst-wet : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in (hasDry (proj₁ r) ≡ false)
     × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
             (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) 1)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
burst-wet e ins =
  subscribeE-wet (budgetAt e ins 0) e root 0 0
                 (sched-init e ins) (st-init e)
                 (init-INV e ins 0) refl
                 (size≤sizeCapAt e ins 0)
                 (m≤m+n (fnCapᵉ e) (slotsFnCap ins))
                 (caps-fuel-root e ins)

burst-dry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false
burst-dry e ins = proj₁ (burst-wet e ins)

burst-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
          (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) 1)
          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-bounded e ins = proj₂ (burst-wet e ins)

-- `cascade-dry`, `drain-dry`, `budget-sufficient` MOVED to
-- `.Caps-Bridge` (PROOF-STATE.md § "RULING: Caps-Bridge was built
-- UPSIDE DOWN") — caps-threaded there, consuming `cascade-wet-via-caps`
-- in place of `cascadeGo-wet` below.  `burst-wet`/`burst-dry`/
-- `burst-bounded`/`pop-INV`/`pop-head-bounded` stay here: `.Caps-Bridge`
-- consumes all five unchanged as the INV?-only half of its own burst
-- and pop.
