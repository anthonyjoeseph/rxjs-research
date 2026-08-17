-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation, in three layers.
--   1. Inv (CONCRETE below) relates evaluator state to automaton
--      state between cascades.
--   2. Two frame relations — BurstInv (mid-subscribe-frame) and Mid
--      (mid-cascade, indexed by the chains still to fold) — both
--      CONCRETE records now, with entry/step/exit lemmas.  Proven:
--      burst-init, burst-final.  Postulated (all believed true and
--      properly hypothesised — no known-false placeholders): the
--      step lemmas
--      (subscribeE-wf, mid-step — the per-clause preservation
--      grind), mid-init, mid-skip, mid-final.  Budget sufficiency
--      is no longer assumed here: it is imported, proven, from
--      Verify-Budget-Sufficient.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed.Part12 where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (∨-assoc; ∨-comm; ∨-identityʳ)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-pred; m≤n+m; 1+n≰n; ≤⇒≤ᵇ; ≤ᵇ⇒≤; +-suc; +-comm; +-assoc; +-identityʳ; +-cancelʳ-≡; m+n∸n≡m)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Relation.Nullary using (Dec; yes; no)

-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.  MOVED 2026-08-05 from .Wet (the 2026-08-05 upside-down ruling) — `budget-sufficient`'s TYPE did
-- not change, only which module proves it, so nothing else here needed
-- to move with it.
open import Verify-Budget-Sufficient.Caps-Bridge using (budget-sufficient)
open import Rx.Prim      using (Fuel; Gas; g0; gs; Tick; Id; Source; Ordinal; InstEmit;
                                InstEvent; init; value; close; handoff; complete;
                                EmitKind; delivery; subscribe; plumbing; CloseReason; exhausted;
                                dried;
                                cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty; _≟ᵗ_; Val; Fn; obs; applyFn; mapᵉ;
                                unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; Tm; scanᵉ; takeᵉ; evalTm;
                                input; ofᵉ; emptyᵉ; varᵉ; deferᵉ; mergeAllᵉ; concatAllᵉ;
                                switchAllᵉ; exhaustAllᵉ; μᵉ; unfoldμ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; aliveThroughᶠ;
                                takeVals; takeDispatch; cutThrough; setNode; pathHasNode; memberSource;
                                NodeId; NodeState; lookupNode; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                sched-init; st-init; sched-next; LiveSource;
                                schedGo; schedHeadOf; schedFinish; schedEarlier;
                                arrTy; arrSource; arrVal; arrTick;
                                chainsOf; chainsGo; chainStep;
                                foldPath; dispatchShare; stepFrame;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate;
                                oneShotBurst; mintSource; register; splitEvents;
                                pushBurst; scanVals; installNode; mintNode; retagEvents;
                                sameSource; dryEvent; hasDry;
                                dropSource; sweepLive; budgetAt)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; protocol-init;
                                stepProtocol; runProtocol; paidUp; settle; hasOwed;
                                payOwed; paidOff; applyEvents; removeOne;
                                cancelOwed; bumpOwed; settleInstant;
                                checkFinal; Accepted; accepted; WellFormed;
                                hasValue; valsLast?)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part11 public

dropSource-other : ∀ {n} {Γ : Ctx n} {t}
  (s s′ : Source) (reg : List (RegId × Source × Chain Γ t)) →
  (s ≡ᵇ s′) ≡ false →
  countRegs s (dropSource s′ reg) ≡ countRegs s reg
dropSource-other s s′ []                  neq = refl
dropSource-other s s′ ((rid , x , c) ∷ r) neq with s ≡ᵇ x in sx | s′ ≡ᵇ x in s′x
... | true  | true  =
      let s≡s′ = trans (≡ᵇ→≡ s x sx) (sym (≡ᵇ→≡ s′ x s′x))
          p    = trans (sym (cong (s ≡ᵇ_) s≡s′)) (≡ᵇ-refl s)
      in true≢false (trans (sym p) neq)
... | true  | false rewrite sx = cong suc (dropSource-other s s′ r neq)
... | false | true             = dropSource-other s s′ r neq
... | false | false rewrite sx = dropSource-other s s′ r neq

-- dropping preserves "every registration is share-sunk"
allShareSunk-drop : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  allShareSunk reg ≡ true → allShareSunk (dropSource s reg) ≡ true
allShareSunk-drop s []                        h = refl
allShareSunk-drop s ((rid , x , (u , p)) ∷ r) h with s ≡ᵇ x
... | true  = allShareSunk-drop s r (∧-trueʳ h)
... | false = ∧-intro (∧-trueˡ h) (allShareSunk-drop s r (∧-trueʳ h))

-- the conditional form of done-plumbed, established from the full-registry
-- form: identity when the guard is false, allShareSunk-drop when true
allShareSunk-if : ∀ {n} {Γ : Ctx n} {t}
  (b : Bool) (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  allShareSunk reg ≡ true →
  allShareSunk (if b then dropSource s reg else reg) ≡ true
allShareSunk-if false s reg h = h
allShareSunk-if true  s reg h = allShareSunk-drop s reg h

-- cascadeFinish reduced under each isLast branch (two-column trick: the
-- `with Arrival.isLast a` won't unfold under rewrite).  isLast=false
-- leaves the state; isLast=true sweeps the spent source's registry
cascadeFinish-false : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ false → cascadeFinish a sched st ≡ (sched , st)
cascadeFinish-false a sched st eq with Arrival.isLast a | eq
... | false | refl = refl

finishReg-true : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ true →
  EvalSt.registry (proj₂ (cascadeFinish a sched st))
    ≡ dropSource (arrSource a) (EvalSt.registry st)
finishReg-true a sched st eq with Arrival.isLast a | eq
... | true | refl = refl

finishSched-true : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ true →
  Sched.live (proj₁ (cascadeFinish a sched st))
    ≡ sweepLive (dropSource (arrSource a) (EvalSt.registry st)) (Sched.live sched)
finishSched-true a sched st eq with Arrival.isLast a | eq
... | true | refl = refl

-- cascadeFinish never touches the node table (only drops the spent source's
-- regs and sweeps live) — the node counters ride through unchanged
finishNodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  EvalSt.nodes (proj₂ (cascadeFinish a sched st)) ≡ EvalSt.nodes st
finishNodes a sched st with Arrival.isLast a
... | false = refl
... | true  = refl

-- leaving: all chains folded ⇒ fully paid; finish (drop the spent
-- source, sweep) lands Inv-related at suc nextId
mid-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId [] sched st S →
  Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                   (proj₂ (cascadeFinish a sched st)) S
  × (paidUp S ≡ true)
mid-final {a = a} {nextId} {sched} {st} {S} mid = inv , paidUp-S
  where
  paidUp-S : paidUp S ≡ true
  paidUp-S with Mid.ledger mid
  ... | inj₁ (_ , pd)             = pd
  ... | inj₂ (ow , cur , lk , zx) =
        paid-allzero S cur
          (allZero-clean (arrSource a) ow (Mid.owed-unique mid ow cur) zx lk)

  cpast : CurrentPast (ProtocolSt.current S) (suc nextId)
  cpast with Mid.ledger mid
  ... | inj₁ (cp , _)        = currentPast-up (ProtocolSt.current S) nextId cp
  ... | inj₂ (ow , cur , _ , _) =
        subst (λ c → CurrentPast c (suc nextId)) (sym cur) ≤-refl

  -- the arrival source's live count, read off Mid.live-source per isLast
  live-src-nl : Arrival.isLast a ≡ false →
    countIn (arrSource a) (ProtocolSt.live S)
      ≡ countRegs (arrSource a) (EvalSt.registry st)
  live-src-nl isL = trans (Mid.live-source mid) (if-false (Arrival.isLast a) isL)

  live-src-tl : Arrival.isLast a ≡ true →
    countIn (arrSource a) (ProtocolSt.live S) ≡ 0
  live-src-tl isL = trans (Mid.live-source mid) (if-true (Arrival.isLast a) isL)

  lm-false : Arrival.isLast a ≡ false → ∀ (s : Source) →
    countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
  lm-false isL s with sameSource s (arrSource a) in seq
  ... | false = Mid.live-others mid s seq
  ... | true  =
        subst (λ z → countIn z (ProtocolSt.live S)
                       ≡ countRegs z (EvalSt.registry st))
              (sym (≡ᵇ→≡ s (arrSource a) seq)) (live-src-nl isL)

  lm-true : Arrival.isLast a ≡ true → ∀ (s : Source) →
    countIn s (ProtocolSt.live S)
      ≡ countRegs s (dropSource (arrSource a) (EvalSt.registry st))
  lm-true isL s with sameSource s (arrSource a) in seq
  ... | false = trans (Mid.live-others mid s seq)
                  (sym (dropSource-other s (arrSource a) (EvalSt.registry st) seq))
  ... | true  =
        let s≡ = ≡ᵇ→≡ s (arrSource a) seq in
        trans (subst (λ z → countIn z (ProtocolSt.live S) ≡ 0) (sym s≡)
                 (live-src-tl isL))
              (sym (subst (λ z → countRegs z (dropSource (arrSource a)
                                   (EvalSt.registry st)) ≡ 0) (sym s≡)
                     (dropSource-self (arrSource a) (EvalSt.registry st))))

  inv : Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                         (proj₂ (cascadeFinish a sched st)) S
  inv = go (Arrival.isLast a) refl
    where
    go : (b : Bool) → Arrival.isLast a ≡ b →
         Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                          (proj₂ (cascadeFinish a sched st)) S
    -- isLast=false: cascadeFinish is the identity; rewrite the goal flat
    go false isL rewrite cascadeFinish-false a sched st isL = record
      { live-matches = lm-false isL
      ; reg-typed    = Mid.reg-typed mid
      ; horizon-low  = ≤-up (Mid.horizon-low mid)
      ; hot-live     = Mid.hot-live mid       -- goal flattened by the rewrite
      ; current-past = cpast
      ; done-plumbed = λ deq →
          subst (λ b → allShareSunk (if b then dropSource (arrSource a) (EvalSt.registry st)
                          else EvalSt.registry st) ≡ true)
                isL (Mid.done-plumbed mid deq)
      ; caches       =
          subst (λ b → cachesValid (EvalSt.nodes st)
                          (if b then dropSource (arrSource a) (EvalSt.registry st)
                           else EvalSt.registry st) ≡ true)
                isL
                (trans (sym (cachesValidMid-nil a (EvalSt.nodes st) st)) (Mid.caches mid))
      }
    -- isLast=true: keep cascadeFinish symbolic; convert registry and live
    -- field-by-field, reg-typed via the dropSource/sweepLive preservation
    go true isL = record
      { live-matches = λ s →
          subst (λ reg → countIn s (ProtocolSt.live S) ≡ countRegs s reg)
                (sym (finishReg-true a sched st isL)) (lm-true isL s)
      ; reg-typed    =
          subst (λ reg → regTyped? reg (Sched.live (proj₁ (cascadeFinish a sched st))) ≡ true)
                (sym (finishReg-true a sched st isL))
                (subst (λ lv → regTyped? (dropSource (arrSource a) (EvalSt.registry st)) lv ≡ true)
                       (sym (finishSched-true a sched st isL))
                       (reg-typed-finish (arrSource a) (EvalSt.registry st)
                          (Sched.live sched) (Mid.reg-typed mid)))
      ; horizon-low  = ≤-up (Mid.horizon-low mid)
      ; hot-live     = cascadeFinish-hot-live a sched st (Mid.hot-live mid)
      ; current-past = cpast
      ; done-plumbed = λ deq →
          subst (λ reg → allShareSunk reg ≡ true)
                (sym (finishReg-true a sched st isL))
                (subst (λ b → allShareSunk (if b then dropSource (arrSource a) (EvalSt.registry st)
                                else EvalSt.registry st) ≡ true)
                       isL (Mid.done-plumbed mid deq))
      ; caches       =
          subst (λ nds → cachesValid nds (EvalSt.registry (proj₂ (cascadeFinish a sched st))) ≡ true)
                (sym (finishNodes a sched st))
            (subst (λ reg → cachesValid (EvalSt.nodes st) reg ≡ true)
                   (sym (finishReg-true a sched st isL))
              (subst (λ b → cachesValid (EvalSt.nodes st)
                              (if b then dropSource (arrSource a) (EvalSt.registry st)
                               else EvalSt.registry st) ≡ true)
                     isL
                     (trans (sym (cachesValidMid-nil a (EvalSt.nodes st) st)) (Mid.caches mid))))
      }

-- the chain fold, composed (mirrors cascadeGo's own recursion —
-- structural on the snapshot, no termination debt at this level)
cascadeGo-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  Mid a nextId chains sched st S →
  Σ ProtocolSt λ S′ →
    let r = cascadeGo {e = e} a nextId chains sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Mid a nextId [] (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
cascadeGo-wf a nextId [] sched st S mid = S , refl , mid
cascadeGo-wf a nextId ((rid , p) ∷ ps) sched st S mid
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in ceq
... | true  = cascadeGo-wf a nextId ps sched st S (mid-skip mid ceq)
... | false
  with mid-step {ps = ps} mid ceq
... | S₁ , run₁ , mid₁
  with cascadeGo-wf a nextId ps
         (proj₁ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         (proj₂ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         S₁ mid₁
... | S₂ , run₂ , mid₂ =
  S₂
  , run-++-just S
      (proj₁ (chainStep nextId a p sched
               (record st { delivered = rid ∷ EvalSt.delivered st })))
      _ run₁ run₂
  , mid₂

-- the latch leaves the registry untouched (it only resets the per-cascade
-- ledger and stamps the watermark / dying set)
latch-registry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  EvalSt.registry (cascadeLatch a st) ≡ EvalSt.registry st
latch-registry a st with Arrival.isLast a
... | true  = refl
... | false = refl

-- an all-fresh snapshot (no cancellations yet) has every entry obliged
countRemaining-[] : ∀ {X : Set} (ps : List (RegId × X)) →
  countRemaining ps [] ≡ length ps
countRemaining-[] []             = refl
countRemaining-[] ((rid , _) ∷ ps) = cong suc (countRemaining-[] ps)

-- the latch leaves the node table untouched (only resets the ledger)
latch-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  EvalSt.nodes (cascadeLatch a st) ≡ EvalSt.nodes st
latch-nodes a st with Arrival.isLast a
... | true  = refl
... | false = refl

-- Bool scaffolding for the guard algebra
∨-fˡ : ∀ (b c : Bool) → (b ∨ c) ≡ false → b ≡ false
∨-fˡ false c h = refl
∨-fˡ true  c h = h
∨-fʳ : ∀ (b c : Bool) → (b ∨ c) ≡ false → c ≡ false
∨-fʳ false c h = h
∨-fʳ true  c ()
∨-zeroʳ : ∀ (b : Bool) → (b ∨ true) ≡ true
∨-zeroʳ true  = refl
∨-zeroʳ false = refl

------------------------------------------------------------------
-- pure elemℕ / nubLen / keepAbsent combinatorics — the set-partition
-- and permutation-invariance behind countLiveInners-partition
------------------------------------------------------------------

f≢t : false ≡ true → ⊥
f≢t ()

elemℕ-++ : ∀ (x : NodeId) (xs ys : List NodeId) →
  elemℕ x (xs ++ ys) ≡ (elemℕ x xs ∨ elemℕ x ys)
elemℕ-++ x []       ys = refl
elemℕ-++ x (z ∷ xs) ys =
  trans (cong ((x ≡ᵇ z) ∨_) (elemℕ-++ x xs ys))
        (sym (∨-assoc (x ≡ᵇ z) (elemℕ x xs) (elemℕ x ys)))

-- if x∉surv but y∈surv then x≠y
elem-neq : ∀ (x y : NodeId) (surv : List NodeId) →
  elemℕ x surv ≡ false → elemℕ y surv ≡ true → (x ≡ᵇ y) ≡ false
elem-neq x y surv hx hy with x ≡ᵇ y in eqxy
... | false = refl
... | true  = ⊥-elim (f≢t (trans (sym hx)
                (trans (cong (λ z → elemℕ z surv) (≡ᵇ→≡ x y eqxy)) hy)))

-- membership through keepAbsent, on the branch where x is not a survivor
elemℕ-keepAbsent-absent : ∀ (x : NodeId) (surv xs : List NodeId) →
  elemℕ x surv ≡ false → elemℕ x (keepAbsent surv xs) ≡ elemℕ x xs
elemℕ-keepAbsent-absent x surv []       hx = refl
elemℕ-keepAbsent-absent x surv (y ∷ xs) hx with elemℕ y surv in eqY
... | true  rewrite elem-neq x y surv hx eqY = elemℕ-keepAbsent-absent x surv xs hx
... | false = cong ((x ≡ᵇ y) ∨_) (elemℕ-keepAbsent-absent x surv xs hx)

-- THE PARTITION: distinct count of A++B splits into A-minus-B plus B
nubLen-partition : ∀ (A B : List NodeId) →
  nubLen (A ++ B) ≡ nubLen (keepAbsent B A) + nubLen B
nubLen-partition []       B = refl
nubLen-partition (x ∷ xs) B with elemℕ x B in eqB
... | true  rewrite elemℕ-++ x xs B | eqB | ∨-zeroʳ (elemℕ x xs) = nubLen-partition xs B
... | false rewrite elemℕ-++ x xs B | eqB | ∨-identityʳ (elemℕ x xs)
                  | elemℕ-keepAbsent-absent x B xs eqB with elemℕ x xs
...   | true  = nubLen-partition xs B
...   | false = cong suc (nubLen-partition xs B)

-- ── nubLen permutation-invariance (via same membership) ──
∨-swap : ∀ (a b c : Bool) → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
∨-swap a b c = trans (sym (∨-assoc a b c))
                     (trans (cong (_∨ c) (∨-comm a b)) (∨-assoc b a c))

≡ᵇ-sym : ∀ (a b : ℕ) → (a ≡ᵇ b) ≡ (b ≡ᵇ a)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc b) = refl
≡ᵇ-sym (suc a) zero    = refl
≡ᵇ-sym (suc a) (suc b) = ≡ᵇ-sym a b

elem-head : ∀ (y : NodeId) (ys : List NodeId) → elemℕ y (y ∷ ys) ≡ true
elem-head y ys rewrite ≡ᵇ-refl y = refl

elem-cons-neq : ∀ (z y : NodeId) (ys : List NodeId) →
  (z ≡ᵇ y) ≡ false → elemℕ z (y ∷ ys) ≡ elemℕ z ys
elem-cons-neq z y ys h rewrite h = refl

elem-cons-recur : ∀ (x : NodeId) (xs : List NodeId) → elemℕ x xs ≡ true →
  ∀ (z : NodeId) → elemℕ z (x ∷ xs) ≡ elemℕ z xs
elem-cons-recur x xs hx z with z ≡ᵇ x in ezx
... | false = refl
... | true  = sym (trans (cong (λ w → elemℕ w xs) (≡ᵇ→≡ z x ezx)) hx)

removeℕ : NodeId → List NodeId → List NodeId
removeℕ x []       = []
removeℕ x (y ∷ ys) = if x ≡ᵇ y then removeℕ x ys else y ∷ removeℕ x ys

removeℕ-absent : ∀ (x : NodeId) (ys : List NodeId) →
  elemℕ x ys ≡ false → removeℕ x ys ≡ ys
removeℕ-absent x []       h = refl
removeℕ-absent x (y ∷ ys) h with x ≡ᵇ y in exy
... | true  = ⊥-elim (f≢t (sym h))
... | false = cong (y ∷_) (removeℕ-absent x ys h)

removeℕ-other : ∀ (x z : NodeId) (ys : List NodeId) → (z ≡ᵇ x) ≡ false →
  elemℕ z (removeℕ x ys) ≡ elemℕ z ys
removeℕ-other x z []       hzx = refl
removeℕ-other x z (y ∷ ys) hzx with x ≡ᵇ y in exy
... | true  = trans (removeℕ-other x z ys hzx)
                    (sym (elem-cons-neq z y ys
                      (trans (cong (z ≡ᵇ_) (sym (≡ᵇ→≡ x y exy))) hzx)))
... | false = cong ((z ≡ᵇ y) ∨_) (removeℕ-other x z ys hzx)

elem-removeℕ-self : ∀ (x : NodeId) (ys : List NodeId) →
  elemℕ x (removeℕ x ys) ≡ false
elem-removeℕ-self x []       = refl
elem-removeℕ-self x (y ∷ ys) with x ≡ᵇ y in exy
... | true          = elem-removeℕ-self x ys
... | false rewrite exy = elem-removeℕ-self x ys

nubLen-empty : ∀ (ys : List NodeId) → (∀ z → elemℕ z ys ≡ false) → nubLen ys ≡ 0
nubLen-empty []       h = refl
nubLen-empty (y ∷ ys) h = ⊥-elim (f≢t (trans (sym (h y)) (elem-head y ys)))

nubLen-remove : ∀ (x : NodeId) (ys : List NodeId) →
  elemℕ x ys ≡ true → nubLen ys ≡ suc (nubLen (removeℕ x ys))
nubLen-remove x []       h = ⊥-elim (f≢t h)
nubLen-remove x (y ∷ ys) h with x ≡ᵇ y in exy
... | true  with elemℕ y ys in eqYY
...   | true  = nubLen-remove x ys (trans (cong (λ w → elemℕ w ys) (≡ᵇ→≡ x y exy)) eqYY)
...   | false rewrite removeℕ-absent x ys
                        (trans (cong (λ w → elemℕ w ys) (≡ᵇ→≡ x y exy)) eqYY) = refl
nubLen-remove x (y ∷ ys) h | false
  rewrite removeℕ-other x y ys (trans (≡ᵇ-sym y x) exy) with elemℕ y ys in eqYY
... | true  = nubLen-remove x ys h
... | false = cong suc (nubLen-remove x ys h)

nubLen-same-elems : ∀ (xs ys : List NodeId) →
  (∀ z → elemℕ z xs ≡ elemℕ z ys) → nubLen xs ≡ nubLen ys
nubLen-same-elems []       ys h = sym (nubLen-empty ys (λ z → sym (h z)))
nubLen-same-elems (x ∷ xs) ys h with elemℕ x xs in eqX
... | true  = nubLen-same-elems xs ys
                (λ z → trans (sym (elem-cons-recur x xs eqX z)) (h z))
... | false =
      trans (cong suc (nubLen-same-elems xs (removeℕ x ys) h''))
            (sym (nubLen-remove x ys x∈ys))
  where
  x∈ys : elemℕ x ys ≡ true
  x∈ys = trans (sym (h x)) (elem-head x xs)
  h'' : ∀ z → elemℕ z xs ≡ elemℕ z (removeℕ x ys)
  h'' z with z ≡ᵇ x in ezx
  ... | true  rewrite ≡ᵇ→≡ z x ezx = trans eqX (sym (elem-removeℕ-self x ys))
  ... | false = trans (trans (sym (elem-cons-neq z x xs ezx)) (h z))
                      (sym (removeℕ-other x z ys ezx))

-- guard monotone: dropping a source cannot create thru-outer reachability,
-- so ¬reachable is preserved (the cut case stays vacuous under dropSource)
mergeReachable-drop-false : ∀ {n} {Γ : Ctx n} {t}
  (nid : NodeId) (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  mergeReachable nid reg ≡ false → mergeReachable nid (dropSource s reg) ≡ false
mergeReachable-drop-false nid s []                    h = refl
mergeReachable-drop-false nid s ((rid , x , (u , p)) ∷ r) h with sameSource s x
... | true  = mergeReachable-drop-false nid s r (∨-fʳ (pathThruOuter nid p) (mergeReachable nid r) h)
... | false rewrite ∨-fˡ (pathThruOuter nid p) (mergeReachable nid r) h =
      mergeReachable-drop-false nid s r (∨-fʳ (pathThruOuter nid p) (mergeReachable nid r) h)

-- the pure nubLen SET-PARTITION (PROVEN, 2026-07-19), isolated from the
-- latch/guard/isLast shell.  At full ps and cancelled ≡ [] the arrSource inners
-- dropSource removes are EXACTLY those mergeAdjust adds back: countLiveInners of
-- the full registry splits into the adjustment plus countLiveInners of the
-- dropSourced registry.  Discharged (below) via nubLen-partition (nubLen(A++B)
-- ≡ nubLen(keepAbsent B A) + nubLen B, pure list algebra) + nubLen-same-elems
-- (permutation-invariance of nubLen, via removeℕ / nubLen-remove) + memб-split
-- (the source-split membership, reg-typed ruling out mistyped arrSource entries
-- exactly as count-eq does).  No postulate, no evaluator dynamics.
-- the adjustment, UNFOLDED over (registry st, cancelled ≡ []) — the form the
-- goal's `mergeAdjust … (cascadeLatch a st)` reduces to under isLast (the latch
-- keeps registry, resets cancelled); stated plainly to dodge with-abstraction
mergeAdjustSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → (a : Arrival Γ) → EvalSt e → ℕ
mergeAdjustSt nid a st =
  nubLen (keepAbsent (innerInstsR nid (dropSource (arrSource a) (EvalSt.registry st)))
                     (collectAdjInsts nid [] (chainsOf a st)))

-- the membership SOURCE-SPLIT: an inst z threads the full registry iff it
-- threads an arrSource entry (via chainsGo, type-filtered) or a non-arrSource
-- entry (dropSource).  Mirrors count-eq: the mistyped arrSource case is ruled
-- out by regTyped? + the live source (liveTypeOK?-extract / sameTy-sound).
memб-split : ∀ {n} {Γ : Ctx n} {t} (nid : NodeId) (a : Arrival Γ)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → liveHas (arrSource a) (arrTy a) live ≡ true →
  ∀ (z : NodeId) →
  elemℕ z (innerInstsR nid reg)
    ≡ (elemℕ z (collectAdjInsts nid [] (chainsGo a reg))
        ∨ elemℕ z (innerInstsR nid (dropSource (arrSource a) reg)))
memб-split nid a []                      live rt lh z = refl
memб-split nid a ((rid , s , (u , p)) ∷ r) live rt lh z
  with sameSource (arrSource a) s in sseq
... | false =
      trans (elemℕ-++ z (innerInstsP nid p) (innerInstsR nid r))
        (trans (cong (elemℕ z (innerInstsP nid p) ∨_)
                     (memб-split nid a r live (∧-trueʳ rt) lh z))
          (trans (∨-swap (elemℕ z (innerInstsP nid p))
                         (elemℕ z (collectAdjInsts nid [] (chainsGo a r)))
                         (elemℕ z (innerInstsR nid (dropSource (arrSource a) r))))
                 (cong (elemℕ z (collectAdjInsts nid [] (chainsGo a r)) ∨_)
                       (sym (elemℕ-++ z (innerInstsP nid p)
                              (innerInstsR nid (dropSource (arrSource a) r)))))))
... | true  with u ≟ᵗ arrTy a
...   | yes refl =
      trans (elemℕ-++ z (innerInstsP nid p) (innerInstsR nid r))
        (trans (cong (elemℕ z (innerInstsP nid p) ∨_)
                     (memб-split nid a r live (∧-trueʳ rt) lh z))
          (trans (sym (∨-assoc (elemℕ z (innerInstsP nid p))
                               (elemℕ z (collectAdjInsts nid [] (chainsGo a r)))
                               (elemℕ z (innerInstsR nid (dropSource (arrSource a) r)))))
                 (cong (_∨ elemℕ z (innerInstsR nid (dropSource (arrSource a) r)))
                       (sym (elemℕ-++ z (innerInstsP nid p)
                              (collectAdjInsts nid [] (chainsGo a r)))))))
...   | no ¬p = ⊥-elim (¬p (sameTy-sound u (arrTy a)
                  (liveTypeOK?-extract (arrSource a) u (arrTy a) live
                    (subst (λ w → liveTypeOK? w u live ≡ true)
                           (sym (≡ᵇ→≡ (arrSource a) s sseq)) (∧-trueˡ rt))
                    lh)))

-- countLiveInners of the full registry SPLITS into the adjustment plus
-- countLiveInners of the dropSourced registry (assembling memб-split with the
-- nubLen set-partition and permutation-invariance).  reg-typed threaded via the
-- schedule (mirrors chains-count-derived's liveHas extraction).
