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
module Verify-Well-Formed.Part13 where

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
-- clock.  MOVED 2026-08-05 from .Wet (PROOF-STATE.md § "RULING:
-- Caps-Bridge was built UPSIDE DOWN") — `budget-sufficient`'s TYPE did
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

open import Verify-Well-Formed.Part12 public

countLiveInners-partition : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (a : Arrival Γ) (sched sched″ : Sched Γ) (st : EvalSt e) →
  regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true →
  sched-next sched ≡ inj₂ (a , sched″) →
  countLiveInners nid (EvalSt.registry st)
    ≡ mergeAdjustSt nid a st
      + countLiveInners nid (dropSource (arrSource a) (EvalSt.registry st))
countLiveInners-partition nid a sched sched″ st rt eq with schedGo (Sched.live sched) in geq
... | inj₁ _ with eq
...   | ()
countLiveInners-partition nid a sched sched″ st rt eq | inj₂ (a₀ , ls) with eq
...   | refl =
      trans (nubLen-same-elems (innerInstsR nid (EvalSt.registry st))
               (collectAdjInsts nid [] (chainsOf a st)
                 ++ innerInstsR nid (dropSource (arrSource a) (EvalSt.registry st)))
               (λ z → trans (memб-split nid a (EvalSt.registry st) (Sched.live sched) rt
                               (schedGo-mem (Sched.live sched) geq) z)
                            (sym (elemℕ-++ z (collectAdjInsts nid [] (chainsOf a st))
                                   (innerInstsR nid (dropSource (arrSource a) (EvalSt.registry st)))))))
            (nubLen-partition (collectAdjInsts nid [] (chainsOf a st))
              (innerInstsR nid (dropSource (arrSource a) (EvalSt.registry st))))

-- mid-init PARTITION, PROVEN down to countLiveInners-partition: the plain
-- cachesValid (from Inv) implies the full-ps Mid shadow.  Per merge node,
-- guard-false stays vacuous (mergeReachable-drop-false) and guard-true feeds
-- the exact count k through the partition; non-merge nodes and isLast≡false
-- are the plain checker verbatim.
mid-init-caches : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched sched″ : Sched Γ) (st : EvalSt e) →
  regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true →
  sched-next sched ≡ inj₂ (a , sched″) →
  cachesValid (EvalSt.nodes st) (EvalSt.registry st) ≡ true →
  cachesValidMid a (chainsOf a st) (EvalSt.nodes (cascadeLatch a st))
                 (cascadeLatch a st) ≡ true
mid-init-caches {Γ = Γ} a sched sched″ st rt eq h rewrite latch-nodes a st = go (EvalSt.nodes st) h
  where
  nodeOK→Mid : (nid : NodeId) (s : NodeState Γ) →
    nodeCacheOK nid s (EvalSt.registry st) ≡ true →
    nodeCacheMid nid a (chainsOf a st) s (cascadeLatch a st) ≡ true
  nodeOK→Mid nid (scan-st _)       hn = refl
  nodeOK→Mid nid (take-st _)       hn = refl
  nodeOK→Mid nid (concat-st _ _ _) hn = refl
  nodeOK→Mid nid (switch-st _ _)   hn = refl
  nodeOK→Mid nid (exhaust-st _ _)  hn = refl
  nodeOK→Mid nid (merge-st k od) hn with Arrival.isLast a
  ... | false = hn
  ... | true  with mergeReachable nid (EvalSt.registry st) in eqM
  ...   | false rewrite mergeReachable-drop-false nid (arrSource a) (EvalSt.registry st) eqM = refl
  ...   | true  =
        -- `with … in eqM` reduced hn to its second disjunct here: k ≡ᵇ count
        let keq : k ≡ mergeAdjustSt nid a st
                        + countLiveInners nid (dropSource (arrSource a) (EvalSt.registry st))
            keq = trans (≡ᵇ→≡ k (countLiveInners nid (EvalSt.registry st)) hn)
                        (countLiveInners-partition nid a sched sched″ st rt eq)
            snd : (k ≡ᵇ (mergeAdjustSt nid a st
                          + countLiveInners nid (dropSource (arrSource a) (EvalSt.registry st)))) ≡ true
            snd = subst (λ z → (k ≡ᵇ z) ≡ true) keq (≡ᵇ-refl k)
        in trans (cong (not (mergeReachable nid (dropSource (arrSource a) (EvalSt.registry st))) ∨_) snd)
                 (∨-zeroʳ (not (mergeReachable nid (dropSource (arrSource a) (EvalSt.registry st)))))

  go : (nodes : List (NodeId × NodeState Γ)) →
       cachesValid nodes (EvalSt.registry st) ≡ true →
       cachesValidMid a (chainsOf a st) nodes (cascadeLatch a st) ≡ true
  go []              hg = refl
  go ((nid , s) ∷ ns) hg =
    ∧-intro (nodeOK→Mid nid s (∧-trueˡ hg)) (go ns (∧-trueʳ hg))

-- entering: the latch opens the ledger; the automaton, Inv-related and
-- paid, stands ready to open instant nextId (still on the previous,
-- settled instant, so the ledger is the paid branch).  reg-typed threads
-- from Inv across the scheduler pop; the count fact live-source needs is
-- read off chains-count-derived
mid-init : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
  (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascadeGo a nextId (chainsOf a st) sched′
                           (cascadeLatch a st))) ≡ false →
  Mid a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
mid-init nextId sched a sched′ st S eq inv paid nodry = record
  { live-others  = λ s _ → trans (Inv.live-matches inv s)
                     (cong (countRegs s) (sym (latch-registry a st)))
  ; live-source  = live-src
  ; reg-typed    = subst (λ reg → regTyped? reg (Sched.live sched′) ≡ true)
                     (sym (latch-registry a st))
                     (regTyped?-pop-sched sched sched′ (EvalSt.registry st) eq
                       (Inv.reg-typed inv))
  ; horizon-low  = Inv.horizon-low inv
  ; ledger       = inj₁ (Inv.current-past inv , paid)
  ; done-plumbed = λ deq →
      subst (λ reg → allShareSunk (if Arrival.isLast a
                       then dropSource (arrSource a) reg else reg) ≡ true)
            (sym (latch-registry a st))
            (allShareSunk-if (Arrival.isLast a) (arrSource a)
              (EvalSt.registry st) (Inv.done-plumbed inv deq))
  ; caches       = mid-init-caches a sched sched′ st (Inv.reg-typed inv) eq (Inv.caches inv)
  ; fold-live    = nodry
  ; owed-unique  = λ ow cur → ⊥-elim (1+n≰n
                     (subst (λ c → CurrentPast c nextId) cur (Inv.current-past inv)))
  ; dying-src    = dsrc
  ; reg-bound    = subst
      (λ reg → countRemaining (chainsOf a st) [] ≤ countRegs (arrSource a) reg)
      (sym (latch-registry a st))
      (≤-reflexive (trans (countRemaining-[] (chainsOf a st))
        (sym (chains-count-derived a sched sched′ st (Inv.reg-typed inv) eq))))
  }
  where
  -- cascadeLatch sets dying ≡ if isLast then arrSource a ∷ [] else []
  dsrc : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
    memberSource s (EvalSt.dying (cascadeLatch a st)) ≡ false
  dsrc s h with Arrival.isLast a
  ... | true  rewrite h = refl
  ... | false = refl
  live-src : countIn (arrSource a) (ProtocolSt.live S)
    ≡ (if Arrival.isLast a
       then countRemaining (chainsOf a st) (EvalSt.cancelled (cascadeLatch a st))
       else countRegs (arrSource a) (EvalSt.registry (cascadeLatch a st)))
  live-src with Arrival.isLast a
  ... | true  = trans (Inv.live-matches inv (arrSource a))
                  (trans (chains-count-derived a sched sched′ st (Inv.reg-typed inv) eq)
                         (sym (countRemaining-[] (chainsOf a st))))
  ... | false = Inv.live-matches inv (arrSource a)

-- one arrival's cascade, composed.  The dry-freeness premise is
-- stated on the cascade's own emits — definitionally the cascadeGo
-- fold's emits, which is the shape mid-init wants
cascade-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascade a nextId sched′ st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = cascade a nextId sched′ st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Inv (suc nextId) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (paidUp S′ ≡ true)
cascade-wf nextId sched a sched′ st S eq inv paid nodry
  with cascadeGo-wf a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
         (mid-init nextId sched a sched′ st S eq inv paid nodry)
... | S′ , run , mid
  with mid-final mid
... | inv′ , paid′ = S′ , run , inv′ , paid′

------------------------------------------------------------------
-- the composition: fuel induction over drain, then the theorem
------------------------------------------------------------------

drain-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
    (S : ProtocolSt) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (drain {e = e} fuel nextId sched st) ≡ false →
  Σ ProtocolSt λ S′ →
    (runProtocol S (drain {e = e} fuel nextId sched st) ≡ just S′)
    × (paidUp S′ ≡ true)
drain-wf zero    nextId sched st S inv paid _  = S , refl , paid
drain-wf (suc k) nextId sched st S inv paid hd with sched-next sched in eq
... | inj₁ _            = S , refl , paid
... | inj₂ (a , sched′)
  -- the with-abstraction has already rewritten hd's type to the
  -- unfolded `cascade emits ++ drain k …` shape — split it there
  with hasDry-++ (proj₁ (cascade a nextId sched′ st))
         (drain k (suc nextId)
           (proj₁ (proj₂ (cascade a nextId sched′ st)))
           (proj₂ (proj₂ (cascade a nextId sched′ st))))
         hd
... | nodry₁ , nodry₂
  with cascade-wf nextId sched a sched′ st S eq inv paid nodry₁
... | S₁ , run₁ , inv₁ , paid₁
  with drain-wf k (suc nextId)
         (proj₁ (proj₂ (cascade a nextId sched′ st)))
         (proj₂ (proj₂ (cascade a nextId sched′ st)))
         S₁ inv₁ paid₁ nodry₂
... | S₂ , run₂ , paid₂ =
  S₂
  , run-++-just S (proj₁ (cascade a nextId sched′ st)) _ run₁ run₂
  , paid₂

-- the reified termination debt — the seeded sync budget never runs
-- dry on a canonical run, the old TERMINATING pragma's claim.  NO
-- LONGER A POSTULATE HERE: Verify-Budget-Sufficient PROVES it (the
-- instant-indexed size invariant, its burst cores, cascade-dry and
-- drain-dry), and this module now imports that proof.  What the
-- proof still rests on is named and scoped there — subscribeE-wet
-- and cascadeGo-wet, the fuel-accounting cores — rather than the
-- whole totality conjecture assumed outright.

-- the primitives' half of the sandwich: remaining debt is the frame
-- relations and their step lemmas
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins
  with hasDry-++
         (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e)))
         (drain fuel 1
           (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e))))
           (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e)))))
         (budget-sufficient fuel e ins)
... | nodry₀ , nodry₁
  with subscribe-wf e ins nodry₀
... | S₀ , run₀ , inv₀ , paid₀
  with drain-wf fuel 1
         (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         S₀ inv₀ paid₀ nodry₁
... | S₁ , run₁ , paid₁
  rewrite run-++-just protocol-init
            (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                               (sched-init e ins) (st-init e)))
            (drain fuel 1
              (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e))))
              (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e)))))
            run₀ run₁
  = acceptPaid S₁ paid₁
