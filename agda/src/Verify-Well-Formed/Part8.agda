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
module Verify-Well-Formed.Part8 where

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

open import Verify-Well-Formed.Part7 public

pushBurst-take-cut-joint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
  (es : List (InstEvent (Val Γ s))) (i : Id) (src : Source) (ek : EmitKind)
  (sched : Sched Γ) (st : EvalSt e) (kCount : ℕ) (S S₁ : ProtocolSt) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st kCount) →
  proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)))) ≡ true →
  stepProtocol (es at i from src as ek) S ≡ just S₁ →
  BurstInv id sched st S₁ →
  (∀ s → memberSource s (EvalSt.dying st) ≡ false) →
  Σ ProtocolSt λ S″ →
    (runProtocol S (proj₁ (pushBurst fuel id now (take-f nid) κ
                            ((es at i from src as ek) ∷ []) sched st)) ≡ just S″)
    × BurstInv id
        (proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ []) sched st)))
        (proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ []) sched st))) S″
pushBurst-take-cut-joint {Γ = Γ} {t = t} {e = e} {s = s}
  fuel id now nid κ es i src ek sched st kCount S S₁ lk dc seq binv₁ dyF =
  let (S″ , step , binv″) =
        cut-head-joint id nid es i src ek sched st kCount S S₁ lk dc seq binv₁ dyF
  in S″
   , subst (λ (b : Stream Γ s) → runProtocol S b ≡ just S″)
       (sym (pushBurst-take-cut-cons fuel id now nid κ es i src ek [] sched st kCount lk dc))
       (runProtocol-cons _ [] S S″ S″ step refl)
   , subst (λ (p : Sched Γ × EvalSt e) → BurstInv id (proj₁ p) (proj₂ p) S″) (sym stEq) binv″
  where
  -- proj₂ (pushBurst (em ∷ [])) as a function of the frame's step result, so
  -- `cong` transports takeDispatch-cut by conversion
  stateFrom : (List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e)
            → Sched Γ × EvalSt e
  stateFrom fr =
    ( proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ []
              (proj₁ (proj₂ (proj₂ (proj₂ fr)))) (proj₂ (proj₂ (proj₂ (proj₂ fr))))))
    , proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ []
              (proj₁ (proj₂ (proj₂ (proj₂ fr)))) (proj₂ (proj₂ (proj₂ (proj₂ fr)))))) )
  stEq : ( proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ []) sched st))
         , proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ []) sched st)) )
       ≡ ( cutSched nid sched st , cutSt nid st )
  stEq = cong stateFrom (takeDispatch-cut nid (proj₁ (splitEvents {A = Val Γ s} es))
                          (proj₂ (proj₂ (splitEvents {A = Val Γ s} es))) sched st kCount lk dc)

-- ── the joint take-burst walk ─────────────────────────────────────────────
-- ONE induction over the burst giving BOTH the reshaped burst's protocol run and
-- the BurstInv at its end.  NON-CUT emits leave registry/schedule fixed (exactly
-- like scan): the reshaped head steps the protocol identically (stepProtocol-
-- faithful — the automaton ignores value payloads), and the only node write is
-- the take counter, so every BurstInv field transfers verbatim.
-- The recursion threads run + invariant + the valsLast discipline together; only
-- the CUT emit — which severs the registry and sweeps live — is the named
-- residue, and valsLast? makes it the burst's LAST emit (cut-tail-nil), so the
-- residue is a single step rather than a step plus a re-run tail.
pushBurst-take-joint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
  (burst : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) (kCount : ℕ)
  (S S′ : ProtocolSt) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st kCount) →
  valsLast? burst ≡ true →
  BurstInv id sched st S′ →
  runProtocol S burst ≡ just S′ →
  (∀ s → memberSource s (EvalSt.dying st) ≡ false) →
  Σ ProtocolSt λ S″ →
    (runProtocol S (proj₁ (pushBurst fuel id now (take-f nid) κ burst sched st)) ≡ just S″)
    × BurstInv id (proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ burst sched st)))
                  (proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ burst sched st))) S″
pushBurst-take-joint fuel id now nid κ [] sched st kCount S S′ lk vl binv₀ runEq dyF
  = S , refl , subst (BurstInv id sched st) (sym (just-injᵂ runEq)) binv₀
pushBurst-take-joint {Γ = Γ} {t = t} {e = e} {s = s}
  fuel id now nid κ ((es at i from src as ek) ∷ ems) sched st kCount S S′ lk vl binv₀ runEq dyF
  with stepProtocol (es at i from src as ek) S in seq
... | nothing = ⊥-elim (n≢jᵂ runEq)
... | just S₁ with takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)) in tvEq
...   | out , rem , true
        with cut-tail-nil kCount es i src ek ems
               (takeVals-flag kCount (proj₁ (splitEvents {A = Val Γ s} es)) tvEq) vl
...     | refl =
          pushBurst-take-cut-joint {Γ = Γ} {s = s} fuel id now nid κ es i src ek sched st
            kCount S S₁ lk
            (takeVals-flag kCount (proj₁ (splitEvents {A = Val Γ s} es)) tvEq)
            seq (subst (BurstInv id sched st) (sym (just-injᵂ runEq)) binv₀) dyF
pushBurst-take-joint {Γ = Γ} {t = t} {e = e} {s = s}
  fuel id now nid κ ((es at i from src as ek) ∷ ems) sched st kCount S S′ lk vl binv₀ runEq dyF
  | just S₁ | out , rem , false =
        let rem′ : ℕ
            rem′ = proj₁ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es))))
            ust : EvalSt e
            ust = record st { nodes = setNode nid (take-st rem′) (EvalSt.nodes st) }
            dcF : proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)))) ≡ false
            dcF = takeVals-flag kCount (proj₁ (splitEvents {A = Val Γ s} es)) tvEq
            -- the reshaped non-cut head steps the protocol to the SAME S₁
            fstep : stepProtocol
                      ((proj₁ (proj₂ (splitEvents {A = Val Γ s} es))
                         ++ map value (proj₁ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es))))
                         ++ (if proj₂ (proj₂ (splitEvents {A = Val Γ s} es)) then complete ∷ [] else []))
                        at i from src as ek) S ≡ just S₁
            fstep = stepProtocol-faithful (λ vs → proj₁ (takeVals kCount vs)) es i src ek S S₁
                      (takeVals-nil kCount) seq
            tailBinv : BurstInv id sched ust S′
            tailBinv = record
              { live-matches  = BurstInv.live-matches binv₀
              ; reg-typed     = BurstInv.reg-typed binv₀
              ; horizon-low   = BurstInv.horizon-low binv₀
              ; current-frame = BurstInv.current-frame binv₀
              }
            -- the whole burst's residual sched/st ARE the tail's (non-cut head
            -- leaves sched fixed, writes only the node) — by cong over takeDispatch
            stateFrom : (List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e)
                      → Sched Γ × EvalSt e
            stateFrom fr =
              ( proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ ems
                        (proj₁ (proj₂ (proj₂ (proj₂ fr)))) (proj₂ (proj₂ (proj₂ (proj₂ fr))))))
              , proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ ems
                        (proj₁ (proj₂ (proj₂ (proj₂ fr)))) (proj₂ (proj₂ (proj₂ (proj₂ fr)))))) )
            stEq : ( proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ ems) sched st))
                   , proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ ems) sched st)) )
                 ≡ ( proj₁ (proj₂ (pushBurst fuel id now (take-f nid) κ ems sched ust))
                   , proj₂ (proj₂ (pushBurst fuel id now (take-f nid) κ ems sched ust)) )
            stEq = cong stateFrom
                     (takeDispatch-noncut nid (proj₁ (splitEvents {A = Val Γ s} es))
                        (proj₂ (proj₂ (splitEvents {A = Val Γ s} es))) sched st kCount lk dcF)
            (S″ , tailRun , rec) =
              pushBurst-take-joint fuel id now nid κ ems sched ust rem′ S₁ S′
                (lookupNode-setNode nid (take-st rem′) (EvalSt.nodes st))
                (valsLast-tail (es at i from src as ek) ems vl) tailBinv runEq dyF
        in S″
         , subst (λ (b : Stream Γ s) → runProtocol S b ≡ just S″)
             (sym (pushBurst-take-noncut-cons fuel id now nid κ es i src ek ems sched st kCount lk dcF))
             (runProtocol-cons _ _ S S₁ S″ fstep tailRun)
         , subst (λ (p : Sched Γ × EvalSt e) → BurstInv id (proj₁ p) (proj₂ p) S″) (sym stEq) rec

-- ── the takeᵉ (positive-count) clause of subscribeE-wf ────────────────────
-- subscribeE (takeᵉ count b) with count ≡ suc k mints+installs the take node,
-- subscribes b under take-f, pushBursts.  ONE call to pushBurst-take-joint now
-- carries the IH's inner run AND its BurstInv through the frame to an existential
-- S″ (existential because a cut transforms the burst); pushBurst-take-valsLast
-- carries the payload discipline the next take up the tree will need.
-- (The count ≡ zero branch is emptyᵉ-shaped, handled by oneShotBurst-wf.)
subscribeE-take-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) (k : ℕ) →
  evalTm count ≡ suc k →
  BurstInv id sched st S →
  (let nid = proj₁ (mintNode sched)
       r₀  = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
               (installNode nid (take-st (suc k)) st)
   in Σ ProtocolSt λ S′ →
        (runProtocol S (proj₁ r₀) ≡ just S′)
        × BurstInv id (proj₁ (proj₂ r₀)) (proj₂ (proj₂ r₀)) S′
        × (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (take-st (suc k)))
        × (valsLast? (proj₁ r₀) ≡ true)
        -- the cut's live/registry balance is off a dying source only; subscribeE
        -- never writes `dying` (cascadeLatch alone does), so this rides in from
        -- the enclosing cascade — free at a root subscribe, where st-init has it []
        × (∀ s → memberSource s (EvalSt.dying (proj₂ (proj₂ r₀))) ≡ false)) →
  Σ ProtocolSt λ S″ →
    (runProtocol S (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ just S″)
    × BurstInv id (proj₁ (proj₂ (subscribeE fuel (takeᵉ count b) κ id now sched st)))
               (proj₂ (proj₂ (subscribeE fuel (takeᵉ count b) κ id now sched st))) S″
    × (valsLast? (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ true)
subscribeE-take-wf fuel count b κ id now sched st S k ecEq binv
  (S′ , run₀ , binv₀ , nodeP , vl₀ , dyF)
  rewrite ecEq =
  let (S″ , run , binv″) =
        pushBurst-take-joint fuel id now nid κ burst sched₂ st₁ (suc k) S S′ nodeP vl₀ binv₀
          run₀ dyF
  in S″ , run , binv″
   , pushBurst-take-valsLast fuel id now nid κ burst sched₂ st₁ (suc k) nodeP vl₀
  where
  nid    = proj₁ (mintNode sched)
  r₀     = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
             (installNode nid (take-st (suc k)) st)
  burst  = proj₁ r₀
  sched₂ = proj₁ (proj₂ r₀)
  st₁    = proj₂ (proj₂ r₀)

-- the takeᵉ clause, assembled over its core.  Declared HERE rather than
-- with the other per-clause postulates because the positive-count clause
-- it consumes (`subscribeE-take-wf`, just above) is defined further down
-- the file than that block, and a postulate cannot reference a definition
-- that follows it.  Its one consumer is the takeᵉ clause of subscribeE-wf,
-- below.
subscribeE-takeᵉ-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  ProtocolSt.done S ≡ false →
  hasDry (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = subscribeE fuel (takeᵉ count b) κ id now sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (valsLast? (proj₁ r) ≡ true)
subscribeE-takeᵉ-wf =
  subscribeE-takeᵉ-wf-core
    (λ {n} {Γ} {t} {e} {s} → subscribeE-take-wf {n} {Γ} {t} {e} {s})

subscribeE-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  ProtocolSt.done S ≡ false →
  hasDry (proj₁ (subscribeE fuel b κ id now sched st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = subscribeE fuel b κ id now sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       -- the PAYLOAD DISCIPLINE, carried alongside the state relation: a burst
       -- puts its values in its last emit or nowhere.  Not a fact about the
       -- automaton, so BurstInv is the wrong home for it — but a take frame
       -- ABOVE this subscription needs it about THIS burst (it is what empties
       -- the cut's tail), so the burst-shaped conclusion is.  Every clause
       -- supplies it: one-shots are single-emit, sharedConnect prepends a
       -- value-free init emit, and the pushing operators cannot manufacture a
       -- payload from none (pushBurst-take-valsLast for takeᵉ).
       × (valsLast? (proj₁ r) ≡ true)

subscribeE-wf fuel (input i) κ id now sched st S binv deq nodry =
  subscribeE-input-wf fuel i κ id now sched st S binv deq nodry

-- ── ofᵉ: REAL oneShotBurst-wf called here ────────────────────────────────────
-- oneShotBurst-wf returns (S′, run, binv′) with no valsLast?.
-- valsLast? (proj₁ (oneShotBurst vals id sched)) = true by computation (refl).
subscribeE-wf fuel (ofᵉ ts) κ id now sched st S binv deq nodry =
  let vals = map evalTm ts
      (S′ , run , binv′) = oneShotBurst-wf vals id sched st S binv deq
  in S′ , run , binv′ , refl

-- ── emptyᵉ: same shape as ofᵉ ────────────────────────────────────────────────
subscribeE-wf fuel emptyᵉ κ id now sched st S binv deq nodry =
  let (S′ , run , binv′) = oneShotBurst-wf [] id sched st S binv deq
  in S′ , run , binv′ , refl

-- ── mapᵉ: REAL subscribeE-map-wf called here ─────────────────────────────────
-- Gap: map-valsLast-push bridges inner valsLast? to outer (~line 1920 has no valsLast?).
subscribeE-wf fuel (mapᵉ f b) κ id now sched st S binv deq nodry =
  let (S′ , run₀ , binv₀ , vl₀) =
        subscribeE-wf fuel b (map-f f ↠ κ) id now sched st S binv deq
          (map-nodry-push fuel f b κ id now sched st nodry)
      (S″ , run , binv″) =
        subscribeE-map-wf fuel f b κ id now sched st S binv (S′ , run₀ , binv₀)
  in S″ , run , binv″ , map-valsLast-push fuel f b κ id now sched st vl₀

-- ── takeᵉ: postulated (WITH-ABSTRACTION; see per-clause postulates above) ────
subscribeE-wf fuel (takeᵉ count b) κ id now sched st S binv deq nodry =
  subscribeE-takeᵉ-wf fuel count b κ id now sched st S binv deq nodry

-- ── scanᵉ: REAL subscribeE-scan-wf called here ───────────────────────────────
-- Gap: scan-valsLast-push bridges inner valsLast? to outer (~line 2003 has no valsLast?).
subscribeE-wf fuel (scanᵉ f seed b) κ id now sched st S binv deq nodry =
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₁    = installNode nid (scan-st (evalTm seed)) st
      (S′ , run₀ , binv₀ , vl₀) =
        subscribeE-wf fuel b (scan-f f nid ↠ κ) id now sched₁ st₁ S
          (scan-binv-adapt fuel f seed b κ id now sched st S binv)
          deq
          (scan-nodry-push fuel f seed b κ id now sched st nodry)
      (S″ , run , binv″) =
        subscribeE-scan-wf fuel f seed b κ id now sched st S binv
          (S′ , run₀ , binv₀ , scan-nodeP fuel f seed b κ id now sched st)
  in S″ , run , binv″ , scan-valsLast-push fuel f seed b κ id now sched st vl₀

-- ── *All ─────────────────────────────────────────────────────────────────────
subscribeE-wf fuel (mergeAllᵉ b)   κ id now sched st S binv deq nodry =
  subscribeE-mergeAll-wf  fuel b κ id now sched st S binv deq nodry
subscribeE-wf fuel (concatAllᵉ b)  κ id now sched st S binv deq nodry =
  subscribeE-concatAll-wf fuel b κ id now sched st S binv deq nodry
subscribeE-wf fuel (switchAllᵉ b)  κ id now sched st S binv deq nodry =
  subscribeE-switchAll-wf fuel b κ id now sched st S binv deq nodry
subscribeE-wf fuel (exhaustAllᵉ b) κ id now sched st S binv deq nodry =
  subscribeE-exhaustAll-wf fuel b κ id now sched st S binv deq nodry

-- ── μᵉ g0: dryBurst → hasDry = true → ⊥ ─────────────────────────────────────
subscribeE-wf g0 (μᵉ body) κ id now sched st S binv deq nodry =
  ⊥-elim (true≢false nodry)

-- ── μᵉ (gs fuel): RECURSIVE CALL, Gas decreases ──────────────────────────────
-- subscribeE (gs fuel) (μᵉ body) κ ... reduces definitionally to
-- subscribeE fuel (unfoldμ body) κ ..., so nodry and output type pass through.
subscribeE-wf (gs fuel) (μᵉ body) κ id now sched st S binv deq nodry =
  subscribeE-wf fuel (unfoldμ body) κ id now sched st S binv deq nodry

-- ── varᵉ (): absurd ───────────────────────────────────────────────────────────
subscribeE-wf fuel (varᵉ ()) κ id now sched st S binv deq nodry

-- ── deferᵉ ───────────────────────────────────────────────────────────────────
subscribeE-wf fuel (deferᵉ body) κ id now sched st S binv deq nodry =
  subscribeE-defer-wf fuel body κ id now sched st S binv deq nodry


-- ════════════════════════════════════════════════════════════════
-- subscribeE-wf BODY
-- Forward type declaration is at the start of this section (~line 1097).
-- All five proven lemmas it calls are defined above:
--   oneShotBurst-wf  (~882), subscribeE-map-wf  (~1920),
--   subscribeE-scan-wf (~2003), subscribeE-take-wf (~3060).
-- Gap and per-clause postulates are also defined above.
-- ════════════════════════════════════════════════════════════════

-- ── input ────────────────────────────────────────────────────────────────────

subscribe-wf :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false →
  Σ ProtocolSt λ S →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in (runProtocol protocol-init (proj₁ r) ≡ just S)
       × Inv 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
       × (paidUp S ≡ true)

subscribe-wf e ins nodry
  with subscribeE-wf (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
                     protocol-init (burst-init e ins) refl nodry
... | S , run , binv , _
  with burst-final _ _ S binv (root-done-plumbed e ins S run) (root-caches e ins)
... | inv , paid = S , run , inv , paid


-- foldPath-wf, ROOT clause (PROVEN): a chain that reaches the root emits
-- its ONE delivery — accumulated bookkeeping evs, then the (possibly
-- empty) value list, then complete iff the source is spent.  The
-- automaton admits it (enterInstant), pays envSrc's owed (settle), folds
-- the evs (which never touch `done`), and the values ride only if not
-- already done (done-nil).  sched/st are untouched at root.
foldPath-root-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (vals : List (Val Γ t)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
  (ob : Owed) (hz : Id) (ob′ : Owed) (Lv : List Source) (Ov : Owed) →
  enterInstant S id ≡ just (ob , hz) →
  settle delivery envSrc (ProtocolSt.live S) ob ≡ just ob′ →
  applyEvents evs (ProtocolSt.live S) ob′ (ProtocolSt.done S)
    ≡ just (Lv , Ov , ProtocolSt.done S) →
  (ProtocolSt.done S ≡ true → vals ≡ []) →
  runProtocol S (proj₁ (foldPath sf gas id now envSrc root vals evs fin sched st))
    ≡ just (record { live = Lv ; horizon = hz ; current = just (id , Ov)
                   ; done = (if fin then true else ProtocolSt.done S) })
foldPath-root-wf sf gas id now envSrc vals evs fin sched st S ob hz ob′ Lv Ov
  entEq payEq apEq dn =
  trans (runProtocol-one S _) stepEq
  where
  target : ProtocolSt
  target = record { live = Lv ; horizon = hz ; current = just (id , Ov)
                  ; done = (if fin then true else ProtocolSt.done S) }
  apply-full :
    applyEvents (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
      (ProtocolSt.live S) ob′ (ProtocolSt.done S)
      ≡ just (Lv , Ov , (if fin then true else ProtocolSt.done S))
  apply-full = trans
    (applyEvents-++just evs (map value vals ++ (if fin then complete ∷ [] else []))
      (ProtocolSt.live S) ob′ (ProtocolSt.done S) apEq)
    (applyEvents-vc vals fin Lv Ov (ProtocolSt.done S) dn)
  stepEq :
    stepProtocol
      ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
        at id from envSrc as delivery) S
      ≡ just target
  stepEq = stepProtocol-enter
    (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    id envSrc delivery S entEq payEq apply-full

------------------------------------------------------------------
-- foldPath-wf: one chain's fold, by induction on the Path (free source
-- type u — the split lives HERE, not at mid-step, see the blueprint).
-- FoldInv is the mid-fold relation: the automaton admits instant id,
-- pays envSrc, and the bookkeeping accumulated so far (evs) folds
-- cleanly, with the value list gated by done-nil.  root is PROVEN
-- (foldPath-root-wf); the frame case is IH ∘ stepFrame-wf (same emits,
-- definitionally — a frame accumulates evs, never emits); share defers
-- to dispatchShare-wf.  Acceptance only for now; the Mid-preservation
-- half (the POST) is the next layer.
------------------------------------------------------------------

-- (no `vals` parameter: FoldInv constrains only the bookkeeping evs / open
-- instant, never the carried value list — the value list rides at the root
-- emit gated by done-nil, outside FoldInv.  Dropping it makes every frame's
-- value transform irrelevant to FoldInv-preservation.)
record FoldInv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
       (id : Id) (envSrc : Source)
       (evs : List (InstEvent (Val Γ t))) (fin : Bool)
       (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) : Set where
  field
    ob   : Owed
    hz   : Id
    ob′  : Owed
    Lv   : List Source
    Ov   : Owed
    enters   : enterInstant S id ≡ just (ob , hz)
    pays     : settle delivery envSrc (ProtocolSt.live S) ob ≡ just ob′
    applies  : applyEvents evs (ProtocolSt.live S) ob′ (ProtocolSt.done S)
                 ≡ just (Lv , Ov , ProtocolSt.done S)
    -- SHADOW (three-way): mid-fold the registry LEADS the automaton's live
    -- multiset by exactly the pending evs (stepFrame mutates the registry and
    -- brackets it with init/close in evs, but never steps the protocol; the
    -- terminal emit drains evs into live).  For every source but the chain's
    -- own, live + pending inits ≡ registry + pending closes.  Collapses to
    -- Mid.live-others at the seed (evs has no init, its lone close is envSrc's)
    -- and resyncs to live-others-out once applyEvents drains evs at the root.
    shadow   : ∀ (s : Source) → sameSource s envSrc ≡ false →
      countIn s (ProtocolSt.live S) + initCount s evs
        ≡ countRegs s (EvalSt.registry st) + closeCount s evs
    -- ADJUDICATED (2026-07): an envShadow twin of SHADOW here — countIn envSrc
    -- live + initCount ≡ countRegs envSrc registry + cutCloseCount — is FALSE
    -- at the mid-seed isLast branch: it reduces to countIn ≡ countRegs, but
    -- Mid.live-source (isLast) gives countIn ≡ countRemaining, and mid-cascade
    -- countRegs ≠ countRemaining (delivered isLast chains linger in the
    -- registry until cascadeFinish).  So envSrc is NOT a seed-provable FoldInv
    -- invariant; its live-source readoff lives in FoldOut as output deltas
    -- (live-envSrc-out : live S′ ≡ live S ∸ (if fin then 1 else 0), universal;
    -- reg-envSrc-out via cutCloseCount over the emit, no-take-head first).
    -- (DROPPED 2026-07-19) a `done-plumbed : done S ≡ true → allShareSunk (if fin
    -- then dropSource envSrc reg else reg)` field used to live here.  Its `if fin`
    -- keying is frame-unstable under from-inner absorption (fin true→false with reg
    -- unchanged flips the dropSource off, demanding the full registry be share-sunk
    -- — false mid-cascade, since the completing chain lingers un-swept) — the same
    -- family as the env-close instability.  And like env-close it has NO wired
    -- consumer: the ACTUAL root handler foldPath-root-wf takes only enters/pays/
    -- applies/done-nil (done-nil comes from the `ds` discipline, not this field),
    -- foldPath-wf returns just the runProtocol result (no FoldOut), and
    -- foldPath-root-out (a standalone inhabitation check) uses its own steady/flip
    -- hypotheses.  So this field was threaded but never cashed in.  Dropped — which
    -- leaves FoldInv fully fin-INDEPENDENT (the point that actually unblocks the
    -- from-inner fin-flip clauses).  The done-plumbing obligation lives where it has
    -- readers: Inv.done-plumbed (full registry, between cascades) and Mid.done-plumbed
    -- (the `if isLast` cascade-window form, read by mid-final).
    -- carried straight through the fold for the readoff's non-live fields:
    -- registry well-typedness (stepFrame subscribes well-typed inners) and the
    -- horizon bound (S is untouched until the terminal emit, so horizon S ≤ id
    -- rides unchanged).  At root st″ = st, sched″ = sched, so reg-typed-out is
    -- reg-typed verbatim and horizon-out reads hz ≤ id off enters + horizon-low.
    reg-typed   : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low : ProtocolSt.horizon S ≤ id
    -- the open instant's owed table (Ov = the applyEvents output owed, which
    -- becomes current S′ at the root) keeps the seed's ledger shape all fold:
    -- zeroExcept envSrc (only envSrc may be owed) and UniqueOwed (no repeated
    -- key), with owed[envSrc] pinned to ob′'s (settle/fan-out never touch it —
    -- a handoff bump is repaid within its own dispatch).  These feed FoldOut's
    -- current-out, from which mid-step rebuilds Mid ps's ledger + owed-unique.
    ov-zero   : zeroExcept envSrc Ov ≡ true
    ov-unique : UniqueOwed Ov ≡ true
    ov-envSrc : lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′
    -- envSrc's own footprint in the pending evs: no envSrc init (a chain never
    -- re-subscribes its own source mid-fold), and exactly (if fin) one envSrc
    -- close — the seed exhausted close, present iff completing.  With
    -- applyEvents-count at envSrc these give live-envSrc-out (live drains by
    -- if fin then 1 else 0).  The take-head cut is the one edge stepFrame-wf must
    -- carry (a head take flips fin AND closes envSrc), pinned by Unit-Test.
    env-init  : initCount envSrc evs ≡ 0
    -- (DROPPED 2026-07-19) an `env-close : closeCount envSrc evs ≡ if fin then 1
    -- else 0` field used to live here.  It was FRAME-UNSTABLE under from-inner
    -- absorption (envSrc = the completing inner chain's own source, so its close
    -- sits in evs with fin ≡ true; a live sibling under the same instance absorbs
    -- the completion to fin′ ≡ false with evs unchanged, demanding closeCount ≡ 0
    -- while it is still 1) — the same instability FoldOut.live-envSrc-out was
    -- re-keyed off of.  It had NO consumer: foldPath-root-out derives live-envSrc-out
    -- from env-init + applyEvents-count, and only the postulated mid-step imagined
    -- wanting it.  Per the keying rule (folded artifacts only) it is gone.
    -- IF mid-step's eventual proof turns out to need an input-side drain ledger,
    -- re-add it BORN-STABLE, keyed on the frame-stable quantity `closeCount envSrc
    -- evs` (additive over ++, so it threads through frames) — e.g. tie the live
    -- drain to it directly (countIn envSrc (live S) ∸ closeCount …), never `if fin`.
    -- Re-adding is then a transcription against a real consumer, not a design call.
    -- the cascade's `dying` set holds only envSrc (cascadeLatch seeds it to
    -- [arrSource a] iff isLast, else []; the fold never grows it).  Stable
    -- through every frame (no stepFrame clause touches dying), it lets the
    -- take-cut edge invoke cutThrough-balance for s ≠ envSrc (cutThrough only
    -- skips a close on delivered ∧ dying, vacuous off envSrc).  Established at
    -- the Mid→FoldInv seed; carried unchanged by every clause.
    dying-envSrc : ∀ (s : Source) → sameSource s envSrc ≡ false →
      memberSource s (EvalSt.dying st) ≡ false

------------------------------------------------------------------
-- FoldOut — the readoff companion to FoldInv (DESIGN, worked out 2026-07;
-- not yet stated as code — see the obligations below, any one of which if
-- false would make FoldOut a false postulate, so they are discharged before
-- the record lands).  foldPath-wf will return, alongside `Σ S′ (runProtocol
-- ≡ just S′)`, a FoldOut relating the fold's OUTPUT triple (S′, st″, sched″)
-- to its inputs, from which mid-step reads Mid ps off directly.
--
-- WHY A THREE-WAY INVARIANT (the frame case is NOT a live↔registry
-- pass-through).  stepFrame mutates the registry — subscribeInner adds an
-- entry AND emits `init`; a take/switch cut removes an entry AND emits
-- `close` (Evaluator take-f, lines ~540) — but stepFrame does NOT step the
-- protocol.  live S only catches up when the ACCUMULATED evs are applied at
-- the terminal root/share emit.  So mid-fold the registry LEADS and live LAGS
-- by exactly the pending evs.  The invariant threading through frames is thus
-- three-way, per source s ≠ envSrc:
--
--   countIn s (live S) + initCount s evs ≡ countRegs s (registry st)
--                                          + closeCount s evs      … (SHADOW)
--
--   (initCount/closeCount = # of `init s` / `close s _` in the pending evs;
--    envSrc is excluded — its own delivery/close is accounted separately.)
--   • SEED: evs = if isLast then [close envSrc] else []; for s≠envSrc both
--     counts are 0, so SHADOW ⇔ Mid.live-others — provided by mid-seed.
--   • stepFrame PRESERVES SHADOW: each clause's registry delta is matched by
--     its evs′ init/close delta (bracketing) — the enriched stepFrame-wf duty.
--   • ROOT base: applyEvents drains evs into live, so countIn s Lv = countIn s
--     (live S) + initCount − closeCount = countRegs s (registry st) (registry
--     unchanged by root) ⇒ live-others-out.  SHADOW is thus added to FoldInv.
--
-- FoldOut FIELDS (postcondition at the output S′, st″, sched″), each tagged
-- with the Mid ps field it discharges and its establishing obligation:
--   1 live-others-out : ∀ s≠envSrc, countIn s (live S′) ≡ countRegs s
--       (registry st″)                                    [Mid ps.live-others]
--   2 live-src-out    : countIn envSrc (live S′) ≡
--       countIn envSrc (live S) ∸ closeCount envSrc evsᶠ  [→ live-source]
--       (evsᶠ = the accumulated evs reaching the root).  KEYED ON closeCount,
--       NOT on fin: the seed close of envSrc rides evs (isLast), and a take
--       CUT also emits `close envSrc` (cutThrough, Evaluator 253) — both must
--       count.  At the seed closeCount envSrc evs = if isLast then 1 else 0.
--       OBLIGATION: frames/shares emit no OTHER close on envSrc (inner sources
--       are fresh defs; a share node toℕ i is downstream, so envSrc ≢ toℕ i —
--       shown, not assumed).  With Mid(head∷ps).live-source (isLast branch):
--       countRemaining(head∷ps) ∸1 = countRemaining ps (head uncancelled, ceq).
--   3 reg-envSrc-fixed: countRegs envSrc (registry st″) ≡ countRegs envSrc
--       (registry st) ∸ closeCount envSrc evsᶠ — the fold removes an envSrc
--       registration exactly when it emits an envSrc close (a take cut does
--       BOTH atomically: cutThrough drops it from `kept` AND emits its close;
--       the seed isLast close is the LONE exception — it removes from live but
--       leaves the registration for cascadeFinish).  So for s = envSrc the
--       SHADOW three-way holds up to that one seed close, which is precisely
--       why the done-plumbed conditional (drop iff isLast) is correct: an
--       isLast exhaustion leaves the registration for cascadeFinish (drop
--       branch); a take completion already removed it in-band (full-registry
--       branch is clean).  The two completion routes hit the two branches.
--   4 reg-typed-out   : regTyped? (registry st″) (Sched.live sched″) ≡ true
--                                                         [Mid ps.reg-typed]
--   5 horizon-out     : ProtocolSt.horizon S′ ≡ FoldInv.hz ⇒ ≤ nextId, via
--       enters + Mid.horizon-low                          [Mid ps.horizon-low]
--   6 current-out     : current S′ ≡ just (nextId , Ov) with lookupOwed envSrc
--       Ov = (owed after the head's delivery decrement)   [ledger inj₂,
--       owed-unique] — the OUTPUT-side twin of mid-seed's owed arithmetic.
--   7 done-out        : done S′ ≡ (if finᶠ then true else done S) where finᶠ is
--       the THREADED fin at the root (a take cut flips it true even when not
--       isLast — foldPath root, Evaluator 961); done-plumbed via the
--       conditional field, correct by the field-3 self-healing argument.
--                                                         [Mid ps.done-plumbed]
--   (fold-live is NOT a FoldOut field — it names a/nextId/ps, absent from the
--    fold; mid-step peels it from Mid(head∷ps).fold-live directly.)
--
-- PER-CASE establishment of FoldOut:
--   root        : all fields concrete from foldPath-root-wf + SHADOW.
--   f ↠ path′   : foldPath frame ≡ foldPath path′ (transformed state), so the
--                 OUTPUT triple is the recursion's — the OUTPUT-ONLY fields
--                 pass THROUGH unchanged (only st″/sched″/S′, identical for
--                 outer and recursion); the frame's bookkeeping is absorbed by
--                 SHADOW (enriched stepFrame-wf re-establishes FoldInv).
--   share-sink i: handoff + fan-out (enriched dispatchShare-wf).  handoff
--                 bumps owed[i] by countIn i (live); the fan-out repays one
--                 per registration and (isLast) dropSource i at finish resyncs
--                 registry i against the fan-out's closes — the diamond.
--
-- WHICH FIELDS ARE FoldOut vs. FoldInv (traced 2026-07):
--  • OUTPUT-ONLY (clean FoldOut fields — reference only st″/sched″/S′, so they
--    pass through the frame recursion): live-others-out (s≠envSrc, from SHADOW),
--    reg-typed-out, horizon-out, current-out, done-plumbed-out.  current-out is
--      Σ Ov, current S′ ≡ just(id,Ov) × zeroExcept envSrc Ov × UniqueOwed Ov
--            × lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′
--    (ob′ = FoldInv.ob′ — post-settle owed, invariant through frames).  OWED
--    TRACE: settle delivery seeds owed[envSrc]=countIn envSrc live on the first
--    delivery then pays one (later deliveries just pay); close envSrc exhausted
--    is non-cutPending so applyEvents leaves owed alone; the fan-out touches
--    only owed[toℕ i].  Hence lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′,
--    uniformly.  mid-step then ties lookupOwed envSrc ob′ to countRemaining ps
--    via the ledger (inj₂ pays the entered owed once; inj₁ seeds countIn∸1).
--  • The envSrc LIVE/REGISTRY readoff is NOT a clean FoldOut field — it is
--    entangled with the cascade snapshot and belongs in FoldInv (threaded),
--    for three reasons found by tracing:
--     (1) reason-based drops: cut/cutPending drop registry+live together
--         (cutThrough); the seed exhausted is live-ONLY (registry deferred to
--         cascadeFinish).  So the envSrc analog of SHADOW must use a
--         cutCloseCount (cut+cutPending only), not closeCount.
--     (2) a take in the head path cuts the head's OWN envSrc registration
--         mid-fold, so any statement keyed on the seed evs undercounts — the
--         real count is the full accumulated evs, an internal fold quantity, so
--         it cannot be a FoldOut field parameterised by the seed evs.
--     (3) isLast vs not use DIFFERENT targets (countRemaining ps vs countRegs),
--         and mid-cascade countRegs envSrc ≠ countRemaining (delivered isLast
--         chains linger in the registry), so no single output-only envSrc
--         identity covers both.
--    DESIGN NEXT: add envShadow to FoldInv —
--      countIn envSrc live + initCount envSrc evs
--        ≡ countRegs envSrc registry + cutCloseCount envSrc evs
--    (the seed exhausted close is excluded on BOTH sides: not a cutClose, and
--    it is the lone live-drop the registry defers), threaded by stepFrame-wf/
--    dispatchShare-wf exactly like SHADOW, with the isLast/countRemaining
--    connection made at mid-step off Mid.live-source + the ledger.  The
--    take-head corner (head's own cut close + cancellation) is the one edge to
--    pin with a Unit-Test before relying on it.
--
-- VERIFIED 2026-07-19 (foldPath-root-out groundwork):
--  • live-others-out is now MECHANISED end-to-end for the root: readoff-cancel
--    = applyEvents-count (drains evs into live) ∘ SHADOW ∘ +-cancelʳ-≡
--    (cancel the shared closeCount) ⇒ countIn s Lv ≡ countRegs s (registry st).
--    At root foldSt = st, foldSched = sched (Evaluator 960-962), so the two
--    registry/sched fields reduce to reg-envSrc-out = refl and reg-typed-out =
--    FoldInv.reg-typed verbatim.  current-out reads off FoldInv.ov-zero/
--    ov-unique/ov-envSrc (added today) with Ov = the applies output.
--  • done-plumbed-out is the ONE genuinely hard field, and it is NOT a
--    seed-threadable FoldInv invariant — established here (2026-07-19):
--     - done S′ = if fin then true else done S, so a completing chain
--       (fin ≡ true, done S ≡ false) sets done S′ ≡ true while
--       FoldInv.done-plumbed (keyed on done S ≡ true) does NOT fire.  cascadeGo
--       only builds emits; runProtocol flips done at the first `complete`, so
--       the first chain of the last arrival flips it and every later ps chain
--       runs with done ≡ true — the flip case is reachable, not a corner.
--     - The tempting fix (a FoldInv field `fin ≡ true → allShareSunk(dropSource
--       envSrc registry)`, threaded like SHADOW) is FALSE at the seed: the seed
--       fin = isLast a, but a downstream *All frame ABSORBS a completing inner
--       (stepFrame from-inner `react true`: fin′ ≡ false whenever any sibling
--       aliveThrough, Evaluator 599-603; `finish` only propagates on the
--       count/od gate).  So isLast a ≡ true does NOT imply the subtree
--       completes, and with a live merge sibling every other root-direct source
--       is still non-share-sunk — allShareSunk(dropSource envSrc registry) is
--       plainly false there.  A seed field would be a FALSE leaf.
--     - RESOLUTION (higher model, 2026-07-19): the fin ≡ true plumbing is a
--       post-frame property, so it belongs in FoldOut keyed on fin-OUT, NOT
--       threaded from the seed.  fin-out is not returned by foldPath, so encode
--       it frame-stably as done S ≡ false ∧ done S′ ≡ true (⟺ fin-out ≡ true
--       under done-nil; done S/S′ are protocol states, identical for outer and
--       recursion since frames never step the automaton).  Absorption ⇒ done S′
--       ≡ false ⇒ VACUOUS — which is exactly what lets it establish clause-by-
--       clause.  Two FoldOut fields now (see the record above):
--         flip-plumbed-out : done S ≡ false → done S′ ≡ true → allShareSunk(drop)
--         done-plumbed-out : done S ≡ true  → allShareSunk(full)
--       ESTABLISHMENT: from-inner comes nearly free — fin passes it only when
--       the evaluator's own `any aliveThrough ≡ false` scrutinee holds, an
--       operational certificate the proof converts into the invariant.  thru-
--       outer wrap gates on NODE counts (merge-st k / concat queue / switch
--       Maybe), so they force a node↔registry coherence fact — added MINIMALLY
--       as threaded FoldInv fields per wrap clause as forced (same discipline as
--       SHADOW), never globally up front.  Couples with the take-head cut (take-f
--       flips fin AND emits cutThrough closes, Evaluator 540-548).
--       MERGE COHERENCE — candidate FALSIFIED by the guardrail-3 hand-check
--       (2026-07-19).  The identified candidate field
--         merge k@nid : (merge-st k _ at nid) ⇒ k ≡ countRegsUnder nid registry
--       (k ≡ #live registrations whose path threads nid, via pathHasNode) is
--       FALSE — THREE independent reasons, each a concrete counterexample:
--        (1) The OUTER stream itself flows through `thru-outer mergeᵒ nid`, so
--            the outer registration threads nid too (frameNodes (thru-outer _ k)
--            = k ∷ []), yet `k` counts only ACTIVE INNERS.  Whenever the outer is
--            live, countRegsUnder nid ≥ 1 while k may be 0.  Airtight, needs no
--            nesting: `mergeAll(of(a))` after a completes but before outer does.
--        (2) An inner obs is an ARBITRARY closed Exp (Rx.Exp: Val Γ (obs u) =
--            Exp Γ [] [] [] u), so a multi-source inner — e.g. `mergeAll(of(
--            merge(a,b)))` — makes subscribeE register TWO chains threading nid
--            (subscribeInner path = from-inner mergeᵒ nid inst ↠ κ, and
--            pathHasNode nid fires on the from-inner allNid), but `bump`
--            (Evaluator 609-611) does a single `suc k` for the whole inner.
--        (3) `finish mergeᵒ` (Evaluator 568-570) does `merge-st (pred k)` and
--            does NOT touch the registry, so a completed inner's registrations
--            LINGER (dropped only at cut/cascadeFinish).  k decrements; the raw
--            structural count does not.
--       COROLLARY (the real lesson): the gate-relevant count is NOT a raw
--       structural pathHasNode count.  k tracks distinct LIVE inner INSTANCES
--       (one inst per subscribeInner, pred on finish), so the true measure must
--       (a) key on the from-inner allNid=nid frame only (excludes the outer's
--       thru-outer, reason 1), (b) dedup by `inst` (collapses a multi-source
--       inner, reason 2), and (c) exclude spent registrations mirroring
--       `aliveThrough`'s liveness (cancelled / dying∧delivered, reason 3).  That
--       is a from-inner-instance liveness count, not countRegsUnder.  Probe code
--       (countRegsUnder + mergeWrap-nil-coherent) reverted; git has it.  DO NOT
--       generalise to a global node↔registry theory, and NOT onto dispatchShare.
--     - flip-plumbed-out IS SOUND — the count field is not even needed (2026-07-19).
--       A false alarm ("a co-completing inner's lingering reg breaks allShareSunk
--       (dropSource envSrc)") was chased down and REFUTED by the cascade lifecycle:
--        • A cascade is SINGLE-SOURCE: cascadeGo folds only chainsOf a (arrSource a
--          = envSrc); every chain folded in one cascade shares that one source.
--        • cascadeFinish drops arrSource a's regs at the END of each cascade (Evtr
--          1088-1093), and sync-completing sources never linger at all (of/empty/
--          finite-cold never `register`; a share def dying in its connect burst
--          self-drops, Evtr 830).  Only genuinely-live async/hot sources hold regs.
--        • So "simultaneous" completions are still SEPARATE cascades (drain pulls
--          one arrival at a time, distinct ids).  A co-completing inner is a prior
--          cascade whose cascadeFinish already dropped its reg before envSrc's
--          cascade runs — it cannot linger into envSrc's flip.
--       Hence at ANY flip the live registry splits into: (a) envSrc's own regs
--       (removed by dropSource envSrc), (b) share-sunk regs, (c) other-source LIVE
--       root-sinkers — but a live root-sinking sibling ABSORBS fin (from-inner
--       react true / merge-st k>0 / concat queue), so it could not have let fin
--       reach root in the first place.  (c)-root-sinking is thus incompatible with
--       the flip; only (a)+(b) coexist with it ⇒ allShareSunk(dropSource envSrc).
--     - ESTABLISHMENT, REDIRECTED: flip-plumbed-out is NOT a per-frame node-COUNT
--       fact — it is the contrapositive of ABSORPTION, assembled from the per-frame
--       GATE CERTIFICATES along the fold path.  Two ingredients:
--        (i) TOPOLOGY (verified 2026-07-19): there is no binary static merge —
--            mergeAllᵉ is the ONLY merge (Evtr 896), so `merge(a,b)` desugars to
--            mergeAll(of(a,b)) with a,b inners of ONE node nid (from-inner mergeᵒ
--            nid _).  concat/switch/exhaust likewise.  Hence ANY two root-sinking
--            sources that must jointly-complete-before-root are inners under a
--            COMMON *All gate; there are no independent root-sinkers whose fins
--            race to root ungated.  (foldPath root emits `if fin complete` with no
--            join, Evtr 960-962 — soundness relies entirely on this gating.)
--        (ii) CERTIFICATE: when the fold's fin passes a gate on envSrc's path, the
--            evaluator's own scrutinee fired.  A merge gate absorbs on TWO axes,
--            and fin passes only when BOTH clear:
--              · the completing inner's OWN (multi-source) subtree — from-inner
--                `any aliveThrough registry ≡ false` (Evtr 601).  aliveThrough
--                tests `pathHasNode inst p` (the completing INSTANCE inst, not the
--                node), so this axis is structural/no-count and handles reason (2)'s
--                multi-source inner directly.
--              · the OTHER active inners — `pred k ≡ᵇ 0` at from-inner finish (Evtr
--                569), `k ≡ᵇ 0` at the outer's thru-outer wrap (Evtr 625-628).
--                Sibling inners carry DISTINCT insts, so aliveThrough does NOT see
--                them; only k does.  So the count is NOT fully avoidable — but the
--                needed fact is one-directional and liveness-aware:
--                  merge-cert : (merge-st k _ at nid) ⇒ k ≡ 0 ⇒ no aliveThrough
--                               inner INSTANCE under nid survives
--                (the CORRECTED coherence: key on from-inner allNid=nid, dedup by
--                inst, exclude spent — NOT the false raw countRegsUnder equality).
--       So a live non-envSrc root-sinker r must share a gate g with envSrc's path
--       (topology); envSrc's fin passing g fired g's certificate; the certificate
--       (aliveThrough=false for r's own inst, or merge-cert via k for a sibling
--       inst) says r is not live — contradiction.  ⇒ allShareSunk(dropSource
--       envSrc).  OPEN (next), both operational (guardrail 1), carried by the
--       enriched stepFrame-wf: (a) the aliveThrough=false / merge-cert certificate
--       as from-inner/thru-outer's enriched conclusion; (b) the "root-sinker shares
--       a gate with envSrc's path" topology lemma over Path (pathHasNode /
--       frameNodes).  The merge-cert still needs the CORRECTED k↔live-inst
--       coherence as a threaded FoldInv field — its exact statement (and whether
--       k≡0⇒none is seed-provable) is the remaining design point, NOT countRegsUnder.
--     - Option 2 (derive from Inv.done-plumbed) is STRUCTURALLY DEAD: its premise
--       is done ≡ true, vacuous right up until the flip; the flip is mid-cascade,
--       where Inv does not exist.  Nothing to derive from at the one moment the
--       conclusion is needed.
--     - GUARD (standing): if fin reaches root while a non-envSrc root-sinking
--       registration survives, that is an evaluator completion BUG, not an
--       invariant gap — stop and surface it.  (Not a spec counterexample: the
--       batching is not in question; no falsifying emit-stream pair was found.)
------------------------------------------------------------------

-- the fold's output EvalSt (st″) and Sched (sched″)
