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
module Verify-Well-Formed.Part6 where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (∨-assoc; ∨-comm; ∨-identityʳ)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-pred; m≤n+m; 1+n≰n; ≤⇒≤ᵇ; ≤ᵇ⇒≤; +-suc; +-comm; +-assoc; +-identityʳ; +-cancelʳ-≡; m+n∸n≡m)
open import Data.List    using (List; []; _∷_; _++_; any; length; map)
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

open import Verify-Well-Formed.Part5 public

pushBurst-scan-fixed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (κ : Path Γ u t) (burst : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) (acc : Val Γ u) →
  lookupNode nid (EvalSt.nodes st) ≡ just (scan-st acc) →
  (EvalSt.registry (proj₂ (proj₂ (pushBurst fuel id now (scan-f fn nid) κ burst sched st)))
     ≡ EvalSt.registry st)
  × (proj₁ (proj₂ (pushBurst fuel id now (scan-f fn nid) κ burst sched st)) ≡ sched)
pushBurst-scan-fixed fuel id now fn nid κ [] sched st acc lk = refl , refl
pushBurst-scan-fixed {u = u} fuel id now fn nid κ ((es at i from s as k) ∷ ems) sched st acc lk
  rewrite lk | ≟ᵗ-refl u =
  pushBurst-scan-fixed fuel id now fn nid κ ems sched
    (record st { nodes = setNode nid (scan-st acc′) (EvalSt.nodes st) }) acc′
    (lookupNode-setNode nid (scan-st acc′) (EvalSt.nodes st))
  where acc′ = proj₂ (scanVals fn acc (proj₁ (splitEvents es)))

-- ── the scanᵉ clause of subscribeE-wf (given the IH on b + node persistence) ─
-- subscribeE (scanᵉ f seed b) = mint+install the scan node, subscribe b under
-- scan-f, pushBurst.  The IH runs b's burst to S′ under BurstInv and (deferred:
-- subscribeE only mints fresh nodes) leaves the scan node present; pushBurst-scan-
-- run threads the accumulator and runs to the SAME S′; pushBurst-scan-fixed
-- shows registry/schedule are untouched, so live-matches/reg-typed carry.
-- The `acc, nodeP` node-persistence witness is the one piece
-- still owed from the walk's fresh-node discipline.
subscribeE-scan-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  (let nid = proj₁ (mintNode sched)
       r₀  = subscribeE fuel b (scan-f f nid ↠ κ) id now (proj₂ (mintNode sched))
               (installNode nid (scan-st (evalTm seed)) st)
   in Σ ProtocolSt λ S′ →
        (runProtocol S (proj₁ r₀) ≡ just S′)
        × BurstInv id (proj₁ (proj₂ r₀)) (proj₂ (proj₂ r₀)) S′
        × (Σ (Val Γ u) λ acc → lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (scan-st acc))) →
  Σ ProtocolSt λ S″ →
    (runProtocol S (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ just S″)
    × BurstInv id (proj₁ (proj₂ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)))
               (proj₂ (proj₂ (subscribeE fuel (scanᵉ f seed b) κ id now sched st))) S″
subscribeE-scan-wf fuel f seed b κ id now sched st S binv (S′ , run₀ , binv₀ , acc , nodeP) =
  S′ , run″ , binv″
  where
  nid    = proj₁ (mintNode sched)
  r₀     = subscribeE fuel b (scan-f f nid ↠ κ) id now (proj₂ (mintNode sched))
             (installNode nid (scan-st (evalTm seed)) st)
  burst  = proj₁ r₀
  sched₂ = proj₁ (proj₂ r₀)
  st₁    = proj₂ (proj₂ r₀)

  cRes   = pushBurst-scan-fixed fuel id now f nid κ burst sched₂ st₁ acc nodeP
  regEq  = proj₁ cRes
  schEq  = proj₂ cRes

  stF  = proj₂ (proj₂ (subscribeE fuel (scanᵉ f seed b) κ id now sched st))
  schF = proj₁ (proj₂ (subscribeE fuel (scanᵉ f seed b) κ id now sched st))

  run″ : runProtocol S (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ just S′
  run″ = pushBurst-scan-run fuel id now f nid κ burst sched₂ st₁ acc S S′ nodeP run₀

  lmF : ∀ s → countIn s (ProtocolSt.live S′) ≡ countRegs s (EvalSt.registry stF)
  lmF s rewrite regEq = BurstInv.live-matches binv₀ s

  regTF : regTyped? (EvalSt.registry stF) (Sched.live schF) ≡ true
  regTF rewrite regEq | schEq = BurstInv.reg-typed binv₀

  binv″ : BurstInv id schF stF S′
  binv″ = record
    { live-matches  = lmF
    ; reg-typed     = regTF
    ; horizon-low   = BurstInv.horizon-low binv₀
    ; current-frame = BurstInv.current-frame binv₀
    }

-- takeVals never fabricates output from nothing: an empty input yields an
-- empty take (needed so g = proj₁ ∘ takeVals satisfies stepProtocol-faithful).
takeVals-nil : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) → proj₁ (takeVals {Γ = Γ} {s = s} k []) ≡ []
takeVals-nil zero    = refl
takeVals-nil (suc k) = refl

-- read the cut flag out of a takeVals equation (cleanly-bound implicits so the
-- element type is pinned at the use site).
takeVals-flag : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (vs : List (Val Γ s))
  {out : List (Val Γ s)} {rem : ℕ} {b : Bool} →
  takeVals k vs ≡ (out , rem , b) → proj₂ (proj₂ (takeVals k vs)) ≡ b
takeVals-flag k vs eq = cong (λ x → proj₂ (proj₂ x)) eq

-- takeDispatch over a stuck node lookup reduces to the non-cut re-emit once we
-- know the node is take-st k and the budget is not exhausted.  Stated over the
-- stuck `lookupNode` call so `rewrite` can fire it inside pushBurst's goal.
takeDispatch-noncut : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st k) →
  proj₂ (proj₂ (takeVals k vals)) ≡ false →
  takeDispatch {t = t} nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
    ≡ (proj₁ (takeVals k vals) , [] , fin , sched ,
       record st { nodes = setNode nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                                     (EvalSt.nodes st) })
takeDispatch-noncut nid vals fin sched st k lk dc rewrite lk | dc = refl

-- ── the take cut's residual state, named ─────────────────────────────────
-- The cut severs the registry (keeping only the regs cutThrough spares),
-- sweeps `live` to match, and resets the node's budget to zero.  This pair of
-- names is the single vocabulary for that residue: takeDispatch-cut computes
-- it, pushBurst-take-cut-cons reduces the cut head onto it, and cut-head-joint
-- states its obligations over it.  They are plain transparent definitions, so
-- everything downstream still converts with the raw record forms.
cutSched : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (sched : Sched Γ) (st : EvalSt e) → Sched Γ
cutSched nid sched st = record sched
  { live = sweepLive
      (proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                         (EvalSt.dying st) (EvalSt.registry st)))
      (Sched.live sched) }

cutSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (st : EvalSt e) → EvalSt e
cutSt nid st = record st
  { registry = proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                 (EvalSt.dying st) (EvalSt.registry st))
  ; cancelled = proj₂ (proj₂ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                         (EvalSt.dying st) (EvalSt.registry st)))
                ++ EvalSt.cancelled st
  ; nodes = setNode nid (take-st zero) (EvalSt.nodes st) }

-- the dual: when the budget IS exhausted, takeDispatch cuts — emits the
-- truncated prefix, the cutThrough closes, forces `complete` (fin′ ≡ true),
-- sweeps live, severs the registry, and resets the node to take-st zero.
takeDispatch-cut : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st k) →
  proj₂ (proj₂ (takeVals k vals)) ≡ true →
  takeDispatch {t = t} nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
    ≡ (proj₁ (takeVals k vals)
      , proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                 (EvalSt.dying st) (EvalSt.registry st)))
      , true
      , cutSched nid sched st
      , cutSt nid st)
takeDispatch-cut nid vals fin sched st k lk dc rewrite lk | dc = refl

-- ── takeᵉ: reduce pushBurst's non-cut head to a plain re-emit ─────────────
-- An equation over the stuck pushBurst call (proven by rewriting lookupNode
-- inside), so the fold can `rewrite` it without touching lookupNode in its own
-- goal.  A non-exhausted budget re-emits proj₁ (takeVals kCount vals) with no
-- bookkeeping of its own, threading the remaining count into the node.
pushBurst-take-noncut-cons : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
  (es : List (InstEvent (Val Γ s))) (i : Id) (src : Source) (ek : EmitKind)
  (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) (kCount : ℕ) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st kCount) →
  proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents es)))) ≡ false →
  proj₁ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ ems) sched st)
    ≡ ((proj₁ (proj₂ (splitEvents es))
         ++ map value (proj₁ (takeVals kCount (proj₁ (splitEvents es))))
         ++ (if proj₂ (proj₂ (splitEvents es)) then complete ∷ [] else []))
        at i from src as ek)
      ∷ proj₁ (pushBurst fuel id now (take-f nid) κ ems sched
                (record st { nodes = setNode nid
                    (take-st (proj₁ (proj₂ (takeVals kCount (proj₁ (splitEvents es))))))
                    (EvalSt.nodes st) }))
pushBurst-take-noncut-cons {Γ = Γ} {t = t} {e = e} {s = s}
  fuel id now nid κ es i src ek ems sched st kCount lk dc
  = cong consFrom (takeDispatch-noncut nid (proj₁ (splitEvents es))
                     (proj₂ (proj₂ (splitEvents es))) sched st kCount lk dc)
  where
  -- proj₁ (pushBurst (em ∷ ems)) as a function of the frame's step result, so
  -- `cong` transports takeDispatch-noncut by conversion (bridging the defeq
  -- forms that a syntactic rewrite/with cannot).
  consFrom : List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e → Stream Γ s
  consFrom fr =
    ((proj₁ (proj₂ (splitEvents es)) ++ retagEvents (proj₁ (proj₂ fr)) ++ map value (proj₁ fr)
       ++ (if proj₁ (proj₂ (proj₂ fr)) then complete ∷ [] else []))
      at i from src as ek)
    ∷ proj₁ (pushBurst fuel id now (take-f nid) κ ems
              (proj₁ (proj₂ (proj₂ (proj₂ fr)))) (proj₂ (proj₂ (proj₂ (proj₂ fr)))))

-- the cut analogue: proj₁ (pushBurst (em ∷ ems)) reduced to the cut head emit
-- (bookkeeping ++ the cutThrough closes ++ the truncated values ++ complete)
-- followed by the tail pushed through the severed state (registry = kept,
-- live swept, node reset to take-st zero).
pushBurst-take-cut-cons : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
  (es : List (InstEvent (Val Γ s))) (i : Id) (src : Source) (ek : EmitKind)
  (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) (kCount : ℕ) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st kCount) →
  proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents es)))) ≡ true →
  proj₁ (pushBurst fuel id now (take-f nid) κ ((es at i from src as ek) ∷ ems) sched st)
    ≡ ((proj₁ (proj₂ (splitEvents es))
         ++ retagEvents (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                                  (EvalSt.dying st) (EvalSt.registry st))))
         ++ map value (proj₁ (takeVals kCount (proj₁ (splitEvents es))))
         ++ complete ∷ [])
        at i from src as ek)
      ∷ proj₁ (pushBurst fuel id now (take-f nid) κ ems (cutSched nid sched st) (cutSt nid st))
pushBurst-take-cut-cons {Γ = Γ} {t = t} {e = e} {s = s}
  fuel id now nid κ es i src ek ems sched st kCount lk dc
  = cong consFrom (takeDispatch-cut nid (proj₁ (splitEvents es))
                     (proj₂ (proj₂ (splitEvents es))) sched st kCount lk dc)
  where
  consFrom : List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e → Stream Γ s
  consFrom fr =
    ((proj₁ (proj₂ (splitEvents es)) ++ retagEvents (proj₁ (proj₂ fr)) ++ map value (proj₁ fr)
       ++ (if proj₁ (proj₂ (proj₂ fr)) then complete ∷ [] else []))
      at i from src as ek)
    ∷ proj₁ (pushBurst fuel id now (take-f nid) κ ems
              (proj₁ (proj₂ (proj₂ (proj₂ fr)))) (proj₂ (proj₂ (proj₂ (proj₂ fr)))))

-- ── valsLast: the burst payload discipline ───────────────────────────────
-- Defined in Rx.Protocol (once shared with a measurement harness, retired
-- 2026-08-09);
-- see the design note there.  What lives here is the peeling, the fact that a
-- take cut needs a payload — which together EMPTY the cut's tail — and the
-- preservation lemma that carries the discipline through a pushBurst.

∧-true : (x y : Bool) → x ∧ y ≡ true → (x ≡ true) × (y ≡ true)
∧-true true  y eq = refl , eq
∧-true false y ()

not-true : (b : Bool) → not b ≡ true → b ≡ false
not-true false eq = refl
not-true true  ()

-- peel one emit: the tail of a valsLast burst is valsLast
valsLast-tail : ∀ {A : Set} (em : InstEmit A) (ems : List (InstEmit A)) →
  valsLast? (em ∷ ems) ≡ true → valsLast? ems ≡ true
valsLast-tail em []          vl = refl
valsLast-tail em (em′ ∷ ems) vl = proj₂ (∧-true _ _ vl)

-- THE COLLAPSE: a payload-carrying emit is the LAST emit of a valsLast burst
valsLast-cut : ∀ {A : Set} (em : InstEmit A) (ems : List (InstEmit A)) →
  hasValue (InstEmit.events em) ≡ true → valsLast? (em ∷ ems) ≡ true → ems ≡ []
valsLast-cut em []          hv vl = refl
valsLast-cut em (em′ ∷ ems) hv vl =
  true≢false (trans (sym hv) (not-true _ (proj₁ (∧-true _ _ vl))))

-- a takeVals cut NEEDS a payload: budget zero and an empty value list both leave
-- the flag down, so a raised flag means the emit really carried a value
takeVals-cut-cons : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (vs : List (Val Γ s)) →
  proj₂ (proj₂ (takeVals k vs)) ≡ true →
  Σ (Val Γ s) λ v → Σ (List (Val Γ s)) λ vs′ → vs ≡ v ∷ vs′
takeVals-cut-cons zero          vs       ()
takeVals-cut-cons (suc k)       []       ()
takeVals-cut-cons (suc zero)    (v ∷ vs) dc = v , vs , refl
takeVals-cut-cons (suc (suc k)) (v ∷ vs) dc = v , vs , refl

takeVals-nil-flag : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) →
  proj₂ (proj₂ (takeVals {Γ = Γ} {s = s} k [])) ≡ false
takeVals-nil-flag zero    = refl
takeVals-nil-flag (suc k) = refl

-- splitEvents' two halves against hasValue: a nonempty grafted value list means
-- the emit carried a payload, an absent one means it did not, and the retagged
-- bookkeeping skeleton never carries one at all
splitEvents-vals-hasValue : ∀ {n} {Γ : Ctx n} {s} {A : Set}
  (es : List (InstEvent (Val Γ s))) (v : Val Γ s) (vs : List (Val Γ s)) →
  proj₁ (splitEvents {A = A} es) ≡ v ∷ vs → hasValue es ≡ true
splitEvents-vals-hasValue []               v vs ()
splitEvents-vals-hasValue (value _   ∷ es) v vs eq = refl
splitEvents-vals-hasValue (init _    ∷ es) v vs eq = splitEvents-vals-hasValue es v vs eq
splitEvents-vals-hasValue (close _ _ ∷ es) v vs eq = splitEvents-vals-hasValue es v vs eq
splitEvents-vals-hasValue (handoff _ ∷ es) v vs eq = splitEvents-vals-hasValue es v vs eq
splitEvents-vals-hasValue (complete  ∷ es) v vs eq = splitEvents-vals-hasValue es v vs eq

splitEvents-noValue : ∀ {n} {Γ : Ctx n} {s} {A : Set}
  (es : List (InstEvent (Val Γ s))) →
  hasValue es ≡ false → proj₁ (splitEvents {A = A} es) ≡ []
splitEvents-noValue []               hv = refl
splitEvents-noValue (value _   ∷ es) ()
splitEvents-noValue (init _    ∷ es) hv = splitEvents-noValue es hv
splitEvents-noValue (close _ _ ∷ es) hv = splitEvents-noValue es hv
splitEvents-noValue (handoff _ ∷ es) hv = splitEvents-noValue es hv
splitEvents-noValue (complete  ∷ es) hv = splitEvents-noValue es hv

splitEvents-bs-valueFree : ∀ {n} {Γ : Ctx n} {s} {A : Set}
  (es : List (InstEvent (Val Γ s))) →
  hasValue (proj₁ (proj₂ (splitEvents {A = A} es))) ≡ false
splitEvents-bs-valueFree []               = refl
splitEvents-bs-valueFree (value _   ∷ es) = splitEvents-bs-valueFree es
splitEvents-bs-valueFree (init _    ∷ es) = splitEvents-bs-valueFree es
splitEvents-bs-valueFree (close _ _ ∷ es) = splitEvents-bs-valueFree es
splitEvents-bs-valueFree (handoff _ ∷ es) = splitEvents-bs-valueFree es
splitEvents-bs-valueFree (complete  ∷ es) = splitEvents-bs-valueFree es

hasValue-++ : ∀ {A : Set} (xs ys : List (InstEvent A)) →
  hasValue xs ≡ false → hasValue ys ≡ false → hasValue (xs ++ ys) ≡ false
hasValue-++ []               ys hx hy = hy
hasValue-++ (value _   ∷ xs) ys ()  hy
hasValue-++ (init _    ∷ xs) ys hx hy = hasValue-++ xs ys hx hy
hasValue-++ (close _ _ ∷ xs) ys hx hy = hasValue-++ xs ys hx hy
hasValue-++ (handoff _ ∷ xs) ys hx hy = hasValue-++ xs ys hx hy
hasValue-++ (complete  ∷ xs) ys hx hy = hasValue-++ xs ys hx hy

hasValue-if-complete : ∀ {A : Set} (b : Bool) →
  hasValue {A = A} (if b then complete ∷ [] else []) ≡ false
hasValue-if-complete true  = refl
hasValue-if-complete false = refl

-- the cut's tail is empty, packaged for the one place that consumes it
cut-tail-nil : ∀ {n} {Γ : Ctx n} {s} (kCount : ℕ)
  (es : List (InstEvent (Val Γ s))) (i : Id) (src : Source) (ek : EmitKind)
  (ems : Stream Γ s) →
  proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)))) ≡ true →
  valsLast? ((es at i from src as ek) ∷ ems) ≡ true →
  ems ≡ []
cut-tail-nil {Γ = Γ} {s = s} kCount es i src ek ems dc vl
  with takeVals-cut-cons kCount (proj₁ (splitEvents {A = Val Γ s} es)) dc
... | v , vs′ , veq =
      valsLast-cut (es at i from src as ek) ems
        (splitEvents-vals-hasValue es v vs′ veq) vl

-- ── pushBurst through a take frame preserves the discipline ──────────────
-- A value-free emit hands the frame no values, so takeVals returns none — its
-- flag stays down, so such an emit can never BE the cut — and the re-emitted
-- events are pure bookkeeping: splitEvents' skeleton (which drops values by
-- construction) plus an optional `complete`.  So a burst whose payload rides its
-- last emit is pushed to a burst whose payload rides its last emit.  This is
-- what lets subscribeE-wf's Σ-conclusion carry valsLast? through takeᵉ.
pushBurst-take-valsLast : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
  (burst : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) (kCount : ℕ) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st kCount) →
  valsLast? burst ≡ true →
  valsLast? (proj₁ (pushBurst fuel id now (take-f nid) κ burst sched st)) ≡ true
pushBurst-take-valsLast fuel id now nid κ [] sched st kCount lk vl = refl
pushBurst-take-valsLast fuel id now nid κ (em ∷ []) sched st kCount lk vl = refl
pushBurst-take-valsLast {Γ = Γ} {e = e} {s = s}
  fuel id now nid κ ((es at i from src as ek) ∷ em′ ∷ ems) sched st kCount lk vl =
  subst (λ (b : Stream Γ s) → valsLast? b ≡ true) (sym red)
    (cong₂ _∧_ (cong not headFree)
      (pushBurst-take-valsLast fuel id now nid κ (em′ ∷ ems) sched ust rem′
        (lookupNode-setNode nid (take-st rem′) (EvalSt.nodes st))
        (proj₂ (∧-true _ _ vl))))
  where
  hv0 : hasValue es ≡ false
  hv0 = not-true _ (proj₁ (∧-true _ _ vl))

  nilv : proj₁ (splitEvents {A = Val Γ s} es) ≡ []
  nilv = splitEvents-noValue es hv0

  dc : proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)))) ≡ false
  dc = trans (cong (λ vs → proj₂ (proj₂ (takeVals kCount vs))) nilv)
             (takeVals-nil-flag kCount)

  valsNil : proj₁ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es))) ≡ []
  valsNil = trans (cong (λ vs → proj₁ (takeVals kCount vs)) nilv) (takeVals-nil kCount)

  rem′ : ℕ
  rem′ = proj₁ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es))))

  ust : EvalSt e
  ust = record st { nodes = setNode nid (take-st rem′) (EvalSt.nodes st) }

  red = pushBurst-take-noncut-cons fuel id now nid κ es i src ek (em′ ∷ ems) sched st kCount lk dc

  headFree : hasValue (proj₁ (proj₂ (splitEvents {A = Val Γ s} es))
                        ++ map value (proj₁ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es))))
                        ++ (if proj₂ (proj₂ (splitEvents {A = Val Γ s} es))
                            then complete ∷ [] else []))
             ≡ false
  headFree =
    hasValue-++ (proj₁ (proj₂ (splitEvents {A = Val Γ s} es))) _
      (splitEvents-bs-valueFree es)
      (subst (λ vs → hasValue (map value vs
                       ++ (if proj₂ (proj₂ (splitEvents {A = Val Γ s} es))
                           then complete ∷ [] else []))
                     ≡ false)
        (sym valsNil)
        (hasValue-if-complete (proj₂ (proj₂ (splitEvents {A = Val Γ s} es)))))

-- ── the take cut's residue: ONE emit ─────────────────────────────────────
-- RESOLVED 2026-07-26 — this is what replaced TailRel and the tail transport.
--
-- The shape this residue used to have was: cut head emit, THEN a value-stripped
-- tail re-run at the severed/done state.  That tail was the whole difficulty.
-- Running it needed a relation (TailRel) between the raw and the transformed
-- state, and TailRel's `acc-le` field — "the accumulator's still-open sources
-- survive on the transformed side" — turned out not to be constructible at the
-- cut: the cut closes PRECISELY the sources acc-le asserts stay live, so the two
-- sides wanted opposite things.  Measurement (2026-07-26) confirmed the
-- design note behind acc-le was simply false — cross-emit opens are NOT closed by
-- a later frame, the take cut closes them in the same burst — while also
-- reporting `cut with a tail` ≡ 0 across every corpus.
--
-- The invariant behind that zero is valsLast?, and it is stronger and simpler
-- than anything TailRel was reaching for: a burst carries its payload in its
-- LAST emit or not at all.  Values enter a burst at a leaf (one emit);
-- sharedConnect only PREPENDS a value-free `init` emit to its def's burst;
-- pushBurst is 1:1 on emits and cannot manufacture a payload out of none
-- (pushBurst-take-valsLast); an inner subscription's whole burst is flattened
-- into one emit by splitBurst.  A cut fires only on an emit that admitted values
-- (takeVals-cut-cons), so under valsLast? the cutting emit is the last one and
-- THERE IS NO TAIL.  cut-tail-nil is that argument in three lines.
--
-- MEASURED 2026-07-26 as counter 0 of the burst harness — with Rx.Protocol's valsLast?
-- itself, on every burst any subscribeE mints.  Depth 3 / depth 4, per corpus
-- (A: the plain generator; B: A with shared slots; C: 19 directed 2-slot
-- programs; C₃: 36 directed 3-slot ones — the original 26 plus 10 adversarial
-- programs targeting the thru-outer drain path specifically: sync-only inners
-- that trigger the drain during the connect burst itself, and scaled versions of
-- the deep *All nest that made corpus-B depth 5 expensive.  Bottom slot of C₃ is
-- a scripted cold so BOTH shares stay live past their connect — the only way to
-- put two live connects on one subscribe frame, which is the shape that would put
-- two payloads in one burst.  Directed corpora are independent of depth; all
-- three depth rows give the same 228 C₃ bursts):
--
--                          A            B          C        C₃
--   bursts d3/d4       2704/3415   3389/5194    86/86   228/228
--   bursts d5 (1 seed)      269         335        86       228
--   multi-emit bursts      0/  0     172/ 219    41/41    80/ 80
--   bursts with values  1717/2250   2147/3351    76/76   224/224
--   valsLast failures      0/  0       0/   0     0/ 0     0/  0
--   …with 2+ val emits     0/  0       0/   0     0/ 0     0/  0
--
-- Not one burst in ~14k had a payload anywhere but its last emit, and not one
-- had two payload-carrying emits at all.  `cut with a tail` is 0 for the same
-- reason, and is now visibly the consequence rather than the claim.
--
-- So the residue collapses to the head alone, and with it go TailRel, the
-- transport, and the frameFresh threading that existed only to keep the tail
-- honest.  (frameFresh? survives in Rx.Protocol as the probe's assertion; it has
-- no consumer in this file any more.)  What is left is exactly (H):
--   the reshaped cutting emit — bookkeeping, the cutThrough closes, the truncated
--   values, a forced `complete` — steps the protocol, and BurstInv is
--   re-established over the CUT registry/schedule.  Its closes are pre-paid by
--   cutThrough-balance against BurstInv.live-matches, which the joint induction
--   puts in scope here.  Mechanical off takeDispatch-cut; postulated while it is
--   written.
-- cut+sweep preserves registry well-typedness: kept ⊆ registry (cutThrough only
-- drops) and sweepLive only removes now-dead live sources (a conjunction shrink)
