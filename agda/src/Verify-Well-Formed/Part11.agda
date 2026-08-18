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
module Verify-Well-Formed.Part11 where

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

open import Verify-Well-Formed.Part10 public

seed-live-pos : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ ℕ λ k → countIn (arrSource a) (ProtocolSt.live S) ≡ suc k
seed-live-pos {a = a} {rid = rid} {p = p} {ps = ps} {st = st} mid ceq
  with Arrival.isLast a in isl | Mid.live-source mid
... | true  | lsm =
      countRemaining ps (EvalSt.cancelled st)
      , trans lsm (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
... | false | lsm =
      let (k , req) = countRegs-arrSrc-pos mid ceq isl in k , trans lsm req

-- the enter/pay seed fields: the automaton admits instant nextId and the
-- delivery pays arrSource — continuing the open owed (inj₂), or opening
-- fresh and seeding owed[arrSource] from the live count (inj₁)
seed-enter-pay : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ Owed λ ob → Σ Id λ hz → Σ Owed λ ob′ →
    (enterInstant S nextId ≡ just (ob , hz))
  × (settle delivery (arrSource a) (ProtocolSt.live S) ob ≡ just ob′)
  × (zeroExcept (arrSource a) ob′ ≡ true)
  × (UniqueOwed ob′ ≡ true)
seed-enter-pay {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq
  with Mid.ledger mid
... | inj₂ (ow , cur , lk , zx) =
      ow , ProtocolSt.horizon S , proj₁ pk
      , enterInstant-cont S nextId ow cur
          (lookup-pos-not-paidOff (arrSource a) ow _ lk-suc)
      , trans (settle-hit (arrSource a) (ProtocolSt.live S) ow
                (lookup-pos-hasOwed (arrSource a) ow _ lk-suc))
              (proj₁ (proj₂ pk))
      , zeroExcept-payOwed (arrSource a) ow (proj₁ pk) (proj₁ (proj₂ pk)) zx
      , UniqueOwed-payOwed (arrSource a) ow (proj₁ pk) (proj₁ (proj₂ pk))
          (Mid.owed-unique mid ow cur)
  where
  lk-suc : lookupOwed (arrSource a) ow ≡ suc (countRemaining ps (EvalSt.cancelled st))
  lk-suc = trans lk (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
  pk = payOwed-key (arrSource a) ow (countRemaining ps (EvalSt.cancelled st)) lk-suc
seed-enter-pay {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq
    | inj₁ (cp , paid) =
      [] , proj₁ ef , (arrSource a , k) ∷ []
      , proj₂ ef
      , trans (settle-miss (arrSource a) (ProtocolSt.live S) [] refl)
              (subst (λ c → payOwed (arrSource a) (bumpOwed (arrSource a) c [])
                              ≡ just ((arrSource a , k) ∷ []))
                     (sym ci-eq) (payOwed-seed (arrSource a) k))
      , ze′ , refl
  where
  ef = enterInstant-fresh S nextId cp paid (Mid.horizon-low mid)
  pos = seed-live-pos mid ceq
  k = proj₁ pos
  ci-eq : countIn (arrSource a) (ProtocolSt.live S) ≡ suc k
  ci-eq = proj₂ pos
  ze′ : zeroExcept (arrSource a) ((arrSource a , k) ∷ []) ≡ true
  ze′ rewrite ≡ᵇ-refl (arrSource a) = refl

-- THE seed: Mid (head ∷ ps) ⇒ FoldInv at the chainStep seed
mid-seed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  FoldInv nextId (arrSource a)
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched (record st { delivered = rid ∷ EvalSt.delivered st }) S
mid-seed {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq = record
  { ob = ob ; hz = hz ; ob′ = ob′ ; Lv = proj₁ ap ; Ov = ob′
  ; enters = enters ; pays = pays ; applies = proj₂ ap
  ; shadow = shadow
  ; reg-typed = Mid.reg-typed mid
  ; horizon-low = Mid.horizon-low mid
  ; ov-zero = ze′ ; ov-unique = uq′ ; ov-envSrc = refl
  ; env-init = env-init
  ; dying-envSrc = Mid.dying-src mid   -- dying (record st{delivered}) ≡ dying st
  }
  where
  ep = seed-enter-pay mid ceq
  ob  = proj₁ ep
  hz  = proj₁ (proj₂ ep)
  ob′ = proj₁ (proj₂ (proj₂ ep))
  enters = proj₁ (proj₂ (proj₂ (proj₂ ep)))
  pays   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ep))))
  ze′    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ep)))))
  uq′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ep)))))
  ap = seed-applies ob′ mid ceq
  -- for s ≠ arrSource the seed evs carry no init and (isLast) only an
  -- arrSource close, so initCount/closeCount vanish: SHADOW ⇔ live-others
  shadow : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      countIn s (ProtocolSt.live S)
        + initCount s (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    ≡ countRegs s (EvalSt.registry st)
        + closeCount s (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
  shadow s neq with Arrival.isLast a
  ... | false          = cong₂ _+_ (Mid.live-others mid s neq) refl
  ... | true rewrite neq = cong₂ _+_ (Mid.live-others mid s neq) refl
  -- the seed evs is (isLast) a lone envSrc close, else empty: no init either
  -- way, and its closeCount is exactly if isLast (= fin) then 1 else 0
  env-init : initCount (arrSource a)
      (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else []) ≡ 0
  env-init with Arrival.isLast a
  ... | false = refl
  ... | true  = refl

-- DECOMPOSITION BLUEPRINT (mid-step, the delivery-side sibling of
-- subscribeE-wf — "the per-clause preservation grind").  One surviving
-- chain's emits — its own delivery, any share fan-outs it triggers, any
-- cut closes — are accepted, paying/bumping/cancelling exactly per the
-- ledger.  The tower to grind, mirroring the evaluator's own recursion:
--
--   mid-step  ⇐  foldPath-wf  (induction on the Path)
--                ├─ root         : the chain's ONE delivery emit — the
--                │                  only place a linear path touches the
--                │                  protocol; frames merely accumulate
--                │                  evs/vals (they never step it)
--                ├─ f ↠ path′    : stepFrame-wf transforms the fold state
--                │                  (vals,evs,fin,sched,st) WITHOUT
--                │                  stepping the protocol, then the IH
--                │                  continues down path′ — the direct
--                │                  analog of subscribeE-wf's per-clause
--                │                  induction (map/scan/take/*All)
--                └─ share-sink i : one handoff emit, then dispatchShare-wf
--                                   (MUTUALLY RECURSIVE with foldPath-wf,
--                                   gas-structural) fans out to share i's
--                                   registrations — the handoff's owed
--                                   bump is repaid one-per-fan-out, so the
--                                   share subtree nets owed back to zero
--                                   (the diamond, batched by construction)
--
-- The missing piece is FoldInv — the mid-fold relation foldPath-wf is
-- stated over (BurstInv's delivery-side analog): unlike BurstInv's
-- literally-empty owed table, FoldInv carries the PARTIALLY-PAID open
-- instant (owed[envSrc] = the chain's own unpaid delivery; each pending
-- share bumped-then-being-repaid across its dispatch).  Once FoldInv is
-- pinned, mid-step is the chainStep seed (owed[arrSource] = the snapshot
-- remainder) plus reading Mid back off the FoldInv result.  Kept as ONE
-- postulate until FoldInv lands, so no half-stated (possibly-false) leaf
-- enters the development early — the whole point of the outside-in rule.
--
-- WHERE TO SPLIT (verified empirically, 2026-07): the Path-constructor
-- case split MUST live at foldPath-wf, which — like foldPath itself —
-- quantifies the chain's SOURCE type `u` FREELY (path : Path Γ u t).
-- It CANNOT live at mid-step, where the source type is pinned to the
-- stuck projection `arrTy a`: matching `share-sink i : Path Γ (lookup Γ i) t`
-- there demands `lookup Γ i ≡ arrTy a`, which Agda's unifier rejects
-- (two neutrals), so `mid-step {p = share-sink i} = …` will not even
-- typecheck (root and `f ↠ path′` do — only share-sink clashes).  With a
-- free `u`, matching share-sink cleanly sets `u := lookup Γ i`.  So:
-- mid-step invokes foldPath-wf at `u := arrTy a` with the seed; the
-- three-way induction (root / frame / share) is foldPath-wf's own.
--
-- STATE OF THE DECOMPOSITION (2026-07):
--   PRE   mid-seed : Mid (head∷ps) ⇒ FoldInv              — PROVEN
--   MID   foldPath-wf : FoldInv ⇒ Σ S′, runProtocol ≡ S′  — PROVEN
--           (modulo the two structural leaves stepFrame-wf / dispatchShare-wf,
--            postulated exactly as subscribeE-wf is on the burst side)
--   POST  readoff : … ⇒ Mid ps                            — the remaining gap
--
-- THE READOFF, precisely.  mid-step must return `Mid a nextId ps st″ sched″ S′`
-- where (·,sched″,st″) = chainStep …, and S′ is foldPath-wf's accepted state.
-- Its eight fields all reference st″/sched″/S′, so the readoff needs a
-- CHARACTERISATION of the fold's output triple, not merely `∃ S′`.  For the
-- ROOT case that characterisation is already in hand — foldPath-root-wf pins
-- S′ = record{live=Lv; horizon=hz; current=just(nextId,Ov); done= if fin then
-- true else done S}, and foldPath root leaves the EvalSt untouched, so
-- st″ = record st{delivered=…} (registry st″ ≡ registry st, sched″ ≡ sched).
-- That is the proven anchor to read the root chain's Mid ps off.
--
-- The obstruction is that the SAME `arrTy a` pinning that forces the case
-- split into foldPath-wf also forbids a standalone post-hoc readoff on `p`:
-- Mid ps must be reconstructed by the SAME path induction, so foldPath-wf's
-- CONCLUSION has to carry the readoff data — a `FoldOut` companion to FoldInv,
-- quantified over the free `u`, threaded through root (proven, above),
-- f ↠ path′ (stepFrame-wf, enriched), and share-sink (dispatchShare-wf,
-- enriched).  FoldOut is a genuinely NEW invariant: what a PARTIAL chain fold
-- preserves of the live↔registry shadow.  It is deliberately NOT yet stated —
-- an imprecise FoldOut would be a FALSE postulate (forbidden), and unlike the
-- done-plumbed window below it is not yet pinned down, so it is left as the
-- single mid-step postulate until its shape is settled with care.
--
-- done-plumbed in the readoff (RESOLVED 2026-07): a completing isLast root
-- chain flips done S′≡true while its own non-share-sunk registration is still
-- in registry st″ (dropped only at cascadeFinish).  Handled by the conditional
-- restatement of Mid/FoldInv.done-plumbed (drop arrSource iff isLast) — see
-- those fields.  The readoff's isLast-root obligation, allShareSunk(dropSource
-- arrSource registry st″), then holds BECAUSE at the flip every non-share-sunk
-- survivor belongs to arrSource (fin reaches root only once nothing else can
-- deliver).  GUARD: should a reachable flip ever leave a NON-arrival source
-- holding a root-sinking registration, that falsifies Inv.done-plumbed itself
-- (a completion emitted while something could still deliver — an evaluator
-- bug); STOP and surface the trace, do not patch around it.
-- ════════════════════════════════════════════════════════════════
-- foldPath-out — the FoldOut companion the blueprint above calls for
-- ════════════════════════════════════════════════════════════════
-- The blueprint says the readoff cannot be done post-hoc on `p` (the
-- `arrTy a` pinning makes share-sink unmatchable at mid-step), so
-- "foldPath-wf's CONCLUSION has to carry the readoff data".  This is
-- that statement: foldPath-wf's run equation AND the FoldOut, over the
-- FREE `u` where the Path constructors are matchable.
--
-- Its ROOT arm is PROVEN, and proving it is what gives
-- `foldPath-root-out` a consumer that reduces.  The other two arms are
-- leaves, so this is a 1-of-3 discharge and not a proof of the fold.
postulate
  -- FRAME arm, NOW THE FoldOut ONLY (2026-08-18).  The run equation is
  -- not this leaf's to prove: `foldPath-wf` (.Part9) already proves it
  -- for EVERY path constructor, by the same `stepFrame-wf` + IH
  -- induction this arm was restating — so as posed it was a second
  -- proof of a proven fact, and `foldPath-wf` had no consumer at all.
  -- It now takes the run's own S′ and the equation that pins it, and
  -- owes only the readoff.  What is left is genuinely the blueprint's
  -- "stepFrame-wf, enriched": FoldOut's fields are keyed on `foldSt`/
  -- `foldSched` at the OUTER path, and the flip/steady certificates
  -- speak of the CURRENT (fin, st) which stepFrame rewrites.
  foldPath-frame-out : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {w u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (f : Frame Γ w u) (path′ : Path Γ u t)
    (vals : List (Val Γ w)) (evs : List (InstEvent (Val Γ t)))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
    (fi : FoldInv id envSrc evs fin sched st S) →
    (ProtocolSt.done S ≡ true → sinksToShare path′ ≡ true) →
    ((if fin then true else ProtocolSt.done S) ≡ true → ProtocolSt.done S ≡ false →
       allShareSunk (dropSource envSrc (EvalSt.registry st)) ≡ true) →
    (ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true) →
    (S′ : ProtocolSt) →
    runProtocol S (proj₁ (foldPath sf gas id now envSrc (f ↠ path′) vals evs fin sched st))
      ≡ just S′ →
    FoldOut sf gas id now envSrc (f ↠ path′) vals evs fin sched st (FoldInv.ob′ fi) S S′

  -- SHARE arm, NOW THE FoldOut ONLY (2026-08-18).  The handoff emit plus
  -- one delivery per registration of share i, each its own foldPath.  As
  -- posed this arm re-proved the run equation that `dispatchShare-wf`
  -- (.Part9) already owes — two postulates for one obligation — so it
  -- now takes S′ and the equation from `foldPath-wf` and owes only the
  -- FoldOut, the diamond's net-zero owed statement.
  foldPath-share-out : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (evs : List (InstEvent (Val Γ t)))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
    (fi : FoldInv id envSrc evs fin sched st S) →
    ((if fin then true else ProtocolSt.done S) ≡ true → ProtocolSt.done S ≡ false →
       allShareSunk (dropSource envSrc (EvalSt.registry st)) ≡ true) →
    (ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true) →
    (S′ : ProtocolSt) →
    runProtocol S (proj₁ (foldPath sf gas id now envSrc (share-sink i) vals evs fin sched st))
      ≡ just S′ →
    FoldOut sf gas id now envSrc (share-sink i) vals evs fin sched st (FoldInv.ob′ fi) S S′

foldPath-out : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
  (fi : FoldInv id envSrc evs fin sched st S) →
  (ProtocolSt.done S ≡ true → sinksToShare path ≡ true) →
  ((if fin then true else ProtocolSt.done S) ≡ true → ProtocolSt.done S ≡ false →
     allShareSunk (dropSource envSrc (EvalSt.registry st)) ≡ true) →
  (ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true) →
  Σ ProtocolSt λ S′ →
    (runProtocol S (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st))
       ≡ just S′)
    × FoldOut sf gas id now envSrc path vals evs fin sched st (FoldInv.ob′ fi) S S′
foldPath-out sf gas id now envSrc root vals evs fin sched st S fi ds flip steady =
  _ , foldPath-root-wf sf gas id now envSrc vals evs fin sched st S
        (FoldInv.ob fi) (FoldInv.hz fi) (FoldInv.ob′ fi) (FoldInv.Lv fi) (FoldInv.Ov fi)
        (FoldInv.enters fi) (FoldInv.pays fi) (FoldInv.applies fi) done-nil
    , foldPath-root-out sf gas id now envSrc vals evs fin sched st S fi flip steady
  where
  -- root does not sink to a share, so `ds` forces the automaton not-done
  -- and the value list rides (foldPath-wf's own root argument)
  df : ProtocolSt.done S ≡ false
  df = force-false (ProtocolSt.done S) ds
  done-nil : ProtocolSt.done S ≡ true → vals ≡ []
  done-nil deq with trans (sym df) deq
  ... | ()
foldPath-out sf gas id now envSrc (f ↠ path′) vals evs fin sched st S fi ds flip steady =
  proj₁ W , proj₂ W
  , foldPath-frame-out sf gas id now envSrc f path′ vals evs fin sched st S fi
      ds flip steady (proj₁ W) (proj₂ W)
  where
  W = foldPath-wf sf gas id now envSrc (f ↠ path′) vals evs fin sched st S fi ds
foldPath-out sf gas id now envSrc (share-sink i) vals evs fin sched st S fi ds flip steady =
  proj₁ W , proj₂ W
  , foldPath-share-out sf gas id now envSrc i vals evs fin sched st S fi
      flip steady (proj₁ W) (proj₂ W)
  where
  W = foldPath-wf sf gas id now envSrc (share-sink i) vals evs fin sched st S fi ds

-- ════════════════════════════════════════════════════════════════
-- THE Mid TRANSITION, ASSEMBLED — a real body over three leaves
-- ════════════════════════════════════════════════════════════════
-- The former route list was wrong about itself: FOUR of the six alleged
-- ingredients are not ingredients at all.  `mid-enters`,
-- `enterInstant-idle`, `enterInstant-held` and `paidUp-held` are
-- subsumed by what the real chain already goes through —
-- `seed-enter-pay` reaches the automaton via `enterInstant-cont` and
-- `enterInstant-fresh`, and the latter uses the `-aux` forms directly —
-- so those four were second proofs of facts already proven, kept alive
-- only by appearing in a `-core`'s hypothesis list.  They are deleted;
-- `git show` carries them.  See CLAUDE.md, "A POSTULATE MUST BE A LEAF":
-- a `-core`'s hypothesis list is a hypothesis about the route, not a
-- specification.
--
-- What the assembly actually spends: `mid-seed` (Mid ⇒ FoldInv at the
-- chainStep seed) and, through `foldPath-out` above, `foldPath-root-out`.
postulate
  -- The three certificates the fold demands of the arrival, all of them
  -- near-restatements of `Mid.done-plumbed` — which is stated with the
  -- `if isLast` conditional (drop arrSource iff isLast) while the fold
  -- wants the plain and the dropped registry separately.  Bundled
  -- because they are one case split on `Arrival.isLast a`, not three
  -- independent facts.  The blueprint's GUARD applies to the middle
  -- one: a reachable flip leaving a NON-arrival source holding a
  -- root-sinking registration falsifies Inv.done-plumbed itself — an
  -- evaluator bug, to surface rather than patch around.
  mid-fold-certs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
    {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
    {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
    {S : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    (ProtocolSt.done S ≡ true → sinksToShare p ≡ true)
    × ((if Arrival.isLast a then true else ProtocolSt.done S) ≡ true →
         ProtocolSt.done S ≡ false →
         allShareSunk (dropSource (arrSource a) (EvalSt.registry st)) ≡ true)
    × (ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true)

  -- THE READOFF, the blueprint's remaining POST: rebuild `Mid ps` from
  -- the fold's FoldOut.  Its eight fields all reference the OUTPUT
  -- triple, which is exactly what FoldOut characterises — so this leaf
  -- is field-by-field bookkeeping over a FoldOut now in hand, not the
  -- path induction (that is foldPath-out's).
  mid-readoff : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
    {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
    {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
    {S S′ : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    (fi : FoldInv nextId (arrSource a)
            (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
            (Arrival.isLast a) sched (record st { delivered = rid ∷ EvalSt.delivered st }) S) →
    FoldOut (budgetAt e (Sched.slots sched) nextId) n nextId (arrTick a) (arrSource a)
      p (arrVal a ∷ [])
      (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
      (Arrival.isLast a) sched (record st { delivered = rid ∷ EvalSt.delivered st })
      (FoldInv.ob′ fi) S S′ →
    (let r = chainStep nextId a p sched
               (record st { delivered = rid ∷ EvalSt.delivered st })
     in Mid a nextId ps (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′)

mid-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id} {rid : RegId}
  {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = chainStep nextId a p sched
              (record st { delivered = rid ∷ EvalSt.delivered st })
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Mid a nextId ps (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
mid-step {n = n} {e = e} {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq =
  let fi    = mid-seed mid ceq
      certs = mid-fold-certs mid ceq
      (S′ , run , fo) =
        foldPath-out (budgetAt e (Sched.slots sched) nextId) n nextId
          (arrTick a) (arrSource a) p (arrVal a ∷ [])
          (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
          (Arrival.isLast a) sched (record st { delivered = rid ∷ EvalSt.delivered st })
          S fi (proj₁ certs) (proj₁ (proj₂ certs)) (proj₂ (proj₂ certs))
  in S′ , run , mid-readoff mid ceq fi fo

-- a cancelled head contributes nothing to countRemaining (the `if`
-- takes the then-branch)
cr-skip : ∀ {X : Set} (rid : RegId) (x : X)
          (ps : List (RegId × X)) (c : List RegId) →
          any (_≡ᵇ rid) c ≡ true →
          countRemaining ((rid , x) ∷ ps) c ≡ countRemaining ps c
cr-skip rid x ps c h rewrite h = refl

-- and nothing to cascadeGo: its first clause skips a cancelled head
-- outright, folding the tail with the SAME state (two-column trick —
-- cascadeGo's `with` won't unfold under rewrite)
cascadeGo-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id) (rid : RegId)
  (p : Path Γ (arrTy a) t) (ps : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  cascadeGo {e = e} a nextId ((rid , p) ∷ ps) sched st
    ≡ cascadeGo {e = e} a nextId ps sched st
cascadeGo-skip a nextId rid p ps sched st ceq
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | ceq
... | true | refl = refl

-- a cancelled chain folds to nothing (its close already rode the
-- cutting emit; its owed was forgiven right there): every Mid field is
-- stable when the snapshot head drops, given the head is cancelled
mid-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id} {rid : RegId}
  {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  Mid a nextId ps sched st S
mid-skip {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq = record
  { live-others  = Mid.live-others mid
  ; live-source  = trans (Mid.live-source mid)
      (cong (λ z → if Arrival.isLast a then z
                   else countRegs (arrSource a) (EvalSt.registry st))
            (cr-skip rid p ps (EvalSt.cancelled st) ceq))
  ; reg-typed    = Mid.reg-typed mid       -- same sched, st
  ; horizon-low  = Mid.horizon-low mid
  ; hot-live     = Mid.hot-live mid        -- same sched
  ; ledger       = ledger′
  ; done-plumbed = Mid.done-plumbed mid
  ; caches       = trans (sym (cachesValidMid-skip a rid p ps (EvalSt.nodes st) st ceq))
                         (Mid.caches mid)
  ; fold-live    = subst (λ z → hasDry (proj₁ z) ≡ false)
      (cascadeGo-skip a nextId rid p ps sched st ceq)
      (Mid.fold-live mid)
  ; owed-unique  = Mid.owed-unique mid      -- same S, nextId
  ; dying-src    = Mid.dying-src mid         -- same st
  ; reg-bound    = subst (λ z → z ≤ countRegs (arrSource a) (EvalSt.registry st))
                     (cr-skip rid p ps (EvalSt.cancelled st) ceq)
                     (Mid.reg-bound mid)    -- drop cancelled head, count unchanged
  }
  where
  ledger′ :
      (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
    ⊎ (Σ Owed λ ow →
         (ProtocolSt.current S ≡ just (nextId , ow))
       × (lookupOwed (arrSource a) ow
            ≡ countRemaining ps (EvalSt.cancelled st))
       × (zeroExcept (arrSource a) ow ≡ true))
  ledger′ with Mid.ledger mid
  ... | inj₁ x                    = inj₁ x
  ... | inj₂ (ow , cur , lk , zx) =
        inj₂ (ow , cur
             , trans lk (cr-skip rid p ps (EvalSt.cancelled st) ceq)
             , zx)

------------------------------------------------------------------
-- mid-final: leaving the cascade.  Bool/ℕ glue first, then registry
-- lemmas for the finish sweep, then the assembly.
------------------------------------------------------------------

-- a key absent from the table reads zero
lookupOwed-absent : ∀ (s : Source) (o : Owed) →
  notKeyOwed s o ≡ true → lookupOwed s o ≡ 0
lookupOwed-absent s []            _ = refl
lookupOwed-absent s ((x , n) ∷ o) h with s ≡ᵇ x | h
... | false | h′ = lookupOwed-absent s o h′
... | true  | h′ = true≢false (sym h′)

-- with unique keys, zeroExcept + a zero at s forces the whole table
-- zero.  `with s ≡ᵇ x in seq` rewrites ze/lk in each branch: at the key
-- (true) lk reads n ≡ 0 and ze drops to the tail; off-key (false) ze's
-- head gives n ≡ᵇ 0 and lk passes to the tail
allZero-clean : ∀ (s : Source) (o : Owed) →
  UniqueOwed o ≡ true → zeroExcept s o ≡ true → lookupOwed s o ≡ 0 →
  allZero o ≡ true
allZero-clean s []            _  _  _  = refl
allZero-clean s ((x , n) ∷ o) uq ze lk with s ≡ᵇ x in seq
... | true  =
      subst (λ m → allZero ((x , m) ∷ o) ≡ true) (sym lk)
        (allZero-clean s o (∧-trueʳ uq) ze
          (lookupOwed-absent s o
            (subst (λ z → notKeyOwed z o ≡ true)
                   (sym (≡ᵇ→≡ s x seq)) (∧-trueˡ uq))))
... | false =
      subst (λ m → allZero ((x , m) ∷ o) ≡ true)
            (sym (≡ᵇ→≡ n 0 (∧-trueˡ ze)))
        (allZero-clean s o (∧-trueʳ uq) (∧-trueʳ ze) lk)

-- an all-zero owed table settles: paidUp holds
paid-allzero : (S : ProtocolSt) {j : Id} {ow : Owed} →
  ProtocolSt.current S ≡ just (j , ow) → allZero ow ≡ true → paidUp S ≡ true
paid-allzero S ceq az with ProtocolSt.current S | ceq
... | just (j , ow) | refl rewrite az = refl

-- CurrentPast only weakens as the bound grows
currentPast-up : (c : Maybe (Id × Owed)) (N : Id) →
  CurrentPast c N → CurrentPast c (suc N)
currentPast-up nothing        N cp = tt
currentPast-up (just (j , _)) N cp = ≤-up cp

-- registry sweep: dropping s zeroes s's own count and leaves others'
dropSource-self : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  countRegs s (dropSource s reg) ≡ 0
dropSource-self s []                  = refl
dropSource-self s ((rid , x , c) ∷ r) with s ≡ᵇ x in eq
... | true             = dropSource-self s r
... | false rewrite eq = dropSource-self s r
