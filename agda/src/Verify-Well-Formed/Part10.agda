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
module Verify-Well-Formed.Part10 where

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

open import Verify-Well-Formed.Part9 public

lookup-pos-not-paidOff : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → paidOff ow ≡ false
lookup-pos-not-paidOff s [] k ()
lookup-pos-not-paidOff s (e ∷ ow) k eq = lookup-pos-not-allZero s (e ∷ ow) k eq

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true _ = refl

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → (m ≤ᵇ n) ≡ true
≤→≤ᵇ {m} {n} p = T→≡ (m ≤ᵇ n) (≤⇒≤ᵇ p)

-- the automaton admits an OPEN unpaid instant: enterInstant continues it,
-- seeding go with the running owed and the standing horizon.  Fields taken
-- literally so enterInstant's `with current` reduces (enterInstant reads
-- only current/horizon, never live/done, so the dummies are harmless)
enterInstant-cont-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) (ow : Owed) →
  cur ≡ just (i , ow) → paidOff ow ≡ false →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just (ow , hz)
enterInstant-cont-aux lv hz i .(just (i , ow)) dn ow refl pf rewrite ≡ᵇ-refl i | pf = refl

enterInstant-cont : ∀ (S : ProtocolSt) (i : Id) (ow : Owed) →
  ProtocolSt.current S ≡ just (i , ow) → paidOff ow ≡ false →
  enterInstant S i ≡ just (ow , ProtocolSt.horizon S)
enterInstant-cont S i ow cur pf =
  enterInstant-cont-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i
    (ProtocolSt.current S) (ProtocolSt.done S) ow cur pf

-- a strictly-greater id is not equal (for the held instant's i ≢ j)
≢ᵇ-from-< : ∀ {j i : ℕ} → j ≤ i → (suc i ≡ᵇ j) ≡ false
≢ᵇ-from-< z≤n     = refl
≢ᵇ-from-< (s≤s q) = ≢ᵇ-from-< q

sucle→≢ᵇ : ∀ {j nextId : ℕ} → suc j ≤ nextId → (nextId ≡ᵇ j) ≡ false
sucle→≢ᵇ (s≤s q) = ≢ᵇ-from-< q

-- the automaton opens FRESH over an idle slot: settleInstant is the
-- standing horizon, admitted once horizon ≤ i
enterInstant-idle-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) → cur ≡ nothing → (hz ≤ᵇ i) ≡ true →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just ([] , hz)
enterInstant-idle-aux lv hz i .nothing dn refl hle rewrite hle = refl


-- the automaton opens FRESH over a HELD paid instant j (i ≢ j): the
-- departed instant pushes the horizon to suc j, admitted once suc j ≤ i
enterInstant-held-aux : ∀ (lv : List Source) (hz i j : Id) (cur : Maybe (Id × Owed))
  (ow : Owed) (dn : Bool) → cur ≡ just (j , ow) →
  (i ≡ᵇ j) ≡ false → allZero ow ≡ true → (suc j ≤ᵇ i) ≡ true →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just ([] , suc j)
enterInstant-held-aux lv hz i j .(just (j , ow)) ow dn refl ieq az sle
  rewrite ieq | az | sle = refl


-- a paid automaton holding instant j has that instant's owed all-zero
-- (else settleInstant would reject and paidUp be false)
paidUp-held-aux : ∀ (lv : List Source) (hz : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) (j : Id) (ow : Owed) → cur ≡ just (j , ow) →
  paidUp (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ true →
  allZero ow ≡ true
paidUp-held-aux lv hz .(just (j , ow)) dn j ow refl pu with allZero ow | pu
... | true  | _  = refl
... | false | ()


-- the fresh-open entry, dispatched on the (explicit) current value so
-- enterInstant reduces: idle when the slot is empty, held over a paid
-- departed instant j.  Both need only that the horizon (standing, or the
-- pushed suc j) does not exceed nextId.
enterInstant-fresh-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) → CurrentPast cur i →
  paidUp (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ true →
  hz ≤ i →
  Σ Id λ hz′ →
    enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
      ≡ just ([] , hz′)
enterInstant-fresh-aux lv hz i nothing dn cp pu hle =
  hz , enterInstant-idle-aux lv hz i nothing dn refl (≤→≤ᵇ hle)
enterInstant-fresh-aux lv hz i (just (j , ow)) dn cp pu hle =
  suc j , enterInstant-held-aux lv hz i j (just (j , ow)) ow dn refl
    (sucle→≢ᵇ cp) (paidUp-held-aux lv hz (just (j , ow)) dn j ow refl pu) (≤→≤ᵇ cp)

enterInstant-fresh : ∀ (S : ProtocolSt) (i : Id) →
  CurrentPast (ProtocolSt.current S) i → paidUp S ≡ true → ProtocolSt.horizon S ≤ i →
  Σ Id λ hz′ → enterInstant S i ≡ just ([] , hz′)
enterInstant-fresh S i cp pu hle =
  enterInstant-fresh-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i
    (ProtocolSt.current S) (ProtocolSt.done S) cp pu hle

-- an uncancelled snapshot head is one more obligation than its tail
cr-fresh : ∀ {X : Set} (rid : RegId) (x : X) (ps : List (RegId × X)) (c : List RegId) →
  any (_≡ᵇ rid) c ≡ false → countRemaining ((rid , x) ∷ ps) c ≡ suc (countRemaining ps c)
cr-fresh rid x ps c h rewrite h = refl

------------------------------------------------------------------
-- The pay/applyEvents seed fields turn on decrementing a key: paying a
-- positive owed key drops it by one; removing a present live source
-- drops its count by one.  Small hit/miss reductions feed the two.
------------------------------------------------------------------

suc-inj : ∀ {m k : ℕ} → suc m ≡ suc k → m ≡ k
suc-inj refl = refl

lookupOwed-hit : ∀ (s x : Source) (n : ℕ) (o : Owed) →
  (s ≡ᵇ x) ≡ true → lookupOwed s ((x , n) ∷ o) ≡ n
lookupOwed-hit s x n o sx with s ≡ᵇ x | sx
... | true | refl = refl

lookupOwed-miss : ∀ (s x : Source) (n : ℕ) (o : Owed) →
  (s ≡ᵇ x) ≡ false → lookupOwed s ((x , n) ∷ o) ≡ lookupOwed s o
lookupOwed-miss s x n o sx with s ≡ᵇ x | sx
... | false | refl = refl

-- draining evs into Lv moves each source's count by initCount ∸ closeCount
-- (additive form, no monus): the counting core of the live readoff
applyEvents-count : ∀ {A : Set} (evs : List (InstEvent A)) (lv : List Source)
  (o : Owed) (d : Bool) {Lv : List Source} {Ov : Owed} {d′ : Bool} (s : Source) →
  applyEvents evs lv o d ≡ just (Lv , Ov , d′) →
  countIn s Lv + closeCount s evs ≡ countIn s lv + initCount s evs
applyEvents-count [] lv o d s eq with just-injᵂ eq
... | refl = refl
applyEvents-count (init x ∷ es) lv o d s eq with s ≡ᵇ x in sx
... | true  = trans (applyEvents-count es (x ∷ lv) o d s eq)
                    (trans (cong (_+ initCount s es) (countIn-hit s x lv sx))
                           (sym (+-suc (countIn s lv) (initCount s es))))
... | false = trans (applyEvents-count es (x ∷ lv) o d s eq)
                    (cong (_+ initCount s es) (countIn-miss s x lv sx))
applyEvents-count (value v ∷ es) lv o d s eq with d | eq
... | false | eq′ = applyEvents-count es lv o false s eq′
... | true  | ()
applyEvents-count (handoff x ∷ es) lv o d s eq =
  applyEvents-count es lv (bumpOwed x (countIn x lv) o) d s eq
applyEvents-count (complete ∷ es) lv o d s eq =
  applyEvents-count es lv o true s eq
applyEvents-count (close x cutPending ∷ es) lv o d {Lv} s eq
  with removeOne x lv in rmv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ =
      close-count x s lv lv′ Lv es rmv (applyEvents-count es lv′ o′ d s eq′)
... | just lv′ | nothing | ()
... | nothing  | just o′ | ()
... | nothing  | nothing | ()
applyEvents-count (close x cut ∷ es) lv o d {Lv} s eq with removeOne x lv in rmv | eq
... | just lv′ | eq′ = close-count x s lv lv′ Lv es rmv (applyEvents-count es lv′ o d s eq′)
... | nothing  | ()
applyEvents-count (close x exhausted ∷ es) lv o d {Lv} s eq with removeOne x lv in rmv | eq
... | just lv′ | eq′ = close-count x s lv lv′ Lv es rmv (applyEvents-count es lv′ o d s eq′)
... | nothing  | ()
applyEvents-count (close x dried ∷ es) lv o d {Lv} s eq with removeOne x lv in rmv | eq
... | just lv′ | eq′ = close-count x s lv lv′ Lv es rmv (applyEvents-count es lv′ o d s eq′)
... | nothing  | ()

-- the live-others readoff: applyEvents drains the pending evs into live,
-- and SHADOW (registry leads live by the pending evs' init∸close) then
-- resyncs to a plain live ≡ registry read.  The keystone use of
-- applyEvents-count + SHADOW, with the shared closeCount cancelled off.
readoff-cancel : ∀ {A : Set} (s : Source) (evs : List (InstEvent A))
  (liveS Lv : List Source) (ob′ Ov : Owed) (dn d′ : Bool) (R : ℕ) →
  applyEvents evs liveS ob′ dn ≡ just (Lv , Ov , d′) →
  countIn s liveS + initCount s evs ≡ R + closeCount s evs →
  countIn s Lv ≡ R
readoff-cancel s evs liveS Lv ob′ Ov dn d′ R apEq shEq =
  +-cancelʳ-≡ (closeCount s evs) (countIn s Lv) R
    (trans (applyEvents-count evs liveS ob′ dn s apEq) shEq)

-- foldPath-root-out: the ROOT clause's FoldOut readoff.  At root foldSt = st and
-- foldSched = sched (Evaluator 960-962), so six fields read STRAIGHT off FoldInv:
--   live-others  = readoff-cancel ∘ SHADOW (drains evs into live, cancels closeCount)
--   live-envSrc  = applyEvents-count at envSrc + env-init/env-close (∸ if fin then 1)
--   reg-envSrc   = refl (st″ = st)          reg-typed = FoldInv.reg-typed
--   horizon      = enterInstant-hz≤id ∘ horizon-low
--   current      = FoldInv.ov-zero/ov-unique/ov-envSrc (Ov = the applies output)
-- The two plumbing fields take the completion certificate / steady form as
-- hypotheses — the residual obligations the frame recursion (from-inner's
-- aliveThrough certificate) and a thru-outer node↔registry coherence field will
-- discharge.  This VALIDATES the FoldOut field statements (all inhabited).
foldPath-root-out : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (vals : List (Val Γ t)) (evs : List (InstEvent (Val Γ t)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
  (fi : FoldInv id envSrc evs fin sched st S) →
  -- FLIP certificate: completion reached root (done S′ ≡ true) from not-yet-done
  ((if fin then true else ProtocolSt.done S) ≡ true → ProtocolSt.done S ≡ false →
     allShareSunk (dropSource envSrc (EvalSt.registry st)) ≡ true) →
  -- STEADY: an already-done registry is fully plumbed
  (ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true) →
  FoldOut sf gas id now envSrc root vals evs fin sched st (FoldInv.ob′ fi) S
    (record { live = FoldInv.Lv fi ; horizon = FoldInv.hz fi
            ; current = just (id , FoldInv.Ov fi)
            ; done = if fin then true else ProtocolSt.done S })
foldPath-root-out sf gas id now envSrc vals evs fin sched st S fi flip-cert steady = record
  { live-others-out = λ s neq →
      readoff-cancel s evs (ProtocolSt.live S) (FoldInv.Lv fi) (FoldInv.ob′ fi) (FoldInv.Ov fi)
        (ProtocolSt.done S) (ProtocolSt.done S) (countRegs s (EvalSt.registry st))
        (FoldInv.applies fi) (FoldInv.shadow fi s neq)
  ; live-envSrc-out = live-env
  ; reg-envSrc-out = refl
  ; reg-typed-out = FoldInv.reg-typed fi
  ; horizon-out = enterInstant-hz≤id S id (FoldInv.enters fi) (FoldInv.horizon-low fi)
  ; current-out = FoldInv.Ov fi , refl , FoldInv.ov-zero fi , FoldInv.ov-unique fi
                , FoldInv.ov-envSrc fi
  ; flip-plumbed-out = λ dneq dS′ → flip-cert dS′ dneq
  ; done-plumbed-out = steady
  }
  where
  -- envSrc drains by closeCount: applyEvents-count at envSrc gives
  -- countIn Lv + closeCount ≡ countIn (live S) + initCount, and env-init kills
  -- the init term, leaving the ∸ closeCount readoff by m+n∸n≡m.
  ac : countIn envSrc (FoldInv.Lv fi) + closeCount envSrc evs
     ≡ countIn envSrc (ProtocolSt.live S) + initCount envSrc evs
  ac = applyEvents-count evs (ProtocolSt.live S) (FoldInv.ob′ fi) (ProtocolSt.done S)
         envSrc (FoldInv.applies fi)
  eq : countIn envSrc (FoldInv.Lv fi) + closeCount envSrc evs
     ≡ countIn envSrc (ProtocolSt.live S)
  eq = trans (subst (λ z → countIn envSrc (FoldInv.Lv fi) + closeCount envSrc evs
                             ≡ countIn envSrc (ProtocolSt.live S) + z) (FoldInv.env-init fi) ac)
             (+-identityʳ (countIn envSrc (ProtocolSt.live S)))
  live-env : countIn envSrc (FoldInv.Lv fi)
           ≡ countIn envSrc (ProtocolSt.live S) ∸ closeCount envSrc evs
  live-env = trans (sym (m+n∸n≡m (countIn envSrc (FoldInv.Lv fi)) (closeCount envSrc evs)))
                   (cong (_∸ closeCount envSrc evs) eq)

-- paying the key with positive owed decrements it by one (once the `with`
-- fixes s ≡ᵇ x, payOwed/removeOne on the head reduce, so the equations are
-- refl / rewrite; the constructed tail term still needs the hit/miss read)
payOwed-key : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k →
  Σ Owed λ ow′ → (payOwed s ow ≡ just ow′) × (lookupOwed s ow′ ≡ k)
payOwed-key s [] k ()
payOwed-key s ((x , n) ∷ o) k eq with s ≡ᵇ x in sx
... | true with n | eq
...   | suc m | refl = (x , m) ∷ o , refl , lookupOwed-hit s x m o sx
payOwed-key s ((x , n) ∷ o) k eq | false
  with payOwed-key s o k eq
... | o′ , po , lk rewrite po =
      (x , n) ∷ o′ , refl , trans (lookupOwed-miss s x n o′ sx) lk

-- payOwed changes only the VALUE at key s (keys unchanged), so it
-- preserves both zeroExcept s (which ignores s's own value) and
-- UniqueOwed (keys drive both).  These carry the seed's owed shape
-- (zeroExcept + unique) through the settle into ob′ = FoldInv.Ov.
zeroExcept-payOwed : ∀ (s : Source) (ow ow′ : Owed) →
  payOwed s ow ≡ just ow′ → zeroExcept s ow ≡ true → zeroExcept s ow′ ≡ true
zeroExcept-payOwed s [] ow′ () ze
zeroExcept-payOwed s ((x , n) ∷ o) ow′ eq ze with s ≡ᵇ x in sx
... | true with n | eq
...   | zero  | ()
...   | suc m | refl rewrite sx = ze
zeroExcept-payOwed s ((x , n) ∷ o) ow′ eq ze | false
  with payOwed s o in po | eq
... | just o′ | refl rewrite sx =
      ∧-intro (∧-trueˡ ze) (zeroExcept-payOwed s o o′ po (∧-trueʳ ze))

-- payOwed preserves every key, hence notKeyOwed z reads the same after it
payOwed-notKey : ∀ (s z : Source) (ow ow′ : Owed) →
  payOwed s ow ≡ just ow′ → notKeyOwed z ow ≡ notKeyOwed z ow′
payOwed-notKey s z [] ow′ ()
payOwed-notKey s z ((x , n) ∷ o) ow′ eq with s ≡ᵇ x
... | true with n | eq
...   | zero  | ()
...   | suc m | refl = refl
payOwed-notKey s z ((x , n) ∷ o) ow′ eq | false
  with payOwed s o in po | eq
... | just o′ | refl = cong (λ b → not (z ≡ᵇ x) ∧ b) (payOwed-notKey s z o o′ po)

UniqueOwed-payOwed : ∀ (s : Source) (ow ow′ : Owed) →
  payOwed s ow ≡ just ow′ → UniqueOwed ow ≡ true → UniqueOwed ow′ ≡ true
UniqueOwed-payOwed s [] ow′ () uq
UniqueOwed-payOwed s ((x , n) ∷ o) ow′ eq uq with s ≡ᵇ x
... | true with n | eq
...   | zero  | ()
...   | suc m | refl = uq
UniqueOwed-payOwed s ((x , n) ∷ o) ow′ eq uq | false
  with payOwed s o in po | eq
... | just o′ | refl =
      ∧-intro (trans (sym (payOwed-notKey s x o o′ po)) (∧-trueˡ uq))
              (UniqueOwed-payOwed s o o′ po (∧-trueʳ uq))

-- removing a present live source decrements its count by one
countIn-removeOne : ∀ (s : Source) (lv : List Source) (k : ℕ) →
  countIn s lv ≡ suc k →
  Σ (List Source) λ lv′ → (removeOne s lv ≡ just lv′) × (countIn s lv′ ≡ k)
countIn-removeOne s [] k ()
countIn-removeOne s (x ∷ xs) k eq with s ≡ᵇ x in sx
... | true  = xs , refl , suc-inj eq
countIn-removeOne s (x ∷ xs) k eq | false
  with countIn-removeOne s xs k eq
... | xs′ , ro , ci rewrite ro = x ∷ xs′ , refl , trans (countIn-miss s x xs′ sx) ci

------------------------------------------------------------------
-- pay/applyEvents plumbing for the seed: a delivery whose source is
-- already owed pays it directly (settle-hit); a positive key is owed
-- (lookup-pos-hasOwed); the isLast close retires one live entry.
------------------------------------------------------------------

lookup-pos-hasOwed : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → hasOwed s ow ≡ true
lookup-pos-hasOwed s [] k ()
lookup-pos-hasOwed s ((x , n) ∷ o) k eq with s ≡ᵇ x in sx
... | true  = refl
... | false = lookup-pos-hasOwed s o k eq

settle-hit : ∀ (s : Source) (live : List Source) (owed : Owed) →
  hasOwed s owed ≡ true → settle delivery s live owed ≡ payOwed s owed
settle-hit s live owed h = if-true (hasOwed s owed) h

settle-miss : ∀ (s : Source) (live : List Source) (owed : Owed) →
  hasOwed s owed ≡ false →
  settle delivery s live owed ≡ payOwed s (bumpOwed s (countIn s live) owed)
settle-miss s live owed h = if-false (hasOwed s owed) h

-- an exhausted close of a present source retires its one live entry,
-- leaving owed and done untouched
applyEvents-close-exh : ∀ {A : Set} (x : Source) (live live′ : List Source)
  (owed : Owed) (done : Bool) → removeOne x live ≡ just live′ →
  applyEvents {A} (close x exhausted ∷ []) live owed done ≡ just (live′ , owed , done)
applyEvents-close-exh x live live′ owed done ro rewrite ro = refl

-- the seed's applyEvents field: fold the arrival's initial closes.  Not
-- spent (non-isLast) → no close, live untouched.  Spent (isLast) → the
-- exhausted close retires this source's one live entry (present because
-- live-source counts it: countIn = the uncancelled snapshot remainder,
-- ≥ 1 for a non-cancelled head).
seed-applies : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} (ob′ : Owed) →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ (List Source) λ Lv →
    applyEvents {Val Γ t}
      (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
      (ProtocolSt.live S) ob′ (ProtocolSt.done S) ≡ just (Lv , ob′ , ProtocolSt.done S)
seed-applies {a = a} {rid = rid} {p = p} {ps = ps} {st = st} {S = S} ob′ mid ceq
  with Arrival.isLast a | Mid.live-source mid
... | false | lsm = ProtocolSt.live S , refl
... | true  | lsm =
      live′ , applyEvents-close-exh (arrSource a) (ProtocolSt.live S) live′ ob′
                     (ProtocolSt.done S) ro
  where
  ci-eq : countIn (arrSource a) (ProtocolSt.live S)
            ≡ suc (countRemaining ps (EvalSt.cancelled st))
  ci-eq = trans lsm (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
  rm = countIn-removeOne (arrSource a) (ProtocolSt.live S)
         (countRemaining ps (EvalSt.cancelled st)) ci-eq
  live′ = proj₁ rm
  ro    = proj₁ (proj₂ rm)

-- seeding a fresh instant: a first delivery from s with live count suc k
-- opens owed[s] = suc k and pays one, leaving k
payOwed-seed : ∀ (s : Source) (k : ℕ) →
  payOwed s (bumpOwed s (suc k) []) ≡ just ((s , k) ∷ [])
payOwed-seed s k rewrite ≡ᵇ-refl s = refl

-- suc on the left of ≤ forces the right side to be a successor
≤-suc-inv : ∀ {m n} → suc m ≤ n → Σ ℕ λ k → n ≡ suc k
≤-suc-inv (s≤s {n = n} _) = n , refl

-- the non-isLast registry positivity, DISCHARGED from Mid.reg-bound: a
-- non-cancelled head bumps countRemaining ((rid,p)∷ps) to suc _ (cr-fresh),
-- and reg-bound lower-bounds the arrSource registry count by it, so the
-- registry carries ≥ 1 entry.  (The isLast gate is now vacuous — reg-bound
-- holds unconditionally — but kept so seed-live-pos's call site is unchanged.)
countRegs-arrSrc-pos : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Arrival.isLast a ≡ false →
  Σ ℕ λ k → countRegs (arrSource a) (EvalSt.registry st) ≡ suc k
countRegs-arrSrc-pos {a = a} {rid = rid} {p = p} {ps = ps} {st = st} mid ceq _ =
  ≤-suc-inv (subst (λ z → z ≤ countRegs (arrSource a) (EvalSt.registry st))
                   (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
                   (Mid.reg-bound mid))

-- a non-cancelled head is a live registration of its source ⇒ ≥ 1 live entry.
-- isLast: PROVEN (live-source counts the uncancelled snapshot remainder, ≥ 1
-- for a non-cancelled head — live-source + cr-fresh).  non-isLast: routes
-- through countRegs-arrSrc-pos (the registry positivity above).
