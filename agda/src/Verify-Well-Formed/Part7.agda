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
module Verify-Well-Formed.Part7 where

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

open import Verify-Well-Formed.Part6 public

cut-reg-typed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (sched : Sched Γ) (st : EvalSt e) →
  regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true →
  let (kept , _ , _) =
        cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                   (EvalSt.dying st) (EvalSt.registry st)
  in regTyped? kept (sweepLive kept (Sched.live sched)) ≡ true
cut-reg-typed nid sched st rt =
  regTyped?-sweepLive
    (proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                       (EvalSt.dying st) (EvalSt.registry st)))
    (proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                       (EvalSt.dying st) (EvalSt.registry st)))
    (Sched.live sched)
    (regTyped?-cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                          (EvalSt.dying st) (EvalSt.registry st) (Sched.live sched) rt)

-- under done ≡ true, a successful applyEvents implies hasValue ≡ false
applyEvents-val-done-absurd : ∀ {A : Set} (es : List (InstEvent A))
  (lv : List Source) (o : Owed) {r} →
  applyEvents es lv o true ≡ just r → hasValue es ≡ false
applyEvents-val-done-absurd []                   lv o _ = refl
applyEvents-val-done-absurd (value _ ∷ _)       lv o ()
applyEvents-val-done-absurd (init x ∷ es)       lv o eq =
  applyEvents-val-done-absurd es (x ∷ lv) o eq
applyEvents-val-done-absurd (handoff x ∷ es)    lv o eq =
  applyEvents-val-done-absurd es lv (bumpOwed x (countIn x lv) o) eq
applyEvents-val-done-absurd (complete ∷ es)     lv o eq =
  applyEvents-val-done-absurd es lv o eq
applyEvents-val-done-absurd (close x cutPending ∷ es) lv o eq
  with removeOne x lv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ = applyEvents-val-done-absurd es lv′ o′ eq′
applyEvents-val-done-absurd (close x cut ∷ es)      lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-val-done-absurd es lv′ o eq′
applyEvents-val-done-absurd (close x exhausted ∷ es) lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-val-done-absurd es lv′ o eq′
applyEvents-val-done-absurd (close x dried ∷ es)    lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-val-done-absurd es lv′ o eq′

-- done only ever gates VALUE events, and a value under done fails outright, so a
-- run that SUCCEEDS with done already set never consulted the flag: the same
-- events reach the same live and owed starting from done ≡ false.  (The final
-- flag is not the same — a `complete` still latches it — hence the Σ.)
applyEvents-done-drop : ∀ {A : Set} (es : List (InstEvent A))
  (lv : List Source) (o : Owed) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es lv o true ≡ just (L , O , D) →
  Σ Bool λ D′ → applyEvents es lv o false ≡ just (L , O , D′)
applyEvents-done-drop []                   lv o refl = false , refl
applyEvents-done-drop (value _ ∷ _)        lv o ()
applyEvents-done-drop (init x ∷ es)        lv o eq = applyEvents-done-drop es (x ∷ lv) o eq
applyEvents-done-drop (handoff x ∷ es)     lv o eq =
  applyEvents-done-drop es lv (bumpOwed x (countIn x lv) o) eq
applyEvents-done-drop (complete ∷ es)      lv o eq = _ , eq
applyEvents-done-drop (close x cutPending ∷ es) lv o eq
  with removeOne x lv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ = applyEvents-done-drop es lv′ o′ eq′
applyEvents-done-drop (close x cut ∷ es)       lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-done-drop es lv′ o eq′
applyEvents-done-drop (close x exhausted ∷ es) lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-done-drop es lv′ o eq′
applyEvents-done-drop (close x dried ∷ es)     lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-done-drop es lv′ o eq′

-- bk gives the same live and owed as es: splitEvents routes values and complete
-- out of the bookkeeping list, and those are exactly applyEvents' two
-- traffic-free cases — a value moves nothing (while not done) and a complete
-- only sets the flag.  So the skeleton lands on the same state with done still
-- false.  The `complete` clause is where applyEvents-done-drop is spent: the
-- events AFTER a complete ran with the flag set, and the skeleton runs them
-- without it.
applyEvents-bk-result : ∀ {n} {Γ : Ctx n} {u}
  (es : List (InstEvent (Val Γ u))) (lv : List Source) (o : Owed)
  {L : List Source} {D : Bool} →
  applyEvents es lv o false ≡ just (L , [] , D) →
  applyEvents (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) lv o false
    ≡ just (L , [] , false)
applyEvents-bk-result []                lv o refl = refl
applyEvents-bk-result (value v ∷ es)    lv o eq = applyEvents-bk-result es lv o eq
applyEvents-bk-result (init x ∷ es)     lv o eq = applyEvents-bk-result es (x ∷ lv) o eq
applyEvents-bk-result (handoff x ∷ es)  lv o eq =
  applyEvents-bk-result es lv (bumpOwed x (countIn x lv) o) eq
applyEvents-bk-result (complete ∷ es)   lv o eq =
  applyEvents-bk-result es lv o (proj₂ (applyEvents-done-drop es lv o eq))
applyEvents-bk-result (close x cutPending ∷ es) lv o eq
  with removeOne x lv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ = applyEvents-bk-result es lv′ o′ eq′
applyEvents-bk-result (close x cut ∷ es)       lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-bk-result es lv′ o eq′
applyEvents-bk-result (close x exhausted ∷ es) lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-bk-result es lv′ o eq′
applyEvents-bk-result (close x dried ∷ es)     lv o eq
  with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-bk-result es lv′ o eq′

countIn-miss : ∀ (s x : Source) (xs : List Source) →
  (s ≡ᵇ x) ≡ false → countIn s (x ∷ xs) ≡ countIn s xs
countIn-miss s x xs sx with s ≡ᵇ x | sx
... | false | refl = refl

-- removeOne drops exactly one occurrence of x: the x-count falls by one,
-- every other source's count is untouched (the two reads applyEvents-count
-- needs at a `close x` — hit for s ≡ x, miss for s ≢ x)
countIn-removeOne-hit : ∀ (x : Source) (lv lv′ : List Source) →
  removeOne x lv ≡ just lv′ → countIn x lv ≡ suc (countIn x lv′)
countIn-removeOne-hit x []       lv′ ()
countIn-removeOne-hit x (y ∷ ys) lv′ eq with x ≡ᵇ y in xy
... | true  = cong suc (cong (countIn x) (just-injᵂ eq))
... | false with removeOne x ys in ry | eq
...   | just ys′ | refl rewrite xy = countIn-removeOne-hit x ys ys′ ry
...   | nothing  | ()

countIn-removeOne-miss : ∀ (x s : Source) (lv lv′ : List Source) →
  (s ≡ᵇ x) ≡ false → removeOne x lv ≡ just lv′ → countIn s lv ≡ countIn s lv′
countIn-removeOne-miss x s []       lv′ sx ()
countIn-removeOne-miss x s (y ∷ ys) lv′ sx eq with x ≡ᵇ y in xy
... | true  = trans (countIn-miss s y ys s≢y)
                    (cong (countIn s) (just-injᵂ eq))
  where s≢y : (s ≡ᵇ y) ≡ false
        s≢y = trans (sym (cong (λ z → s ≡ᵇ z) (≡ᵇ→≡ x y xy))) sx
... | false with removeOne x ys in ry | eq
...   | nothing  | ()
...   | just ys′ | refl with s ≡ᵇ y
...     | true  = cong suc (countIn-removeOne-miss x s ys ys′ sx ry)
...     | false = countIn-removeOne-miss x s ys ys′ sx ry

countIn-hit : ∀ (s x : Source) (xs : List Source) →
  (s ≡ᵇ x) ≡ true → countIn s (x ∷ xs) ≡ suc (countIn s xs)
countIn-hit s x xs sx with s ≡ᵇ x | sx
... | true | refl = refl

-- one `close x` event's contribution to the drain count, shared by all three
-- reasons (closeCount counts the close regardless; owed handling differs but
-- the live count does not): given the IH over the tail and removeOne x lv,
-- reconcile the s ≡ x (removeOne-hit) and s ≢ x (removeOne-miss) reads
close-count : ∀ {A : Set} (x s : Source) (lv lv′ Lv : List Source)
  (es : List (InstEvent A)) →
  removeOne x lv ≡ just lv′ →
  countIn s Lv + closeCount s es ≡ countIn s lv′ + initCount s es →
  countIn s Lv + (if s ≡ᵇ x then suc (closeCount s es) else closeCount s es)
    ≡ countIn s lv + initCount s es
close-count x s lv lv′ Lv es rmv ih with s ≡ᵇ x in sx
... | false = trans ih (cong (_+ initCount s es)
                          (sym (countIn-removeOne-miss x s lv lv′ sx rmv)))
... | true  = trans (+-suc (countIn s Lv) (closeCount s es))
                    (trans (cong suc ih) (sym (cong (_+ initCount s es) cs)))
  where s≡x : s ≡ x
        s≡x = ≡ᵇ→≡ s x sx
        cs : countIn s lv ≡ suc (countIn s lv′)
        cs = trans (cong (λ z → countIn z lv) s≡x)
               (trans (countIn-removeOne-hit x lv lv′ rmv)
                      (cong suc (cong (λ z → countIn z lv′) (sym s≡x))))

-- right cancellation, spelled out: the stdlib's +-cancelʳ-≡ changes arity
-- across versions and this is two lines
sucInjᵂ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
sucInjᵂ refl = refl

+-cancelʳᵂ : ∀ (a b c : ℕ) → a + c ≡ b + c → a ≡ b
+-cancelʳᵂ a b zero    eq = trans (sym (+-identityʳ a)) (trans eq (+-identityʳ b))
+-cancelʳᵂ a b (suc c) eq =
  +-cancelʳᵂ a b c (sucInjᵂ (trans (sym (+-suc a c)) (trans eq (+-suc b c))))

-- a source the live list still holds can be closed: removeOne finds an
-- occurrence whenever the count is positive.  The cut needs this to know its
-- own closes APPLY — a close whose source is already gone would fail the emit
removeOne-from-count : ∀ (x : Source) (lv : List Source) →
  1 ≤ countIn x lv → Σ (List Source) λ lv′ → removeOne x lv ≡ just lv′
removeOne-from-count x []       ()
removeOne-from-count x (y ∷ ys) h with x ≡ᵇ y in xy
... | true  = ys , refl
... | false with removeOne x ys in ry
...   | just ys′ = y ∷ ys′ , refl
...   | nothing  =
        ⊥-elim (n≢jᵂ (trans (sym ry) (proj₂ (removeOne-from-count x ys h))))

-- removeOne read at a source EQUAL to the removed one (the ≡ᵇ form, which is
-- what the count arguments below actually hold)
countIn-removeOne-eq : ∀ (x s : Source) (lv lv′ : List Source) →
  (s ≡ᵇ x) ≡ true → removeOne x lv ≡ just lv′ → countIn s lv ≡ suc (countIn s lv′)
countIn-removeOne-eq x s lv lv′ sx rmv =
  trans (cong (λ z → countIn z lv) (≡ᵇ→≡ s x sx))
    (trans (countIn-removeOne-hit x lv lv′ rmv)
           (cong suc (cong (λ z → countIn z lv′) (sym (≡ᵇ→≡ s x sx)))))

-- close-count with the init side dropped: cutThrough emits closes only, so
-- there is no initCount term to carry through the cut's balance
close-count₀ : ∀ {A : Set} (x s : Source) (lv lv′ Lv : List Source)
  (es : List (InstEvent A)) →
  removeOne x lv ≡ just lv′ →
  countIn s Lv + closeCount s es ≡ countIn s lv′ →
  countIn s Lv + (if s ≡ᵇ x then suc (closeCount s es) else closeCount s es)
    ≡ countIn s lv
close-count₀ x s lv lv′ Lv es rmv ih with s ≡ᵇ x in sx
... | false = trans ih (sym (countIn-removeOne-miss x s lv lv′ sx rmv))
... | true  = trans (+-suc (countIn s Lv) (closeCount s es))
                    (trans (cong suc ih)
                           (sym (countIn-removeOne-eq x s lv lv′ sx rmv)))

-- the shape cutThrough's event output has: closes and nothing else
data AllCloses {A : Set} : List (InstEvent A) → Set where
  ac-[] : AllCloses []
  ac-∷  : ∀ {x cr es} → AllCloses es → AllCloses (close x cr ∷ es)

-- one close applied, at EITHER reason: owed is [] throughout, and cancelOwed
-- on [] is a no-op, so cut and cutPending take the same live step
close-apply : ∀ {A : Set} (x : Source) (cr : CloseReason)
  (es : List (InstEvent A)) (lv lv″ : List Source) {res} →
  removeOne x lv ≡ just lv″ →
  applyEvents es lv″ [] false ≡ res →
  applyEvents (close x cr ∷ es) lv [] false ≡ res
close-apply x cut        es lv lv″ rmv ap rewrite rmv = ap
close-apply x cutPending es lv lv″ rmv ap rewrite rmv = ap
close-apply x exhausted  es lv lv″ rmv ap rewrite rmv = ap
close-apply x dried      es lv lv″ rmv ap rewrite rmv = ap

-- the head close's own budget: its source must still be live
closes-head-pos : ∀ {A : Set} (x : Source) (cr : CloseReason) (cs : List (InstEvent A))
  (lv : List Source) →
  (∀ s → closeCount s (close x cr ∷ cs) ≤ countIn s lv) → 1 ≤ countIn x lv
closes-head-pos x cr cs lv h =
  ≤-trans (s≤s z≤n)
    (subst (λ b → (if b then suc (closeCount x cs) else closeCount x cs) ≤ countIn x lv)
           (≡ᵇ-refl x) (h x))

-- and the tail's, once the head has been drained off the live list
closes-tail-bound : ∀ {A : Set} (x : Source) (cr : CloseReason) (cs : List (InstEvent A))
  (lv lv″ : List Source) →
  removeOne x lv ≡ just lv″ →
  (∀ s → closeCount s (close x cr ∷ cs) ≤ countIn s lv) →
  (∀ s → closeCount s cs ≤ countIn s lv″)
closes-tail-bound x cr cs lv lv″ rmv h s with s ≡ᵇ x in sx | h s
... | true  | hs = ≤-pred (subst (suc (closeCount s cs) ≤_)
                                 (countIn-removeOne-eq x s lv lv″ sx rmv) hs)
... | false | hs = subst (closeCount s cs ≤_)
                         (countIn-removeOne-miss x s lv lv″ sx rmv) hs

-- THE CLOSE LIST, APPLIED.  Given enough live entries per source, a pure-close
-- emit runs to a `just` and moves each source's count down by exactly its close
-- count.  Owed stays [] the whole way, so no owed obligation is ever consulted.
closes-apply : ∀ {A : Set} (cs : List (InstEvent A)) (lv : List Source) →
  AllCloses cs →
  (∀ s → closeCount s cs ≤ countIn s lv) →
  Σ (List Source) λ lv′ →
    applyEvents cs lv [] false ≡ just (lv′ , [] , false)
    × (∀ s → countIn s lv′ + closeCount s cs ≡ countIn s lv)
closes-apply []                lv ac-[]     h = lv , refl , λ s → +-identityʳ (countIn s lv)
closes-apply (close x cr ∷ cs) lv (ac-∷ ac) h
  with removeOne-from-count x lv (closes-head-pos x cr cs lv h)
... | lv″ , rmv with closes-apply cs lv″ ac (closes-tail-bound x cr cs lv lv″ rmv h)
...   | lv′ , ap , cnt =
        lv′ , close-apply x cr cs lv lv″ rmv ap
            , λ s → close-count₀ x s lv lv″ lv′ cs rmv (cnt s)

-- cutThrough's event output is all closes, and retagging keeps it that way
cutThrough-allCloses : ∀ {A : Set} {n} {Γ : Ctx n} {t}
  (nid : NodeId) (dlv : List RegId) (wm : RegId) (dying : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  AllCloses {A} (retagEvents (proj₁ (proj₂ (cutThrough nid dlv wm dying reg))))
cutThrough-allCloses nid dlv wm dying [] = ac-[]
cutThrough-allCloses {A} nid dlv wm dying ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c)
     | cutThrough nid dlv wm dying r
     | cutThrough-allCloses {A} nid dlv wm dying r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih with any (_≡ᵇ rid) dlv ∧ memberSource src dying
...   | true  = ih
...   | false = ac-∷ ih

-- retagging is invisible to the close count (it keeps every close verbatim)
retag-closeCount : ∀ {A B : Set} (s : Source) (es : List (InstEvent A)) →
  closeCount s (retagEvents {A} {B} es) ≡ closeCount s es
retag-closeCount s []               = refl
retag-closeCount s (init x    ∷ es) = retag-closeCount s es
retag-closeCount s (handoff x ∷ es) = retag-closeCount s es
retag-closeCount s (complete  ∷ es) = retag-closeCount s es
retag-closeCount s (value _   ∷ es) = retag-closeCount s es
retag-closeCount s (close x r ∷ es) with s ≡ᵇ x
... | true  = cong suc (retag-closeCount s es)
... | false = retag-closeCount s es

-- the cut's registry/close balance, and the fact that it emits no inits
cutThrough-balance : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (nid : NodeId) (dlv : List RegId) (wm : RegId)
  (dying : List Source) (reg : List (RegId × Source × Chain Γ t)) →
  memberSource s dying ≡ false →
  countRegs s reg
    ≡ countRegs s (proj₁ (cutThrough nid dlv wm dying reg))
      + closeCount s (proj₁ (proj₂ (cutThrough nid dlv wm dying reg)))
cutThrough-balance s nid dlv wm dying [] mem = refl
cutThrough-balance s nid dlv wm dying ((rid , src , c) ∷ r) mem
  with pathHasNode nid (proj₂ c)
     | cutThrough nid dlv wm dying r
     | cutThrough-balance s nid dlv wm dying r mem
-- survivor: kept keeps (rid,src,c); closes unchanged
... | false | kept , closes , rids | ih with s ≡ᵇ src
...   | true  = cong suc ih
...   | false = ih
-- victim: removed from registry; a close for src is emitted unless delivered∧dying
cutThrough-balance s nid dlv wm dying ((rid , src , c) ∷ r) mem
    | true | kept , closes , rids | ih with s ≡ᵇ src in seq
-- s ≢ src: this victim is not an s-reg; the (src-tagged) close, emitted or not,
-- contributes nothing to closeCount s, and countRegs s is unchanged
...   | false with any (_≡ᵇ rid) dlv ∧ memberSource src dying
...     | true              = ih
...     | false rewrite seq = ih
-- s ≡ src: src ≡ s, so memberSource src dying ≡ mem ≡ false ⇒ close ALWAYS emitted
cutThrough-balance s nid dlv wm dying ((rid , src , c) ∷ r) mem
    | true | kept , closes , rids | ih | true rewrite sym (≡ᵇ→≡ s src seq)
  with any (_≡ᵇ rid) dlv
...   | false rewrite ≡ᵇ-refl s =
        trans (cong suc ih) (sym (+-suc (countRegs s kept) (closeCount s closes)))
...   | true  rewrite mem | ≡ᵇ-refl s =
        trans (cong suc ih) (sym (+-suc (countRegs s kept) (closeCount s closes)))

-- cutThrough emits only `close` events, never `init` — so its close list adds
-- nothing to any source's init count (take-cut sub-obligation, feeds shadow/env-init).
cutThrough-no-init : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (nid : NodeId) (dlv : List RegId) (wm : RegId)
  (dying : List Source) (reg : List (RegId × Source × Chain Γ t)) →
  initCount s (proj₁ (proj₂ (cutThrough nid dlv wm dying reg))) ≡ 0
cutThrough-no-init s nid dlv wm dying [] = refl
cutThrough-no-init s nid dlv wm dying ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c)
     | cutThrough nid dlv wm dying r
     | cutThrough-no-init s nid dlv wm dying r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih with any (_≡ᵇ rid) dlv ∧ memberSource src dying
...   | true  = ih
...   | false = ih

-- every close cutThrough emits has a live entry to land on: the closes are
-- bounded by the registry (cutThrough-balance) and the registry is what the
-- live list shadows (live-matches)
cutThrough-close-bound : ∀ {A : Set} {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (st : EvalSt e) (L₁ : List Source) →
  (∀ s → memberSource s (EvalSt.dying st) ≡ false) →
  (∀ s → countIn s L₁ ≡ countRegs s (EvalSt.registry st)) →
  ∀ s → closeCount s (retagEvents {B = A}
          (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                    (EvalSt.dying st) (EvalSt.registry st)))))
        ≤ countIn s L₁
cutThrough-close-bound {A} nid st L₁ dyF lm s =
  subst (_≤ countIn s L₁) (sym (retag-closeCount s (proj₁ (proj₂ CT))))
    (subst (closeCount s (proj₁ (proj₂ CT)) ≤_) (sym (lm s))
      (subst (closeCount s (proj₁ (proj₂ CT)) ≤_)
        (sym (cutThrough-balance s nid (EvalSt.delivered st) (EvalSt.regWatermark st)
               (EvalSt.dying st) (EvalSt.registry st) (dyF s)))
        (m≤n+m (closeCount s (proj₁ (proj₂ CT))) (countRegs s (proj₁ CT)))))
  where
  CT = cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                  (EvalSt.dying st) (EvalSt.registry st)

-- THE CUT'S LIVE BALANCE.  The closes cutThrough emits, applied to a live list
-- that shadows the pre-cut registry, land on a live list that shadows the KEPT
-- registry — which is what the cut's BurstInv needs.  Both halves come off
-- cutThrough-balance: it bounds the closes by the registry (so every close
-- applies) and it accounts for them exactly (so the residue matches kept).
-- The `dying` guard is cutThrough-balance's own: a victim that already
-- delivered on a dying source carried its exhausted close on its own emit, so
-- the registry would drop an entry the live list does not.
cutThrough-live-apply : ∀ {A : Set} {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (st : EvalSt e) (L₁ : List Source) →
  (∀ s → memberSource s (EvalSt.dying st) ≡ false) →
  (∀ s → countIn s L₁ ≡ countRegs s (EvalSt.registry st)) →
  Σ (List Source) λ L′ →
    applyEvents {A}
      (retagEvents (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                              (EvalSt.dying st) (EvalSt.registry st)))))
      L₁ [] false ≡ just (L′ , [] , false)
    × (∀ s → countIn s L′ ≡ countRegs s
               (proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                  (EvalSt.dying st) (EvalSt.registry st))))
cutThrough-live-apply {A} nid st L₁ dyF lm
  with closes-apply {A}
         (retagEvents (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st)
                        (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st)))))
         L₁
         (cutThrough-allCloses {A} nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                               (EvalSt.dying st) (EvalSt.registry st))
         (cutThrough-close-bound {A} nid st L₁ dyF lm)
... | L′ , ap , cnt = L′ , ap , final
  where
  CT = cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                  (EvalSt.dying st) (EvalSt.registry st)
  final : ∀ s → countIn s L′ ≡ countRegs s (proj₁ CT)
  final s = +-cancelʳᵂ (countIn s L′) (countRegs s (proj₁ CT))
              (closeCount s (proj₁ (proj₂ CT)))
              (trans (trans (sym (cong (countIn s L′ +_)
                                    (retag-closeCount s (proj₁ (proj₂ CT))))) (cnt s))
                     (trans (lm s)
                            (cutThrough-balance s nid (EvalSt.delivered st)
                              (EvalSt.regWatermark st) (EvalSt.dying st)
                              (EvalSt.registry st) (dyF s))))

cut-head-joint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (id : Id) (nid : NodeId)
  (es : List (InstEvent (Val Γ s))) (i : Id) (src : Source) (ek : EmitKind)
  (sched : Sched Γ) (st : EvalSt e) (kCount : ℕ) (S S₁ : ProtocolSt) →
  lookupNode nid (EvalSt.nodes st) ≡ just (take-st kCount) →
  proj₂ (proj₂ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)))) ≡ true →
  stepProtocol (es at i from src as ek) S ≡ just S₁ →
  BurstInv id sched st S₁ →
  -- the cut's live/registry balance holds only off a dying source: a victim
  -- that already delivered carried its own exhausted close, so no close is
  -- emitted for it and the registry drops an entry the live list does not
  (∀ s → memberSource s (EvalSt.dying st) ≡ false) →
  Σ ProtocolSt λ S″ →
    (stepProtocol
      ((proj₁ (proj₂ (splitEvents {A = Val Γ s} es))
         ++ retagEvents (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                                  (EvalSt.dying st) (EvalSt.registry st))))
         ++ map value (proj₁ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es))))
         ++ complete ∷ [])
        at i from src as ek) S ≡ just S″)
    × BurstInv id (cutSched nid sched st) (cutSt nid st) S″
cut-head-joint {Γ = Γ} {e = e} {s = s}
  id nid es i src ek sched st kCount S S₁ lk dc step binv₁ dyF
  with stepProtocol-extract-enter es i src ek S step
... | ob , hz′ , ob′ , O₁ , entEq , stEq , aeEq , hzEq , curEq = S″ , cutStep , binv″
  where
  lv   = ProtocolSt.live S
  bk   = proj₁ (proj₂ (splitEvents {A = Val Γ s} es))
  vs   = proj₁ (takeVals kCount (proj₁ (splitEvents {A = Val Γ s} es)))
  CT   = cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                    (EvalSt.dying st) (EvalSt.registry st)
  kept = proj₁ CT
  cuts = retagEvents (proj₁ (proj₂ CT))
  tv   = takeVals-cut-cons kCount (proj₁ (splitEvents {A = Val Γ s} es)) dc
  hv   : hasValue es ≡ true
  hv   = splitEvents-vals-hasValue es (proj₁ tv) (proj₁ (proj₂ tv)) (proj₂ (proj₂ tv))
  -- extract i = id and O₁ = [] from BurstInv.current-frame
  cur-id-nil : just (i , O₁) ≡ just (id , [])
  cur-id-nil with BurstInv.current-frame binv₁
  ... | inj₁ cn = ⊥-elim (n≢jᵂ (sym (trans (sym curEq) cn)))
  ... | inj₂ cj = trans (sym curEq) cj
  i=id : i ≡ id
  i=id = cong proj₁ (just-injᵂ cur-id-nil)
  O₁-nil : O₁ ≡ []
  O₁-nil = cong proj₂ (just-injᵂ cur-id-nil)
  -- done S = false: if done were true, applyEvents would reject the value
  dn-false : applyEvents es lv ob′ (ProtocolSt.done S)
               ≡ just (ProtocolSt.live S₁ , O₁ , ProtocolSt.done S₁) →
             ProtocolSt.done S ≡ false
  dn-false ae with ProtocolSt.done S
  ... | false = refl
  ... | true  = ⊥-elim (t≢fᵂ (trans (sym hv) (applyEvents-val-done-absurd es lv ob′ ae)))
  done-false : ProtocolSt.done S ≡ false
  done-false = dn-false aeEq
  -- normalize aeEq with done = false and O₁ = []
  aeEq₁ : applyEvents es lv ob′ false
             ≡ just (ProtocolSt.live S₁ , O₁ , ProtocolSt.done S₁)
  aeEq₁ = subst (λ d → applyEvents es lv ob′ d
                          ≡ just (ProtocolSt.live S₁ , O₁ , ProtocolSt.done S₁))
                done-false aeEq
  aeEq₀ : applyEvents es lv ob′ false
             ≡ just (ProtocolSt.live S₁ , [] , ProtocolSt.done S₁)
  aeEq₀ = subst (λ O → applyEvents es lv ob′ false
                          ≡ just (ProtocolSt.live S₁ , O , ProtocolSt.done S₁))
                O₁-nil aeEq₁
  -- bookkeeping events give the same live, zero owed, done = false
  bk-res : applyEvents bk lv ob′ false ≡ just (ProtocolSt.live S₁ , [] , false)
  bk-res = applyEvents-bk-result es lv ob′ aeEq₀
  -- cutThrough closes applied to S₁.live give L′ matching kept
  CTA : Σ (List Source) λ Lx →
          applyEvents {Val Γ s} cuts (ProtocolSt.live S₁) [] false ≡ just (Lx , [] , false)
          × (∀ s₁ → countIn s₁ Lx ≡ countRegs s₁ kept)
  CTA      = cutThrough-live-apply {Val Γ s} nid st (ProtocolSt.live S₁) dyF
               (BurstInv.live-matches binv₁)
  L′ : List Source
  L′       = proj₁ CTA
  cuts-res : applyEvents {Val Γ s} cuts (ProtocolSt.live S₁) [] false ≡ just (L′ , [] , false)
  cuts-res = proj₁ (proj₂ CTA)
  lm′ : ∀ s₁ → countIn s₁ L′ ≡ countRegs s₁ kept
  lm′      = proj₂ (proj₂ CTA)
  -- full cut event list steps applyEvents to just (L′, [], true)
  full-ae  : applyEvents (bk ++ cuts ++ map value vs ++ complete ∷ []) lv ob′ false
             ≡ just (L′ , [] , true)
  full-ae  =
    trans (applyEvents-++just bk (cuts ++ map value vs ++ complete ∷ []) lv ob′ false bk-res)
    (trans (applyEvents-++just cuts (map value vs ++ complete ∷ []) (ProtocolSt.live S₁) [] false cuts-res)
           (applyEvents-vc vs true L′ [] false (λ ())))
  -- coerce done S (= false) to match stepProtocol-enter's expectation
  full-ae′ : applyEvents (bk ++ cuts ++ map value vs ++ complete ∷ []) lv ob′ (ProtocolSt.done S)
             ≡ just (L′ , [] , true)
  full-ae′ = subst (λ d → applyEvents (bk ++ cuts ++ map value vs ++ complete ∷ []) lv ob′ d
                           ≡ just (L′ , [] , true))
                   (sym done-false) full-ae
  -- the cut protocol state
  S″ : ProtocolSt
  S″ = record { live = L′ ; horizon = hz′ ; current = just (i , []) ; done = true }
  -- assemble the cut step
  cutStep : stepProtocol ((bk ++ cuts ++ map value vs ++ complete ∷ []) at i from src as ek) S
            ≡ just S″
  cutStep = stepProtocol-enter (bk ++ cuts ++ map value vs ++ complete ∷ []) i src ek S
              entEq stEq full-ae′
  -- assemble BurstInv for S″
  binv″ : BurstInv id (cutSched nid sched st) (cutSt nid st) S″
  binv″ = record
    { live-matches  = lm′
    ; reg-typed     = cut-reg-typed nid sched st (BurstInv.reg-typed binv₁)
    ; horizon-low   = subst (λ hz → hz ≤ id) hzEq (BurstInv.horizon-low binv₁)
    ; current-frame = inj₂ (cong (λ j → just (j , [])) i=id)
    }

-- assembled: the cut, transported off the reduced cons form onto the unreduced
-- pushBurst.  The emit list rides pushBurst-take-cut-cons (at the empty tail, so
-- the pushed burst is a singleton and its run IS the head's step); the residual
-- sched/st ride takeDispatch-cut, by the same cong-over-the-frame-result trick
-- the non-cut clause uses.  Existential in S″ because take TRANSFORMS the burst —
-- a cut reaches a DIFFERENT final state than the untouched inner run.
