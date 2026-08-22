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
module Verify-Well-Formed.Part5 where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (suc; _≡ᵇ_; _≤ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)


-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.
open import Rx.Prim      using (Gas; Tick; Id; Source; InstEmit; InstEvent; init; value; close; handoff; complete; EmitKind;
  exhausted; dried; cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Val; Fn; applyFn; mapᵉ; _×ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Stream; Path; _↠_; map-f; scan-f; setNode; NodeId; lookupNode; scan-st;
  subscribeE; splitEvents; pushBurst; scanVals)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; stepProtocol; runProtocol; settle; paidOff; applyEvents;
  removeOne; cancelOwed; bumpOwed)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part4 using (applyEvents-++just; applyEvents-done-mono;
                                           applyEvents-vc)
open import Verify-Budget-Sufficient.Node-Table using
  (lookupNode-setNode; ≟ᵗ-refl)
open import Verify-Well-Formed.Part2 using (BurstInv)
open import Decide using (just-injᵂ; n≢jᵂ)

splitEvents-faithful-done : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (es : List (InstEvent (Val Γ u))) (vals′ : List B)
  (lv : List Source) (o : Owed) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es lv o true ≡ just (L , O , D) →
  applyEvents (proj₁ (proj₂ (splitEvents {A = B} es)) ++ map value vals′ ++ complete ∷ [])
              lv o false
    ≡ just (L , O , D)
splitEvents-faithful-done []               vals′ lv o hyp with just-injᵂ hyp
... | refl = applyEvents-vc vals′ true lv o false (λ ())
splitEvents-faithful-done (init s ∷ es)    vals′ lv o hyp =
  splitEvents-faithful-done es vals′ (s ∷ lv) o hyp
splitEvents-faithful-done (value v ∷ es)   vals′ lv o ()
splitEvents-faithful-done (handoff s ∷ es) vals′ lv o hyp =
  splitEvents-faithful-done es vals′ lv (bumpOwed s (countIn s lv) o) hyp
splitEvents-faithful-done (complete ∷ es)  vals′ lv o hyp =
  splitEvents-faithful-done es vals′ lv o hyp
splitEvents-faithful-done (close s cutPending ∷ es) vals′ lv o hyp
  with removeOne s lv | cancelOwed s o | hyp
... | just lv′ | just o′ | hyp′ = splitEvents-faithful-done es vals′ lv′ o′ hyp′
splitEvents-faithful-done (close s cut ∷ es) vals′ lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-faithful-done es vals′ lv′ o hyp′
splitEvents-faithful-done (close s exhausted ∷ es) vals′ lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-faithful-done es vals′ lv′ o hyp′
splitEvents-faithful-done (close s dried ∷ es) vals′ lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-faithful-done es vals′ lv′ o hyp′

-- main, done ≡ false: the re-emit's bookkeeping + frame values + maybe-complete
-- reproduces the original events' (live, owed, done)
splitEvents-faithful : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (es : List (InstEvent (Val Γ u))) (vals′ : List B)
  (lv : List Source) (o : Owed) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es lv o false ≡ just (L , O , D) →
  applyEvents (proj₁ (proj₂ (splitEvents {A = B} es)) ++ map value vals′
               ++ (if proj₂ (proj₂ (splitEvents {A = B} es)) then complete ∷ [] else []))
              lv o false
    ≡ just (L , O , D)
splitEvents-faithful []               vals′ lv o hyp with just-injᵂ hyp
... | refl = applyEvents-vc vals′ false lv o false (λ ())
splitEvents-faithful (init s ∷ es)    vals′ lv o hyp =
  splitEvents-faithful es vals′ (s ∷ lv) o hyp
splitEvents-faithful (value v ∷ es)   vals′ lv o hyp =
  splitEvents-faithful es vals′ lv o hyp
splitEvents-faithful (handoff s ∷ es) vals′ lv o hyp =
  splitEvents-faithful es vals′ lv (bumpOwed s (countIn s lv) o) hyp
splitEvents-faithful (complete ∷ es)  vals′ lv o hyp =
  splitEvents-faithful-done es vals′ lv o hyp
splitEvents-faithful (close s cutPending ∷ es) vals′ lv o hyp
  with removeOne s lv | cancelOwed s o | hyp
... | just lv′ | just o′ | hyp′ = splitEvents-faithful es vals′ lv′ o′ hyp′
splitEvents-faithful (close s cut ∷ es) vals′ lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-faithful es vals′ lv′ o hyp′
splitEvents-faithful (close s exhausted ∷ es) vals′ lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-faithful es vals′ lv′ o hyp′
splitEvents-faithful (close s dried ∷ es) vals′ lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-faithful es vals′ lv′ o hyp′

-- ── the completing case: faithfulness when the emit ENTERS already done ──
-- appending a `complete` under done is idempotent
applyEvents-append-complete-true : ∀ {A : Set} (xs : List (InstEvent A))
  (lv : List Source) (o : Owed) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents xs lv o true ≡ just (L , O , D) →
  applyEvents (xs ++ complete ∷ []) lv o true ≡ just (L , O , true)
applyEvents-append-complete-true xs lv o hyp =
  applyEvents-++just xs (complete ∷ []) lv o true hyp

-- under a done entry a successful run carries NO values (a value rejects),
-- so splitEvents routes nothing to the value list
splitEvents-novals-true : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (es : List (InstEvent (Val Γ u))) (lv : List Source) (o : Owed) {r} →
  applyEvents es lv o true ≡ just r → proj₁ (splitEvents {A = A} es) ≡ []
splitEvents-novals-true []               lv o hyp = refl
splitEvents-novals-true (init s ∷ es)    lv o hyp = splitEvents-novals-true es (s ∷ lv) o hyp
splitEvents-novals-true (value v ∷ es)   lv o ()
splitEvents-novals-true (handoff s ∷ es) lv o hyp =
  splitEvents-novals-true es lv (bumpOwed s (countIn s lv) o) hyp
splitEvents-novals-true (complete ∷ es)  lv o hyp = splitEvents-novals-true es lv o hyp
splitEvents-novals-true (close s cutPending ∷ es) lv o hyp
  with removeOne s lv | cancelOwed s o | hyp
... | just lv′ | just o′ | hyp′ = splitEvents-novals-true es lv′ o′ hyp′
splitEvents-novals-true (close s cut ∷ es) lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-novals-true es lv′ o hyp′
splitEvents-novals-true (close s exhausted ∷ es) lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-novals-true es lv′ o hyp′
splitEvents-novals-true (close s dried ∷ es) lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitEvents-novals-true es lv′ o hyp′

-- the bookkeeping alone reproduces a done-entry run's (live, owed), latching
-- done (values are absent by success, completes are idempotent no-ops)
splitBk-faithful-true : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (es : List (InstEvent (Val Γ u))) (lv : List Source) (o : Owed)
  {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es lv o true ≡ just (L , O , D) →
  applyEvents (proj₁ (proj₂ (splitEvents {A = B} es))) lv o true ≡ just (L , O , true)
splitBk-faithful-true []               lv o hyp with just-injᵂ hyp
... | refl = refl
splitBk-faithful-true (init s ∷ es)    lv o hyp = splitBk-faithful-true es (s ∷ lv) o hyp
splitBk-faithful-true (value v ∷ es)   lv o ()
splitBk-faithful-true (handoff s ∷ es) lv o hyp =
  splitBk-faithful-true es lv (bumpOwed s (countIn s lv) o) hyp
splitBk-faithful-true (complete ∷ es)  lv o hyp = splitBk-faithful-true es lv o hyp
splitBk-faithful-true (close s cutPending ∷ es) lv o hyp
  with removeOne s lv | cancelOwed s o | hyp
... | just lv′ | just o′ | hyp′ = splitBk-faithful-true es lv′ o′ hyp′
splitBk-faithful-true (close s cut ∷ es) lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitBk-faithful-true es lv′ o hyp′
splitBk-faithful-true (close s exhausted ∷ es) lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitBk-faithful-true es lv′ o hyp′
splitBk-faithful-true (close s dried ∷ es) lv o hyp
  with removeOne s lv | hyp
... | just lv′ | hyp′ = splitBk-faithful-true es lv′ o hyp′

-- so a done-entry emit's re-emit (bookkeeping + its own maybe-complete)
-- reproduces the original's (live, owed) and keeps done latched
splitEvents-faithful-true : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (es : List (InstEvent (Val Γ u))) (lv : List Source) (o : Owed)
  {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es lv o true ≡ just (L , O , D) →
  applyEvents (proj₁ (proj₂ (splitEvents {A = B} es))
               ++ (if proj₂ (proj₂ (splitEvents {A = B} es)) then complete ∷ [] else []))
              lv o true
    ≡ just (L , O , true)
splitEvents-faithful-true {B = B} es lv o {L = L} {O = O} hyp
  with proj₂ (proj₂ (splitEvents {A = B} es)) in ceq
... | true  = applyEvents-append-complete-true (proj₁ (proj₂ (splitEvents {A = B} es)))
                lv o (splitBk-faithful-true es lv o hyp)
... | false = subst (λ z → applyEvents z lv o true ≡ just (L , O , true))
                    (sym (++-identityʳ (proj₁ (proj₂ (splitEvents {A = B} es)))))
                    (splitBk-faithful-true es lv o hyp)

-- ── done-agnostic per-emit faithfulness ─────────────────────────────────
-- A transparent frame's per-emit value transform `g` (map-f: map applyFn;
-- scan/take: analogous) is empty-preserving.  Whatever the entry `done`, the
-- re-emit (bookkeeping ++ map value (g of the emit's values) ++ maybe-complete)
-- runs applyEvents to the SAME result: done ≡ false is splitEvents-faithful; a
-- done entry carries no values (splitEvents-novals-true), so g's output vanishes
-- and it reduces to splitEvents-faithful-true.
faithful-g : ∀ {n} {Γ : Ctx n} {u} {B : Set} (g : List (Val Γ u) → List B)
  (es : List (InstEvent (Val Γ u))) (lv : List Source) (o : Owed) (dn : Bool)
  {L : List Source} {O : Owed} {D : Bool} →
  g [] ≡ [] →
  applyEvents es lv o dn ≡ just (L , O , D) →
  applyEvents (proj₁ (proj₂ (splitEvents {A = B} es))
               ++ map value (g (proj₁ (splitEvents {A = B} es)))
               ++ (if proj₂ (proj₂ (splitEvents {A = B} es)) then complete ∷ [] else []))
              lv o dn
    ≡ just (L , O , D)
faithful-g {B = B} g es lv o false gempty hyp =
  splitEvents-faithful es (g (proj₁ (splitEvents {A = B} es))) lv o hyp
faithful-g {B = B} g es lv o true {L} {O} {D} gempty hyp
  rewrite trans (cong g (splitEvents-novals-true {A = B} es lv o hyp)) gempty =
  subst (λ d → applyEvents (proj₁ (proj₂ (splitEvents {A = B} es))
                 ++ (if proj₂ (proj₂ (splitEvents {A = B} es)) then complete ∷ [] else []))
                lv o true ≡ just (L , O , d))
        (sym (applyEvents-done-mono es lv o true hyp refl))
        (splitEvents-faithful-true es lv o hyp)

runProtocol-one : ∀ {A : Set} (S : ProtocolSt) (x : InstEmit A) →
  runProtocol S (x ∷ []) ≡ stepProtocol x S
runProtocol-one S x with stepProtocol x S
... | just S′ = refl
... | nothing = refl

-- ── per-emit frame transparency: the re-emit steps to the SAME state ─────
-- A transparent frame (evs = []: map/scan/take-noncut) re-emits an emit as
-- bookkeeping ++ map value (g of the emit's values) ++ maybe-complete, `g` its
-- empty-preserving value transform.  At the same instant/source/kind, its
-- stepProtocol lands on the SAME S′ as the original: whatever owed `ob` the
-- automaton admitted the instant with, the original's applyEvents succeeded
-- there (analysis of the given success), so faithful-g hands the re-emit the
-- identical applyEvents result — for EITHER entry done — and the automaton
-- rebuilds the identical state.  The aux takes the fields literally so the
-- `enter`/`go` clauses reduce; the guards and settle are events-independent, so
-- they drive the original and the re-emit down the same path.
stepProtocol-faithful-aux : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (g : List (Val Γ u) → List B)
  (es : List (InstEvent (Val Γ u)))
  (i : Id) (s : Source) (k : EmitKind) (lv : List Source) (hz : Id)
  (dn : Bool) (cur : Maybe (Id × Owed)) (S′ : ProtocolSt) →
  g [] ≡ [] →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ just S′ →
  stepProtocol ((proj₁ (proj₂ (splitEvents {A = B} es))
                 ++ map value (g (proj₁ (splitEvents {A = B} es)))
                 ++ (if proj₂ (proj₂ (splitEvents {A = B} es)) then complete ∷ [] else []))
                at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ just S′
stepProtocol-faithful-aux g es i s k lv hz dn nothing S′ gempty stepEq
  with hz ≤ᵇ i
... | false = ⊥-elim (n≢jᵂ stepEq)
... | true  with settle k s lv []
...   | nothing = ⊥-elim (n≢jᵂ stepEq)
...   | just o₁ with applyEvents es lv o₁ dn in aeq
...     | nothing = ⊥-elim (n≢jᵂ stepEq)
...     | just r  rewrite faithful-g g es lv o₁ dn gempty aeq = stepEq
stepProtocol-faithful-aux g es i s k lv hz dn (just (j , oⱼ)) S′ gempty stepEq
  with i ≡ᵇ j
... | true  with paidOff oⱼ
...   | true  = ⊥-elim (n≢jᵂ stepEq)
...   | false with settle k s lv oⱼ
...     | nothing = ⊥-elim (n≢jᵂ stepEq)
...     | just o₁ with applyEvents es lv o₁ dn in aeq
...       | nothing = ⊥-elim (n≢jᵂ stepEq)
...       | just r  rewrite faithful-g g es lv o₁ dn gempty aeq = stepEq
stepProtocol-faithful-aux g es i s k lv hz dn (just (j , oⱼ)) S′ gempty stepEq
    | false with allZero oⱼ
...   | false = ⊥-elim (n≢jᵂ stepEq)
...   | true  with suc j ≤ᵇ i
...     | false = ⊥-elim (n≢jᵂ stepEq)
...     | true  with settle k s lv []
...       | nothing = ⊥-elim (n≢jᵂ stepEq)
...       | just o₁ with applyEvents es lv o₁ dn in aeq
...         | nothing = ⊥-elim (n≢jᵂ stepEq)
...         | just r  rewrite faithful-g g es lv o₁ dn gempty aeq = stepEq

stepProtocol-faithful : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (g : List (Val Γ u) → List B)
  (es : List (InstEvent (Val Γ u)))
  (i : Id) (s : Source) (k : EmitKind) (S S′ : ProtocolSt) →
  g [] ≡ [] →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  stepProtocol ((proj₁ (proj₂ (splitEvents {A = B} es))
                 ++ map value (g (proj₁ (splitEvents {A = B} es)))
                 ++ (if proj₂ (proj₂ (splitEvents {A = B} es)) then complete ∷ [] else []))
                at i from s as k) S ≡ just S′
stepProtocol-faithful g es i s k S S′ gempty stepEq =
  stepProtocol-faithful-aux g es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) (ProtocolSt.current S) S′ gempty stepEq

-- stepProtocol preserves a latched done (the automaton analysis, extracting
-- S′.done and passing it to applyEvents-done-mono)
stepProtocol-done-mono-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (cur : Maybe (Id × Owed)) (S′ : ProtocolSt) →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = true }) ≡ just S′ →
  ProtocolSt.done S′ ≡ true
stepProtocol-done-mono-aux es i s k lv hz nothing S′ stepEq
  with hz ≤ᵇ i
... | false = ⊥-elim (n≢jᵂ stepEq)
... | true  with settle k s lv []
...   | nothing = ⊥-elim (n≢jᵂ stepEq)
...   | just o₁ with applyEvents es lv o₁ true in aeq
...     | nothing = ⊥-elim (n≢jᵂ stepEq)
...     | just (l″ , o″ , d″) =
          trans (sym (cong ProtocolSt.done (just-injᵂ stepEq)))
                (applyEvents-done-mono es lv o₁ true aeq refl)
stepProtocol-done-mono-aux es i s k lv hz (just (j , oⱼ)) S′ stepEq
  with i ≡ᵇ j
... | true  with paidOff oⱼ
...   | true  = ⊥-elim (n≢jᵂ stepEq)
...   | false with settle k s lv oⱼ
...     | nothing = ⊥-elim (n≢jᵂ stepEq)
...     | just o₁ with applyEvents es lv o₁ true in aeq
...       | nothing = ⊥-elim (n≢jᵂ stepEq)
...       | just (l″ , o″ , d″) =
            trans (sym (cong ProtocolSt.done (just-injᵂ stepEq)))
                  (applyEvents-done-mono es lv o₁ true aeq refl)
stepProtocol-done-mono-aux es i s k lv hz (just (j , oⱼ)) S′ stepEq
    | false with allZero oⱼ
...   | false = ⊥-elim (n≢jᵂ stepEq)
...   | true  with suc j ≤ᵇ i
...     | false = ⊥-elim (n≢jᵂ stepEq)
...     | true  with settle k s lv []
...       | nothing = ⊥-elim (n≢jᵂ stepEq)
...       | just o₁ with applyEvents es lv o₁ true in aeq
...         | nothing = ⊥-elim (n≢jᵂ stepEq)
...         | just (l″ , o″ , d″) =
              trans (sym (cong ProtocolSt.done (just-injᵂ stepEq)))
                    (applyEvents-done-mono es lv o₁ true aeq refl)

stepProtocol-done-mono : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S S′ : ProtocolSt) →
  ProtocolSt.done S ≡ true →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  ProtocolSt.done S′ ≡ true
stepProtocol-done-mono es i s k S S′ dt stepEq =
  stepProtocol-done-mono-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.current S) S′
    (subst (λ d → stepProtocol (es at i from s as k)
            (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                    ; current = ProtocolSt.current S ; done = d }) ≡ just S′)
           dt stepEq)

-- … and so does a whole run
runProtocol-done-mono : ∀ {A : Set} (S S′ : ProtocolSt) (xs : List (InstEmit A)) →
  ProtocolSt.done S ≡ true → runProtocol S xs ≡ just S′ → ProtocolSt.done S′ ≡ true
runProtocol-done-mono S S′ []       dt runEq = trans (sym (cong ProtocolSt.done (just-injᵂ runEq))) dt
runProtocol-done-mono S S′ (x ∷ xs) dt runEq with x
... | es at i from s as k with stepProtocol (es at i from s as k) S in seq
...   | just S₁ = runProtocol-done-mono S₁ S′ xs
                    (stepProtocol-done-mono es i s k S S₁ dt seq) runEq
...   | nothing = ⊥-elim (n≢jᵂ runEq)

-- consing a known step onto a known run
runProtocol-cons : ∀ {A : Set} (x : InstEmit A) (xs : List (InstEmit A))
  (S S₁ S′ : ProtocolSt) →
  stepProtocol x S ≡ just S₁ → runProtocol S₁ xs ≡ just S′ →
  runProtocol S (x ∷ xs) ≡ just S′
runProtocol-cons x xs S S₁ S′ stepEq restEq with stepProtocol x S | stepEq
... | just .S₁ | refl = restEq

-- ── the frame fold: a transparent frame's whole re-emitted burst runs like
-- the original ──────────────────────────────────────────────────────────
-- reEmit is the per-emit re-emission (bookkeeping ++ map value (g of the emit's
-- values) ++ maybe-complete) at the same instant/source/kind; `g` is the frame's
-- empty-preserving value transform.  runProtocol-faithful folds stepProtocol-
-- faithful over the burst — done-agnostic, so it covers completing bursts too.
reEmit : ∀ {n} {Γ : Ctx n} {u} {B : Set}
       → (List (Val Γ u) → List B) → InstEmit (Val Γ u) → InstEmit B
reEmit {B = B} g em =
  (proj₁ (proj₂ (splitEvents {A = B} (InstEmit.events em)))
    ++ map value (g (proj₁ (splitEvents {A = B} (InstEmit.events em))))
    ++ (if proj₂ (proj₂ (splitEvents {A = B} (InstEmit.events em)))
        then complete ∷ [] else []))
   at InstEmit.instant em from InstEmit.source em as InstEmit.kind em

runProtocol-faithful : ∀ {n} {Γ : Ctx n} {u} {B : Set}
  (g : List (Val Γ u) → List B) (burst : List (InstEmit (Val Γ u)))
  (S S′ : ProtocolSt) →
  g [] ≡ [] →
  runProtocol S burst ≡ just S′ →
  runProtocol S (map (reEmit g) burst) ≡ just S′
runProtocol-faithful g []                          S S′ gempty runEq = runEq
runProtocol-faithful g ((es at i from s as k) ∷ ems) S S′ gempty runEq
  with stepProtocol (es at i from s as k) S in seq
... | nothing = ⊥-elim (n≢jᵂ runEq)
... | just S₁ =
      runProtocol-cons (reEmit g (es at i from s as k)) (map (reEmit g) ems) S S₁ S′
        (stepProtocol-faithful g es i s k S S₁ gempty seq)
        (runProtocol-faithful g ems S₁ S′ gempty runEq)

-- pushBurst over a map-f frame IS the reEmit map: stepFrame (map-f) only relabels
-- values (evs = [], st/sched untouched), so each emit re-emits transparently
pushBurst-map-char : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u) (κ : Path Γ u t)
  (burst : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  pushBurst fuel id now (map-f fn) κ burst sched st
    ≡ (map (reEmit (map (applyFn fn))) burst , sched , st)
pushBurst-map-char fuel id now fn κ []         sched st = refl
pushBurst-map-char fuel id now fn κ (em ∷ ems) sched st =
  cong (λ r → (reEmit (map (applyFn fn)) em ∷ proj₁ r) , proj₂ r)
       (pushBurst-map-char fuel id now fn κ ems sched st)

-- ── the mapᵉ clause of subscribeE-wf (given the IH on b) ─────────────────
-- subscribeE (mapᵉ f b) = pushBurst (map-f f) over subscribeE b's burst.  The
-- IH runs b's burst to S′ under BurstInv; the char rewrites the map frame's
-- output to the reEmit map (st/sched untouched), and runProtocol-faithful shows
-- it runs to the SAME S′ — so BurstInv transfers verbatim.  map (applyFn f) is
-- empty-preserving (refl), the fold's `g [] ≡ []` obligation.
subscribeE-map-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  (Σ ProtocolSt λ S′ →
    (runProtocol S (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ just S′)
    × BurstInv id (proj₁ (proj₂ (subscribeE fuel b (map-f f ↠ κ) id now sched st)))
               (proj₂ (proj₂ (subscribeE fuel b (map-f f ↠ κ) id now sched st))) S′) →
  Σ ProtocolSt λ S″ →
    (runProtocol S (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ just S″)
    × BurstInv id (proj₁ (proj₂ (subscribeE fuel (mapᵉ f b) κ id now sched st)))
               (proj₂ (proj₂ (subscribeE fuel (mapᵉ f b) κ id now sched st))) S″
subscribeE-map-wf fuel f b κ id now sched st S binv (S′ , run₀ , binv₀) =
  S′ , run″ , binv″
  where
  r₀ = subscribeE fuel b (map-f f ↠ κ) id now sched st
  char : subscribeE fuel (mapᵉ f b) κ id now sched st
         ≡ (map (reEmit (map (applyFn f))) (proj₁ r₀) , proj₁ (proj₂ r₀) , proj₂ (proj₂ r₀))
  char = pushBurst-map-char fuel id now f κ (proj₁ r₀) (proj₁ (proj₂ r₀)) (proj₂ (proj₂ r₀))

  run″ : runProtocol S (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ just S′
  run″ rewrite cong proj₁ char =
    runProtocol-faithful (map (applyFn f)) (proj₁ r₀) S S′ refl run₀

  binv″ : BurstInv id (proj₁ (proj₂ (subscribeE fuel (mapᵉ f b) κ id now sched st)))
                     (proj₂ (proj₂ (subscribeE fuel (mapᵉ f b) κ id now sched st))) S′
  binv″ rewrite cong (λ z → proj₁ (proj₂ z)) char
              | cong (λ z → proj₂ (proj₂ z)) char = binv₀

-- ── the scanᵉ frame fold (stateful) ─────────────────────────────────────
-- scan threads an accumulator node across the burst: each emit reads scan-st,
-- folds its values (scanVals — one running output per input, count-preserving),
-- and writes the new accumulator.  The protocol ignores value payloads, so this
-- runs like the original burst: at each emit the value transform is `scanVals fn
-- acc` (empty-preserving), stepProtocol-faithful gives the identical step, and
-- lookupNode-setNode carries the just-written node to the next.  Given the node
-- is present (lk — the subscribeE clause installs it), no global node-persistence
-- invariant is needed.
pushBurst-scan-run : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (κ : Path Γ u t) (burst : Stream Γ s) (sched : Sched Γ) (st : EvalSt e)
  (acc : Val Γ u) (S S′ : ProtocolSt) →
  lookupNode nid (EvalSt.nodes st) ≡ just (scan-st acc) →
  runProtocol S burst ≡ just S′ →
  runProtocol S (proj₁ (pushBurst fuel id now (scan-f fn nid) κ burst sched st)) ≡ just S′
pushBurst-scan-run fuel id now fn nid κ [] sched st acc S S′ lk runEq = runEq
pushBurst-scan-run {u = u} fuel id now fn nid κ ((es at i from s as k) ∷ ems) sched st acc S S′ lk runEq
  with stepProtocol (es at i from s as k) S in seq
... | nothing = ⊥-elim (n≢jᵂ runEq)
... | just S₁ rewrite lk | ≟ᵗ-refl u =
      runProtocol-cons _ _ S S₁ S′
        (stepProtocol-faithful (λ vs → proj₁ (scanVals fn acc vs)) es i s k S S₁ refl seq)
        (pushBurst-scan-run fuel id now fn nid κ ems sched
          (record st { nodes = setNode nid (scan-st acc′) (EvalSt.nodes st) }) acc′ S₁ S′
          (lookupNode-setNode nid (scan-st acc′) (EvalSt.nodes st)) runEq)
  where acc′ = proj₂ (scanVals fn acc (proj₁ (splitEvents es)))

-- scan-f leaves registry and schedule untouched: every emit only rewrites the
-- accumulator in the node table — the st-side of the scanᵉ clause's BurstInv
-- (live-matches/reg-typed carry from the IH since the registry is fixed)
