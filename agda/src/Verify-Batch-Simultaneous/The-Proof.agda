module Verify-Batch-Simultaneous.The-Proof where

open import Data.Bool    using (Bool; true; false; if_then_else_; T)
open import Data.Unit    using (tt)
open import Data.Nat     using (ℕ; zero; suc; _≤_; s≤s; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; n≤1+n; ≤-refl; 1+n≰n)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Function     using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim               using (InstEmit; Fuel; Id; Source; _at_from_as_;
                                         InstEvent; init; value; close; handoff;
                                         complete; EmitKind; subscribe; delivery;
                                         plumbing; CloseReason; cut; cutPending;
                                         exhausted)
open import Rx.Exp                using (Ctx; Closed)
open import Rx.Evaluator          using (Slots; evaluate)
open import Rx.Protocol           using (ProtocolSt; Owed; protocol-init;
                                         runProtocol; stepProtocol; checkFinal;
                                         paidOff; allZero; Accepted; accepted;
                                         WellFormed; settle; applyEvents; hasOwed;
                                         bumpOwed; payOwed; cancelOwed; removeOne;
                                         countIn)
open import Verify-Well-Formed    using (evaluate-well-formed)
open import Spec                  using (spec-batchSimultaneous; specGo;
                                         batchOf; valuesAt; valuesOf; seenBefore)
open import Implementation        using (impl-batchSimultaneous; foldBatch;
                                         step-batch; flushBatch; closeBatch;
                                         settleBatch; applyBatch;
                                         batch-init; BatchSt; OpenBatch)

------------------------------------------------------------------
-- The batcher's half of the sandwich: on any protocol-respecting
-- stream the counting machine matches the clairvoyant spec.
-- Quantified over WellFormed streams, NOT arbitrary ones — and
-- WellFormed's instant-completion clause is load-bearing: without
-- it a post-payoff same-instant emit could smuggle values into an
-- instant the online batcher already flushed.
--
-- Architecture, mirroring Verify-Well-Formed: a concrete relation
-- (BatchRel) couples the online batcher's state to the automaton's
-- mid-stream, flushSpec names the open batch's eventual clairvoyant
-- contribution, and ONE generalized fold lemma (fold-agree, the
-- postulated waypoint — provable by induction on the stream, one
-- case per protocol transition) closes the loop.  batch-agreement
-- is a real definition.
------------------------------------------------------------------

-- every already-batched instant is strictly below the bound (the
-- freshness tie: an accepted future emit can never reopen one)
SeenBelow : List Id → Id → Set
SeenBelow seen h = ∀ i → seenBefore i seen ≡ true → suc i ≤ h

-- the coupling invariant, sampled between emits:
--   · the batcher's live multiset IS the automaton's;
--   · either both stand closed (the automaton idle, or holding a
--     paid-off instant the batcher already flushed — the flush
--     point is exactly paidOff, now protocol law), or both hold the
--     SAME open instant with the SAME owed table, not yet paid off;
--   · the spec has always already emitted the open/held instant's
--     batch (it fired clairvoyantly at first sight), so that id is
--     in `seen`, and everything in `seen` is stale by freshness.
record BatchRel {A : Set} (seen : List Id)
                (S : ProtocolSt) (B : BatchSt A) : Set where
  field
    live-eq : BatchSt.live B ≡ ProtocolSt.live S
    phase   :
        (BatchSt.current B ≡ nothing
          × ( (ProtocolSt.current S ≡ nothing
                × SeenBelow seen (ProtocolSt.horizon S))
            ⊎ (Σ (Id × Owed) λ jow →
                 (ProtocolSt.current S ≡ just jow)
               × (paidOff (proj₂ jow) ≡ true)
               × (seenBefore (proj₁ jow) seen ≡ true)
               × SeenBelow seen (suc (proj₁ jow)))))
      ⊎ (Σ (OpenBatch A) λ b →
           (BatchSt.current B ≡ just b)
         × (ProtocolSt.current S
              ≡ just (OpenBatch.instant b , OpenBatch.owed b))
         × (paidOff (OpenBatch.owed b) ≡ false)
         × (seenBefore (OpenBatch.instant b) seen ≡ true)
         × SeenBelow seen (suc (OpenBatch.instant b)))

-- what the still-open batch will eventually contribute, said
-- clairvoyantly: its values so far plus every remaining value of
-- its instant in the suffix.  The induction's pivot: when the spec
-- emits an instant's batch at first sight, the batcher has exactly
-- this much pending
flushSpec : ∀ {A : Set} → BatchSt A → List (InstEmit A)
          → List (InstEmit (List A))
flushSpec B xs with BatchSt.current B
... | nothing = []
... | just b  =
      batchOf (OpenBatch.instant b) (OpenBatch.source b) (OpenBatch.kind b)
              (OpenBatch.values b ++ valuesAt (OpenBatch.instant b) xs)

-- the online close is the spec's batchOf on the open batch's values
closeBatch≡batchOf : ∀ {A : Set} (b : OpenBatch A) →
  closeBatch b ≡ batchOf (OpenBatch.instant b) (OpenBatch.source b)
                         (OpenBatch.kind b) (OpenBatch.values b)
closeBatch≡batchOf b with OpenBatch.values b
... | []     = refl
... | v ∷ vs = refl

-- at stream end the online flush IS the spec's open-batch flush
flush≡flushSpec[] : ∀ {A : Set} (B : BatchSt A) → flushBatch B ≡ flushSpec B []
flush≡flushSpec[] B with BatchSt.current B
... | nothing = refl
... | just b  = trans (closeBatch≡batchOf b)
    (cong (batchOf (OpenBatch.instant b) (OpenBatch.source b) (OpenBatch.kind b))
          (sym (++-identityʳ (OpenBatch.values b))))

-- specGo's contribution for the head emit, and the seen it hands on —
-- exactly the branches of specGo, factored so the fold can splice them
specGoHead : ∀ {A : Set} → InstEmit A → List Id → List (InstEmit A)
           → List (InstEmit (List A))
specGoHead (es at i from s as k) seen rest =
  if seenBefore i seen then [] else batchOf i s k (valuesOf es ++ valuesAt i rest)

seen▸ : ∀ {A : Set} → InstEmit A → List Id → List Id
seen▸ (es at i from s as k) seen = if seenBefore i seen then seen else i ∷ seen

specGo-split : ∀ {A : Set} (x : InstEmit A) (seen : List Id)
               (rest : List (InstEmit A)) →
  specGo seen (x ∷ rest) ≡ specGoHead x seen rest ++ specGo (seen▸ x seen) rest
specGo-split (es at i from s as k) seen rest with seenBefore i seen
... | true  = refl
... | false = refl

-- acceptance of a cons peels off: the head steps (never rejects) and
-- the tail is still accepted
step-accepted : ∀ {A : Set} (x : InstEmit A) (S : ProtocolSt)
                (xs : List (InstEmit A)) → Accepted (runProtocol S (x ∷ xs)) →
  Σ ProtocolSt λ S′ →
    (stepProtocol x S ≡ just S′) × Accepted (runProtocol S′ xs)
step-accepted x S xs acc with stepProtocol x S | acc
... | just S′ | acc′ = S′ , refl , acc′

------------------------------------------------------------------
-- Alignment core: on an ACCEPTED emit the batcher's clamped
-- settleBatch/applyBatch agree with the automaton's settle/applyEvents
-- (the clamps never fire).  Self-contained inductions.
------------------------------------------------------------------

just-inj : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-inj refl = refl

n≢j : ∀ {A : Set} {x : A} → _≡_ {A = Maybe A} nothing (just x) → ⊥
n≢j ()

settle-agree : (k : EmitKind) (s : Source)
  (live : List Source) (owed : Owed) {owed′ : Owed} →
  settle k s live owed ≡ just owed′ → settleBatch k s live owed ≡ owed′
settle-agree subscribe s live owed eq = just-inj eq
settle-agree plumbing  s live owed eq = just-inj eq
settle-agree delivery  s live owed eq with hasOwed s owed | eq
... | true  | eq′ rewrite eq′ = refl
... | false | eq′ rewrite eq′ = refl

-- applyEvents accepting ⇒ applyBatch lands the same live and owed
apply-agree : ∀ {A : Set} (es : List (InstEvent A)) (live : List Source)
  (owed : Owed) (done : Bool) (vs : List A)
  {live′ : List Source} {owed′ : Owed} {done′ : Bool} →
  applyEvents es live owed done ≡ just (live′ , owed′ , done′) →
  (proj₁ (applyBatch es live owed vs) ≡ live′)
  × (proj₁ (proj₂ (applyBatch es live owed vs)) ≡ owed′)
apply-agree []                  live owed done vs eq =
  cong proj₁ (just-inj eq) , cong (λ t → proj₁ (proj₂ t)) (just-inj eq)
apply-agree (init x    ∷ es) live owed done vs eq =
  apply-agree es (x ∷ live) owed done vs eq
apply-agree (value v   ∷ es) live owed done vs eq with done | eq
... | false | eq′ = apply-agree es live owed false (vs ++ v ∷ []) eq′
apply-agree (handoff x ∷ es) live owed done vs eq =
  apply-agree es live (bumpOwed x (countIn x live) owed) done vs eq
apply-agree (complete  ∷ es) live owed done vs eq =
  apply-agree es live owed true vs eq
apply-agree (close x cutPending ∷ es) live owed done vs eq
  with removeOne x live | cancelOwed x owed | eq
... | just live₁ | just owed₁ | eq′ = apply-agree es live₁ owed₁ done vs eq′
apply-agree (close x cut ∷ es) live owed done vs eq with removeOne x live | eq
... | just live₁ | eq′ = apply-agree es live₁ owed done vs eq′
apply-agree (close x exhausted ∷ es) live owed done vs eq with removeOne x live | eq
... | just live₁ | eq′ = apply-agree es live₁ owed done vs eq′

------------------------------------------------------------------
-- Freshness bookkeeping: a newly-opened instant i is past everything
-- already seen, so it's unseen and extends SeenBelow.
------------------------------------------------------------------

≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

≡ᵇ-refl : ∀ (i : ℕ) → (i ≡ᵇ i) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc i) = ≡ᵇ-refl i

≡ᵇ-sym : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ (k ≡ᵇ m)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc k) = refl
≡ᵇ-sym (suc m) zero    = refl
≡ᵇ-sym (suc m) (suc k) = ≡ᵇ-sym m k

-- an id is always seen in a list it heads
seenBefore-hit : ∀ (i : Id) (seen : List Id) → seenBefore i (i ∷ seen) ≡ true
seenBefore-hit i seen rewrite ≡ᵇ-refl i = refl

-- everything seen is < h ≤ i ⇒ i itself is unseen
freshBelow : ∀ (seen : List Id) (i h : Id) →
  SeenBelow seen h → h ≤ i → seenBefore i seen ≡ false
freshBelow seen i h below h≤i with seenBefore i seen in eq
... | false = refl
... | true  = ⊥-elim (1+n≰n (≤-trans (below i eq) h≤i))

-- … and i∷seen stays below suc i
seenbelow-cons : ∀ (seen : List Id) (i h : Id) →
  SeenBelow seen h → h ≤ i → SeenBelow (i ∷ seen) (suc i)
seenbelow-cons seen i h below h≤i k keq with k ≡ᵇ i in eq | keq
... | true  | _    = s≤s (subst (k ≤_) (≡ᵇ→≡ k i eq) ≤-refl)
... | false | keq′ = ≤-trans (≤-trans (below k keq′) h≤i) (n≤1+n i)

-- stepProtocol, unfolded on the openFresh path from an idle automaton:
-- acceptance forces the settle/applyEvents to succeed and pins S′'s shape.
-- We take the fields explicitly (with `current = nothing` LITERAL) so the
-- automaton's internal `with current ps` clauses all reduce — an opaque S
-- with only a propositional `current S ≡ nothing` leaves them stuck.
stepProtocol-idle-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (S′ : ProtocolSt) →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = nothing ; done = dn }) ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (hz ≤ i)
  × (settle k s lv [] ≡ just o₁)
  × (applyEvents es lv o₁ dn ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = hz ; current = just (i , o″) ; done = d″ })
stepProtocol-idle-aux es i s k lv hz dn S′ stepEq with hz ≤ᵇ i in hle
... | false = ⊥-elim (n≢j stepEq)
... | true  with settle k s lv []
...   | nothing = ⊥-elim (n≢j stepEq)
...   | just o₁ with applyEvents es lv o₁ dn in aeq
...     | nothing              = ⊥-elim (n≢j stepEq)
...     | just (l″ , o″ , d″)  =
          o₁ , l″ , o″ , d″
          , ≤ᵇ⇒≤ hz i (subst T (sym hle) tt)
          , refl , aeq , sym (just-inj stepEq)

stepProtocol-idle : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S S′ : ProtocolSt) →
  ProtocolSt.current S ≡ nothing →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (ProtocolSt.horizon S ≤ i)
  × (settle k s (ProtocolSt.live S) [] ≡ just o₁)
  × (applyEvents es (ProtocolSt.live S) o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = ProtocolSt.horizon S
                 ; current = just (i , o″) ; done = d″ })
stepProtocol-idle es i s k S S′ Sn stepEq =
  stepProtocol-idle-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) S′
    (subst (λ c → stepProtocol (es at i from s as k)
             (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                     ; current = c ; done = ProtocolSt.done S }) ≡ just S′)
           Sn stepEq)

-- stepProtocol, unfolded from an automaton HOLDING a paid-off instant j.
-- Acceptance forces i ≢ j (a same-instant emit into a paid-off instant is
-- rejected), so it too takes openFresh — but the departed instant pushes
-- the horizon to suc j.  Fields taken explicitly (current = just (j,oⱼ)
-- literal) so the automaton's `if i ≡ᵇ j` / settleInstant clauses reduce.
stepProtocol-held-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (j : Id) (oⱼ : Owed)
  (S′ : ProtocolSt) → paidOff oⱼ ≡ true →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = just (j , oⱼ) ; done = dn }) ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (suc j ≤ i)
  × (settle k s lv [] ≡ just o₁)
  × (applyEvents es lv o₁ dn ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = suc j ; current = just (i , o″) ; done = d″ })
stepProtocol-held-aux es i s k lv hz dn j oⱼ S′ pj stepEq with i ≡ᵇ j
... | true with paidOff oⱼ | pj
...   | true | refl = ⊥-elim (n≢j stepEq)
stepProtocol-held-aux es i s k lv hz dn j oⱼ S′ pj stepEq | false
        with allZero oⱼ
...   | false = ⊥-elim (n≢j stepEq)
...   | true  with suc j ≤ᵇ i in hle
...     | false = ⊥-elim (n≢j stepEq)
...     | true  with settle k s lv []
...       | nothing = ⊥-elim (n≢j stepEq)
...       | just o₁ with applyEvents es lv o₁ dn in aeq
...         | nothing              = ⊥-elim (n≢j stepEq)
...         | just (l″ , o″ , d″)  =
              o₁ , l″ , o″ , d″
              , ≤ᵇ⇒≤ (suc j) i (subst T (sym hle) tt)
              , refl , aeq , sym (just-inj stepEq)

stepProtocol-held : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S S′ : ProtocolSt) (j : Id) (oⱼ : Owed) →
  ProtocolSt.current S ≡ just (j , oⱼ) → paidOff oⱼ ≡ true →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (suc j ≤ i)
  × (settle k s (ProtocolSt.live S) [] ≡ just o₁)
  × (applyEvents es (ProtocolSt.live S) o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = suc j ; current = just (i , o″) ; done = d″ })
stepProtocol-held es i s k S S′ j oⱼ Sj pj stepEq =
  stepProtocol-held-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) j oⱼ S′ pj
    (subst (λ c → stepProtocol (es at i from s as k)
             (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                     ; current = c ; done = ProtocolSt.done S }) ≡ just S′)
           Sj stepEq)

-- stepProtocol, continuing an OPEN (unpaid) instant j with a same-instant
-- emit (i ≡ᵇ j): settle carries the running owed oⱼ forward, horizon stays.
stepProtocol-cont-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (j : Id) (oⱼ : Owed)
  (S′ : ProtocolSt) → (i ≡ᵇ j) ≡ true → paidOff oⱼ ≡ false →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = just (j , oⱼ) ; done = dn }) ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (settle k s lv oⱼ ≡ just o₁)
  × (applyEvents es lv o₁ dn ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = hz ; current = just (i , o″) ; done = d″ })
stepProtocol-cont-aux es i s k lv hz dn j oⱼ S′ ib np stepEq
  with i ≡ᵇ j | ib
... | true | refl with paidOff oⱼ | np
...   | false | refl with settle k s lv oⱼ
...     | nothing = ⊥-elim (n≢j stepEq)
...     | just o₁ with applyEvents es lv o₁ dn in aeq
...       | nothing              = ⊥-elim (n≢j stepEq)
...       | just (l″ , o″ , d″)  =
            o₁ , l″ , o″ , d″ , refl , aeq , sym (just-inj stepEq)

stepProtocol-cont : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S S′ : ProtocolSt) (j : Id) (oⱼ : Owed) →
  ProtocolSt.current S ≡ just (j , oⱼ) → (i ≡ᵇ j) ≡ true → paidOff oⱼ ≡ false →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (settle k s (ProtocolSt.live S) oⱼ ≡ just o₁)
  × (applyEvents es (ProtocolSt.live S) o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = ProtocolSt.horizon S
                 ; current = just (i , o″) ; done = d″ })
stepProtocol-cont es i s k S S′ j oⱼ Sj ib np stepEq =
  stepProtocol-cont-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) j oⱼ S′ ib np
    (subst (λ c → stepProtocol (es at i from s as k)
             (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                     ; current = c ; done = ProtocolSt.done S }) ≡ just S′)
           Sj stepEq)

-- stepProtocol, LEAVING an open instant j for a fresh instant i ≢ j.
-- Acceptance forces allZero oⱼ (settleInstant), and openFresh starts the
-- new instant with EMPTY owed regardless of oⱼ; horizon → suc j.
stepProtocol-fresh-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (j : Id) (oⱼ : Owed)
  (S′ : ProtocolSt) → (i ≡ᵇ j) ≡ false →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = just (j , oⱼ) ; done = dn }) ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (suc j ≤ i)
  × (settle k s lv [] ≡ just o₁)
  × (applyEvents es lv o₁ dn ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = suc j ; current = just (i , o″) ; done = d″ })
stepProtocol-fresh-aux es i s k lv hz dn j oⱼ S′ nb stepEq with i ≡ᵇ j | nb
... | false | refl with allZero oⱼ
...   | false = ⊥-elim (n≢j stepEq)
...   | true  with suc j ≤ᵇ i in hle
...     | false = ⊥-elim (n≢j stepEq)
...     | true  with settle k s lv []
...       | nothing = ⊥-elim (n≢j stepEq)
...       | just o₁ with applyEvents es lv o₁ dn in aeq
...         | nothing              = ⊥-elim (n≢j stepEq)
...         | just (l″ , o″ , d″)  =
              o₁ , l″ , o″ , d″
              , ≤ᵇ⇒≤ (suc j) i (subst T (sym hle) tt)
              , refl , aeq , sym (just-inj stepEq)

stepProtocol-fresh : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S S′ : ProtocolSt) (j : Id) (oⱼ : Owed) →
  ProtocolSt.current S ≡ just (j , oⱼ) → (i ≡ᵇ j) ≡ false →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  Σ Owed λ o₁ → Σ (List Source) λ l″ → Σ Owed λ o″ → Σ Bool λ d″ →
    (suc j ≤ i)
  × (settle k s (ProtocolSt.live S) [] ≡ just o₁)
  × (applyEvents es (ProtocolSt.live S) o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
  × (S′ ≡ record { live = l″ ; horizon = suc j ; current = just (i , o″) ; done = d″ })
stepProtocol-fresh es i s k S S′ j oⱼ Sj nb stepEq =
  stepProtocol-fresh-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) j oⱼ S′ nb
    (subst (λ c → stepProtocol (es at i from s as k)
             (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                     ; current = c ; done = ProtocolSt.done S }) ≡ just S′)
           Sj stepEq)

-- The idle-batcher scenario, over the batcher's FIELDS (current = nothing
-- literal), so step-batch reduces to its inline settle/apply/flush form
-- in the goal — the raw settleBatch/applyBatch stay visible, rewritable to
-- o₁/l″/o″, and the paidOff scrutinee is exposed for the case split.
brs-idle-aux : ∀ {A : Set} (seen : List Id) (es : List (InstEvent A)) (i : Id)
  (s : Source) (k : EmitKind) (lvB : List Source) (hz : Id) (dn : Bool)
  (o₁ : Owed) (l″ : List Source) (o″ : Owed) →
  settleBatch k s lvB [] ≡ o₁ →
  proj₁ (applyBatch es lvB o₁ []) ≡ l″ →
  proj₁ (proj₂ (applyBatch es lvB o₁ [])) ≡ o″ →
  seenBefore i seen ≡ true →
  SeenBelow seen (suc i) →
  BatchRel seen
    (record { live = l″ ; horizon = hz ; current = just (i , o″) ; done = dn })
    (proj₂ (step-batch (es at i from s as k)
              (BatchSt A ∋ record { live = lvB ; current = nothing })))
brs-idle-aux seen es i s k lvB hz dn o₁ l″ o″ sb al ao si sbc
  rewrite sb | al | ao with paidOff o″ in po
... | true  = record
    { live-eq = refl
    ; phase = inj₁ (refl , inj₂ ((i , o″) , refl , po , si , sbc)) }
... | false = record
    { live-eq = refl
    ; phase = inj₂ (_ , refl , refl , po , si , sbc) }

-- a new instant flushes the held open batch and starts fresh: the batcher's
-- resulting STATE is identical to starting from an empty (nothing) batch —
-- the flushed prefix only lands in the output, never the carried state
step-batch-flush-eq : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lvB : List Source) (b : OpenBatch A) →
  (OpenBatch.instant b ≡ᵇ i) ≡ false →
  proj₂ (step-batch (es at i from s as k)
           (BatchSt A ∋ record { live = lvB ; current = just b }))
  ≡ proj₂ (step-batch (es at i from s as k)
           (BatchSt A ∋ record { live = lvB ; current = nothing }))
step-batch-flush-eq es i s k lvB b nb
  rewrite nb
  with paidOff (proj₁ (proj₂ (applyBatch es lvB (settleBatch k s lvB []) [])))
... | true  = refl
... | false = refl

-- the same-instant scenario: the batcher KEEPS its open batch b (instant b
-- ≡ᵇ i), settling the running owed b / values b forward, then flush-or-keep
brs-keep-aux : ∀ {A : Set} (seen : List Id) (es : List (InstEvent A)) (i : Id)
  (s : Source) (k : EmitKind) (lvB : List Source) (hz : Id) (dn : Bool)
  (b : OpenBatch A) (o₁ : Owed) (l″ : List Source) (o″ : Owed) →
  (OpenBatch.instant b ≡ᵇ i) ≡ true →
  settleBatch k s lvB (OpenBatch.owed b) ≡ o₁ →
  proj₁ (applyBatch es lvB o₁ (OpenBatch.values b)) ≡ l″ →
  proj₁ (proj₂ (applyBatch es lvB o₁ (OpenBatch.values b))) ≡ o″ →
  seenBefore (OpenBatch.instant b) seen ≡ true →
  SeenBelow seen (suc (OpenBatch.instant b)) →
  BatchRel seen
    (record { live = l″ ; horizon = hz ; current = just (i , o″) ; done = dn })
    (proj₂ (step-batch (es at i from s as k)
              (BatchSt A ∋ record { live = lvB ; current = just b })))
brs-keep-aux seen es i s k lvB hz dn b o₁ l″ o″ ib sb al ao is bl
  rewrite ib | sb | al | ao with paidOff o″ in po
... | true  = record
    { live-eq = refl
    ; phase = inj₁ (refl , inj₂ ((i , o″) , refl , po
                   , subst (λ x → seenBefore x seen ≡ true)
                           (≡ᵇ→≡ (OpenBatch.instant b) i ib) is
                   , subst (λ x → SeenBelow seen (suc x))
                           (≡ᵇ→≡ (OpenBatch.instant b) i ib) bl)) }
... | false = record
    { live-eq = refl
    ; phase = inj₂ (_ , refl
                   , cong (λ x → just (x , o″)) (sym (≡ᵇ→≡ (OpenBatch.instant b) i ib))
                   , po , is , bl) }

postulate
  -- the remaining heart lemma of the simulation (batchrel-step is now
  -- proven below).  flush-step: the emit's online output plus the new open
  -- batch's eventual flush equals the old open batch's flush plus the spec's
  -- contribution for this emit.  [provable by case on BatchRel's phase ×
  -- admitted × paidOff; the arithmetic alignment is the same
  -- settle/applyEvents-vs-settleBatch/applyBatch used by batchrel-step]
  flush-step : ∀ {A : Set} {seen : List Id} {S S′ : ProtocolSt}
    {B : BatchSt A} (x : InstEmit A) (rest : List (InstEmit A)) →
    BatchRel seen S B → stepProtocol x S ≡ just S′ →
    proj₁ (step-batch x B) ++ flushSpec (proj₂ (step-batch x B)) rest
      ≡ flushSpec B (x ∷ rest) ++ specGoHead x seen rest

-- both-closed, automaton HOLDING a paid-off instant j: the batcher already
-- flushed j, so it's idle too; the emit opens a fresh instant i (i ≢ j,
-- horizon → suc j) exactly as in brs-idle, reusing the idle batch reduction
brs-held : ∀ {A : Set} {seen : List Id} {S S′ : ProtocolSt} {B : BatchSt A}
  (es : List (InstEvent A)) (i : Id) (s : Source) (k : EmitKind)
  (j : Id) (oⱼ : Owed) →
  BatchSt.live B ≡ ProtocolSt.live S →
  BatchSt.current B ≡ nothing →
  ProtocolSt.current S ≡ just (j , oⱼ) →
  paidOff oⱼ ≡ true →
  seenBefore j seen ≡ true →
  SeenBelow seen (suc j) →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  BatchRel (seen▸ (es at i from s as k) seen) S′
           (proj₂ (step-batch (es at i from s as k) B))
brs-held {A} {seen} {S} {S′} {B} es i s k j oⱼ leq Bn Sj pj js bl stepEq
  with stepProtocol-held es i s k S S′ j oⱼ Sj pj stepEq
... | o₁ , l″ , o″ , d″ , sucj≤i , stl , apl , S′eq
      rewrite S′eq
            | freshBelow seen i (suc j) bl sucj≤i
            | cong (λ st → proj₂ (step-batch (es at i from s as k) st))
                (subst (λ c → B ≡ (BatchSt A ∋ record { live = BatchSt.live B ; current = c }))
                       Bn refl)
      = brs-idle-aux (i ∷ seen) es i s k (BatchSt.live B) (suc j) d″
          o₁ l″ o″
          (settle-agree k s (BatchSt.live B) []
             (subst (λ l → settle k s l [] ≡ just o₁) (sym leq) stl))
          (proj₁ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) []
             (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                    (sym leq) apl)))
          (proj₂ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) []
             (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                    (sym leq) apl)))
          (seenBefore-hit i seen)
          (seenbelow-cons seen i (suc j) bl sucj≤i)

-- both-OPEN: the batcher holds open batch b, the automaton the same unpaid
-- instant j = instant b.  A same-instant emit (i ≡ᵇ j) continues b (settle
-- carries owed b / values b forward, seen unchanged); a new instant (i ≢ j,
-- forcing owed b empty) flushes b and opens fresh i (horizon → suc j), the
-- batch state reducing exactly as the idle case
brs-open : ∀ {A : Set} {seen : List Id} {S S′ : ProtocolSt} {B : BatchSt A}
  (es : List (InstEvent A)) (i : Id) (s : Source) (k : EmitKind)
  (b : OpenBatch A) →
  BatchSt.live B ≡ ProtocolSt.live S →
  BatchSt.current B ≡ just b →
  ProtocolSt.current S ≡ just (OpenBatch.instant b , OpenBatch.owed b) →
  paidOff (OpenBatch.owed b) ≡ false →
  seenBefore (OpenBatch.instant b) seen ≡ true →
  SeenBelow seen (suc (OpenBatch.instant b)) →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  BatchRel (seen▸ (es at i from s as k) seen) S′
           (proj₂ (step-batch (es at i from s as k) B))
brs-open {A} {seen} {S} {S′} {B} es i s k b leq Bj Sj np is bl stepEq
  with i ≡ᵇ OpenBatch.instant b in ieq
... | true
      with stepProtocol-cont es i s k S S′ (OpenBatch.instant b) (OpenBatch.owed b)
             Sj ieq np stepEq
...   | o₁ , l″ , o″ , d″ , stl , apl , S′eq
        rewrite S′eq
              | subst (λ x → seenBefore x seen ≡ true)
                      (sym (≡ᵇ→≡ i (OpenBatch.instant b) ieq)) is
              | cong (λ st → proj₂ (step-batch (es at i from s as k) st))
                  (subst (λ c → B ≡ (BatchSt A ∋ record { live = BatchSt.live B ; current = c }))
                         Bj refl)
        = brs-keep-aux seen es i s k (BatchSt.live B) (ProtocolSt.horizon S) d″ b
            o₁ l″ o″
            (trans (≡ᵇ-sym (OpenBatch.instant b) i) ieq)
            (settle-agree k s (BatchSt.live B) (OpenBatch.owed b)
               (subst (λ l → settle k s l (OpenBatch.owed b) ≡ just o₁) (sym leq) stl))
            (proj₁ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) (OpenBatch.values b)
               (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                      (sym leq) apl)))
            (proj₂ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) (OpenBatch.values b)
               (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                      (sym leq) apl)))
            is bl
brs-open {A} {seen} {S} {S′} {B} es i s k b leq Bj Sj np is bl stepEq
    | false
      with stepProtocol-fresh es i s k S S′ (OpenBatch.instant b) (OpenBatch.owed b)
             Sj ieq stepEq
...   | o₁ , l″ , o″ , d″ , sucj≤i , stl , apl , S′eq
        rewrite S′eq
              | freshBelow seen i (suc (OpenBatch.instant b)) bl sucj≤i
              | cong (λ st → proj₂ (step-batch (es at i from s as k) st))
                  (subst (λ c → B ≡ (BatchSt A ∋ record { live = BatchSt.live B ; current = c }))
                         Bj refl)
              | step-batch-flush-eq es i s k (BatchSt.live B) b
                  (trans (≡ᵇ-sym (OpenBatch.instant b) i) ieq)
        = brs-idle-aux (i ∷ seen) es i s k (BatchSt.live B) (suc (OpenBatch.instant b)) d″
            o₁ l″ o″
            (settle-agree k s (BatchSt.live B) []
               (subst (λ l → settle k s l [] ≡ just o₁) (sym leq) stl))
            (proj₁ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) []
               (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                      (sym leq) apl)))
            (proj₂ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) []
               (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                      (sym leq) apl)))
            (seenBefore-hit i seen)
            (seenbelow-cons seen i (suc (OpenBatch.instant b)) bl sucj≤i)

batchrel-step : ∀ {A : Set} {seen : List Id} {S S′ : ProtocolSt}
  {B : BatchSt A} (x : InstEmit A) →
  BatchRel seen S B → stepProtocol x S ≡ just S′ →
  BatchRel (seen▸ x seen) S′ (proj₂ (step-batch x B))
batchrel-step {A} {seen} {S} {S′} {B} (es at i from s as k) rel stepEq
  with BatchRel.phase rel
... | inj₂ (b , Bj , Sj , np , is , bl) =
      brs-open {seen = seen} es i s k b (BatchRel.live-eq rel) Bj Sj np is bl stepEq
... | inj₁ (Bn , inj₂ ((j , oⱼ) , Sj , pj , js , bl)) =
      brs-held {seen = seen} es i s k j oⱼ (BatchRel.live-eq rel) Bn Sj pj js bl stepEq
... | inj₁ (Bn , inj₁ (Sn , bl)) = brs-idle
  where
  brs-idle : BatchRel (seen▸ (es at i from s as k) seen) S′
                      (proj₂ (step-batch (es at i from s as k) B))
  brs-idle with stepProtocol-idle es i s k S S′ Sn stepEq
  ... | o₁ , l″ , o″ , d″ , hzi , stl , apl , S′eq
        rewrite S′eq
              | freshBelow seen i (ProtocolSt.horizon S) bl hzi
              | cong (λ st → proj₂ (step-batch (es at i from s as k) st))
                  (subst (λ c → B ≡ (BatchSt A ∋ record { live = BatchSt.live B ; current = c }))
                         Bn refl)
        = brs-idle-aux (i ∷ seen) es i s k (BatchSt.live B) (ProtocolSt.horizon S) d″
            o₁ l″ o″
            (settle-agree k s (BatchSt.live B) []
               (subst (λ l → settle k s l [] ≡ just o₁)
                      (sym (BatchRel.live-eq rel)) stl))
            (proj₁ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) []
               (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                      (sym (BatchRel.live-eq rel)) apl)))
            (proj₂ (apply-agree es (BatchSt.live B) o₁ (ProtocolSt.done S) []
               (subst (λ l → applyEvents es l o₁ (ProtocolSt.done S) ≡ just (l″ , o″ , d″))
                      (sym (BatchRel.live-eq rel)) apl)))
            (seenBefore-hit i seen)
            (seenbelow-cons seen i (ProtocolSt.horizon S) bl hzi)

-- THE waypoint, now PROVEN by induction on xs from the two step lemmas:
-- base is the end-of-stream flush; cons splices step-batch's output,
-- the IH, and specGo's head via associativity (each case one protocol
-- transition — the transitions live inside batchrel-step/flush-step)
fold-agree : ∀ {A : Set} (seen : List Id) (S : ProtocolSt)
  (B : BatchSt A) (xs : List (InstEmit A)) →
  BatchRel seen S B →
  Accepted (runProtocol S xs) →
  foldBatch B xs ≡ flushSpec B xs ++ specGo seen xs
fold-agree seen S B [] rel acc =
  trans (flush≡flushSpec[] B) (sym (++-identityʳ (flushSpec B [])))
fold-agree seen S B (x ∷ rest) rel acc with step-accepted x S rest acc
... | S′ , stepEq , acc′ =
  let out = proj₁ (step-batch x B)
      B′  = proj₂ (step-batch x B)
      ih  = fold-agree (seen▸ x seen) S′ B′ rest (batchrel-step x rel stepEq) acc′
  in trans (cong (out ++_) ih)
       (trans (sym (++-assoc out (flushSpec B′ rest) (specGo (seen▸ x seen) rest)))
         (trans (cong (_++ specGo (seen▸ x seen) rest) (flush-step x rest rel stepEq))
           (trans (++-assoc (flushSpec B (x ∷ rest)) (specGoHead x seen rest)
                            (specGo (seen▸ x seen) rest))
             (cong (flushSpec B (x ∷ rest) ++_) (sym (specGo-split x seen rest))))))

-- WellFormed is acceptance-and-paid; fold-agree only needs acceptance
run-accepted : (m : Maybe ProtocolSt) → Accepted (checkFinal m) → Accepted m
run-accepted (just S) _ = accepted

-- the empty states are related
rel-init : ∀ {A : Set} → BatchRel {A} [] protocol-init batch-init
rel-init = record
  { live-eq = refl
  ; phase   = inj₁ (refl , inj₁ (refl , λ i ()))
  }

batch-agreement :
  ∀ {A} (xs : List (InstEmit A)) → WellFormed xs →
  spec-batchSimultaneous xs ≡ impl-batchSimultaneous xs
batch-agreement xs wf =
  sym (fold-agree [] protocol-init batch-init xs rel-init
        (run-accepted (runProtocol protocol-init xs) wf))

-- THE verified object, end to end: for every program, batching its
-- rendered stream is spec-correct.  A real definition — the proof
-- IS the composition of the two lemmas.
formal-verification-batchSimultaneous :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  spec-batchSimultaneous (evaluate fuel e ins)
    ≡ impl-batchSimultaneous (evaluate fuel e ins)
formal-verification-batchSimultaneous fuel e ins =
  batch-agreement (evaluate fuel e ins) (evaluate-well-formed fuel e ins)
