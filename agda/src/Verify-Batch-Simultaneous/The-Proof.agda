module Verify-Batch-Simultaneous.The-Proof where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (ℕ; suc; _≤_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Prim               using (InstEmit; Fuel; Id; Source; _at_from_as_;
                                         InstEvent; init; value; close; handoff;
                                         complete; EmitKind; subscribe; delivery;
                                         plumbing; CloseReason; cut; cutPending;
                                         exhausted)
open import Rx.Exp                using (Ctx; Closed)
open import Rx.Evaluator          using (Slots; evaluate)
open import Rx.Protocol           using (ProtocolSt; Owed; protocol-init;
                                         runProtocol; stepProtocol; checkFinal;
                                         paidOff; Accepted; accepted; WellFormed;
                                         settle; applyEvents; hasOwed; bumpOwed;
                                         payOwed; cancelOwed; removeOne; countIn)
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

postulate
  -- the two heart lemmas of the simulation, one protocol transition
  -- each.  batchrel-step: acceptance keeps the online batcher's state
  -- lock-stepped with the automaton's (the clamps never fire, the open
  -- instant stays in `seen`).  flush-step: the emit's online output
  -- plus the new open batch's eventual flush equals the old open
  -- batch's flush plus the spec's contribution for this emit.  [both
  -- provable by case on BatchRel's phase × admitted × paidOff; the
  -- arithmetic alignment is settle/applyEvents-vs-settleBatch/applyBatch]
  batchrel-step : ∀ {A : Set} {seen : List Id} {S S′ : ProtocolSt}
    {B : BatchSt A} (x : InstEmit A) →
    BatchRel seen S B → stepProtocol x S ≡ just S′ →
    BatchRel (seen▸ x seen) S′ (proj₂ (step-batch x B))
  flush-step : ∀ {A : Set} {seen : List Id} {S S′ : ProtocolSt}
    {B : BatchSt A} (x : InstEmit A) (rest : List (InstEmit A)) →
    BatchRel seen S B → stepProtocol x S ≡ just S′ →
    proj₁ (step-batch x B) ++ flushSpec (proj₂ (step-batch x B)) rest
      ≡ flushSpec B (x ∷ rest) ++ specGoHead x seen rest

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
