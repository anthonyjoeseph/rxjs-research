module Verify-Batch-Simultaneous.The-Proof where

open import Data.Bool    using (true; false)
open import Data.Nat     using (ℕ; suc; _≤_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim               using (InstEmit; Fuel; Id)
open import Rx.Exp                using (Ctx; Closed)
open import Rx.Evaluator          using (Slots; evaluate)
open import Rx.Protocol           using (ProtocolSt; Owed; protocol-init;
                                         runProtocol; checkFinal; paidOff;
                                         Accepted; accepted; WellFormed)
open import Verify-Well-Formed    using (evaluate-well-formed)
open import Spec                  using (spec-batchSimultaneous; specGo;
                                         batchOf; valuesAt; seenBefore)
open import Implementation        using (impl-batchSimultaneous; foldBatch;
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

postulate
  -- THE waypoint: the generalized fold agreement.  By induction on
  -- xs; each case is one protocol transition (same-instant continue,
  -- payoff flush, instant change, stream end), using acceptance to
  -- rule the clamps out and freshness to keep specGo's guard honest
  fold-agree : ∀ {A : Set} (seen : List Id) (S : ProtocolSt)
    (B : BatchSt A) (xs : List (InstEmit A)) →
    BatchRel seen S B →
    Accepted (runProtocol S xs) →
    foldBatch B xs ≡ flushSpec B xs ++ specGo seen xs

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
