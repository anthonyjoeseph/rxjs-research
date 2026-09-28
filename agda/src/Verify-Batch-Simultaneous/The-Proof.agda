------------------------------------------------------------------
-- THE TOP LINE: four statements, and together they are the claim that
-- `batchSimultaneous` batches what plain rxjs would deliver, by
-- instant, without reordering and without waiting.
--
--   left-to-right      the batches, joined back up, are the values the
--                      program read as plain rxjs delivers, in order
--   timing-correct     the impl's instant stamps group emits exactly
--                      as the timed translation's packets do
--   countable-output   the impl's stream tells a batcher where each
--                      instant ends
--   countable-batches  handed any such stream, the batcher gives the
--                      spec's batches, each with the emit that ends
--                      its instant
--
-- EACH CLOSES A CHEAT THE OTHERS LEAVE OPEN.  Elaborating every program
-- to `empty` is countable and trivially batched, and fails
-- left-to-right.  Stamping every emit with one instant, or each with
-- its own, fails timing-correct, since the packets are the translation's
-- and not the impl's to arrange.  A batcher that holds each batch until
-- the next instant starts fails countable-batches, which pins every
-- batch to one delivery.
--
-- `timed-faithful` IS THE TRANSLATION'S OWN OBLIGATION, not the impl's:
-- a translation to `empty` would make timing-correct say nothing.
--
-- THE STATEMENTS MEET IN RAW VALUES, as a subscriber sees them.  No
-- envelope is compared anywhere; valueless emits contribute nothing.
------------------------------------------------------------------
module Verify-Batch-Simultaneous.The-Proof where

open import Data.Bool    using (T)
open import Data.Fin     using (zero; suc)
open import Data.List    using (List; []; _∷_; concat; map; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Maybe   using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Data.Vec     using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Function     using (_∘_; _⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Fuel; InstEmit; valueᵖ; hot; after_,_)
open import Rx.Exp       using (Ctx; Ty; Val; Closed; isData; unitᵗ; _+ᵗ_; listᵗ;
                                input; ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ; inlᵗ; inrᵗ; varᵗ; unit̂)
open import Rx.SExp      using (SExp; Kinds)
open import Rx.Slots     using (Slots; scripted)
open import Rx.Envelope  using (machineEmitᵗ)
open import Rx.Envelope.Decode using (encodeEmit)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Plain     using (plainExp; unplainᵈ; plainValues)
open import Rx.Simul-Slots using (SimulSlots; plainSlots)
open import Rx.Batch     using (batchSimultaneousᵖ)
open import Rx.Protocol  using (protocol-init)
open import Rx.Elaborated using (elab-mint; elab-toEnvelope; elab-slots)
open import Rx.Timed     using (timed; timedSlots; packetOf; valuesᵀ; untimedᵈ)
open import Implementation.Pipeline using (elaborateImpl; embedSlotsImpl; runᴵ; batchesᴵ; unwrapImpl)
open import Verify-Input-Well-Formed.Run-Well-Formed using (run-wellFormed)
open import Verify-Batch-Simultaneous.Countable using (Countable; toSpec; stampRuns; ends?; due)

------------------------------------------------------------------
-- LEFT-TO-RIGHT.
------------------------------------------------------------------

-- AT DATA TYPES ONLY, AND THAT IS A LIMIT OF WHAT `≡` CAN SAY RATHER
-- THAN OF THE CLAIM.  The two runs stand in different contexts -- the
-- elaboration's reads a share at the envelope -- and a value at `obs`
-- is a closure over its context, so two of them are not comparable by
-- equality at all.  A data value is the same value in every context,
-- which `unplainᵈ` says.
--
-- OVER EVERY PROGRAM, SO OVER EVERY TIMED ONE: at `timed κ e` the
-- values compared are (packet, value) pairs, and the batches are then
-- read against the packets.
--
-- THE IMPL'S SHARED-SLOT FALLBACK IS OWED HERE.  `embedSlotsImpl`
-- checks stratification of the elaborated definition and falls back to
-- `empty` if it fails; the table only certifies the plain one, so this
-- statement is where "the check never fails" is paid.
Left-To-Right : Set
Left-To-Right =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  map (unplainᵈ t ok) (concat (batchesᴵ κ fuel e ins))
    ≡ plainValues (concat (evaluate↓ fuel (plainExp e) (plainSlots ins)))

postulate
  left-to-right : Left-To-Right

------------------------------------------------------------------
-- TIMING-CORRECT.
------------------------------------------------------------------

-- EVERY PAIR OF VALUES THE IMPL EMITS FOR A TIMED PROGRAM: same stamp
-- exactly when same packet.  END items carry packets too, so a
-- completion's instant is pinned as well as a value's.
Timing-Correct : Set
Timing-Correct =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  AllPairs (λ p q → (proj₁ p ≡ proj₁ q) ⇔ (packetOf t (proj₂ p) ≡ packetOf t (proj₂ q)))
           (toSpec (runᴵ κ fuel (timed κ e) (timedSlots ins)))

postulate
  timing-correct : Timing-Correct

------------------------------------------------------------------
-- COUNTABLE-OUTPUT.
------------------------------------------------------------------

Countable-Output : Set
Countable-Output =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  Countable (runᴵ κ fuel e ins)

-- FALSE ON TODAY'S IMPL AT EVERY SUBSCRIBE FRAME THE QUICKCHECK
-- REACHES: a `subscribe`-kind emit settles nothing, so its instant's
-- owed list stays empty and `paidOff` never reads it as closed.
postulate
  output-ends :
    ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
      (ins : SimulSlots Γ κ) →
    T (ends? protocol-init (stampRuns (runᴵ κ fuel e ins)))

-- ACCEPTANCE IS NOT A LEAF HERE: it is `run-wellFormed`, whose own
-- leaves are tier 3's.
countable-output : Countable-Output
countable-output κ fuel e ins = record
  { accepted = run-wellFormed fuel (elaborateImpl κ e) (embedSlotsImpl ins)
                              (elab-mint (elab-toEnvelope κ e)) (elab-slots refl ins refl)
  ; ends     = output-ends κ fuel e ins
  }

------------------------------------------------------------------
-- COUNTABLE-BATCHES.
------------------------------------------------------------------

-- THE REPLAY: a stream handed to the batcher as a hot script of
-- envelope values, one scheduled delivery per emit.  The batcher sees
-- nothing of the program that made it, so its proof can use nothing
-- but `Countable`.
Γᴿ : Ty → Ctx 1
Γᴿ a = machineEmitᵗ a ∷ⱽ []ⱽ

replay : ∀ {a} → T (isData (machineEmitᵗ a)) → List (InstEmit (Val (Γᴿ a) a)) → Slots (Γᴿ a)
replay ok xs zero    = scripted {ok = ok} (hot (map (λ x → after 0 , encodeEmit x) xs))
replay ok xs (suc ())

-- A SUBSCRIBER WATCHING THE REPLAY AND THE BATCHES AT ONCE.  It
-- subscribes to the replay first, so each delivery reaches it as a
-- tick before the batcher sees it, and whatever the batcher emits in
-- that delivery's cascade lands after the tick and before the next.
-- This is how "when" is read without the evaluator's cut: from plain
-- rxjs's own ordering of two subscribers to one hot source.
clockᵖ : ∀ {a} → Closed (Γᴿ a) (unitᵗ +ᵗ machineEmitᵗ (listᵗ a))
clockᵖ = mergeAllᵉ nothing
  (ofᵉ (strmᵗ (mapᵉ (inlᵗ unit̂) (input zero))
      ∷ strmᵗ (mapᵉ (inrᵗ (varᵗ (here refl))) (batchSimultaneousᵖ (input zero)))
      ∷ []))

private
  cut : ∀ {B : Set} → List (⊤ ⊎ B) → List B × List (List B)
  cut []            = [] , []
  cut (inj₁ _ ∷ xs) = [] , (proj₁ (cut xs) ∷ proj₂ (cut xs))
  cut (inj₂ b ∷ xs) = (b ∷ proj₁ (cut xs)) , proj₂ (cut xs)

-- what the subscriber saw before the first tick, then after each
windows : ∀ {B : Set} → List (⊤ ⊎ B) → List (List B)
windows xs = proj₁ (cut xs) ∷ proj₂ (cut xs)

-- NOTHING AT SUBSCRIBE, THEN AFTER EACH DELIVERY EXACTLY WHAT IT OWES
-- (`Countable.due`): a batch with the emit that ends its stamp run,
-- and nothing with any other.
--
-- RECOVERY: git show f5ba6a6c:agda/src/Verify-Batch-Simultaneous/The-Proof.agda
--   restores `batch-agreement` and `fold-agree`: an online fold over an
--   accepted stream proven equal to a grouping spec, by a relation
--   between the fold's state, the protocol's and the spec's pending
--   instants -- the shape a proof of this statement through a
--   meta-level mirror of the operator would take.
Countable-Batches : Set
Countable-Batches =
  ∀ {a} (ok : T (isData (machineEmitᵗ a))) (xs : List (InstEmit (Val (Γᴿ a) a))) →
  Countable xs →
  map (unwrapImpl ∘ map valueᵖ)
      (windows (plainValues (concat (evaluate↓ (length xs) clockᵖ (replay ok xs)))))
    ≡ [] ∷ due xs

postulate
  countable-batches : Countable-Batches

------------------------------------------------------------------
-- TIMED-FAITHFUL.
------------------------------------------------------------------

-- the timed run, packets and END items dropped, is the plain run
Timed-Faithful : Set
Timed-Faithful =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  map (untimedᵈ t ok)
      (valuesᵀ {t = t} (plainValues (concat (evaluate↓ fuel (plainExp (timed κ e))
                                                         (plainSlots (timedSlots ins))))))
    ≡ plainValues (concat (evaluate↓ fuel (plainExp e) (plainSlots ins)))

postulate
  timed-faithful : Timed-Faithful

------------------------------------------------------------------
-- THE VERIFIED OBJECT.
------------------------------------------------------------------

formal-verification-batchSimultaneous :
  Left-To-Right × Timing-Correct × Countable-Output × Countable-Batches × Timed-Faithful
formal-verification-batchSimultaneous =
  left-to-right , timing-correct , countable-output , countable-batches , timed-faithful
