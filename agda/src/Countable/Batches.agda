------------------------------------------------------------------
-- COUNTABLE-BATCHES: handed any such stream, the batcher gives the
-- spec's batches, each with the emit that ends its instant.
--
-- CLOSES A CHEAT THE OTHER TOP-LINE STATEMENTS LEAVE OPEN.  A batcher
-- that holds each batch until the next instant starts fails this one,
-- which pins every batch to one delivery.
--
-- THE STATEMENTS MEET IN RAW VALUES, as a subscriber sees them.  No
-- envelope is compared anywhere; valueless emits contribute nothing.
------------------------------------------------------------------
module Countable.Batches where

open import Data.Bool    using (T)
open import Data.Fin     using (zero; suc)
open import Data.List    using (List; []; _∷_; concat; map; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe   using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Data.Vec     using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Function     using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (InstEmit; valueᵖ; hot; after_,_)
open import Rx.Exp       using (Ctx; Ty; Val; Closed; isData; unitᵗ; _+ᵗ_; listᵗ;
                                input; ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ; inlᵗ; inrᵗ; varᵗ; unit̂)
open import Rx.Slots     using (Slots; scripted)
open import Rx.Envelope  using (machineEmitᵗ)
open import Rx.Envelope.Decode using (encodeEmit)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Plain     using (plainValues)
open import Rx.Batch     using (batchSimultaneousᵖ)
open import Implementation.Pipeline using (unwrapImpl)
open import Countable.Countable using (Countable; due)

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
