------------------------------------------------------------------
-- WHAT A BATCHER NEEDS OF A STREAM TO BATCH IT WITHOUT WAITING.
--
-- A stream here is flat: emits in the order a subscriber receives
-- them, each stamped with an instant.  Its STAMP RUNS are its maximal
-- stretches of one stamp, which is exactly how the spec cuts it
-- (`Spec.batchFrom` closes a batch the moment the instant changes).
-- The spec reads the next emit to learn that a run is over; a batcher
-- running live cannot, so the stream has to say so itself.
--
-- `Countable` IS THE STREAM SAYING SO.  The envelope obeys the
-- protocol, and the protocol's counting automaton reads the last emit
-- of every stamp run as closing its instant, and no earlier one.  A
-- batch can then leave with the emit that ends its run instead of
-- with the next run's first.
--
-- THE STAMPS ARE NOT CONSTRAINED HERE.  Whether they are the right
-- instants is `Timing-Correct`'s question, about one program; this is
-- the batcher's, about any stream at all.
------------------------------------------------------------------
module Verify-Batch-Simultaneous.Countable where

open import Data.Bool    using (Bool; true; false; T; if_then_else_)
open import Data.List    using (List; []; _∷_; _++_; _∷ʳ_; concat; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (_≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Rx.Prim     using (Id; InstEvent; value; InstEmit)
open import Rx.Protocol using (ProtocolSt; protocol-init; stepProtocol; runProtocol;
                               Accepted; paidOff)
import Spec
open Spec Id _≟_ using (spec-batchSimultaneous)

------------------------------------------------------------------
-- What a subscriber sees of a stream, and what the spec is handed.
------------------------------------------------------------------

valuesᴱ : ∀ {A : Set} → List (InstEvent A) → List A
valuesᴱ []             = []
valuesᴱ (value v ∷ es) = v ∷ valuesᴱ es
valuesᴱ (_       ∷ es) = valuesᴱ es

-- the spec's input: every value tagged with its emit's instant; a
-- valueless emit contributes nothing, which is what a subscriber would
-- see of it
toSpec : ∀ {A : Set} → List (InstEmit A) → List (Id × A)
toSpec []       = []
toSpec (x ∷ xs) = map (InstEmit.instant x ,_) (valuesᴱ (InstEmit.events x)) ++ toSpec xs

------------------------------------------------------------------
-- Stamp runs.
------------------------------------------------------------------

runsFrom : ∀ {A : Set} → Id → List (InstEmit A) → List (InstEmit A) → List (List (InstEmit A))
runsFrom i run []       = run ∷ []
runsFrom i run (x ∷ xs) with i ≟ InstEmit.instant x
... | yes _ = runsFrom i (run ∷ʳ x) xs
... | no  _ = run ∷ runsFrom (InstEmit.instant x) (x ∷ []) xs

stampRuns : ∀ {A : Set} → List (InstEmit A) → List (List (InstEmit A))
stampRuns []       = []
stampRuns (x ∷ xs) = runsFrom (InstEmit.instant x) (x ∷ []) xs

------------------------------------------------------------------
-- `ends`, read by the protocol automaton.
------------------------------------------------------------------

-- the open instant is paid off: nothing more can join it
closes : ProtocolSt → Bool
closes ps with ProtocolSt.current ps
... | just (_ , owed) = paidOff owed
... | nothing         = false

-- one run: every emit but the last leaves its instant open, and the
-- last one closes it
markStep : ∀ {A : Set} → Maybe ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
markStep nothing    _        = nothing
markStep (just ps) []       = if closes ps then just ps else nothing
markStep (just ps) (y ∷ ys) = if closes ps then nothing else markStep (stepProtocol y ps) ys

marks : ∀ {A : Set} → ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
marks ps []       = just ps
marks ps (x ∷ xs) = markStep (stepProtocol x ps) xs

endsFrom : ∀ {A : Set} → Maybe ProtocolSt → List (List (InstEmit A)) → Bool
endsFrom nothing    _           = false
endsFrom (just ps) []          = true
endsFrom (just ps) (run ∷ rs)  = endsFrom (marks ps run) rs

ends? : ∀ {A : Set} → ProtocolSt → List (List (InstEmit A)) → Bool
ends? ps runs = endsFrom (just ps) runs

------------------------------------------------------------------
-- The record.
------------------------------------------------------------------

record Countable {A : Set} (xs : List (InstEmit A)) : Set where
  field
    -- the envelope obeys the protocol
    accepted : Accepted (runProtocol protocol-init xs)
    -- and marks the last emit of each stamp run, and no earlier one
    ends     : T (ends? protocol-init (stampRuns xs))

------------------------------------------------------------------
-- What a batcher owes, emit by emit.
------------------------------------------------------------------

-- NOTHING UNTIL THE LAST EMIT OF A STAMP RUN, which owes the spec's
-- batching of that run: one batch of its values, or none if it had
-- none.  Owing it any earlier is clairvoyance; owing it any later is
-- waiting for the next run.
dueIn : ∀ {A B : Set} → List (List A) → List B → List (List (List A))
dueIn b []           = []
dueIn b (_ ∷ [])     = b ∷ []
dueIn b (_ ∷ y ∷ ys) = [] ∷ dueIn b (y ∷ ys)

due : ∀ {A : Set} → List (InstEmit A) → List (List (List A))
due xs = concat (map (λ run → dueIn (spec-batchSimultaneous (toSpec run)) run) (stampRuns xs))
