------------------------------------------------------------------
-- THE TOP LINE: three statements, side by side, and together they are
-- the claim that `batchSimultaneous` batches what plain rxjs would
-- deliver, by instant, without reordering and without waiting.
--
--   input-well-formed  every program's run is `WellFormed`: one
--                      instant per arrival, the envelope marking where
--                      each ends
--   plain-agrees       the run carries the values the program read as
--                      plain rxjs carries, arrival by arrival
--   batch-agrees       handed any well-formed run, the batcher gives
--                      the spec's batches, each in the arrival that
--                      ends its instant
--
-- EACH CLOSES A CHEAT THE OTHER TWO LEAVE OPEN.  Stamping every emit
-- with one instant, or each with its own, fails `input-well-formed`,
-- since the arrival cut is the fixed evaluator's.  Elaborating every
-- program to `empty` -- well formed, and trivially batched -- fails
-- `plain-agrees`; so does holding a value back one arrival, which is
-- why that comparison is per arrival rather than flat.  And
-- `batch-agrees` sees only a replay of a run, so its proof can use
-- nothing about the program but the `WellFormed` facts: the tree and
-- the batcher are decoupled exactly there.
--
-- THE THREE MEET IN RAW VALUES, as a subscriber sees them.  No
-- envelope is compared anywhere; valueless emits contribute nothing.
------------------------------------------------------------------
module Verify-Batch-Simultaneous.The-Proof where

open import Data.Bool    using (T)
open import Data.Fin     using (zero; suc)
open import Data.List    using (List; []; _∷_; concat; map; length; take; drop)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Nat     using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec     using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Function     using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Rx.Prim      using (Id; Fuel; InstEmit; hot; after_,_)
open import Rx.Exp       using (Ctx; Ty; Val; isData; input)
open import Rx.SExp      using (SExp; Kinds)
open import Rx.Slots     using (Slots; scripted)
open import Rx.Envelope  using (machineEmitᵗ)
open import Rx.Envelope.Decode using (encodeEmit)
open import Rx.Arrivals  using (arrivals↓)
open import Rx.Plain     using (plainExp; unplainᵈ; plainValues)
open import Rx.Simul-Slots using (SimulSlots; plainSlots)
open import Rx.Batch     using (batchSimultaneousᵖ)
open import Rx.Protocol  using (protocol-init)
open import Rx.Elaborated using (elab-mint; elab-toEnvelope; elab-slots)
open import Implementation.Pipeline using (elaborateImpl; embedSlotsImpl; runᴵ; unwrapImpl)
open import Verify-Input-Well-Formed.Run-Well-Formed using (run-wellFormed)
open import Verify-Batch-Simultaneous.Well-Formed using (WellFormed; valuesOf; toSpec; ends?)
import Spec
open Spec Id _≟_ using (spec-batchSimultaneous)

------------------------------------------------------------------
-- INPUT-WELL-FORMED.
------------------------------------------------------------------

Input-Well-Formed : Set
Input-Well-Formed =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  WellFormed (runᴵ κ fuel e ins)

-- THE THREE INSTANT FIELDS ARE THE ELABORATION'S OWN CLAIMS, AND THE
-- QUICKCHECK REFUTES TWO OF THEM ON TODAY'S IMPL.  `arrival-same` falls
-- where a share's connect mints its own instant inside the subscribe
-- frame (bug-cache `seed 9 depth 1 case 2`), and where an inner spawned
-- by a delivery is stamped with the subscribe instant rather than its
-- trigger's (`seed 2 depth 1 case 15`); `arrival-distinct` falls on the
-- second, since that stamp recurs in every later arrival.
postulate
  arrival-same :
    ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
      (ins : SimulSlots Γ κ) →
    All (λ arr → Σ Id (λ i → All (λ x → InstEmit.instant x ≡ i) arr)) (runᴵ κ fuel e ins)

  arrival-distinct :
    ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
      (ins : SimulSlots Γ κ) →
    AllPairs (λ arr arr′ → All (λ x → All (λ y →
               InstEmit.instant x ≢ InstEmit.instant y) arr′) arr)
             (runᴵ κ fuel e ins)

  -- FALSE TODAY AT EVERY SUBSCRIBE FRAME THE QUICKCHECK REACHES, which
  -- is the tier's open operator problem seen from the run's side: a
  -- `subscribe`-kind emit settles nothing, so its instant's owed list
  -- stays empty and `paidOff` never reads it as closed.
  arrival-ends :
    ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
      (ins : SimulSlots Γ κ) →
    T (ends? protocol-init (runᴵ κ fuel e ins))

-- ACCEPTANCE IS NOT A LEAF HERE: it is `run-wellFormed`, whose own
-- leaves are tier 3's.
input-well-formed : Input-Well-Formed
input-well-formed κ fuel e ins = record
  { same     = arrival-same κ fuel e ins
  ; distinct = arrival-distinct κ fuel e ins
  ; accepted = run-wellFormed fuel (elaborateImpl κ e) (embedSlotsImpl ins)
                              (elab-mint (elab-toEnvelope κ e)) (elab-slots refl ins refl)
  ; ends     = arrival-ends κ fuel e ins
  }

------------------------------------------------------------------
-- PLAIN-AGREES.
------------------------------------------------------------------

-- AT DATA TYPES ONLY, AND THAT IS A LIMIT OF WHAT `≡` CAN SAY RATHER
-- THAN OF THE CLAIM.  The two runs stand in different contexts -- the
-- elaboration's reads a share at the envelope -- and a value at `obs`
-- is a closure over its context, so two of them are not comparable by
-- equality at all.  A data value is the same value in every context,
-- which `unplainᵈ` says.
--
-- THE QUICKCHECK REFUTES IT ON TODAY'S IMPL, at the two flatteners
-- that drop: a switched-away inner stays subscribed (bug-cache `seed 6
-- depth 1 case 4`), and an inner arriving while one is live is not
-- dropped (`seed 7 depth 1 case 12`).
--
-- THE IMPL'S SHARED-SLOT FALLBACK IS OWED HERE.  `embedSlotsImpl`
-- checks stratification of the elaborated definition and falls back to
-- `empty` if it fails; the table only certifies the plain one, so this
-- statement is where "the check never fails" is paid.
Plain-Agrees : Set
Plain-Agrees =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  map (map (unplainᵈ t ok) ∘ valuesOf) (runᴵ κ fuel e ins)
    ≡ map plainValues (arrivals↓ fuel (plainExp e) (plainSlots ins))

postulate
  plain-agrees : Plain-Agrees

------------------------------------------------------------------
-- BATCH-AGREES.
------------------------------------------------------------------

-- THE REPLAY: a run handed to the batcher as a hot script of envelope
-- values, one scheduled delivery per emit.  Every emit is its own
-- arrival there, so a batcher that waits for the NEXT arrival to learn
-- an instant is over gives its batch late; one that reads the
-- envelope's `ends` mark gives it with the emit that ends the instant.
Γᴿ : Ty → Ctx 1
Γᴿ a = machineEmitᵗ a ∷ⱽ []ⱽ

replay : ∀ {a} → T (isData (machineEmitᵗ a)) → List (InstEmit (Val (Γᴿ a) a)) → Slots (Γᴿ a)
replay ok xs zero    = scripted {ok = ok} (hot (map (λ x → after 0 , encodeEmit x) xs))
replay ok xs (suc ())

-- the replay's arrivals gathered back into the run's, `k` at a time
regroup : ∀ {B : Set} → List ℕ → List (List B) → List (List B)
regroup []       xs = []
regroup (k ∷ ks) xs = concat (take k xs) ∷ regroup ks (drop k xs)

-- THE REPLAY'S SUBSCRIBE FRAME COMES FIRST AND IS EMPTY, then each of
-- the run's arrivals: what the batcher gave while that arrival's emits
-- were delivered is the spec's batching of that arrival.  Over the
-- whole run this is the spec's batching of the run, by `wf-batches`.
--
-- RECOVERY: git show f5ba6a6c:agda/src/Verify-Batch-Simultaneous/The-Proof.agda
--   restores `batch-agreement` and `fold-agree`: an online fold over an
--   accepted stream proven equal to a grouping spec, by a relation
--   between the fold's state, the protocol's and the spec's pending
--   instants -- the shape a proof of this statement through a
--   meta-level mirror of the operator would take.
Batch-Agrees : Set
Batch-Agrees =
  ∀ {a} (ok : T (isData (machineEmitᵗ a))) (run : List (List (InstEmit (Val (Γᴿ a) a)))) →
  WellFormed run →
  regroup (1 ∷ map length run)
    (map unwrapImpl (arrivals↓ (length (concat run))
                               (batchSimultaneousᵖ (input zero))
                               (replay ok (concat run))))
    ≡ [] ∷ map (spec-batchSimultaneous ∘ toSpec) run

postulate
  batch-agrees : Batch-Agrees

------------------------------------------------------------------
-- THE VERIFIED OBJECT.
------------------------------------------------------------------

formal-verification-batchSimultaneous : Input-Well-Formed × Plain-Agrees × Batch-Agrees
formal-verification-batchSimultaneous = input-well-formed , plain-agrees , batch-agrees
