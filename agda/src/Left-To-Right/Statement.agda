------------------------------------------------------------------
-- LEFT-TO-RIGHT: run the program with `batchSimultaneousᵖ` on the end,
-- read each emit's values, and join the batches back up -- that is the
-- values the program read as plain rxjs delivers, in order.
--
-- CLOSES A CHEAT THE OTHER TOP-LINE STATEMENTS LEAVE OPEN.
-- Elaborating every program to `empty` is trivially batched, and fails
-- left-to-right.
--
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
------------------------------------------------------------------
module Left-To-Right.Statement where

open import Data.Bool    using (T)
open import Data.List    using ([]; concat; map)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx; isData)
open import SExp.Syntax      using (SExp; Kinds)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Plain     using (plainExp; unplainᵈ; plainValues)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Rx.Envelope.Decode using (decodeEmits)
open import Rx.Batch     using (batchSimultaneousᵖ)
open import Implementation.Pipeline using (elaborateImpl; embedSlotsImpl)
open import Batchable.Inst-Extract using (instExtract)

Left-To-Right : Set
Left-To-Right =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  map (unplainᵈ t ok) (concat (map proj₂ (instExtract (decodeEmits
      (concat (evaluate↓ fuel (batchSimultaneousᵖ (elaborateImpl κ e)) (embedSlotsImpl ins)))))))
    ≡ plainValues (concat (evaluate↓ fuel (plainExp e) (plainSlots ins)))

postulate
  left-to-right : Left-To-Right
