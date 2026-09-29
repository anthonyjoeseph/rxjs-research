------------------------------------------------------------------
-- COUNTABLE-OUTPUT: the impl's stream tells a batcher where each
-- instant ends.
--
-- CLOSES A CHEAT THE OTHER TOP-LINE STATEMENTS LEAVE OPEN.  A batcher
-- that holds each batch until the next instant starts fails
-- countable-batches, which pins every batch to one delivery -- this
-- statement is what makes that batcher answerable at all, by giving it
-- a stream that says when an instant is over.
------------------------------------------------------------------
module Countable.Output where

open import Data.List    using ([])
open import Data.Bool    using (T)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx)
open import Rx.SExp      using (SExp; Kinds)
open import Rx.Simul-Slots using (SimulSlots)
open import Rx.Protocol  using (protocol-init)
open import Rx.Elaborated using (elab-mint; elab-toEnvelope; elab-slots)
open import Implementation.Pipeline using (elaborateImpl; embedSlotsImpl; runᴵ)
open import Verify-Input-Well-Formed.Run-Well-Formed using (run-wellFormed)
open import Countable.Countable using (Countable; stampRuns; ends?)

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
