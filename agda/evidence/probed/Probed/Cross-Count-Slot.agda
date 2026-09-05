-- ══════════════════════════════════════════════════════════════════
-- THE OUTER CROSSING'S COUNT, INSTANTIATED WHERE READING THE ARRIVAL
-- ALONE FAILS: an observable that names a shared slot.
--
-- TARGET: stepFrame-sz-outer @f4940f
--
-- WHY THIS IS THE REGION WORTH BUYING.  A crossing frame subscribes
-- what arrived, and a variable is the one arrival whose syntax says
-- nothing about the run: it prices at a single node while connecting
-- it runs the whole of the slot's shared definition.  So this is the
-- shape where a count taken off the arrival is furthest from what the
-- frame does, and it is the shape the count's telescope summand
-- exists for.
--
-- THE ROWS ARE THE TWO THAT KILL A COUNT BLIND TO THE TELESCOPE, run
-- against the count that is not.  Twelve duplication rungs behind the
-- slot, then thirteen with the cap moved to match: the emission
-- doubles across the pair, which is what makes the pair measure-side
-- rather than a choice of cap.  Both hold.
--
-- AND THE FIGURES SAY THE COUNT NOW MOVES WITH THE SLOT, which is the
-- finding and not decoration.  The reading these rows replace is
-- pinned at one across both witnesses -- the arriving syntax is a
-- variable in each -- so a green pair would prove nothing about the
-- repair if the count were still constant along the axis the emission
-- grows on.  It is not: it grows by the definition's own four nodes,
-- and `iterSize` doubles per unit of it.
--
-- NOT COVERED: an arrival whose syntax IS what runs -- a chain or a
-- reified value, which is the region `Probed.Cross-Count-Fork` reads;
-- a `scripted` slot, whose contents are data rather than a program to
-- connect; a telescope of more than one slot, where the summand is a
-- sum and the stratification is what bounds a slot naming another; the
-- `from-inner` arm, which reaches its program through the store; and
-- both store halves, whose count is the same quantity but whose
-- conclusion is about the node table.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Slot where

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Evaluator using (root; mergeAllᵒ; thru-outer; sched-init)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (szCount; stepFrame-sz-outer)
open import Refuted.Frame-Step-Size-Slot
  using (Pw; Γ₂; sl₂; e₂; st₂; vals₂; Γ₃; sl₃; e₃; st₃; vals₃)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- WHAT THE COUNT READS AT EACH WITNESS.  The first figure of each pair
-- is the arriving syntax the predecessor reading was confined to; the
-- second is the count as it now stands.
----------------------------------------------------------------------
counts : ℕ
counts = szCount sl₂ (thru-outer {Γ = Γ₂} {u = Pw 12} mergeAllᵒ 0) vals₂
       + 100 * szCount sl₃ (thru-outer {Γ = Γ₃} {u = Pw 13} mergeAllᵒ 0) vals₃

-- LOAD-BEARING: it is what says the count moved along the axis the
-- emission moves on.  A reading blind to the telescope reports `1` at
-- both witnesses, so this row fails for every such reading.
counts≡ : counts ≡ 5652
counts≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The type is generated from the statement as it reads, so
-- a restatement changes both rows underneath rather than leaving a
-- count copied out beside them.  The premises are left as arguments:
-- what each row asserts is the conclusion with them unasked, which is
-- stronger than the instance rather than weaker.
----------------------------------------------------------------------

-- LOAD-BEARING: twelve rungs behind the slot emit `8191` against a cap
-- of `51`, and the arriving syntax is one node.  It fails for any
-- count the emission outruns.
tieSlot12 : Confirms
  (stepFrame-sz-outer {e = e₂} (gasPad 64 g0) 0 0 mergeAllᵒ 0 root vals₂ false
     (sched-init e₂ sl₂) st₂ 51 51)
tieSlot12 = λ _ _ _ → refl

-- LOAD-BEARING jointly with the row above: one more rung doubles the
-- emission to `16383` and moves the cap with it, so a count that did
-- not grow with the definition would lose here even if it cleared the
-- first row.
tieSlot13 : Confirms
  (stepFrame-sz-outer {e = e₃} (gasPad 64 g0) 0 0 mergeAllᵒ 0 root vals₃ false
     (sched-init e₃ sl₃) st₃ 55 55)
tieSlot13 = λ _ _ _ → refl
