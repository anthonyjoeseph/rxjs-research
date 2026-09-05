-- ══════════════════════════════════════════════════════════════════
-- THE TELESCOPE SUMMAND, READ AT THE ONE SHAPE THAT FORCED IT.
--
-- TARGET: subscribeE-sz @c1fd3b
--
-- WHY THIS POINT AND NOT ANOTHER.  Every other reading of this leaf is
-- taken at a program written out, where the summand is a rounding and
-- the program's own depth is the charge.  The summand was added for
-- the other shape: subscribing a bare SLOT REFERENCE, whose layers are
-- zero and whose run is the whole of the slot's definition.  There the
-- summand is not a rounding but the entire charge, so it is the one
-- place a green row says something the predecessor reading did not
-- already say.  Both rows stand at the refutation's own program, its
-- own telescope and its own state.
--
-- WHAT THE PAIRED ROWS BUY.  Each depth reads the same delivered
-- quantity against two rungs -- the telescope-free charge and the
-- repaired one -- and reports `false` then `true`.  The first entry of
-- each pair IS the refutation's row, since the queue it refutes at is
-- a singleton and a singleton drain delivers exactly what the one
-- subscription below it delivers.  So a repair that had reached the
-- schedule without reading the slot table would repeat that row in the
-- second.  What the pair decides is REACHABILITY: the subscription is
-- handed a `Sched`, and whether the telescope standing behind a parked
-- reference is legible from there is what the row answers.
--
-- AND THE CHARGE MOVES WITH THE SLOT, which is what makes the second
-- depth worth taking.  One more rung behind the reference doubles the
-- emission and moves the charge from fifty-one to fifty-five, where the
-- predecessor's charge was zero at both.  So the axis swept is
-- measure-side and the rows could have failed on it.
--
-- WHAT THE ROWS DO NOT SAY, and it is the honest half: the clearance
-- here is not tight and cannot be.  This family spends four units of
-- slot syntax per doubling of emission while a rung admits size
-- geometrically in the charge, so once the telescope is in the charge
-- at all the summand dominates by construction.  The rows are evidence
-- that the summand REACHES the subscription, not that its size is
-- right.
--
-- NOT COVERED: a program family whose emission outruns four units of
-- slot syntax per doubling, which is where the summand's SIZE would be
-- decided rather than its reach; a telescope of several slots, since
-- both rows carry one; a slot that is `scripted` rather than `shared`,
-- whose definition the subscription does not run; an operator other
-- than `mergeAllᵒ` at the path's inner end; and the ledger tie, which
-- these rows say nothing about -- the charge reaches the whole
-- telescope, so a per-frame ceiling that is a fixed product is a
-- separate question.
-- ══════════════════════════════════════════════════════════════════
module Probed.Drain-Count-Slot where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Val)
open import Rx.Slots using (slotsSize)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Evaluator
  using (root; mergeAllᵒ; from-inner; _↠_; sched-init; iterSize; subscribeInner)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; subscribeE-sz)
open import Refuted.Frame-Step-Size-Slot
  using (Pw; Γ₂; sl₂; e₂; Γ₃; sl₃; e₃)
open import Refuted.Drain-Queue-Slot
  using (o₂; st₂; o₃; st₃)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- WHAT ONE SUBSCRIPTION OF THE PARKED REFERENCE DELIVERS, at the two
-- depths.  The state is the one the drain runs off, so the row stands
-- where the arm actually reaches this leaf.
----------------------------------------------------------------------
out₂ : List (Val Γ₂ (Pw 12))
out₂ = proj₁ (proj₂ (subscribeInner {e = e₂} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                       o₂ (sched-init e₂ sl₂) st₂))

out₃ : List (Val Γ₃ (Pw 13))
out₃ = proj₁ (proj₂ (subscribeInner {e = e₃} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                       o₃ (sched-init e₃ sl₃) st₃))

----------------------------------------------------------------------
-- THE FOUR CHARGES, READ OFF THE STATES THE ROWS STAND AT: the parked
-- program's own layers, and those layers plus the telescope the
-- reference names.  The first of each pair is what the refuted reading
-- saw.
----------------------------------------------------------------------
slotCharges : List ℕ
slotCharges = layᵉ o₂
            ∷ layᵉ o₂ + slotsSize sl₂
            ∷ layᵉ o₃
            ∷ layᵉ o₃ + slotsSize sl₃
            ∷ []

slotCharges≡ : slotCharges ≡ 0 ∷ 51 ∷ 0 ∷ 55 ∷ []
slotCharges≡ = refl

----------------------------------------------------------------------
-- THE CONCLUSION AT BOTH RUNGS, TWICE OVER.
----------------------------------------------------------------------

-- LOAD-BEARING: entries one and three are the refutation's own rows, so
-- a summand that had failed to reach the slot table would report
-- `false` four times; entries two and four are the repaired reading at
-- charges that moved with the slot and not with the program.
slotRows : List Bool
slotRows = valsSz? {Γ = Γ₂} {s = Pw 12} (iterSize 51 (layᵉ o₂) 51) out₂
         ∷ valsSz? {Γ = Γ₂} {s = Pw 12}
             (iterSize 51 (layᵉ o₂ + slotsSize sl₂) 51) out₂
         ∷ valsSz? {Γ = Γ₃} {s = Pw 13} (iterSize 55 (layᵉ o₃) 55) out₃
         ∷ valsSz? {Γ = Γ₃} {s = Pw 13}
             (iterSize 55 (layᵉ o₃ + slotsSize sl₃) 55) out₃
         ∷ []

slotRows≡ : slotRows ≡ false ∷ true ∷ false ∷ true ∷ []
slotRows≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The types are generated from the statement as it reads,
-- so a restatement changes them rather than leaving the rungs above
-- copied out beside a claim.  The premises are left as arguments: each
-- row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: the schedule and the state are the ones an exiting
-- inner hands the drain at this door, and the drain hands straight on,
-- so the row stands where the arm actually reaches it.
tieDrainSlot12 : Confirms
  (subscribeE-sz {e = e₂} (gasPad 63 g0) o₂ (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init e₂ sl₂) { nextNode = 1 }) st₂ 51 51)
tieDrainSlot12 = λ _ _ → refl

-- LOAD-BEARING: same statement one rung deeper behind the reference,
-- which is the sweep's measure-side axis.
tieDrainSlot13 : Confirms
  (subscribeE-sz {e = e₃} (gasPad 63 g0) o₃ (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init e₃ sl₃) { nextNode = 1 }) st₃ 55 55)
tieDrainSlot13 = λ _ _ → refl
