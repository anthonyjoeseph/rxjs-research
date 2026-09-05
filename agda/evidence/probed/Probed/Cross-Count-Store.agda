-- ══════════════════════════════════════════════════════════════════
-- WHAT ONE SUBSCRIPTION OF A PARKED PROGRAM DELIVERS, READ AT THE VERY
-- WITNESS THAT KILLED THE CONSTANT IT REPLACES.
--
-- TARGET: subscribeE-sz @c1fd3b
--
-- WHY THIS POINT AND NOT ANOTHER.  The inner arm subscribes what the
-- `*All` node has PARKED, so the program it runs is in the node table
-- and not among the arriving values -- which is why the charge reads
-- the queue at the frame's own node, and why the whole arm reduces to
-- what one SUBSCRIPTION of a parked program delivers.  A receipt for
-- that reading is worth having only where the predecessor reading
-- FAILED, since anywhere else a green row is bought by the program
-- being small rather than by the denomination being right.  So the
-- rows are taken at the refutation's own state: the drain door with a
-- twelve-rung duplication chain parked behind it.
--
-- WHAT THE PAIRED FIGURES BUY.  The same delivered quantity is read
-- against two rungs -- the constant one and the parked program's own
-- plus the telescope -- and reports `false` then `true`.  The
-- telescope is a single scripted slot, so what the second rung is
-- bought by is the queue and not the summand.  That is the finding
-- stated as a row rather than as a claim: the quantity did not move,
-- the charge did, and it moved far enough to clear the very reading
-- that refuted its predecessor.  A restatement that had merely renamed
-- the bound would report `false` twice here.
--
-- AND THE CHARGE IS SMALL WHERE THE CAP WAS LARGE, which is what makes
-- these rows worth re-reading rather than a repeat.  Twelve layers
-- against a cap of fifty-one: the charge fell by a factor and the
-- conclusion still clears, so what the predecessor was buying was
-- slack and not denomination.  A rung doubles, so a program's own
-- layers already dominate what running it can emit.
--
-- NOT COVERED: a parked SLOT REFERENCE, whose layers are zero and
-- whose whole charge is the summand -- `Probed.Drain-Count-Slot` reads
-- that point; and the ledger tie, which these rows say nothing about
-- -- a parked program is bounded only by the level the store premise
-- carries, so the charge still reaches the level and a per-frame
-- ceiling is still a fixed product.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Store where

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
open import Refuted.Frame-Step-Size-Cross
  using () renaming (Γ₁ to ΓV; Pow to PowV; chain to chainV;
                     e₂ to eV; sl₁ to slV; stQ to stV)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE VALUE HALF.  One subscription delivers what a twelve-rung chain
-- emits, read against the rung the constant bought and then against
-- the rung the parked program's own layers buy.
----------------------------------------------------------------------

-- WHAT THE ONE SUBSCRIPTION DELIVERS.  The refutation drains a
-- singleton queue, and a singleton drain delivers exactly what the one
-- subscription below it delivers, so the row below stands at the very
-- quantity that killed the constant.
outV : List (Val ΓV (PowV 12))
outV = proj₁ (proj₂ (subscribeInner {e = eV} (gasPad 8 g0) mergeAllᵒ 0 root 0 0
                       (chainV 12) (sched-init eV slV) stV))

-- THE CHARGE, READ OFF THE STATE THE ROWS STAND AT.  It is the parked
-- program's layer count plus a one-slot telescope, over a twelve-rung
-- chain.
charges : List ℕ
charges = layᵉ (chainV 12) + slotsSize slV ∷ []

charges≡ : charges ≡ 13 ∷ []
charges≡ = refl

-- LOAD-BEARING: the first entry is the refutation's own row, so a
-- charge that had not actually grown would repeat it in the second.
valRows : List Bool
valRows = valsSz? {Γ = ΓV} {s = PowV 12} (iterSize 51 1 51) outV
        ∷ valsSz? {Γ = ΓV} {s = PowV 12}
            (iterSize 51 (layᵉ (chainV 12) + slotsSize slV) 51)
            outV
        ∷ []

valRows≡ : valRows ≡ false ∷ true ∷ []
valRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied out
-- beside a claim.  The premises are left as arguments: the row asserts
-- the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it fails for any charge the parked chain's emission
-- outruns, which the constant it replaces did.  The schedule and the
-- state are the ones the exit hands the drain at this door, and the
-- drain hands straight on, so the row stands where the arm actually
-- reaches it.
tieDrain : Confirms
  (subscribeE-sz {e = eV} (gasPad 7 g0) (chainV 12)
     (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init eV slV) { nextNode = 1 }) stV 51 51)
tieDrain = λ _ _ → refl
