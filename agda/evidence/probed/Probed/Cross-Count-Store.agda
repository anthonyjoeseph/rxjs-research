-- ══════════════════════════════════════════════════════════════════
-- THE INNER CROSSING'S TWO HALVES, INSTANTIATED AT THE VERY WITNESSES
-- THAT KILLED THE CONSTANT THEY REPLACE.
--
-- TARGET: subscribeInner-sz @e1520e
-- TARGET: stepFrame-sz-store-inner @b7ce7a
--
-- WHY THESE POINTS AND NOT OTHERS.  The inner arm subscribes what the
-- `*All` node has PARKED, so the program it runs is in the node table
-- and not among the arriving values -- which is why the charge reads
-- the queue at the frame's own node, and why the whole arm now reduces
-- to what one SUBSCRIPTION of a parked program delivers.  A receipt
-- for that reading is worth having only where the predecessor reading
-- FAILED, since anywhere else a green row is bought by the program
-- being small rather than by the denomination being right.  So both
-- rows are taken at the refutations' own states: the drain door with a
-- twelve-rung duplication chain parked behind it, and the same door
-- with a scan whose accumulator reifies what the run emits.
--
-- WHAT THE PAIRED FIGURES BUY.  Each half reads the same delivered
-- quantity against two rungs -- the constant one and the parked
-- program's own plus the telescope -- and reports `false` then `true`.
-- Both telescopes here are a single scripted slot, so what the second
-- rung is bought by is the queue and not the summand.  That is the
-- finding stated as a row rather than as a claim: the quantity did not
-- move, the charge did, and it moved far enough to clear the very
-- reading that refuted its predecessor.  A restatement that had merely
-- renamed the bound would report `false` twice here.
--
-- AND THE CHARGE IS SMALL WHERE THE CAP WAS LARGE, which is what makes
-- these rows worth re-reading rather than a repeat.  Twelve layers and
-- fourteen against caps of fifty-one and sixty-three: the charge fell
-- by a factor and the conclusion still clears, so what the predecessor
-- was buying was slack and not denomination.  A rung doubles, so a
-- program's own layers already dominate what running it can emit.
--
-- NOT COVERED: a parked SLOT REFERENCE, whose layers are zero and
-- whose whole charge is the summand -- `Probed.Drain-Count-Slot` reads
-- the value half there, and nothing reads the store half at that
-- shape; a chain of installed nodes, since each witness installs one;
-- the outer arm's store half, whose count reads the arrival and the
-- slot telescope instead and which nothing reads; and the ledger tie,
-- which these rows say nothing about -- a
-- parked program is bounded only by the level the store premise
-- carries, so the charge still reaches the level and a per-frame
-- ceiling is still a fixed product.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Val)
open import Rx.Slots using (slotsSize)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Evaluator
  using (EvalSt; root; mergeAllᵒ; sched-init; iterSize; subscribeInner)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; parkedLayAt; subscribeInner-sz; stepFrame-sz-store-inner)
open import Refuted.Frame-Step-Size-Cross
  using () renaming (Γ₁ to ΓV; Pow to PowV; chain to chainV;
                     e₂ to eV; sl₁ to slV; stQ to stV)
open import Refuted.Frame-Step-Size-Cross-Store
  using () renaming (e₀ to eS; sl₁ to slS; stQ to stS; postQ to postS)
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

-- THE TWO CHARGES, READ OFF THE STATES THE ROWS STAND AT.  They are
-- the parked programs' layer counts plus a one-slot telescope: a
-- twelve-rung chain, and a scan over a thirteen-rung one.
charges : List ℕ
charges = layᵉ (chainV 12) + slotsSize slV
        ∷ parkedLayAt 0 (EvalSt.nodes stS) + slotsSize slS ∷ []

charges≡ : charges ≡ 13 ∷ 15 ∷ []
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
-- THE STORE HALF.  The same door with the accumulator reifying the
-- emission, so the quantity lands in the node table rather than in the
-- delivered list, and the table is read at both rungs.
----------------------------------------------------------------------

-- LOAD-BEARING jointly with the row above: it says the two halves are
-- one decision, since the same denomination clears the same quantity
-- through the other conclusion.
storeRows : List Bool
storeRows = all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv))
                (EvalSt.nodes postS)
          ∷ all (λ kv → boundedNode
                          (iterSize 63 (parkedLayAt 0 (EvalSt.nodes stS)
                                         + slotsSize slS) 63)
                          (proj₂ kv))
                (EvalSt.nodes postS)
          ∷ []

storeRows≡ : storeRows ≡ false ∷ true ∷ []
storeRows≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The types are generated from the statements as they read,
-- so a restatement changes them rather than leaving the rungs above
-- copied out beside a claim.  The premises are left as arguments: each
-- row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it fails for any charge the parked chain's emission
-- outruns, which the constant it replaces did.  The schedule and the
-- state are the ones the exit hands the drain at this door, and the
-- drain hands straight on, so the row stands where the arm actually
-- reaches it.
tieDrain : Confirms
  (subscribeInner-sz {e = eV} (gasPad 8 g0) mergeAllᵒ 0 root 0 0
     (chainV 12) (sched-init eV slV) stV 51 51)
tieDrain = λ _ _ → refl

-- LOAD-BEARING: same, through the conclusion about the node table.
tieStore : Confirms
  (stepFrame-sz-store-inner {e = eS} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root [] true
     (sched-init eS slS) stS 63 63)
tieStore = λ _ _ _ → refl
