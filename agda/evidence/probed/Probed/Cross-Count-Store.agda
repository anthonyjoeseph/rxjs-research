-- ══════════════════════════════════════════════════════════════════
-- THE INNER CROSSING'S TWO HALVES, INSTANTIATED AT THE VERY WITNESSES
-- THAT KILLED THE CONSTANT THEY REPLACE.
--
-- TARGET: stepFrame-sz-inner @6d34df
-- TARGET: stepFrame-sz-store-inner @f82490
--
-- WHY THESE POINTS AND NOT OTHERS.  The inner arm subscribes what the
-- `*All` node has PARKED, so the program it runs is in the store and
-- not among the arguments a count can read -- which is why the charge
-- is denominated in the store bound the premise already carries.  A
-- receipt for that reading is worth having only where the predecessor
-- reading FAILED, since anywhere else a green row is bought by the
-- program being small rather than by the denomination being right.  So
-- both rows are taken at the refutations' own states: the drain door
-- with a twelve-rung duplication chain parked behind it, and the same
-- door with a scan whose accumulator reifies what the drain emits.
--
-- WHAT THE PAIRED FIGURES BUY.  Each half reads the same delivered
-- quantity against two rungs -- the constant one and the store-
-- denominated one -- and reports `false` then `true`.  That is the
-- finding stated as a row rather than as a claim: the quantity did not
-- move, the charge did, and it moved far enough to clear the very
-- reading that refuted its predecessor.  A restatement that had merely
-- renamed the bound would report `false` twice here.
--
-- AND THE MARGIN IS NOT NARROW, WHICH IS THE POINT OF CHARGING RUNGS
-- RATHER THAN A SUM.  A rung doubles, so charging the bound's own
-- worth of them dominates two to the bound outright -- and two to the
-- bound is what a parked program of that size can emit.  The rows
-- below therefore hold with room that grows in the bound, so nothing
-- here rests on the witnesses' particular numerals.
--
-- NOT COVERED: a queue holding MORE THAN ONE parked program, where the
-- drain runs several and the arm's single `B` is asked to cover their
-- sum; a chain of installed nodes, since each witness installs one; the
-- outer arm and its store half, whose count reads the arrival and the
-- slot telescope instead and which `Probed.Cross-Count-Slot` reads; and
-- the ledger tie, which these rows say nothing about -- the charge here
-- CLIMBS with the walk's level while a per-frame ceiling is a fixed
-- product, and that gap is what leaves both arms outside any discharge
-- of the walk's ceiling conjunct denominated in `frameCh`.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; sched-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; stepFrame-sz-inner; stepFrame-sz-store-inner)
open import Refuted.Frame-Step-Size-Cross
  using () renaming (Γ₁ to ΓV; Pow to PowV;
                     e₂ to eV; sl₁ to slV; stQ to stV; outQ to outV)
open import Refuted.Frame-Step-Size-Cross-Store
  using () renaming (e₀ to eS; sl₁ to slS; stQ to stS; postQ to postS)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE VALUE HALF.  The drain delivers what a twelve-rung chain emits,
-- read against the rung the constant bought and then against the rung
-- the store bound buys.
----------------------------------------------------------------------

-- LOAD-BEARING: the first entry is the refutation's own row, so a
-- charge that had not actually grown would repeat it in the second.
valRows : List Bool
valRows = valsSz? {Γ = ΓV} {s = PowV 12} (iterSize 51 1 51) outV
        ∷ valsSz? {Γ = ΓV} {s = PowV 12} (iterSize 51 51 51) outV
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
          ∷ all (λ kv → boundedNode (iterSize 63 63 63) (proj₂ kv))
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
-- outruns, which the constant it replaces did.
tieInner : Confirms
  (stepFrame-sz-inner {e = eV} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root [] true
     (sched-init eV slV) stV 51 51)
tieInner = λ _ _ _ → refl

-- LOAD-BEARING: same, through the conclusion about the node table.
tieStore : Confirms
  (stepFrame-sz-store-inner {e = eS} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root [] true
     (sched-init eS slS) stS 63 63)
tieStore = λ _ _ _ → refl
