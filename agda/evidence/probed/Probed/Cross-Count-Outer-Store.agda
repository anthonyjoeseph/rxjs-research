-- ══════════════════════════════════════════════════════════════════
-- THE OUTER CROSSING'S TABLE, WHICH IS THE ONE CONCLUSION OF THIS ARM
-- NOTHING HAD EVER STOOD AT.
--
-- TARGET: stepFrame-sz-store-outer @62e3c5
--
-- WHY THE OTHER HALF'S ROWS DO NOT REACH HERE.  The count is one
-- object across both halves of the arm -- the arrivals' layers joined
-- by max, plus the telescope -- and every separation it rests on was
-- taken at the DELIVERED list.  What a subscription WRITES is a
-- different reading of the same run: the arrival is reified by
-- whatever operator it lands under, so a scan the subscription
-- installs holds an emission rather than an arrival, and `sizeᵛ` at an
-- `obs` reads the expression that emission became.  A quantity settled
-- against what came out says nothing about that until it is run.
--
-- THE ROWS.  The state is the one that killed the constant this
-- reading replaces: a `mergeAll` door with no queue, handed a scan
-- whose step discards its accumulator and stores the arriving datum
-- back as a one-shot observable, over a thirteen-rung duplication
-- chain.  The table is read at the refuted rung and then at the
-- repaired one, and reports `false` then `true` -- so the charge did
-- not merely rename the bound.  The figures beside them say by how
-- much: fourteen layers and a one-slot telescope, against a program
-- of size sixty-three whose stored emission is exponential in it.
--
-- ALL THREE SINKS ARE RUN at the same arrival, since a merging door
-- admits everything and is the weakest of the three to stand on
-- alone.  A switch cancels the inner it holds as the arrival lands and
-- an exhaust drops what arrives while busy, so the table is reached
-- under admission rules that differ across the pair.
--
-- WHAT THE ROWS DO NOT BUY.  One installed node per witness, so
-- nothing about a table whose entries accumulate across frames;
-- nothing about a parked QUEUE at this arm, where the entries are
-- programs the run never delivered and the reading is `sizeᵉ` rather
-- than a scan's `sizeᵛ`; and nothing about a telescope of more than
-- one slot, which is the summand's own gap and not this arm's.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Outer-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (obs)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; switchᵒ; exhaustᵒ;
  thru-outer; switch-st; exhaust-st; installNode; st-init; stepFrame;
  sched-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (szCount; stepFrame-sz-store-outer)
open import Refuted.Frame-Step-Size-Cross-Store
  using (Γ₁; sl₁; Pow; K; inner; e₀; st₀; vals₀; post₀)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CHARGE, READ OFF THE STATE THE ROWS STAND AT.  It is `src`'s own
-- count applied at this file's frame, so a restatement of the count
-- moves the rows rather than leaving a copy of it here.
----------------------------------------------------------------------
charge : ℕ
charge = szCount sl₁ (EvalSt.nodes st₀)
           (thru-outer {Γ = Γ₁} {u = obs (Pow K)} mergeAllᵒ 0) vals₀

-- LOAD-BEARING: it is what says the charge is the PROGRAM's and not
-- the run's.  The arrival's layers and the one scripted slot against
-- the emission the table ends up holding -- a reading that had grown
-- with what the run produced would not report fourteen here.
figures : List ℕ
figures = layᵉ inner ∷ slotsSize sl₁ ∷ charge ∷ []

figures≡ : figures ≡ 14 ∷ 1 ∷ 15 ∷ []
figures≡ = refl

----------------------------------------------------------------------
-- THE TABLE AT THE TWO RUNGS.  The first is the refutation's own row,
-- so a charge that had not actually grown would repeat it in the
-- second.
----------------------------------------------------------------------
storeRows : List Bool
storeRows = all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv))
                (EvalSt.nodes post₀)
          ∷ all (λ kv → boundedNode (iterSize 63 charge 63) (proj₂ kv))
                (EvalSt.nodes post₀)
          ∷ []

storeRows≡ : storeRows ≡ false ∷ true ∷ []
storeRows≡ = refl

----------------------------------------------------------------------
-- THE OTHER TWO SINKS, at the same arrival and the same rung.  Each is
-- entered at its own idle state, so the admission rule is the live one.
----------------------------------------------------------------------
stSw : EvalSt e₀
stSw = installNode 0 (switch-st {Γ = Γ₁} nothing false) (st-init e₀)

stEx : EvalSt e₀
stEx = installNode 0 (exhaust-st {Γ = Γ₁} false false) (st-init e₀)

postSw : EvalSt e₀
postSw = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
           (thru-outer switchᵒ 0) root vals₀ false (sched-init e₀ sl₁) stSw))))

postEx : EvalSt e₀
postEx = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
           (thru-outer exhaustᵒ 0) root vals₀ false (sched-init e₀ sl₁) stEx))))

-- LOAD-BEARING: each door is entered idle, so each ADMITS this arrival
-- and installs the reifying scan itself -- the same table reading
-- reached down three different admission paths rather than the one that
-- lets everything in.  A door whose subscription wrote more than the
-- arrival's own layers buy would lose here.
sinkRows : List Bool
sinkRows = all (λ kv → boundedNode (iterSize 63 charge 63) (proj₂ kv))
               (EvalSt.nodes postSw)
         ∷ all (λ kv → boundedNode (iterSize 63 charge 63) (proj₂ kv))
               (EvalSt.nodes postEx)
         ∷ []

sinkRows≡ : sinkRows ≡ true ∷ true ∷ []
sinkRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied out
-- beside a claim.  The premises are left as arguments: the row asserts
-- the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it fails for any charge the stored emission outruns,
-- which the constant it replaces does.
tieOuterStore : Confirms
  (stepFrame-sz-store-outer {e = e₀} (gasPad 8 g0) 0 0 mergeAllᵒ 0 root
     vals₀ false (sched-init e₀ sl₁) st₀ 63 63)
tieOuterStore = λ _ _ _ → refl
