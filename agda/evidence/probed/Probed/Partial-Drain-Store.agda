-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN THAT STOPS MID-QUEUE, WHERE THE TABLE CARRIES BOTH KINDS
-- OF ENTRY AT ONCE.
--
-- TARGET: stepFrame-sz-store-inner @b7ce7a
--
-- WHAT A DRAINED QUEUE LEFT OPEN.  Every queue read at this arm so far
-- runs to exhaustion, so the queue the frame LEAVES is empty and the
-- two readings -- the queue as ENTERED and the queue as LEFT -- were
-- never separated by a row.  A LIMIT is what separates them: the drain
-- takes lanes until the door is full and stops, so one table then
-- carries the cells the admitted entries wrote AND, inside the door's
-- own node, the entries that never ran.
--
-- THE ROWS.  A queue of three behind a door of one lane: the reifying
-- scan, which completes in the instant and so gives its lane back, and
-- two deferred bodies, which do not.  The first fills the lane and the
-- third is left standing.  A control at no limit at all drains the
-- same queue to the end, and its table is one node wider -- which is
-- what says the limit bit rather than the queue being short.
--
-- WHAT THEY FIND.  The charge must read the queue the frame ENTERED.
-- Read as the frame LEAVES it, the surviving entries carry no layer
-- and the charge collapses to the telescope alone -- the very rung the
-- refutation killed -- while the cell the admitted entry wrote is
-- still standing in the table.  Read as entered, it holds.  And the
-- premise's own bound fails on that same table, so the climb is bought
-- by the entry that RAN: at a limit of nought, where the identical
-- queue is admitted nowhere, rung ZERO holds and the surviving entries
-- are priced by the syntax the premise already bounds.
--
-- WHAT THE ROWS DO NOT BUY.  One lane and one door; nothing about a
-- limit that bites after several admissions rather than one, and
-- nothing about a survivor whose own layers exceed the admitted
-- entry's, where the two readings would not separate at all.
-- ══════════════════════════════════════════════════════════════════
module Probed.Partial-Drain-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Closed; obs; deferᵉ; sizeᵉ)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; root; mergeAllᵒ; from-inner;
  mergeAll-st; installNode; st-init; stepFrame; sched-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (parkedLayAt; stepFrame-sz-store-inner)
open import Refuted.Frame-Step-Size-Cross-Store
  using (Γ₁; sl₁; Pow; K; inner; e₀)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE ENTRY THAT HOLDS A LANE.  A deferred body is subscribed at the
-- NEXT tick, so it neither emits nor closes in this instant: it takes
-- a lane and keeps it, which is the one thing the reifying scan beside
-- it cannot do.  Its own layer count is nought, so it moves neither
-- reading of the queue.
----------------------------------------------------------------------
held : Closed Γ₁ (obs (Pow K))
held = deferᵉ inner

----------------------------------------------------------------------
-- THE PARTIAL DRAIN.  One lane, three entries: the scan gives its lane
-- back on completing, the first deferred body takes it, and the second
-- never runs.  The node counter is advanced past the door's own id,
-- so a fresh subscription cannot land on it.
----------------------------------------------------------------------
schedP : Sched Γ₁
schedP = record (sched-init e₀ sl₁) { nextNode = 7 }

stP : EvalSt e₀
stP = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} (just 1) 1
                      (inner ∷ held ∷ held ∷ [])  false)
        (st-init e₀)

postP : EvalSt e₀
postP = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
          (from-inner mergeAllᵒ 0 7) root [] true schedP stP))))

-- the same queue behind no limit at all: the control that says the
-- limit is what stopped the walk
stFull : EvalSt e₀
stFull = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} nothing 1
                         (inner ∷ held ∷ held ∷ [])  false)
           (st-init e₀)

postFull : EvalSt e₀
postFull = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
             (from-inner mergeAllᵒ 0 7) root [] true schedP stFull))))

enteredCharge : ℕ
enteredCharge = parkedLayAt 0 (EvalSt.nodes stP) + slotsSize sl₁

leftCharge : ℕ
leftCharge = parkedLayAt 0 (EvalSt.nodes postP) + slotsSize sl₁

----------------------------------------------------------------------
-- THE FIGURES.
----------------------------------------------------------------------

-- LOAD-BEARING: the two readings are separated by eleven rungs here,
-- and the entry that survives carries no layer at all, so the charge
-- read at exit is the telescope alone.  The sizes say both entries sit
-- under the premise's own bound as SYNTAX.
drainFigures : List ℕ
drainFigures = layᵉ inner ∷ layᵉ held ∷ sizeᵉ inner ∷ sizeᵉ held
             ∷ enteredCharge ∷ leftCharge ∷ []

drainFigures≡ : drainFigures ≡ 14 ∷ 0 ∷ 63 ∷ 64 ∷ 15 ∷ 1 ∷ []
drainFigures≡ = refl

-- LOAD-BEARING, and it is what makes the drain PARTIAL rather than
-- short: the same queue at no limit installs one node more.  A door
-- that had refused the queue outright would leave the reading at one.
partialNodes≡ : length (EvalSt.nodes stP) ∷ length (EvalSt.nodes postP)
              ∷ length (EvalSt.nodes postFull) ∷ []
              ≡ 1 ∷ 3 ∷ 4 ∷ []
partialNodes≡ = refl

----------------------------------------------------------------------
-- THE CONCLUSION AT THE TWO READINGS OF THE QUEUE.
----------------------------------------------------------------------

-- LOAD-BEARING, and this file's product: the first row is the queue
-- read as the frame LEAVES it, which a partial drain leaves NON-empty
-- and still short -- the surviving entries carry no layer, so it is
-- the rung the refutation killed.  The second is the stated charge,
-- read off the queue as the frame entered it.
partialRows : List Bool
partialRows = all (λ kv → boundedNode (iterSize 65 leftCharge 65) (proj₂ kv))
                  (EvalSt.nodes postP)
            ∷ all (λ kv → boundedNode (iterSize 65 enteredCharge 65) (proj₂ kv))
                  (EvalSt.nodes postP)
            ∷ []

partialRows≡ : partialRows ≡ false ∷ true ∷ []
partialRows≡ = refl

-- LOAD-BEARING: rung ZERO is the premise's own bound climbed by
-- nothing, and it FAILS here -- so the climb this table needs is
-- bought by the entry that ran, not by the entries left standing.
groundRow≡ : all (λ kv → boundedNode (iterSize 65 0 65) (proj₂ kv))
                 (EvalSt.nodes postP)
           ≡ false
groundRow≡ = refl

----------------------------------------------------------------------
-- THE LIMIT THAT ADMITS NOTHING.  The identical queue behind a door of
-- no lanes: every entry survives, nothing is subscribed, and the table
-- the frame leaves is the table it read.
----------------------------------------------------------------------
stZ : EvalSt e₀
stZ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} (just 0) 1
                      (inner ∷ held ∷ held ∷ [])  false)
        (st-init e₀)

postZ : EvalSt e₀
postZ = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
          (from-inner mergeAllᵒ 0 7) root [] true schedP stZ))))

-- LOAD-BEARING, and it is the other half of the finding: at rung ZERO,
-- where the row above fails, a queue admitted NOWHERE holds.  Parked
-- entries are priced by their own syntax and the premise already
-- bounds it, so the entries that never ran cost the ladder nothing.
zeroLaneRow≡ : length (EvalSt.nodes postZ)
             ∷ parkedLayAt 0 (EvalSt.nodes postZ) ∷ []
             ≡ 1 ∷ 14 ∷ []
zeroLaneRow≡ = refl

zeroLaneHolds≡ : all (λ kv → boundedNode (iterSize 65 0 65) (proj₂ kv))
                     (EvalSt.nodes postZ)
               ≡ true
zeroLaneHolds≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: the queue is the statement's own, reached through the
-- state argument, so this is the claim at a drain the door stopped.
tiePartial : Confirms
  (stepFrame-sz-store-inner {e = e₀} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root []
     true schedP stP 65 65)
tiePartial = λ _ _ _ → refl
