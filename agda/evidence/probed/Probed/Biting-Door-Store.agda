-- ══════════════════════════════════════════════════════════════════
-- WHAT A BITING DOOR WRITES, WHICH IS THE HALF EVERY STORE WITNESS
-- SO FAR ENTERED AROUND.
--
-- TARGET: stepFrame-sz-store-outer @62e3c5
-- TARGET: stepFrame-sz-store-inner @b7ce7a
--
-- WHAT THE IDLE WITNESSES LEFT OPEN.  A subscription's delivered burst
-- is invariant in the door, which is already read: the operator enters
-- only through the path and the burst is never pushed through it.  So
-- whatever a switch's CUT and an exhaust's DROP do, they do to the
-- TABLE and to later emits.  Every store witness before these entered
-- its door IDLE, where all three admit alike and the reading is the
-- merge door's under another name.
--
-- THE ROWS.  Each door is entered where its rule bites -- a switch
-- already holding an inner, an exhaust already busy -- with the
-- outgoing inner's own cell standing in the table beside it, a scan
-- holding a program near the premise's bound.  Both arms are read:
-- an arrival crossing outward, and an inner FINISHING, which is the
-- only other way these doors are reached.
--
-- WHAT THEY FIND.  The bite reaches neither reading.  A cut edits the
-- REGISTRY and the schedule's live set; the outgoing inner's cell is
-- left standing, so the table GROWS across a cut rather than
-- shrinking, and what the frame leaves is the idle reading plus a cell
-- the premise already bounds.  A busy exhaust writes nothing at all,
-- and a finishing inner writes only the door's own bit, which is a
-- node id and two flags -- so both are read at rung ZERO, the
-- premise's own bound climbed by nothing, which is the tightest row
-- a store conclusion admits.
--
-- WHAT THE ROWS DO NOT BUY.  One outgoing cell, so nothing about a
-- switch cutting a chain of them; the cut is taken at an EMPTY
-- registry, so nothing about the severing itself, which reaches no
-- table; and nothing about a door biting under a `mergeAll` limit,
-- which is the queue's question and not the door's.
-- ══════════════════════════════════════════════════════════════════
module Probed.Biting-Door-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (obs; sizeᵛ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; root; switchᵒ; exhaustᵒ;
  thru-outer; from-inner; scan-st; switch-st; exhaust-st;
  installNode; st-init; stepFrame; sched-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (szCount; parkedLayAt;
         stepFrame-sz-store-outer; stepFrame-sz-store-inner)
open import Refuted.Frame-Step-Size-Cross-Store
  using (Γ₁; sl₁; Pow; K; chain; e₀; vals₀)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE OUTGOING INNER'S CELL.  A scan holding the thirteen-rung chain
-- as a one-shot observable, which the premise bounds at sixty-three
-- and a cut has no way to reach.
----------------------------------------------------------------------
oldCell : EvalSt e₀ → EvalSt e₀
oldCell st = installNode 1 (scan-st {Γ = Γ₁} {t = obs (Pow K)} (chain K)) st

-- THE COUNTER IS ADVANCED PAST THE TWO NODES STANDING, which is the
-- one thing a hand-built state has to get right here: a door and the
-- inner it holds were minted before this frame, so an id a fresh
-- subscription mints cannot be either of them.  Left at zero, the
-- incoming subscription would land ON the door and the door's own
-- write-back would then erase it, and the row would be reading a
-- collision rather than a cut.
schedB : Sched Γ₁
schedB = record (sched-init e₀ sl₁) { nextNode = 7 }

----------------------------------------------------------------------
-- THE TWO DOORS, EACH ENTERED WHERE ITS RULE BITES.
----------------------------------------------------------------------
stSw : EvalSt e₀
stSw = oldCell (installNode 0 (switch-st {Γ = Γ₁} (just 1) false) (st-init e₀))

stEx : EvalSt e₀
stEx = oldCell (installNode 0 (exhaust-st {Γ = Γ₁} true false) (st-init e₀))

postSw : EvalSt e₀
postSw = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
           (thru-outer switchᵒ 0) root vals₀ false schedB stSw))))

postEx : EvalSt e₀
postEx = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
           (thru-outer exhaustᵒ 0) root vals₀ false schedB stEx))))

----------------------------------------------------------------------
-- THE CHARGE AND WHAT THE TWO DOORS DO TO THE TABLE.
----------------------------------------------------------------------

-- LOAD-BEARING: the outgoing cell sits just under the premise's bound,
-- so a reading that lost it would be visible, and the charge is `src`'s
-- own count applied here rather than a copy of it.
biteFigures : List ℕ
biteFigures = sizeᵛ {Γ = Γ₁} (obs (Pow K)) (chain K)
            ∷ szCount sl₁ (EvalSt.nodes stSw)
                (thru-outer {Γ = Γ₁} {u = obs (Pow K)} switchᵒ 0) vals₀
            ∷ []

biteFigures≡ : biteFigures ≡ 55 ∷ 15 ∷ []
biteFigures≡ = refl

-- LOAD-BEARING, and it is the shape of the finding: a CUT does not
-- shrink the table.  The switch's frame leaves a table one longer than
-- it read -- the outgoing cell standing beside the incoming one -- and
-- the busy exhaust's leaves it exactly as it was.
biteNodes≡ : length (EvalSt.nodes stSw) ∷ length (EvalSt.nodes postSw)
           ∷ length (EvalSt.nodes stEx) ∷ length (EvalSt.nodes postEx) ∷ []
           ≡ 2 ∷ 3 ∷ 2 ∷ 2 ∷ []
biteNodes≡ = refl

-- LOAD-BEARING: the first entry is the refuted constant, which the
-- reified emission outruns exactly as it does at an idle door, so the
-- bite has not bought the row.  The second is the stated charge.
switchRows : List Bool
switchRows = all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv))
                 (EvalSt.nodes postSw)
           ∷ all (λ kv → boundedNode
                           (iterSize 63 (szCount sl₁ (EvalSt.nodes stSw)
                              (thru-outer {Γ = Γ₁} {u = obs (Pow K)} switchᵒ 0)
                              vals₀) 63)
                           (proj₂ kv))
                 (EvalSt.nodes postSw)
           ∷ []

switchRows≡ : switchRows ≡ false ∷ true ∷ []
switchRows≡ = refl

-- LOAD-BEARING, at rung ZERO: the premise's own bound climbed by
-- nothing.  It fails the moment a busy exhaust writes anything derived
-- from the arrival it dropped.
exhaustRow≡ : all (λ kv → boundedNode (iterSize 63 0 63) (proj₂ kv))
                  (EvalSt.nodes postEx)
            ≡ true
exhaustRow≡ = refl

----------------------------------------------------------------------
-- THE OTHER ARM.  An inner FINISHING under each door, which is the one
-- other way a bite is reached: the switch's held inner is the one
-- completing, and the exhaust is busy with it.
----------------------------------------------------------------------
postSwI : EvalSt e₀
postSwI = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
            (from-inner switchᵒ 0 1) root [] true schedB stSw))))

postExI : EvalSt e₀
postExI = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
            (from-inner exhaustᵒ 0 1) root [] true schedB stEx))))

-- LOAD-BEARING: the charge the statement reads at these frames is the
-- telescope alone, since a switch and an exhaust park nothing -- so
-- what the rows below stand at is strictly tighter than the statement
-- asks, and any write at all from a finishing inner would fail them.
finishCharge≡ : parkedLayAt 0 (EvalSt.nodes stSw) + slotsSize sl₁
             ∷ parkedLayAt 0 (EvalSt.nodes stEx) + slotsSize sl₁ ∷ []
             ≡ 1 ∷ 1 ∷ []
finishCharge≡ = refl

-- LOAD-BEARING, at rung ZERO for the same reason the exhaust row is:
-- a finishing inner rewrites only the door's own bit, which is a node
-- id and two flags, and `boundedNode` reads neither.
finishRows≡ : all (λ kv → boundedNode (iterSize 63 0 63) (proj₂ kv))
                 (EvalSt.nodes postSwI)
           ∷ all (λ kv → boundedNode (iterSize 63 0 63) (proj₂ kv))
                 (EvalSt.nodes postExI)
           ∷ [] ≡ true ∷ true ∷ []
finishRows≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The types are generated from the statements as they read,
-- so a restatement changes them rather than leaving the rungs above
-- copied out beside a claim.  The premises are left as arguments: each
-- row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it fails for any charge the incoming subscription's
-- reified emission outruns, which the constant it replaces does.
tieBiteOuterSwitch : Confirms
  (stepFrame-sz-store-outer {e = e₀} (gasPad 8 g0) 0 0 switchᵒ 0 root
     vals₀ false schedB stSw 63 63)
tieBiteOuterSwitch = λ _ _ _ → refl

tieBiteOuterExhaust : Confirms
  (stepFrame-sz-store-outer {e = e₀} (gasPad 8 g0) 0 0 exhaustᵒ 0 root
     vals₀ false schedB stEx 63 63)
tieBiteOuterExhaust = λ _ _ _ → refl

tieBiteInnerSwitch : Confirms
  (stepFrame-sz-store-inner {e = e₀} (gasPad 8 g0) 0 0 switchᵒ 0 1 root []
     true schedB stSw 63 63)
tieBiteInnerSwitch = λ _ _ _ → refl

tieBiteInnerExhaust : Confirms
  (stepFrame-sz-store-inner {e = e₀} (gasPad 8 g0) 0 0 exhaustᵒ 0 1 root []
     true schedB stEx 63 63)
tieBiteInnerExhaust = λ _ _ _ → refl
