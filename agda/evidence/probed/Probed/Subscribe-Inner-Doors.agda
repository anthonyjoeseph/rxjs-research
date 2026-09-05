-- ══════════════════════════════════════════════════════════════════
-- THE LEAF AT THE TWO DOORS EVERY OTHER ROW SUBSCRIBED PAST.
--
-- TARGET: subscribeInner-sz @e1520e
--
-- WHY THE DOOR LOOKED LIKE A RISK.  The statement quantifies over an
-- arbitrary operator and every row standing at it had entered through
-- a merge, which admits everything.  The other two do not: a switch
-- CUTS the inner it holds as the new one lands, and an exhaust DROPS
-- what arrives while it is busy -- so the run a charge prices looked
-- like one the arm might never perform.
--
-- WHAT THE ROWS FIND, AND IT IS STRUCTURAL RATHER THAN NUMERIC.  The
-- door is INVISIBLE to what a subscription delivers.  An operator
-- enters here only by being built into the path, and a subscription
-- does not push its own burst through that frame: the frame is what
-- LATER emits are routed by, which is the drain's statement and not
-- this one.  So the two doors, each entered at the state where its
-- rule bites -- a switch already holding an inner, an exhaust already
-- busy -- deliver the merge door's burst UNCHANGED, and the two
-- equalities are what say so.
--
-- THE POINT.  Both rows stand at the reference whose layers are zero
-- and whose whole charge is the telescope, so the door is the only
-- thing varying across the three.  Each door is read against the
-- telescope-free rung and the repaired one and reports `false` then
-- `true`, which is what keeps them rows rather than restatements of
-- the equalities above them.
--
-- WHAT THE ROWS DO NOT BUY.  One arrival shape and one telescope, so
-- nothing about a door reached with the arrival's layers positive;
-- nothing about the door's effect on a LATER emit, which is where the
-- cut and the drop actually act and where the arms read a different
-- statement; and no row here says the two doors agree on what they
-- WRITE, since each is entered at a state the others cannot hold.
-- ══════════════════════════════════════════════════════════════════
module Probed.Subscribe-Inner-Doors where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Nat using (_+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Val; obs; input; sizeᵛ)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; switchᵒ; exhaustᵒ;
  switch-st; exhaust-st; installNode; st-init; sched-init; iterSize;
  subscribeInner)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; subscribeInner-sz)
open import Refuted.Frame-Step-Size-Slot
  using (Pw; Γ₂; sl₂; e₂; st₂)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE ARRIVAL: the bare reference the slot refutation is built on, so
-- the charge is the telescope and the door is the only axis.
----------------------------------------------------------------------
oS : Val Γ₂ (obs (Pw 12))
oS = input fzero

----------------------------------------------------------------------
-- THE TWO DOORS, EACH AT THE STATE WHERE ITS RULE BITES.  An idle door
-- admits like a merge, which would make the comparison below say
-- nothing: the switch is holding an inner it must cut, and the exhaust
-- is busy and must drop.
----------------------------------------------------------------------
stSw : EvalSt e₂
stSw = installNode 0 (switch-st {Γ = Γ₂} (just 7) false) (st-init e₂)

stEx : EvalSt e₂
stEx = installNode 0 (exhaust-st {Γ = Γ₂} true false) (st-init e₂)

outMg : List (Val Γ₂ (Pw 12))
outMg = proj₁ (proj₂ (subscribeInner {e = e₂} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                        oS (sched-init e₂ sl₂) st₂))

outSw : List (Val Γ₂ (Pw 12))
outSw = proj₁ (proj₂ (subscribeInner {e = e₂} (gasPad 64 g0) switchᵒ 0 root 0 0
                        oS (sched-init e₂ sl₂) stSw))

outEx : List (Val Γ₂ (Pw 12))
outEx = proj₁ (proj₂ (subscribeInner {e = e₂} (gasPad 64 g0) exhaustᵒ 0 root 0 0
                        oS (sched-init e₂ sl₂) stEx))

----------------------------------------------------------------------
-- WHAT THE THREE DOORS DELIVER.
----------------------------------------------------------------------

-- LOAD-BEARING: the merge door's own burst, so the two equalities
-- below are pinned to a quantity and not merely to each other.  A
-- reference that had stopped at the slot it names would report one.
mergeDelivered≡ : map (sizeᵛ {Γ = Γ₂} (Pw 12)) outMg ≡ 8191 ∷ []
mergeDelivered≡ = refl

-- LOAD-BEARING: it fails the moment a cut removes, replaces or
-- reorders anything in the burst of the subscription that caused it.
switchAgrees : outSw ≡ outMg
switchAgrees = refl

-- LOAD-BEARING: it fails the moment a busy exhaust drops the arrival
-- it was handed, which is the whole of that operator's rule.
exhaustAgrees : outEx ≡ outMg
exhaustAgrees = refl

----------------------------------------------------------------------
-- THE CONCLUSION AT EACH DOOR, against the reading the slot
-- refutation killed and against the repaired one.
----------------------------------------------------------------------

-- LOAD-BEARING: entries one and three are the telescope-free rung, so
-- a door at which the charge had failed to reach the slot table would
-- report `false` four times.
doorRows : List Bool
doorRows = valsSz? {Γ = Γ₂} {s = Pw 12} (iterSize 51 (layᵉ oS) 51) outSw
         ∷ valsSz? {Γ = Γ₂} {s = Pw 12}
             (iterSize 51 (layᵉ oS + slotsSize sl₂) 51) outSw
         ∷ valsSz? {Γ = Γ₂} {s = Pw 12} (iterSize 51 (layᵉ oS) 51) outEx
         ∷ valsSz? {Γ = Γ₂} {s = Pw 12}
             (iterSize 51 (layᵉ oS + slotsSize sl₂) 51) outEx
         ∷ []

doorRows≡ : doorRows ≡ false ∷ true ∷ false ∷ true ∷ []
doorRows≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The types are generated from the statement as it reads,
-- so a restatement changes them rather than leaving the rungs above
-- copied out beside a claim.  The premises are left as arguments: each
-- row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: the operator is the statement's own argument, so this
-- is the claim at a door and not a claim about one.
tieDoorSwitch : Confirms
  (subscribeInner-sz {e = e₂} (gasPad 64 g0) switchᵒ 0 root 0 0 oS
     (sched-init e₂ sl₂) stSw 51 51)
tieDoorSwitch = λ _ _ → refl

-- LOAD-BEARING: same, at the door whose rule is to deliver nothing.
tieDoorExhaust : Confirms
  (subscribeInner-sz {e = e₂} (gasPad 64 g0) exhaustᵒ 0 root 0 0 oS
     (sched-init e₂ sl₂) stEx 51 51)
tieDoorExhaust = λ _ _ → refl
