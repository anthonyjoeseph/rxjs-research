-- ══════════════════════════════════════════════════════════════════
-- THE PARKED SLOT REFERENCE, WHERE THE INNER CHARGE'S FIRST SUMMAND
-- READS NOTHING AND THE WHOLE CLIMB IS THE TELESCOPE.
--
-- TARGET: subscribeE-sz-store @f8b804
--
-- WHAT EVERY STORE ROW SO FAR LEFT OPEN.  This charge is the deepest
-- parked program's LAYERS joined over the queue, plus the telescope.
-- Every witness at this half has parked a program written out, where
-- the layers are the charge and the summand is a rounding.  A bare
-- reference is the other shape: its layer count is nought however
-- deep the definition behind it goes, so the first summand
-- contributes nothing at all and the second carries the whole climb.
-- The value half is read at that shape already; the table has never
-- been, and a summand that reached the delivered list without
-- reaching what the run WRITES would show nowhere else.
--
-- THE ROWS.  A single shared slot holding a duplication chain under a
-- scan that reifies what it sees, and a door whose parked queue is
-- the bare reference to it -- drained through the `from-inner` arm,
-- so the table read is the one the arm actually leaves rather than the
-- one the leaf alone writes.  The queue holds ONE entry, so that drain
-- is exactly one subscription and the two readings coincide here.  Two
-- depths, because one more rung behind the reference doubles the
-- emission while moving the charge by four units of slot syntax.
--
-- WHAT THEY FIND.  The parked layer count is nought at both depths
-- and the charge moves with the slot alone.  The table the frame
-- leaves carries the scan's accumulator, which is the emission
-- reified, so it fails the telescope-free reading -- the premise's own
-- bound climbed by nothing, which is what the charge collapses to
-- when the summand is dropped -- and holds at the stated one.  The
-- reference is legible from the schedule the frame is handed, and it
-- is legible there for the WRITTEN table and not merely for the
-- delivered list.
--
-- WHAT THE ROWS DO NOT BUY, and the first half is this file's honest
-- residue.  The clearance is not tight and cannot be: four units of
-- slot syntax per doubling of emission against a rung that admits
-- size geometrically means the summand dominates by construction once
-- it is in the charge at all, so these rows say the telescope REACHES
-- the table, never that its size is right.  And beyond that: one slot
-- in the telescope, one entry in the queue, so nothing about a max
-- joining a reference against a written-out program; and no arm other
-- than the drain.
-- ══════════════════════════════════════════════════════════════════
module Probed.Parked-Slot-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Ctx; Closed; Fn; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; scanᵉ; input; varᵗ; sndᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; shared; slotSize; slotsSize)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; from-inner; _↠_;
  mergeAll-st; installNode; st-init; sched-init; iterSize; stepFrame)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (parkedLayAt; subscribeE-sz-store)
open import Refuted.Frame-Step-Size-Slot using (Pw; chnG)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE SLOT'S DEFINITION.  A duplication chain under a scan whose step
-- throws the accumulator away and re-wraps the arriving value as a
-- one-shot observable, which is the one step that converts an
-- EMISSION into a STORE reading: `sizeᵛ` at an `obs` is the held
-- expression's `sizeᵉ`.
----------------------------------------------------------------------
keepG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (obs (Pw k) ×ᵗ Pw k) (obs (Pw k))
keepG = strmᵗ (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ []))

reifyG : ∀ {n} {Γ : Ctx n} (k : ℕ) → Closed Γ (obs (Pw k))
reifyG k = scanᵉ keepG (strmᵗ emptyᵉ) (chnG k)

----------------------------------------------------------------------
-- WITNESS ONE — twelve rungs behind the reference.
----------------------------------------------------------------------
Γᴾ : Ctx 1
Γᴾ = obs (Pw 12) ∷ⱽ []ⱽ

slᴾ : Slots Γᴾ
slᴾ fz = shared (reifyG 12)

eᴾ : Closed Γᴾ (obs (Pw 12))
eᴾ = emptyᵉ

-- the parked entry is a bare reference, so its layer count is nought
-- whatever stands behind it
oᴾ : Closed Γᴾ (obs (Pw 12))
oᴾ = input fz

stᴾ : EvalSt eᴾ
stᴾ = installNode 0
        (mergeAll-st {Γ = Γᴾ} {t = obs (Pw 12)} nothing 1 (oᴾ ∷ []) true)
        (st-init eᴾ)

postᴾ : EvalSt eᴾ
postᴾ = proj₂ (proj₂ (proj₂ (proj₂
          (stepFrame {e = eᴾ} (gasPad 64 g0) 0 0 (from-inner mergeAllᵒ 0 7)
             root [] true (sched-init eᴾ slᴾ) stᴾ))))

----------------------------------------------------------------------
-- WITNESS TWO — one more rung behind the same reference, which is the
-- sweep's measure-side axis: the emission doubles while the charge
-- moves by four units of slot syntax.
----------------------------------------------------------------------
Γᴿ : Ctx 1
Γᴿ = obs (Pw 13) ∷ⱽ []ⱽ

slᴿ : Slots Γᴿ
slᴿ fz = shared (reifyG 13)

eᴿ : Closed Γᴿ (obs (Pw 13))
eᴿ = emptyᵉ

oᴿ : Closed Γᴿ (obs (Pw 13))
oᴿ = input fz

stᴿ : EvalSt eᴿ
stᴿ = installNode 0
        (mergeAll-st {Γ = Γᴿ} {t = obs (Pw 13)} nothing 1 (oᴿ ∷ []) true)
        (st-init eᴿ)

postᴿ : EvalSt eᴿ
postᴿ = proj₂ (proj₂ (proj₂ (proj₂
          (stepFrame {e = eᴿ} (gasPad 64 g0) 0 0 (from-inner mergeAllᵒ 0 7)
             root [] true (sched-init eᴿ slᴿ) stᴿ))))

----------------------------------------------------------------------
-- THE CHARGES, READ OFF THE STATES THE ROWS STAND AT.
----------------------------------------------------------------------

-- LOAD-BEARING: the first and fourth entries say the queue's own
-- layers contribute NOTHING at either depth, so the charge between the
-- two rows moves with the slot alone -- which is what makes the sweep
-- measure-side rather than an axis that cannot fail.
slotStoreFigures : List ℕ
slotStoreFigures = parkedLayAt 0 (EvalSt.nodes stᴾ)
                 ∷ slotSize (slᴾ fz)
                 ∷ sizeᵉ oᴾ
                 ∷ parkedLayAt 0 (EvalSt.nodes stᴿ)
                 ∷ slotSize (slᴿ fz)
                 ∷ []

slotStoreFigures≡ : slotStoreFigures ≡ 0 ∷ 59 ∷ 1 ∷ 0 ∷ 63 ∷ []
slotStoreFigures≡ = refl

-- LOAD-BEARING: it is what says the run reached the slot's definition
-- at all.  A reference the drain declined to resolve would leave the
-- door's own cell and nothing else.
slotStoreNodes≡ : length (EvalSt.nodes stᴾ) ∷ length (EvalSt.nodes postᴾ)
                ∷ length (EvalSt.nodes postᴿ) ∷ [] ≡ 1 ∷ 2 ∷ 2 ∷ []
slotStoreNodes≡ = refl

----------------------------------------------------------------------
-- THE CONCLUSION AT BOTH RUNGS, TWICE OVER.  The bound is tied to the
-- slot definition's own size, which is the most generous tie the
-- premises admit -- the queue premise reads a reference of syntax one
-- and the store premise reads a queue holding it.
----------------------------------------------------------------------

-- LOAD-BEARING: entries one and three are the charge with the summand
-- DROPPED, which at a parked reference is the premise's own bound
-- climbed by nothing; a table the telescope failed to reach would
-- report `false` four times.
slotStoreRows : List Bool
slotStoreRows =
    all (λ kv → boundedNode (iterSize 59 (parkedLayAt 0 (EvalSt.nodes stᴾ)) 59)
                  (proj₂ kv))
        (EvalSt.nodes postᴾ)
  ∷ all (λ kv → boundedNode
                  (iterSize 59 (parkedLayAt 0 (EvalSt.nodes stᴾ)
                                 + slotsSize slᴾ) 59)
                  (proj₂ kv))
        (EvalSt.nodes postᴾ)
  ∷ all (λ kv → boundedNode (iterSize 63 (parkedLayAt 0 (EvalSt.nodes stᴿ)) 63)
                  (proj₂ kv))
        (EvalSt.nodes postᴿ)
  ∷ all (λ kv → boundedNode
                  (iterSize 63 (parkedLayAt 0 (EvalSt.nodes stᴿ)
                                 + slotsSize slᴿ) 63)
                  (proj₂ kv))
        (EvalSt.nodes postᴿ)
  ∷ []

slotStoreRows≡ : slotStoreRows ≡ false ∷ true ∷ false ∷ true ∷ []
slotStoreRows≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The types are generated from the statement as it reads,
-- so a restatement changes them rather than leaving the rungs above
-- copied out beside a claim.  The premises are left as arguments: each
-- row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the same rungs the rows are, so a charge the
-- resolved slot outran would fail it exactly as the telescope-free
-- reading beside it does.  The queue entry is passed as the arrival,
-- which is what the singleton drain hands the subscription.
tieParkedSlot12 : Confirms
  (subscribeE-sz-store {e = eᴾ} slᴾ (gasPad 63 g0) oᴾ
     (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init eᴾ slᴾ) { nextNode = 1 }) stᴾ 59 59
     (iterSize 59 (layᵉ oᴾ + slotsSize slᴾ) 59))
tieParkedSlot12 = λ _ _ _ _ _ → refl

-- LOAD-BEARING: the same statement one rung deeper behind the
-- reference, which is the sweep's measure-side axis.
tieParkedSlot13 : Confirms
  (subscribeE-sz-store {e = eᴿ} slᴿ (gasPad 63 g0) oᴿ
     (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init eᴿ slᴿ) { nextNode = 1 }) stᴿ 63 63
     (iterSize 63 (layᵉ oᴿ + slotsSize slᴿ) 63))
tieParkedSlot13 = λ _ _ _ _ _ → refl
