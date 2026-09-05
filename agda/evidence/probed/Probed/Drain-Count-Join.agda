-- ══════════════════════════════════════════════════════════════════
-- THE MAX OVER A QUEUE OF SEVERAL, AT THE TWO QUEUES WHERE IT IS NOT
-- A MAX OVER A SINGLETON.
--
-- TARGET: mergeAllDrain-sz @7c7e56
--
-- WHY A QUEUE OF SEVERAL.  Every row this statement has ever stood at
-- parks exactly one program, so the leaf's join has only ever joined
-- one number with the unit and its shape is untested.  A queue of
-- several entries of one kind would still ask it nothing: the entries
-- would agree in what bounds them.  What asks it something is a queue
-- whose entries carry DIFFERENT layer counts and whose runs are
-- nonetheless hidden behind the same shared slot, so the max is a real
-- max and the whole of what it charges is still off the axis the
-- layers can see.
--
-- WHAT THE ROWS DECIDE.  The first queue parks a bare reference beside
-- the same reference under one operator: layer counts zero and one, so
-- the join returns one, and the run behind both is the twelve-rung
-- chain.  Both the bare bound and the max alone fail against what that
-- run delivers, and the statement's own charge -- the max plus the
-- telescope -- holds.  The falsifiable content is the second of those:
-- a max the layers CAN see, at a queue of several, still failing.
--
-- WHAT THE SECOND QUEUE ADDS.  The two references deliver ONE value
-- between them, because connecting a shared slot happens once and the
-- later reference finds it connected -- so the first queue exercises
-- the join in the CHARGE and not in the list.  The second parks the
-- chain written out beside the two references; its delivered list
-- holds two values from two different entries' runs, which is what
-- asks a single charge to cover several runs at once.
--
-- NOT COVERED.  Whether a later entry's run is inflated by state an
-- earlier entry left behind: no queue here makes two HIDDEN runs both
-- deliver, and that is the join's remaining risk.  Nor can any queue
-- in this family separate a max from a SUM -- the two agree at the
-- first queue and stand one apart at the second, and the only entries
-- whose layer counts are large are the visible ones, whose rung of the
-- ladder outruns anything the family can emit, so the row that would
-- tell them apart cannot fail.  Nor a queue whose entries install
-- nodes of their own, these installing none; nor one reaching more
-- than one slot.
-- ══════════════════════════════════════════════════════════════════
module Probed.Drain-Count-Join where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Closed; Val; Fn; obs; input; mapᵉ; varᵗ)
open import Rx.Slots using (slotsSize)
open import Rx.Layer-Count using (layᵛˢ)
open import Rx.Evaluator using (EvalSt; root; mergeAll-st; installNode;
  mergeAllDrain; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; mergeAllDrain-sz)
open import Refuted.Frame-Step-Size-Slot
  using (Pw; chnG; Γ₂; sl₂; e₂)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE TWO QUEUES.  The first holds a bare reference to the shared slot
-- and the same reference under one operator; the second adds the
-- slot's own chain written out.
----------------------------------------------------------------------
idPw : Fn Γ₂ [] [] [] (Pw 12) (Pw 12)
idPw = varᵗ (here refl)

qM : List (Closed Γ₂ (Pw 12))
qM = input fzero ∷ mapᵉ idPw (input fzero) ∷ []

qJ : List (Closed Γ₂ (Pw 12))
qJ = input fzero ∷ mapᵉ idPw (input fzero) ∷ chnG 12 ∷ []

stM : EvalSt e₂
stM = installNode 0 (mergeAll-st {Γ = Γ₂} {t = Pw 12} nothing 2 qM true)
        (st-init e₂)

stJ : EvalSt e₂
stJ = installNode 0 (mergeAll-st {Γ = Γ₂} {t = Pw 12} nothing 3 qJ true)
        (st-init e₂)

outM : List (Val Γ₂ (Pw 12))
outM = proj₁ (mergeAllDrain {e = e₂} (gasPad 64 g0) 0 root 0 0
                nothing 0 qM (sched-init e₂ sl₂) stM)

outJ : List (Val Γ₂ (Pw 12))
outJ = proj₁ (mergeAllDrain {e = e₂} (gasPad 64 g0) 0 root 0 0
                nothing 0 qJ (sched-init e₂ sl₂) stJ)

----------------------------------------------------------------------
-- THE FIGURES: each queue's joined layer count beside how many values
-- its drain delivers.  The first is a max over zero and one; its two
-- entries deliver one value between them.  The second is a max over
-- zero, one and twelve, and its list is assembled from two entries.
----------------------------------------------------------------------
joinFigures : List ℕ
joinFigures = layᵛˢ {Γ = Γ₂} (obs (Pw 12)) qM
            ∷ length outM
            ∷ layᵛˢ {Γ = Γ₂} (obs (Pw 12)) qJ
            ∷ length outJ
            ∷ []

joinFigures≡ : joinFigures ≡ 1 ∷ 1 ∷ 12 ∷ 2 ∷ []
joinFigures≡ = refl

----------------------------------------------------------------------
-- THE ROWS AT THE FIRST QUEUE.
----------------------------------------------------------------------

-- LOAD-BEARING, all three.  The first is the bare bound and the second
-- is the max the layers can see, and either would report `true` if the
-- two references had failed to reach the chain behind the slot; the
-- third is the statement's own charge, and it would report `false` if
-- the telescope summand did not cover a run entered twice.  What moves
-- between the second and the third is the summand alone, the max
-- standing at one throughout.
joinRowsM : List Bool
joinRowsM = valsSz? {Γ = Γ₂} {s = Pw 12} (iterSize 51 0 51) outM
          ∷ valsSz? {Γ = Γ₂} {s = Pw 12}
              (iterSize 51 (layᵛˢ (obs (Pw 12)) qM) 51) outM
          ∷ valsSz? {Γ = Γ₂} {s = Pw 12}
              (iterSize 51 (layᵛˢ (obs (Pw 12)) qM + slotsSize sl₂) 51) outM
          ∷ []

joinRowsM≡ : joinRowsM ≡ false ∷ false ∷ true ∷ []
joinRowsM≡ = refl

----------------------------------------------------------------------
-- THE ROWS AT THE SECOND QUEUE.
----------------------------------------------------------------------

-- The first is LOAD-BEARING: it reports `true` unless the list the
-- drain returns genuinely holds what the deepest run emits, so it is
-- what says the row below is not bought by a quantifier over small
-- values.  The second is DEGENERATE and carried because it is the
-- statement's own reading at a list assembled from two entries: a
-- visible entry of twelve layers puts the charge at a rung of the
-- ladder no program of this family can outgrow, so nothing about this
-- queue could make it fail.
joinRowsJ : List Bool
joinRowsJ = valsSz? {Γ = Γ₂} {s = Pw 12} (iterSize 51 0 51) outJ
          ∷ valsSz? {Γ = Γ₂} {s = Pw 12}
              (iterSize 51 (layᵛˢ (obs (Pw 12)) qJ + slotsSize sl₂) 51) outJ
          ∷ []

joinRowsJ≡ : joinRowsJ ≡ false ∷ true ∷ []
joinRowsJ≡ = refl

----------------------------------------------------------------------
-- THE TIES.  Each bound is the slot definition's own size, which is
-- the most generous tie the premises admit, so the rows above are read
-- against the statement as it stands rather than against a predicate
-- restated here.
----------------------------------------------------------------------
tieJoinM : Confirms
  (mergeAllDrain-sz {e = e₂} (gasPad 64 g0) 0 root 0 0 nothing 0 qM
     (sched-init e₂ sl₂) stM 51 51)
tieJoinM = λ _ _ _ → refl

tieJoinJ : Confirms
  (mergeAllDrain-sz {e = e₂} (gasPad 64 g0) 0 root 0 0 nothing 0 qJ
     (sched-init e₂ sl₂) stJ 51 51)
tieJoinJ = λ _ _ _ → refl
