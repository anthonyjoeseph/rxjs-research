-- THE FRAME'S OWN SPEND, AT THE POINT THE PARENT SPENDS IT.  The chain
-- descent is a body over a `⊔`-fold, and the obligation read here is
-- the one that stands at a single `Frame` and a single `Path` and whose
-- both sides reduce: that a frame's charge fits under the position's
-- ceiling.  The rows read it at states rather than symbolically, and at
-- each arm of `depthFrame` that charges rather than at whichever one a
-- program happens to hand over.
--
-- THIS IS WHAT THE DECOMPOSITION WAS FOR, and it is the whole reading:
-- the parent's own conclusion is CLOSED to instantiation -- the descent
-- does not return at a state a chain has stepped, for a doubling
-- recorded at `depthShareGo` that no instrument gets past -- while this
-- leaf, carved off the same statement, is numerals.  A green row here
-- is therefore evidence about a region the parent's own rows could
-- never reach.
--
-- THE POINT IS THE CHAIN THE ROUND ADMITS FIRST, reused from
-- `Probed.Depth-Sighted` rather than rebuilt, so these rows stand at
-- the same arrival, schedule and state its own descent figure is
-- pinned at.  `shapeFigs` reports what that path IS -- a `from-inner`
-- head over three frames, at the second tick of source one -- because
-- the head decides which arm of `depthFrame` the frame row exercises,
-- and three of the five arms are flatly nought and could not fail.
-- This one is not: `from-inner` charges the react.
--
-- NON-VACUITY IS PINNED, NOT ASSERTED.  `splitP` is total, and its two
-- degenerate arms hand back a `take-f` whose spend is nought -- a row
-- taken there could not fail.  The tag equation says the arm was not
-- taken: five is the `from-inner` head, and it is read in the same
-- build as the rows.
--
-- AND THE STEP OBLIGATIONS ARE NOT HERE, WHICH IS A PROPERTY OF THEIR
-- STATEMENTS AND NOT OF THIS CORPUS.  What a fold or a frame does to
-- the store is now priced against the round's grant, and that grant is
-- a member of the nesting tower's sealed block -- so neither the
-- premise nor the conclusion reduces at any program, and there is no
-- row to stand.  The vocabularies that reached those arms, and the
-- registry readings that established which shares leave a registration
-- alive at all, are in the recovery below; what they FOUND is in the
-- headers of the statements it constrains.
-- TARGET: frame-depth-fit @9d21e7
-- RECOVERY: git show 0b04ccf:agda/evidence/probed/Probed/Depth-Join.agda
--   restores the share corpora -- a share over an empty hot, the same
--   at an observable-typed slot, and one registered on a later share --
--   together with the admit and registry figures that pin which of them
--   the evaluator actually leaves an entry at.
module Probed.Depth-Join where

open import Data.Bool using (Bool; false)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas)
open import Rx.Exp using (Ty; Val; natᵗ; Ctx)
open import Rx.Evaluator
  using (Sched; Arrival; Path; Frame; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; arrTy; arrVal; budgetAt; mergeAllᵒ)

open import Refuted.Demand-Programs using (Γ₂; progU)
open import Probed.Depth-Sighted
  using (uArr; uPth; uSc; uSt; slotsT; deep; wSched; wSt)
open import Probed.Apparatus using (Confirms)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps
  using (frame-depth-fit)

-- WHICH FRAME HEADS THE PATH, WHICH IS WHAT DECIDES WHETHER THE ROWS
-- BELOW COULD FAIL.  Three of `depthFrame`'s five arms are flatly
-- nought, so a row at one of them is unfalsifiable however tight it
-- reads; the tag names the arm, and the length says the path is not
-- the empty one.
pathTag : ∀ {n} {Γ : Ctx n} {v t} → Path Γ v t → ℕ
pathTag root                   = 0
pathTag (share-sink _)         = 1
pathTag (map-f _ ↠ _)          = 2
pathTag (scan-f _ _ ↠ _)       = 3
pathTag (take-f _ ↠ _)         = 4
pathTag (from-inner _ _ _ ↠ _) = 5
pathTag (thru-outer _ _ ↠ _)   = 6

pathLen : ∀ {n} {Γ : Ctx n} {v t} → Path Γ v t → ℕ
pathLen root           = 0
pathLen (share-sink _) = 0
pathLen (_ ↠ p)        = suc (pathLen p)

shapeFigs : ℕ
shapeFigs = pathTag uPth + 10 * pathLen uPth
          + 100 * Arrival.tick uArr + 10000 * Arrival.source uArr

shapeFigs≡ : shapeFigs ≡ 10235
shapeFigs≡ = refl

-- THE EDGE, SPLIT OFF THE PATH THE EVALUATOR BUILT.  The leaf quantifies
-- over a frame and the path below it, and the point has to supply both;
-- taking them off `uPth` is what keeps this a reachable edge rather than
-- a pair written down beside a state that never saw them.  The
-- degenerate arms are total fillers, and `shapeFigs` above says which
-- arm is live.
record Split (v : Ty) : Set where
  constructor spl
  field
    {mid} : Ty
    hd    : Frame Γ₂ v mid
    tl    : Path Γ₂ mid natᵗ

splitP : ∀ {v} → Path Γ₂ v natᵗ → Split v
splitP root           = spl (take-f 0) root
splitP (share-sink i) = spl (take-f 0) (share-sink i)
splitP (f ↠ p)        = spl f p

uSpl : Split (arrTy uArr)
uSpl = splitP uPth

uSf : Gas
uSf = budgetAt (progU 8 2) (Sched.slots uSc) 2

uVals : List (Val Γ₂ (arrTy uArr))
uVals = arrVal uArr ∷ []

uFin : Bool
uFin = Arrival.isLast uArr

-- THE FRAME'S OWN SPEND, at the head the tag names.  Both premises are
-- reflexivity at the tightest value each admits -- the slots are the
-- schedule's own and the gas is the budget the descent itself opens
-- with -- so nothing is weakened to make the row stand.
frameRow : Confirms
  (frame-depth-fit (Sched.slots uSc) uSf 2 (Arrival.tick uArr)
     (Split.hd uSpl) (Split.tl uSpl) uVals uFin uSc uSt refl refl)
frameRow = ≤ᵇ⇒≤ _ _ tt

-- THE OTHER ARM THAT CHARGES, at a frame this tree already builds.
-- `from-inner` above is one of `depthFrame`'s two live arms and
-- `thru-outer` is the other -- a successor above the react, so the
-- larger of the two -- and the reason no row above reaches it is that
-- the corpus does not head a chain with one.  `Probed.Depth-Sighted`
-- assembles exactly that frame for its own walk rows, so the arm is
-- reachable here by spending its state rather than by finding a
-- program, and the row below is the leaf read at it.
--
-- WHAT THIS ROW IS AND IS NOT.  The frame and its state are ASSEMBLED
-- -- a `mergeAll` node installed over the initial state -- not walked
-- to by a run, so this is evidence about the ARM and not about a
-- position a cascade hands out.  That is the weaker half of what the
-- class wants and the half nothing else supplies: the row above stands
-- at a reached edge whose arm cannot fail the way this one can.
-- The nesting is read at two depths so a pass that only survives a
-- flat inner is not one, and the gas is the budget the statement
-- names rather than the pad the walk rows use.
tSf : Gas
tSf = budgetAt (progU 8 2) slotsT 0

thruRow1 : Confirms
  (frame-depth-fit {e = progU 8 2} slotsT tSf 0 0
     (thru-outer mergeAllᵒ 7) (root {Γ = Γ₂} {t = natᵗ})
     (deep 1 ∷ []) false wSched wSt refl refl)
thruRow1 = ≤ᵇ⇒≤ _ _ tt

thruRow4 : Confirms
  (frame-depth-fit {e = progU 8 2} slotsT tSf 0 0
     (thru-outer mergeAllᵒ 7) (root {Γ = Γ₂} {t = natᵗ})
     (deep 4 ∷ []) false wSched wSt refl refl)
thruRow4 = ≤ᵇ⇒≤ _ _ tt
