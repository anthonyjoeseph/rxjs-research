-- THE JOIN'S LEAVES, AT THE POINT THE PARENT SPENDS THEM.  The chain
-- descent is a body over a `⊔`-fold now, and what the fold takes as
-- parameters are the two obligations at ONE edge: that a frame's own
-- spend fits under the position's ceiling, and that the ceiling
-- survives the step that frame makes.  Both are stated at a single
-- `Frame` and a single `Path`, which is the smallest unit this measure
-- has, and both sides of each reduce -- so the rows below read them at
-- states rather than symbolically, and at each arm of `depthFrame`
-- that charges rather than at whichever one a program hands over.
--
-- THIS IS WHAT THE DECOMPOSITION WAS FOR, and it is the whole reading:
-- the parent's own conclusion is CLOSED to instantiation -- the descent
-- does not return at a state a chain has stepped, for a doubling
-- recorded at `depthShareGo` that no instrument gets past -- while
-- these leaves, carved off the same statement, are numerals.  A green
-- row here is therefore evidence about a region the parent's own rows
-- could never reach.
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
-- WHAT IS NOT COVERED IS THE OTHER TWO LEAVES, and their obstructions
-- are not the same one.  `share-fold-fit` is `depthFold` again, so it
-- inherits the parent's own barrier and no instrument reaches it.
-- `share-step-fit` is merely unpointed: its `rid` and `p` are a
-- `shareAdmit` entry, and `admitFig` reads that list off the registry
-- here and finds it empty, so what it wants is a program rather than
-- an instrument.
-- TARGET: frame-depth-fit @9d21e7
-- TARGET: chain-fit-step @266bd8
module Probed.Depth-Join where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (_,_; _×_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas)
open import Rx.Exp using (Ty; Val; natᵗ)
open import Rx.Evaluator
  using (Sched; Arrival; Path; Frame; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; arrTy; arrVal; budgetAt)

open import Data.List renaming (length to lengthL) using ()
open import Data.Fin using (zero)
open import Rx.Evaluator using (shareAdmit; EvalSt; mergeAllᵒ; RegId; memberSource)

open import Refuted.Demand-Programs using (Γ₂; progU; progF; sucGF)
open import Probed.Depth-Sighted
  using (uArr; uPth; uSc; uSt; slotsT; deep; wSched; wSt; after1; slotsF)
open import Probed.Apparatus using (Confirms)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps
  using (frame-depth-fit; chain-fit-step)

-- WHICH FRAME HEADS THE PATH, WHICH IS WHAT DECIDES WHETHER THE ROWS
-- BELOW COULD FAIL.  Three of `depthFrame`'s five arms are flatly
-- nought, so a row at one of them is unfalsifiable however tight it
-- reads; the tag names the arm, and the length says the path is not
-- the empty one.
pathTag : ∀ {v t} → Path Γ₂ v t → ℕ
pathTag root                   = 0
pathTag (share-sink _)         = 1
pathTag (map-f _ ↠ _)          = 2
pathTag (scan-f _ _ ↠ _)       = 3
pathTag (take-f _ ↠ _)         = 4
pathTag (from-inner _ _ _ ↠ _) = 5
pathTag (thru-outer _ _ ↠ _)   = 6

pathLen : ∀ {v t} → Path Γ₂ v t → ℕ
pathLen root           = 0
pathLen (share-sink _) = 0
pathLen (_ ↠ p)        = suc (pathLen p)

shapeFigs : ℕ
shapeFigs = pathTag uPth + 10 * pathLen uPth
          + 100 * Arrival.tick uArr + 10000 * Arrival.source uArr

shapeFigs≡ : shapeFigs ≡ 10235
shapeFigs≡ = refl

-- THE EDGE, SPLIT OFF THE PATH THE EVALUATOR BUILT.  The leaves quantify
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

-- AND THAT THE POSITION'S CEILING SURVIVES THE STEP THAT FRAME MAKES,
-- which is the obligation the fold could not discharge for itself and
-- the reason the invariant is the ceiling rather than the store.  The
-- slots conjunct is `refl` and the ceiling conjunct is a comparison
-- between two numerals at states one `stepFrame` apart.
stepRow : Confirms
  (chain-fit-step (Sched.slots uSc) uSf 2 (Arrival.tick uArr)
     (Split.hd uSpl) (Split.tl uSpl) uVals uFin uSc uSt refl refl)
stepRow = refl , ≤ᵇ⇒≤ _ _ tt

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
-- class wants and the half nothing else supplies: the two rows above
-- stand at a reached edge whose arm cannot fail the way this one can.
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

-- AND THE CEILING SURVIVES THAT FRAME'S STEP TOO, which is the second
-- leaf read at the arm the first pair could not reach.
thruStep4 : Confirms
  (chain-fit-step {e = progU 8 2} slotsT tSf 0 0
     (thru-outer mergeAllᵒ 7) (root {Γ = Γ₂} {t = natᵗ})
     (deep 4 ∷ []) false wSched wSt refl refl)
thruStep4 = refl , ≤ᵇ⇒≤ _ _ tt

-- WHETHER THE ROUND OFFERS A REGISTRATION AT ALL, which is what
-- `share-step-fit` wants and what nothing here has been able to
-- supply.  Its `rid` and `p` are exactly a `shareAdmit` entry, so the
-- question is whether the shared slot has any at the point these rows
-- stand at -- a corpus fact, read off the registry rather than
-- guessed, and a nought is a boundary rather than a failure.
admitFig : ℕ
admitFig = lengthL (shareAdmit zero (EvalSt.registry uSt))

admitFig≡ : admitFig ≡ 0
admitFig≡ = refl

-- AND THE POINT IS NOT ONE FAMILY OVER, which is what this figure was
-- written to test and what it refutes.  The round above defers its
-- shared slot behind a capacity-one outer, so a natural reading of the
-- empty admit list is that the slot is merely unspent yet -- and the
-- width family subscribes every inner at the root, the shared one
-- included, so on that reading its registry should carry the entry at
-- the very first arrival.  It does not.  The figure reads the count
-- and the head of the first admitted path together, because a nought
-- count hands the extractor its degenerate filler, and it reports
-- exactly that pair: no entry, and `root` standing in for the path.
--
-- SO THE BOUNDARY IS WIDER THAN A DEFERRED CONNECT, and what makes it
-- so is NOT established here.  Two families whose shared slots are
-- connected in opposite ways agree, which rules out the connect's
-- timing as the whole story and leaves the question at `shareAdmit`'s
-- own guard -- whether a slot subscribed as a program appears in the
-- registry under the source index the admit filters on at all.  That
-- is a reading of the registration path, not another program.
fSt : EvalSt (progF 3 2)
fSt = proj₂ (after1 (progF 3 2) slotsF (sucGF 1 2 2 3 2))

record Adm : Set where
  constructor adm
  field
    rid : RegId
    pth : Path Γ₂ natᵗ natᵗ

firstAdm : List (RegId × Path Γ₂ natᵗ natᵗ) → Adm
firstAdm []            = adm 0 root
firstAdm ((r , p) ∷ _) = adm r p

fAdm : Adm
fAdm = firstAdm (shareAdmit zero (EvalSt.registry fSt))

admFig : ℕ
admFig = lengthL (shareAdmit zero (EvalSt.registry fSt))
       + 10 * suc (pathTag (Adm.pth fAdm))

admFig≡ : admFig ≡ 10
admFig≡ = refl

-- AND WHAT EMPTIES IT IS THE DEF, WHICH IS NEITHER OF THE TWO THINGS
-- THE WRAPPER CONTROLS.  Reading the admit list alone cannot separate
-- three ways of arriving at a nought -- the slot was never connected
-- because the fuel ran dry at the edge, the slot connected and the
-- entry is simply not admitted, or the entry was written and then
-- taken back -- and only the last of those says anything about the
-- statement's index.  The figure reads the whole registry beside the
-- two latches the connect sets, so one run decides among them: the
-- units are the registrations standing at that point -- the width
-- family subscribes its scripted slot once per copy, so that digit is
-- not a nought and the flags are carried clear of it -- the thousands
-- say whether source nought has completed, the ten-thousands whether
-- it ever connected at all.
--
-- IT IS THE THIRD, AND THAT NAMES THE OBSTRUCTION.  The slot connects
-- and completes in the same call, because `sharedConnect` subscribes
-- the def and asks whether the burst it got back completed -- and the
-- def here is built from one-shots under a scan, so it exhausts inside
-- its own connect burst and the branch that latches it drops every
-- registration on that source before returning.  The registration IS
-- written; it does not survive the call that writes it.  So the
-- emptiness is a property of the DEF being synchronous, which both
-- families share and neither wrapper alters -- which is why connecting
-- eagerly and connecting late agreed.  `Probed.Root` had already read
-- the general fact off a one-shot def; what the flags add is that this
-- corpus reaches it by the connect-and-latch route rather than by a
-- fuel that ran dry before the edge, which is the reading that would
-- have pointed at the gas instead of at the program.
--
-- SO WHAT `share-step-fit` WANTS IS A SHARE WHOSE DEF OUTLIVES ITS OWN
-- CONNECT, and the telescope invariant is what puts that out of this
-- corpus's reach rather than out of reach: a slot's def may reference
-- only STRICTLY EARLIER slots, so a nought-indexed share can name no
-- scripted source at all and every def available to it is sync by
-- construction.  A share at a LATER index over a scripted slot below
-- it is the shape that clears this, and `Probed.Root` builds one -- a
-- share over an empty hot, which never fires and so never completes,
-- whose registrations are pinned there as still standing at the root
-- exit.  The row is unpointed by THIS corpus and not by its own index,
-- and the point it wants already exists one module over.
b2n : Bool → ℕ
b2n false = 0
b2n true  = 1

regFig : ℕ
regFig = lengthL (EvalSt.registry fSt)
       + 1000 * b2n (memberSource 0 (EvalSt.completedSources fSt))
       + 10000 * b2n (memberSource 0 (EvalSt.connectedShares fSt))

regFig≡ : regFig ≡ 11004
regFig≡ = refl
