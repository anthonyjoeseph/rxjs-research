-- ══════════════════════════════════════════════════════════════════
-- THE STORE HALF OF A FRAME'S OWN PARK READING SURVIVES ITS STEP, at
-- the two frame shapes that actually WRITE the cell it is about.  The
-- owner half of the same reading is a body, so the rows below are
-- taken against the node-table conjunct alone -- the premise is still
-- the whole reading, which is what every row supplies.
--
-- TARGET: frameParked-step @000000
--
-- WHAT THE ROWS INSTANTIATE.  A two-slot context, so `pathFloor` at a
-- root-ended chain is 2 and an `input` reference at index 0 or 1 sits
-- below it.  The chain is `map-f (nat̂ 0) ↠ root` where the frame under
-- test needs an observable payload, and `root` where it does not.
--
-- THE SCAN IS THE SHAPE AT RISK, and the two scan rows separate the
-- two ways its conclusion can be reached.  `stepFrame` at a `scan-f`
-- OVERWRITES the cell with `applyFn` of the frame's own closure, so
-- nothing about the old accumulator's reading survives on its own.
-- The TRANSPORT row runs an identity closure, where the post-state
-- accumulator IS the pre-state one and the conclusion comes from the
-- third premise; the BOUGHT row runs a closure that discards the
-- accumulator entirely and manufactures a reference at index 1, where
-- the third premise says nothing about the answer and the conclusion
-- comes from `frameStrat?` alone.  That is the header's claim that a
-- scan's reading is bought rather than transported, instantiated at
-- both of the cases it distinguishes.
--
-- WHAT IS NOT COVERED.  The `switchᵒ` and `exhaustᵒ` arms of
-- `innerFinish`, which write a different cell shape; the
-- `hasRoom = true` arm of the enqueue row; and a `share-sink` chain,
-- where the floor sits below the context width: every row here is
-- taken at a root-ended chain, so nothing says what happens when the
-- floor is not the full width.  `map-f` and `take-f` are covered only
-- degenerately, `framePark?` being `true` at both.
-- ══════════════════════════════════════════════════════════════════
module Probed.FramePark-Step where

open import Data.Bool using (false; true)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold; hot)
open import Rx.Exp
  using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; emptyᵉ; input;
         strmᵗ; fstᵗ; varᵗ; nat̂)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (EvalSt; Path; root; _↠_; map-f; scan-f; from-inner; thru-outer; mergeAllᵒ;
  sched-init; st-init; installNode; scan-st; mergeAll-st; stepFrame; mergeAllDrain)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (framePark?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
  using (frameParked-step)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT.  Two slots, so a root-ended chain has floor 2 and both
-- `input fzero` and `input (fsuc fzero)` sit below it.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

e₂ : Closed Γ₂ natᵗ
e₂ = emptyᵉ

sl₂ : Slots Γ₂
sl₂ fzero        = scripted (cold [] [])
sl₂ (fsuc fzero) = scripted (cold [] [])

----------------------------------------------------------------------
-- THE TWO CLOSURES.  `fn₀` keeps the accumulator, `fn₁` replaces it
-- with an observable naming slot 1 and reads the payload not at all.
----------------------------------------------------------------------

fn₀ : Fn Γ₂ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
fn₀ = fstᵗ (varᵗ (here refl))

fn₁ : Fn Γ₂ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
fn₁ = strmᵗ (input (fsuc fzero))

-- the chain a scan frame sits on: its output is an observable, and the
-- `map-f` below it is what carries the chain down to a `natᵗ` root
κˢ : Path Γ₂ (obs natᵗ) natᵗ
κˢ = map-f (nat̂ 0) ↠ root

-- the accumulator cell, at nid 5, holding an observable that names
-- slot 0
stˢ : EvalSt e₂
stˢ = installNode 5 (scan-st {t = obs natᵗ} (input fzero)) (st-init e₂)

----------------------------------------------------------------------
-- ROW 1 — TRANSPORT.  `applyFn fn₀ (acc , v)` is `acc`, so the cell is
-- rewritten with the value it already held and the post-state reading
-- is the pre-state one.  LOAD-BEARING on the third premise.
----------------------------------------------------------------------

tieScanTransport : Confirms
  (frameParked-step g0 0 0 (scan-f fn₀ 5) κˢ (3 ∷ []) false
     (sched-init e₂ sl₂) stˢ refl refl refl)
tieScanTransport = refl

----------------------------------------------------------------------
-- ROW 2 — BOUGHT.  `applyFn fn₁ (acc , v)` is `input (fsuc fzero)`,
-- which the pre-state cell never held: the post-state reading is
-- `1 <ᵇ 2 = true`, and the only premise that mentions it is the
-- closure's.  LOAD-BEARING on the first premise: drop the floor to 1
-- and the conclusion goes false, `inputsBelowᵉ 1 (input (fsuc fzero))`
-- being `1 <ᵇ 1 = false`, while the closure premise goes false at
-- exactly the same point.  Row 1 is load-bearing on the THIRD premise
-- instead -- at floor 0 the pre-state reading is already false and the
-- hypothesis blocks, an identity closure naming no input.
----------------------------------------------------------------------

tieScanBought : Confirms
  (frameParked-step g0 0 0 (scan-f fn₁ 5) κˢ (3 ∷ []) false
     (sched-init e₂ sl₂) stˢ refl refl refl)
tieScanBought = refl

----------------------------------------------------------------------
-- ROW 3 — THE ENQUEUE, one level above the arm of
-- `thruConsume-cellPark` that reduces without a leaf at all.
-- A capacity-zero mergeAll node at nid 0,
-- so `hasRoom` fails and the arriving observable is appended to the
-- queue the reading is about.  LOAD-BEARING on the vals premise, which
-- prices the appended term.
----------------------------------------------------------------------

stᵗ : EvalSt e₂
stᵗ = installNode 0 (mergeAll-st {t = natᵗ} (just 0) 0 [] false) (st-init e₂)

tieThruEnqueue : Confirms
  (frameParked-step g0 0 0 (thru-outer mergeAllᵒ 0) root
     (input fzero ∷ []) false (sched-init e₂ sl₂) stᵗ refl refl refl)
tieThruEnqueue = refl

----------------------------------------------------------------------
-- ROW 4 — DEGENERATE, and labelled so.  A `map-f` names no cell, so
-- `framePark?` is `true` on both sides and the row could not have
-- failed.  It is here to pin that the free shapes really are free.
----------------------------------------------------------------------

tieMapFree : Confirms
  (frameParked-step g0 0 0 (map-f (nat̂ 0)) root (input fzero ∷ []) false
     (sched-init e₂ sl₂) stᵗ refl refl refl)
tieMapFree = refl

----------------------------------------------------------------------
-- ROWS 5 AND 6 — THE ARM WHERE THE WRITE IS NOT TRANSPARENT.  A
-- `from-inner` step at `fin = true` and an empty registry runs
-- `innerFinish`, which DRAINS the flatten's parked queue and reinstalls
-- the cell with whatever the drain left.  So the post-state reading is
-- about a queue the frame itself rewrote, and the question is whether
-- what it rewrote is priced.
--
-- The cell is at capacity one with one lane live, so the drain's first
-- pop takes the freed lane and its second finds none: the residue is a
-- PROPER SUFFIX and the reading is carried rather than emptied.  Both
-- parked terms name inputs below the floor; drop the floor to one and
-- the second term falsifies the conclusion and the third premise
-- together, which is what makes these LOAD-BEARING on that premise.
--
-- Row 5 runs the pop at `g0`, where `subscribeInner` mints an instance
-- and returns the state untouched, so what is measured is the drain
-- and the reinstall alone.  Row 6 runs it under gas, where the pop
-- re-enters `subscribeE` on a fresh `from-inner` chain and the state
-- coming back is one a subscription built.
----------------------------------------------------------------------

stᶠ : EvalSt e₂
stᶠ = installNode 7
        (mergeAll-st {t = natᵗ} (just 1) 1
          (input fzero ∷ input (fsuc fzero) ∷ []) false)
        (st-init e₂)

-- the drain the step runs, named so its residue can be pinned beside
-- the rows that depend on it
-- slot 0 is HOT, so the inner the drain's first pop subscribes never
-- completes and the freed lane stays taken.  Under gas a COLD inner
-- finishes inside its own subscribe, the count never rises, and the
-- drain empties the queue outright -- which would leave the reading
-- with nothing to carry and the rows below degenerate.
sl₂ʰ : Slots Γ₂
sl₂ʰ fzero        = scripted (hot [])
sl₂ʰ (fsuc fzero) = scripted (cold [] [])

drained : Gas → _
drained g = mergeAllDrain g 7 root 0 0 (just 1) 0
              (input fzero ∷ input (fsuc fzero) ∷ []) (sched-init e₂ sl₂ʰ) stᶠ

tieInnerResidue : Confirms
  (frameParked-step g0 0 0 (from-inner mergeAllᵒ 7 9) root (3 ∷ []) true
     (sched-init e₂ sl₂ʰ) stᶠ refl refl refl)
tieInnerResidue = refl

tieInnerGassed : Confirms
  (frameParked-step (gasPad 40 g0) 0 0 (from-inner mergeAllᵒ 7 9) root
     (3 ∷ []) true (sched-init e₂ sl₂ʰ) stᶠ refl refl refl)
tieInnerGassed = refl

-- what the drain actually left, so the two rows above are not read as
-- a claim about an emptied queue: the second parked term survives the
-- step at both gas settings, and it is the term the reading is about
residue≡ : proj₁ (proj₂ (proj₂ (proj₂ (drained g0)))) ≡ input (fsuc fzero) ∷ []
residue≡ = refl

residueGassed≡ :
  proj₁ (proj₂ (proj₂ (proj₂ (drained (gasPad 40 g0))))) ≡ input (fsuc fzero) ∷ []
residueGassed≡ = refl

-- and the floor at which both the conclusion and the premise it stands
-- on go false together, which is what makes the rows load-bearing
-- rather than degenerate
lowFloorPre : framePark? 1 (from-inner {s = natᵗ} mergeAllᵒ 7 9) stᶠ ≡ false
lowFloorPre = refl

lowFloorPost :
  framePark? 1 (from-inner {s = natᵗ} mergeAllᵒ 7 9)
    (proj₂ (proj₂ (proj₂ (proj₂
      (stepFrame g0 0 0 (from-inner mergeAllᵒ 7 9) root (3 ∷ []) true
         (sched-init e₂ sl₂ʰ) stᶠ)))))
    ≡ false
lowFloorPost = refl
