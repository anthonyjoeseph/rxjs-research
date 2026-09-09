-- THE FRAME PARK READING IS NOT A COROLLARY OF THE CAPS RECEIPT EITHER,
-- and this is the SAME finding as the registry-level one arriving at a
-- statement that is spent rather than merely stated.  `frame-parkStrat`
-- takes a receipt and a stratification reading and hands back the park
-- reading of an ARBITRARY frame -- so it asks the invariant about a cell
-- no part of the invariant is quantified over.  The registry conjuncts
-- cannot reach it: they read the chains the registry HOLDS, and the
-- frame here is in no registry at all.
--
-- SO THE WITNESS IS THE ADMITTED-ENTRY ONE WITH ITS REGISTRY EMPTIED.
-- Emptying it is what makes the row load-bearing rather than a repeat:
-- every registry-keyed conjunct then holds vacuously, so the receipt is
-- as strong as it can be while the reading is still false, and no
-- strengthening of a registry conjunct can close the gap.  The cell is
-- present and holds a queue naming an input the sink's floor cannot
-- cover, which is the one shape the park reading exists to reject.
module Refuted.Frame-Park-From-Caps where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; ofᵉ; emptyᵉ; strmᵗ; nat̂;
  input)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Path; Frame; share-sink; from-inner; _↠_;
  mergeAllᵒ; mergeAll-st; Sched; EvalSt; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; framePark?; pathFloor; pathStrat?)

------------------------------------------------------------------
-- THE PROGRAM, which is the admitted-entry witness's own: slot nought
-- carries an observable scripted by no data, slot one is the input a
-- stored cell names when it is meant to name nothing.
------------------------------------------------------------------

Γᶠ : Ctx 2
Γᶠ = obs natᵗ ∷ natᵗ ∷ []

d₀ : Closed Γᶠ (obs natᵗ)
d₀ = ofᵉ (strmᵗ emptyᵉ ∷ [])

slᶠ : Slots Γᶠ
slᶠ fzero        = shared d₀
slᶠ (fsuc fzero) = shared emptyᵉ

progᶠ : Closed Γᶠ natᵗ
progᶠ = ofᵉ (nat̂ 0 ∷ [])

schedᶠ : Sched Γᶠ
schedᶠ = sched-init progᶠ slᶠ

cᶠ : Caps
cᶠ = caps 99 99 99

-- the frame and the chain it heads.  A `from-inner` names the cell, and
-- the sink below it fixes the floor the cell's contents are read at
badFrame : Frame Γᶠ (obs natᵗ) (obs natᵗ)
badFrame = from-inner mergeAllᵒ 3 3

sinkᶠ : Path Γᶠ (obs natᵗ) natᵗ
sinkᶠ = share-sink fzero

-- THE STATE, AND THE EMPTY REGISTRY IS THE WHOLE POINT: the cell is
-- populated, nothing is registered on it
stᶠ : EvalSt progᶠ
stᶠ = record (st-init progᶠ)
  { nodes = (3 , mergeAll-st nothing 0 (input (fsuc fzero) ∷ []) false) ∷ [] }

-- LOAD-BEARING: the whole separation is that this reads `true`.  It
-- would read `false` at a cap below the witness's own sizes, and again
-- if any registry-keyed conjunct could see the cell -- which is exactly
-- what an empty registry rules out.
stᶠ-capsOK : capsOK? cᶠ schedᶠ stᶠ ≡ true
stᶠ-capsOK = refl

-- LOAD-BEARING: the statement's OTHER premise, so the row separates the
-- conclusion from the receipt rather than from a missing hypothesis
badFrame-stratified : pathStrat? (badFrame ↠ sinkᶠ) ≡ true
badFrame-stratified = refl

-- LOAD-BEARING: it would read `true` at a queue naming an input below
-- the sink's index, and at any cell the frame does not name
badFrame-unparked : framePark? (pathFloor sinkᶠ) badFrame stᶠ ≡ false
badFrame-unparked = refl

------------------------------------------------------------------
-- THE REFUTATION.  Stated over the free variables the postulate has,
-- so the row kills the statement as written rather than one instance
-- of it.
------------------------------------------------------------------

frame-park-from-caps-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
     (c : Caps) (f : Frame Γ s u) (κ : Path Γ u t)
     (sched : Sched Γ) (st : EvalSt e) →
     capsOK? c sched st ≡ true →
     pathStrat? (f ↠ κ) ≡ true →
     framePark? (pathFloor κ) f st ≡ true) →
  ⊥
frame-park-from-caps-absurd h
  with h {e = progᶠ} cᶠ badFrame sinkᶠ schedᶠ stᶠ stᶠ-capsOK badFrame-stratified
... | ()
