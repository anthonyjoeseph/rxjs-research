-- ══════════════════════════════════════════════════════════════════
-- WHAT A SUBSCRIBE EMITS, READ BELOW THE FLOOR, instantiated at the
-- one arm where the premise and the conclusion read DIFFERENT syntax.
-- Everywhere else the claim is a homomorphism -- the source's own
-- subterms are what come back, so premise and conclusion move
-- together and a row cannot separate them.  The slot read is the
-- exception: the premise reads an INDEX and what is emitted is the
-- telescope's DEF, which the source does not contain at all.
--
-- TARGET: subscribeInner-strat @d11e63
--
-- WHAT THE ROWS INSTANTIATE.  Two slots: nought is scripted data, one
-- is a SHARED observable whose def names slot nought.  The source
-- under test is a reference to slot one, so it is an observable OF
-- observables, and what the subscribe hands back is the def's
-- emission -- a value carrying real syntax, which is the only shape
-- where the reading can be false at all.
--
-- WHAT IS NOT COVERED.  Every recursive arm of the evaluator beyond
-- one slot read: no `μ`, no nested `*All`, no take cut, and no
-- arrival that routes back through the frame.  A scripted slot is
-- reached only at DATA, which is where its own type restriction puts
-- it, so nothing here separates a scripted slot from the data arm of
-- the value reading.  The floor is two throughout, so no row
-- distinguishes the floor from the context width.
-- ══════════════════════════════════════════════════════════════════
module Probed.Subscribe-Inner-Strat where

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; emptyᵉ; ofᵉ; input;
                          strmᵗ; nat̂)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Path; root; _↠_; map-f; mergeAllᵒ;
                                sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
  using (subscribeInner-strat)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT.  Slot one is the observable-typed SHARED def, which is
-- the only slot shape whose emission has syntax to read: a scripted
-- slot is restricted to data by its own type.
----------------------------------------------------------------------

Γₚ : Ctx 2
Γₚ = natᵗ ∷ⱽ obs natᵗ ∷ⱽ []ⱽ

eₚ : Closed Γₚ natᵗ
eₚ = emptyᵉ

slₚ : Slots Γₚ
slₚ fzero        = scripted (cold [] [])
slₚ (fsuc fzero) = shared (ofᵉ (strmᵗ (input fzero) ∷ []))

-- the source under test: a reference to the shared observable slot,
-- so subscribing to it emits the def's own payload
oₚ : Val Γₚ (obs (obs natᵗ))
oₚ = input (fsuc fzero)

-- one frame, so the chain is not a bare sink and the path the inner
-- registers under is genuinely extended
κₚ : Path Γₚ (obs natᵗ) natᵗ
κₚ = map-f (nat̂ 0) ↠ root

----------------------------------------------------------------------
-- ROW 1 — THE SLOT READ.  LOAD-BEARING: the premise reads the slot
-- INDEX (`1 <ᵇ 2`) and the conclusion reads the DEF's emission
-- (`input fzero`, so `0 <ᵇ 2`).  Nothing in the source connects the
-- two, so the row fails the moment the evaluator wraps an emission in
-- syntax of its own rather than forwarding the def's.  The gas is
-- padded well past what the def needs, so what the row reads is the
-- emitting branch and not an exhaustion the dry row already covers.
----------------------------------------------------------------------

gₚ : Gas
gₚ = gasPad 400 g0

tieSharedSlot : Confirms
  (subscribeInner-strat 2 gₚ mergeAllᵒ 7 κₚ 0 0 oₚ
     (sched-init eₚ slₚ) (st-init eₚ) refl)
tieSharedSlot = refl

----------------------------------------------------------------------
-- ROW 2 — THE DRY BRANCH.  DEGENERATE: at zero gas the subscribe
-- mints the instance and returns no values at all, so the conclusion
-- holds over an empty list.  It is here to pin that the exhausted
-- branch is not accidentally emitting.
----------------------------------------------------------------------

tieDry : Confirms
  (subscribeInner-strat 2 g0 mergeAllᵒ 7 κₚ 0 0 oₚ
     (sched-init eₚ slₚ) (st-init eₚ) refl)
tieDry = refl
