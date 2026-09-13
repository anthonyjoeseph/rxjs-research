-- THE DOOR'S DEBT AT A GATE IS ONE, AND IT STAYS ONE HOWEVER DEEPLY
-- THE GATES NEST.  That is the measurement the reading's defer clause
-- is calibrated against, and it is the reason a CONSTANT clause is
-- enough where a recursive one would have cost the descent its μ edge.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THE FIGURE DOES NOT CLIMB.  A door subscribes the OUTER gate
-- only.  The body is not walked: it becomes the pending payload of a
-- fresh source, scheduled one tick out, and it is subscribed later at
-- its own door and off its own reading.  So the registry a door hands
-- back holds ONE chain of ONE hop whether the program is one gate or
-- three, and the rows below pin that at one, two and three — the axis
-- along which a term-blind cost would have been expected to grow, and
-- the one place a constant clause could have been refuted.
--
-- THESE ROWS ARE TIGHT, WHICH IS WHAT MAKES THEM WORTH TAKING.  Both
-- sides read ONE, so the fit lands on the nose rather than with a
-- margin: any reading that gave the gate zero fails here, and so does
-- any that gave it two.  The literal families in `Probed.Entry-Fit`
-- cannot be made tight at any length, because their axis moves the term
-- side and leaves the registry where it was; this shape moves neither.
--
-- AND THE ASSEMBLY'S OWN CONCLUSION IS INSTANTIATED, NOT ONLY THE
-- LEAF.  `hasDry` over a real run is what the fit is ultimately for, it
-- computes exactly as the leaf does, and it is the quantity that was
-- observed wrong at this very shape — so it is read back here at each
-- of the three depths and at a fuel eight times what the door needs.
--
-- THE BOUNDARY: GATES OVER A LITERAL, AND NO RECURSION.  What these
-- rows cover is the gate's cost AT ITS OWN DOOR.  A gate under a μ is
-- where the reading's invariance is load-bearing rather than merely
-- preserved, and that axis is `Probed.Entry-Fit`'s fold rows, not
-- these; a gate whose body is itself scheduled late is covered by
-- nothing here.  The slot exists only because the statement quantifies
-- a telescope — no row reads it, which is the point: the figure owes
-- nothing to what a source delivers.
--
-- TARGET: entry-hop-fits @9f8beb
module Probed.Gate-Constant where

open import Data.Bool using (false)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; natᵗ; ofᵉ; deferᵉ; nat̂)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; rootWitness;
  root; sched-init; st-init; evaluate; hasDry)
open import Verify-Rank-Sufficient using (entry-hop-fits)
open import Verify-Rank-Sufficient.Hop using (regsDepth)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE PROGRAMS.  Gates over a one-element literal, nested one, two and
-- three deep.  Nothing else: no slot is read, no template discards
-- anything, no cascade runs before the figures are taken.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

one : Closed Γ₁ natᵗ
one = ofᵉ (nat̂ 1 ∷ [])

gate₁ gate₂ gate₃ : Closed Γ₁ natᵗ
gate₁ = deferᵉ one
gate₂ = deferᵉ (deferᵉ one)
gate₃ = deferᵉ (deferᵉ (deferᵉ one))

door : (e : Closed Γ₁ natᵗ) → Sched Γ₁ × EvalSt e
door e =
  let (_ , sched , st) =
        subscribeE (rootWitness e insLate) e root 0 0 (sched-init e insLate)
          (st-init e)
  in sched , st

----------------------------------------------------------------------
-- BOTH SIDES PINNED SEPARATELY AT EVERY DEPTH, so a figure that moved
-- would fail at the pin rather than quietly agreeing under the `≤`.
-- Every one is LOAD-BEARING: the carried column is what a door that
-- walked its body would have grown, and the term column is what a
-- reading that left the gate free would have read as ZERO.
----------------------------------------------------------------------

carried : Closed Γ₁ natᵗ → ℕ
carried e = regsDepth (slotRd (Sched.slots (proj₁ (door e))))
                      (EvalSt.registry (proj₂ (door e)))

term : Closed Γ₁ natᵗ → ℕ
term e = depthᵉ (slotRd (Sched.slots (proj₁ (door e)))) e

carried₁ : carried gate₁ ≡ 1
carried₁ = refl

carried₂ : carried gate₂ ≡ 1
carried₂ = refl

carried₃ : carried gate₃ ≡ 1
carried₃ = refl

term₁ : term gate₁ ≡ 1
term₁ = refl

term₂ : term gate₂ ≡ 1
term₂ = refl

term₃ : term gate₃ ≡ 1
term₃ = refl

fitGate₁ : Confirms (entry-hop-fits gate₁ insLate)
fitGate₁ = Below

fitGate₂ : Confirms (entry-hop-fits gate₂ insLate)
fitGate₂ = Below

fitGate₃ : Confirms (entry-hop-fits gate₃ insLate)
fitGate₃ = Below

----------------------------------------------------------------------
-- AND THE CONCLUSION THE FIT IS FOR, READ BACK OFF A REAL RUN.  A gate
-- whose rank was seeded at zero took the zero clause and closed dry;
-- these are the same three programs at eight times the fuel the door
-- needs, so a marker surviving here could not be a drain budget.
----------------------------------------------------------------------

dry₁ : hasDry (evaluate 50 gate₁ insLate) ≡ false
dry₁ = refl

dry₂ : hasDry (evaluate 50 gate₂ insLate) ≡ false
dry₂ = refl

dry₃ : hasDry (evaluate 50 gate₃ insLate) ≡ false
dry₃ = refl
