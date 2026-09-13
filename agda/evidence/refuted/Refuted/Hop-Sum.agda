-- THE FIT IS FALSE AT THE DOOR, AND WHAT KILLS IT IS THE CHAIN'S OWN
-- ADDITION.
--
-- The chain measure reads each frame's template at the EMPTY
-- environment and ADDS the readings along the path; the expression
-- measure reads a template against its SOURCE and JOINS.  Those two
-- agree only while every frame's output reaches the next one.  A
-- template that DISCARDS its argument is where they part: the
-- expression measure sees the discard, because the source's reading is
-- what it plugs in and a body that never mentions the bound variable
-- never reads it, while the chain has already forgotten which frame fed
-- which and charges both.
--
-- SO THE WITNESS IS TWO MAPS, NEITHER OF WHICH LOOKS AT WHAT IT IS
-- GIVEN, under one flattener.  Each template is an observable of hop
-- reading one, so the chain charges one, one and the flattener's edge:
-- three.  The expression measure joins the two ones and adds the same
-- edge: two.  The registration is the SLOT's own, installed by the
-- subscribe frame the statement is about, so nothing here is
-- constructed — the state is the one `subscribeE` returns at the door.
--
-- WHAT THIS KILLS.  Not the reading, and not the top-line claim: the
-- run this program performs enters exactly one inner per value and the
-- expression measure's two is the honest figure.  What is dead is the
-- PREMISE, and with it the only route currently assembling the drain's
-- dry-freedom — a premise false at the door cannot be established at
-- the door, and no strengthening of the drain's induction reaches a
-- hypothesis nothing can supply.
--
-- AND THE REPAIR IS ON THE LEFT.  The chain measure is the side that is
-- wrong: a frame's output is read by the NEXT frame, so a path prices a
-- reading THREADED through its frames, joining as the expression
-- measure joins, and only the flattener's edge is additive.  Charging
-- each template at the empty environment is what the header of the
-- statement defends as making the payload's cancellation exact; the
-- cancellation is exact and the addition beside it is not.
module Refuted.Hop-Sum where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs;
  ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ; nat̂; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; ε; rdᵗ; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner; thru-outer; Sched; EvalSt;
  RegRow; subscribeE; rootWitness; sched-init; st-init)

----------------------------------------------------------------------
-- THE MEASURE, WRITTEN OUT RATHER THAN IMPORTED.  This is the summing
-- form, which is the thing refuted; a repair that threads a reading
-- through the frames instead would shrink the imported measure and
-- leave the crossing below a quiet equality.  Localised, the witness
-- goes on saying which form is false whatever `src` now carries.
----------------------------------------------------------------------

chainDepthSum : ∀ {n} {Γ : Ctx n} {lo s t} (ψ : Fin n → Rd₃) →
                Path Γ lo s t → ℕ
chainDepthSum ψ root                    = 0
chainDepthSum ψ (share-sink i _)        = 0
chainDepthSum ψ (map-f fn ↠ κ)          = proj₂ (rdᵗ ψ ε fn) + chainDepthSum ψ κ
chainDepthSum ψ (scan-f fn nid ↠ κ)     = proj₂ (rdᵗ ψ ε fn) + chainDepthSum ψ κ
chainDepthSum ψ (take-f nid ↠ κ)        = chainDepthSum ψ κ
chainDepthSum ψ (from-inner op a i ↠ κ) = chainDepthSum ψ κ
chainDepthSum ψ (thru-outer op nid ↠ κ) = suc (chainDepthSum ψ κ)

regsDepthSum : ∀ {n} {Γ : Ctx n} {t} (ψ : Fin n → Rd₃) →
               List (RegRow Γ t) → ℕ
regsDepthSum ψ []                  = 0
regsDepthSum ψ ((rid , src , c) ∷ r) =
  chainDepthSum ψ (proj₂ c) ⊔ regsDepthSum ψ r

HopFitsSum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
             Sched Γ → EvalSt e → Set
HopFitsSum {e = e} sched st =
  let ψ = slotRd (Sched.slots sched) in
  regsDepthSum ψ (EvalSt.registry st) ≤ depthᵉ ψ e

EntryHopFits : Set
EntryHopFits = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let ent = subscribeE {lo = n} (rootWitness e ins) e root 0 0
              (sched-init e ins) (st-init e)
  in HopFitsSum (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))

----------------------------------------------------------------------
-- THE PROGRAM.  Two maps whose templates ignore the value handed to
-- them, each returning an observable one flattener deep, under a third
-- flattener.  The slot is scripted with three late values, so the
-- registration installed at the door is still live when the door
-- closes — a source that completes inside its own subscribe frame would
-- leave an EMPTY registry and a comparison that could not have failed.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insMany : Slots Γ₁
insMany zero = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ after 0 , 7 ∷ []))

-- hop reading one, and the bound variable does not occur
f₁ : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
f₁ = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])))

f₂ : Fn Γ₁ [] [] [] (obs natᵗ) (obs natᵗ)
f₂ = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 2 ∷ [])) ∷ [])))

twoMaps : Closed Γ₁ natᵗ
twoMaps = mergeAllᵉ nothing (mapᵉ f₂ (mapᵉ f₁ (input zero)))

entry : Sched Γ₁ × EvalSt twoMaps
entry =
  let (_ , sched , st) =
        subscribeE {lo = 1} (rootWitness twoMaps insMany) twoMaps root 0 0
          (sched-init twoMaps insMany) (st-init twoMaps)
  in sched , st

ψ₁ : Fin 1 → Rd₃
ψ₁ = slotRd (Sched.slots (proj₁ entry))

----------------------------------------------------------------------
-- THE CROSSING, PINNED ON BOTH SIDES.  Either figure moving fails a row
-- by name rather than turning the witness into a quiet equality — which
-- is the one way a refutation of an inequality dies without saying so.
----------------------------------------------------------------------

carried : ℕ
carried = regsDepthSum ψ₁ (EvalSt.registry (proj₂ entry))

term : ℕ
term = depthᵉ ψ₁ twoMaps

carried-is : carried ≡ 3
carried-is = refl

term-is : term ≡ 2
term-is = refl

entry-hop-fits-false : EntryHopFits → ⊥
entry-hop-fits-false h with h twoMaps insMany
... | s≤s (s≤s ())
