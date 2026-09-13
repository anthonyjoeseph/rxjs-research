------------------------------------------------------------------
-- THE DRAIN'S PREMISE, STATED PER TEMPLATE.  What a registered chain
-- owes is not a READING of itself against anything the run holds — it
-- is the shelf's own obligation at each frame the chain is built from,
-- taken against the payload that frame is handed.
--
-- THE DIFFERENCE FROM A READING IS THE DIRECTION OF THE COMPARISON,
-- and it is the whole of why this shape is available where six others
-- were not.  A reading prices the chain and then needs a right side to
-- price it against, and every candidate right side is a quantity the
-- run holds: the term's, the registry's, the arrival's seed, the
-- chains one arrival reaches.  Here there is no right side.  Each
-- frame carries what it was handed to what the frame below it is
-- granted, the bounds are THREADED rather than compared, and the only
-- place a number meets another number is at a flattener, where the
-- shelf's own obligation already says what is owed.
--
-- SO THE PREMISE NAMES NO STATE QUANTITY, AND THAT IS DELIBERATE.  It
-- is a conjunction of obligations, one per template the run installed,
-- each quantified over every state meeting the bounds rather than
-- taken at the state in hand.  A quantity the state carries forward
-- cannot repair it and cannot break it, which is what the refutation
-- standing over the leaf that consumes this says from the other side.
--
-- WHAT IT COSTS, AND IT IS PAID ON THE HYPOTHESIS SIDE.  A ∀-statement
-- is not decidable at a numeral, so a premise of this shape cannot be
-- discharged by `refl` at a concrete program the way a reading could.
-- The leaf consuming it is therefore unprobeable in its HYPOTHESES,
-- its conclusion computing exactly as before.  What is bought back is
-- larger than what is spent: the obligations are the shelf's own, so
-- the premise is DERIVABLE from statements this development already
-- carries rather than granted, and a fit that used to be asserted at
-- the door becomes one the typechecker holds.
--
-- THE Σ IS NOT UPWARD-CLOSED, WHICH IS THE CHECK THIS SHAPE OWES.
-- `through` existentially threads the bound handed to the tail, and
-- enlarging it does weaken the frame's own conjunct — but it
-- STRENGTHENS every obligation below, since a flattener's is stated
-- against what it is handed.  A path with no flattener under it is
-- upward-closed and cannot go dry either, so the witness is pinned
-- exactly where dryness is reachable.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Fits where

open import Data.Bool using (Bool; false)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Fuel; Tick; Id)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵉ; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Frame; Path; root; share-sink; _↠_; Sched;
  EvalSt; Arrival; arrTy; arrVal; arrTick; arrivalWitness; chainsOf;
  sched-next; cascade; stepFrame; dispatchShare; dryEvent; hasDry; stHop)
open import Verify-Rank-Sufficient.Carried using (valsHop)
open import Verify-Rank-Sufficient.Push-Carried using (FrameCarries)

----------------------------------------------------------------------
-- A FRAME THAT CANNOT GO DRY UNDER A BOUND.  `FrameDry` is the
-- unconditional form, and it is exactly what the three quiet frames
-- satisfy; a flattener cannot satisfy it, because a spent rank is
-- reachable at a large enough payload.  This is the conditioned form
-- the flattener needs, and it collapses to the unconditional one
-- wherever the bounds are not read.
----------------------------------------------------------------------

FrameDryUnder : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t →
  (Fin n → Rd₃) → ℕ → ℕ → Set
FrameDryUnder {Γ = Γ} {e = e} {s = s} ac id now f κ ψ Rin Rst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    valsHop ψ s vals ≤ Rin → stHop ψ st ≤ Rst →
    any dryEvent (proj₁ (proj₂ (stepFrame ac id now f κ vals fin sd st)))
      ≡ false

----------------------------------------------------------------------
-- AND THE SAME AT A SHARE BOUNDARY, WHICH IS A TEMPLATE TOO.  A sink
-- ends its own chain and hands the values to every chain registered on
-- the share, so the obligation there is over the FAN-OUT rather than
-- over a frame: nothing else in the path can reach those chains, and a
-- trivially-true sink clause would make the composition below false at
-- the first diamond.
----------------------------------------------------------------------

ShareDryUnder : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} →
  Acc _≺_ τ → Id → Tick → (i : Fin n) → (Fin n → Rd₃) → ℕ → ℕ → Set
ShareDryUnder {Γ = Γ} {e = e} ac id now i ψ Rin Rst =
  ∀ (gas : ℕ) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sd : Sched Γ) (st : EvalSt e) →
    valsHop ψ (lookup Γ i) vals ≤ Rin → stHop ψ st ≤ Rst →
    hasDry (proj₁ (dispatchShare ac gas id now i vals fin sd st)) ≡ false

----------------------------------------------------------------------
-- ONE CHAIN'S OBLIGATION: the shelf at every template, threaded.
--
-- THREADED AND NOT SUMMED, AND THE ALTERNATIVE IS DEAD RATHER THAN
-- MERELY UNCHOSEN.  `through` hands the tail the bound the frame above
-- it produced, so a template that DISCARDS its argument costs nothing
-- below it.  Adding each frame's reading instead charges the discard,
-- and the witness below stands at two maps neither of which looks at
-- what it is given.
--
-- REFUTED: `Refuted.Hop-Sum` — the summing form, at the door, where it
--   reads three against the expression measure's two.  It kills the
--   MEASURE and not the claim: the run that program performs enters one
--   inner per value and two is the honest figure.  The witness is named
--   here because a return to the summing shape puts the crossing
--   straight back, and nothing in the type would say so.
----------------------------------------------------------------------

data PathFits {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
       (ac : Acc _≺_ τ) (id : Id) (now : Tick) (ψ : Fin n → Rd₃) (Rst : ℕ)
       : ∀ {u} → Path Γ u t → ℕ → Set where

  at-root : ∀ {R} → PathFits {e = e} ac id now ψ Rst root R

  at-sink : ∀ {i R} → ShareDryUnder {e = e} ac id now i ψ R Rst →
            PathFits {e = e} ac id now ψ Rst (share-sink i) R

  through : ∀ {s u R Rv} {f : Frame Γ s u} {κ : Path Γ u t} →
            FrameCarries {e = e} ac id now f κ ψ R Rv Rst →
            FrameDryUnder {e = e} ac id now f κ ψ R Rst →
            PathFits {e = e} ac id now ψ Rst κ Rv →
            PathFits {e = e} ac id now ψ Rst (f ↠ κ) R

----------------------------------------------------------------------
-- THE RANK AN ARRIVAL ENTERS AT, spelled once.  It is the middle
-- component of the triple `arrivalWitness` is taken at, and it is the
-- store bound every obligation of that arrival is stated against —
-- which is what makes the flattener's own `suc Rin ≤ Rst` available
-- whenever the payload reads strictly under it.
--
-- AND THE RE-SEED IS WHY THE ALLOWANCE IS NOT AN AXIS OF RISK, which is
-- a measurement rather than an argument.  Instantiating one run at six
-- allowances, at a fold whose source is a recursion, holds the term's
-- reading still while what the run hands out reads the allowance plus
-- one — one hop per arrival, overtaking any reading of the program by
-- the third.  A rank read off the program alone therefore does not
-- bound a drain at all; this one is re-minted per arrival at exactly
-- that rate, one for one, which is why it is taken here and not once at
-- the door.
--
-- NOR IS DELIVERY COUNT, AND THAT ONE RUNS THE OTHER WAY.  Lengthening
-- a burst from six deliveries under one arrival to twenty-four takes
-- the TERM reading from 19 to 73 and leaves the registry at two,
-- because a fold reads its source's delivery count as the number of
-- times it refolds.  So the parameter that defines that region inflates
-- the bound rather than the quantity bounded: whatever outruns a
-- reading the term fixes, it is not how many times one cascade
-- delivers.
----------------------------------------------------------------------

arrivalRank : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Arrival Γ → Sched Γ → EvalSt e → ℕ
arrivalRank {e = e} a sched st =
  let ψ = slotRd (Sched.slots sched) in
  depthᵉ ψ e + (depthᵛ ψ (arrTy a) (arrVal a) ⊔ stHop ψ st)

----------------------------------------------------------------------
-- EVERY CHAIN THE ARRIVAL REACHES, at the payload it actually carries.
----------------------------------------------------------------------

ArrivalFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Arrival Γ → Sched Γ → EvalSt e → Set
ArrivalFits {e = e} id a sched st =
  let ψ = slotRd (Sched.slots sched) in
  All (λ rp → PathFits {e = e} (arrivalWitness a sched st) id (arrTick a) ψ
                (arrivalRank a sched st) (proj₂ rp)
                (depthᵛ ψ (arrTy a) (arrVal a)))
      (chainsOf a st)

----------------------------------------------------------------------
-- AND THE PREMISE THE DRAIN'S OWN RECURSION IS STATED OVER, WHICH IS
-- HEREDITARY AND HAS TO BE.  A premise about the NEXT arrival alone
-- would be a strictly stronger statement than the run supports: the
-- conclusion is about every arrival the allowance serves, and nothing
-- says a chain fitting the payload reaching it today fits the one
-- reaching it after a cascade has rewritten the registry.  So this
-- recurses on the allowance exactly as `drain` does, one conjunct per
-- arrival, taken at the very pair that arrival's cascade returns.
--
-- WHICH IS WHY PRESERVATION IS NOT A LEAF HERE.  The shape the six
-- refuted readings all needed was a fit PRESERVED across a cascade,
-- and each died proving it.  Recursing instead asks for the fit at
-- each arrival separately and asks nothing about the step between
-- them, so what a cascade does to the registry is the door's problem
-- and not this statement's.
----------------------------------------------------------------------

DrainFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Fuel → Id → Sched Γ → EvalSt e → Set
DrainFits zero    id sched st = ⊤
DrainFits (suc k) id sched st with sched-next sched
... | inj₁ _            = ⊤
... | inj₂ (a , sched′) =
      ArrivalFits id a sched′ st
      × DrainFits k (suc id) (proj₁ (proj₂ (cascade a id sched′ st)))
                             (proj₂ (proj₂ (cascade a id sched′ st)))
