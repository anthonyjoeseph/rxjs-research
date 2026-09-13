-- THE FIT IS STILL FALSE AT THE DOOR, AND THE SECOND WITNESS IS ONE
-- CONSTRUCTOR LONG.
--
-- `deferᵉ` reads ZERO.  The expression measure gives a defer the same
-- reading as an empty stream — no count, no element, no hop — and that
-- is not an oversight the clause fell into: it is what makes the
-- reading INVARIANT under unfolding, since a recursion's variable is
-- reachable only under a defer and an unfolding puts the whole μ there.
-- A recursive clause would read a defer's body, and a body that is the
-- μ itself reads more than the redex did.
--
-- BUT THE DOOR REGISTERS A FLATTENER FOR IT.  A defer IS a mergeAll of
-- a one-shot scheduled outer — the evaluator says so where it builds
-- one — so subscribing `deferᵉ b` mints a node, schedules `b` as the
-- pending payload of a fresh source, and registers `thru-outer ↠ κ`.
-- The chain measure charges that frame the hop it will really perform:
-- the arrival's own thru-outer subscribes the body one level down.
--
-- SO THE PROGRAM IS `deferᵉ (ofᵉ (nat̂ 1 ∷ []))` AND NOTHING ELSE.  No
-- slot is read, no template discards anything, no cascade runs.  The
-- registry the door returns holds one chain of hop one and the reading
-- of the program is zero, so the fit at the door is `1 ≤ 0`.
--
-- WHAT THIS KILLS, AND WHAT IT DOES NOT.  It does not touch the
-- threaded chain measure, which is the repair its sibling refutation
-- forced and which prices this frame honestly — the run does perform
-- the hop.  It does not touch the top-line claim either: one hop is
-- what this program costs and the machine has the tick to spend it in.
-- What is dead is the fit AS STATED, for a second and independent
-- reason: the two sides are one arithmetic only where the reading and
-- the door agree about what a constructor DOES, and at this one they do
-- not.
--
-- AND THE REPAIR IS NOT AVAILABLE ON EITHER SIDE ALONE, which is why
-- this is worth a file.  Charge the defer in the reading and the μ edge
-- loses its invariance, which the descent is built on.  Stop charging
-- the frame in the chain measure and the registry under-reads a hop the
-- run really takes, which is the shape the drain leaf dies of.  The
-- quantity a defer is owed is a SCHEDULE tick rather than a reading,
-- and neither side of this comparison is denominated in ticks.
module Refuted.Defer-Hop where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Fuel; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; natᵗ; ofᵉ; deferᵉ; nat̂)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; rootWitness;
  root; sched-init; st-init; evaluate; hasDry)
open import Verify-Rank-Sufficient.Hop using (regsDepth)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT SO THE REFUTATION IS A CLOSED CLAIM.  Both
-- MEASURES are imported rather than copied, which is the opposite
-- choice from the sibling and made for the same reason: there the
-- repair was to the measure, so localising it kept the witness alive
-- past its own fix; here the measures are the two things believed
-- right and the disagreement between them is the finding.  A repair to
-- either takes this file red, which is the day it has been answered.
----------------------------------------------------------------------

EntryHopFits : Set
EntryHopFits = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let ent = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
              (st-init e)
      ψ   = slotRd (Sched.slots (proj₁ (proj₂ ent)))
  in regsDepth ψ (EvalSt.registry (proj₂ (proj₂ ent))) ≤ depthᵉ ψ e

----------------------------------------------------------------------
-- THE PROGRAM.  A defer over a one-element literal.  The slot exists
-- only because the statement quantifies a telescope; nothing here
-- reads it, which is the point — the crossing owes nothing to what a
-- source delivers, so no scripting choice can be the thing that made
-- it.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

oneDefer : Closed Γ₁ natᵗ
oneDefer = deferᵉ (ofᵉ (nat̂ 1 ∷ []))

entry : Sched Γ₁ × EvalSt oneDefer
entry =
  let (_ , sched , st) =
        subscribeE (rootWitness oneDefer insLate) oneDefer root 0 0
          (sched-init oneDefer insLate) (st-init oneDefer)
  in sched , st

ψ₁ : Fin 1 → Rd₃
ψ₁ = slotRd (Sched.slots (proj₁ entry))

----------------------------------------------------------------------
-- THE CROSSING, PINNED ON BOTH SIDES.  The right side is ZERO, so this
-- is the one crossing that cannot be repaired by enlarging it a little:
-- any reading that keeps a defer free stays here however the rest of
-- the measure moves.
----------------------------------------------------------------------

carried : ℕ
carried = regsDepth ψ₁ (EvalSt.registry (proj₂ entry))

term : ℕ
term = depthᵉ ψ₁ oneDefer

deferCarried-is : carried ≡ 1
deferCarried-is = refl

deferTerm-is : term ≡ 0
deferTerm-is = refl

entry-hop-fits-defer-false : EntryHopFits → ⊥
entry-hop-fits-defer-false h with h oneDefer insLate
... | ()

----------------------------------------------------------------------
-- AND THE TIER'S TOP LINE GOES WITH IT, WHICH IS THE PART THAT IS NOT
-- ABOUT A MEASURE AT ALL.  The premise above is what the drain's leaf
-- asks for, so a false premise would ordinarily kill a route and leave
-- the claim standing.  Here the machine agrees with the refutation: the
-- rank an arrival is seeded at is the READING, the reading gives this
-- program zero, and the frame the door registered has a hop to spend —
-- so `subscribeInner` takes its ZERO clause and emits the dried close.
-- The marker is really there, at the fuel the probe tree runs at and at
-- eight times it, so no drain budget is what produced it.
--
-- THE STATEMENT IS WRITTEN OUT rather than the definition imported, and
-- deliberately: `rank-sufficient` has a BODY resting on the postulate
-- above, so importing it would put an inhabitant of ⊥ in this tree and
-- every row anywhere would then be suspect.  What is refuted is the
-- claim it makes.
--
-- WHAT THIS SAYS ABOUT THE REPAIR.  A rank seeded off the PROGRAM
-- cannot cover a frame the program does not spell, and the gate is the
-- one constructor that installs such a frame at subscribe time.  The
-- quantity that does cover it is already in this file's other half —
-- the chain's own remaining hop content — so the candidate is to seed
-- an arrival off the CHAIN it is about to walk rather than off the
-- term, which would make the fit definitional instead of a leaf.  That
-- is an evaluator change and it is not attempted here.
----------------------------------------------------------------------

RankSufficient : Set
RankSufficient = ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
                   (ins : Slots Γ) → hasDry (evaluate fuel e ins) ≡ false

deferDry-6 : hasDry (evaluate 6 oneDefer insLate) ≡ true
deferDry-6 = refl

deferDry-50 : hasDry (evaluate 50 oneDefer insLate) ≡ true
deferDry-50 = refl

rank-sufficient-defer-false : RankSufficient → ⊥
rank-sufficient-defer-false h with trans (sym (h 6 oneDefer insLate)) deferDry-6
... | ()
