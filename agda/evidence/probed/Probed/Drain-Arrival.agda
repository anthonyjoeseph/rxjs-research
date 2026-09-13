-- MANY DELIVERIES UNDER ONE ARRIVAL, CARRIED PAST THE ARRIVAL — the one
-- region both drain receipts stop at, from opposite sides.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THIS REGION AND NOT ANOTHER.  One sibling reaches a burst that
-- delivers many times and reads the fit at the DOOR; the other carries
-- the fit through cascades the loop itself ran, but over programs where
-- exactly one delivery lands per arrival.  Neither covers their
-- intersection, and the intersection is the shape a proof of the leaf
-- actually walks: the induction applies the statement at a state a
-- cascade produced, and a cascade is free to deliver as many times as
-- the frames inside it do.

-- WHAT IS DIFFERENT ABOUT THE SLOT.  A scripted source's async entries
-- are delta-encoded with a gap of `suc wait`, so two of its values can
-- never share a tick and one arrival is one value, always.  The many
-- deliveries have to come from the PROGRAM, and they do: each arriving
-- value is mapped to an observable the flattener above then subscribes,
-- so the fold underneath refolds once per element of that observable
-- while the schedule advances one arrival.  Giving the slot three values
-- rather than one is what leaves a live registration behind afterwards —
-- at a single late value the chain is torn down with it and the fit
-- after the arrival is satisfied by an EMPTY registry, which is the row
-- that could not have failed.

-- THE THIRD FAMILY IS THE SHARP ONE.  In the first two, the observable
-- each delivery subscribes is a literal: it completes inside the
-- cascade, so the registry never holds what the burst built.  `cascLive`
-- maps each arriving value to a flattener over six references to the
-- SLOT ITSELF, so every one of the six deliveries installs a
-- registration that is still live when the arrival is over — the burst
-- is carried in the state rather than spent in it.

-- WHAT THE ROWS SAY.  The fit holds at every reached state, and the
-- carried side does not MOVE: two, two, two at six deliveries per
-- arrival; two, two, two at twenty-four; three at all four states where
-- the deliveries stay live.  The registry is not idle underneath that —
-- the node counter climbs 2, 3, 4, 5 on the first family and the
-- registration counter 1, 7, 13 on the third — so a stepper that had
-- become a fixed point is ruled out separately from the reading.

-- AND THE FINDING IS WHICH SIDE THE REGION'S OWN AXIS MOVES.  Lengthening
-- the burst from six deliveries to twenty-four takes the TERM reading
-- from 19 to 73 and leaves the registry at two, because a fold reads its
-- source's delivery count as the number of times it refolds.  So the
-- parameter that defines this region — how many times one cascade can
-- deliver — inflates the bound rather than the quantity bounded, and the
-- margin widens in exactly the direction the boundary was written to
-- worry about.  Whatever can outrun a reading the term fixes, it is not
-- delivery count.

-- THE BOUNDARY, and the first half of it is forced.  NO ROW HERE IS
-- TIGHT: the loosest is two against seventy-three, and tightness is
-- unavailable in this region by construction, since the one parameter
-- that defines it is the one inflating the bound.  A tight row has to
-- hold the deliveries fixed and grow the registry instead, which is the
-- shape the sibling file reaches at the door.  Past that: three
-- arrivals, one slot, one flattening strategy, and the six-delivery
-- family's own third state reads a registry of ZERO — the source is
-- spent and the chain torn down — so that state is pinned rather than
-- claimed.
--
-- TARGET: drain-dry-free @0b82eb
module Probed.Drain-Arrival where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Closed; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; fstᵗ; varᵗ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Probed.Entry-Fit using (Γ₁; casc6; casc24)
open import Probed.Fit-Preserved
  using (FUEL; at; carriedAt; rankAt; mintAt; fitAt)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE SLOT THAT SURVIVES ITS OWN FIRST ARRIVAL.  Three late values,
-- each on its own tick by the delta encoding, so a cascade still has
-- somewhere to arrive from after the first one has run.
----------------------------------------------------------------------

insMany : Slots Γ₁
insMany zero = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ after 0 , 7 ∷ []))

-- The node counter, which is the non-vacuity witness on the family whose
-- deliveries do not register: it is minted per subscribed instance and
-- never reused, so it climbs across a cascade that subscribed anything.
nodeAt : ℕ → (e : Closed Γ₁ (obs natᵗ)) (ins : Slots Γ₁) → ℕ
nodeAt k e ins = Sched.nextNode (proj₁ (at k e ins))

----------------------------------------------------------------------
-- SIX DELIVERIES PER ARRIVAL.  The program is the sibling's own, run
-- against the surviving slot: each arriving value maps to a six-element
-- literal the flattener subscribes, so the fold refolds six times while
-- the schedule advances one arrival.
----------------------------------------------------------------------

_ : nodeAt 0 casc6 insMany ≡ 2        -- LOAD-BEARING
_ = refl

_ : nodeAt 1 casc6 insMany ≡ 3        -- LOAD-BEARING
_ = refl

_ : nodeAt 2 casc6 insMany ≡ 4        -- LOAD-BEARING
_ = refl

_ : nodeAt 3 casc6 insMany ≡ 5        -- LOAD-BEARING
_ = refl

_ : carriedAt 0 casc6 insMany ≡ 2     -- LOAD-BEARING
_ = refl

_ : carriedAt 1 casc6 insMany ≡ 2     -- LOAD-BEARING
_ = refl

_ : carriedAt 2 casc6 insMany ≡ 2     -- LOAD-BEARING
_ = refl

-- DEGENERATE, and pinned for exactly that reason: the source is spent by
-- here and the chain torn down, so the fit at this state is satisfied by
-- an empty registry and no fit row is claimed at it.
_ : carriedAt 3 casc6 insMany ≡ 0
_ = refl

_ : rankAt 0 casc6 insMany ≡ 19       -- LOAD-BEARING
_ = refl

daM6₁ : fitAt 1 casc6 insMany
daM6₁ = Below

daM6₂ : fitAt 2 casc6 insMany
daM6₂ = Below

----------------------------------------------------------------------
-- TWENTY-FOUR DELIVERIES PER ARRIVAL, which is the same family with the
-- literal lengthened — the one axis this region is defined by.  The
-- registry does not notice; the term reading nearly quadruples.
----------------------------------------------------------------------

_ : carriedAt 0 casc24 insMany ≡ 2    -- LOAD-BEARING
_ = refl

_ : carriedAt 1 casc24 insMany ≡ 2    -- LOAD-BEARING
_ = refl

_ : carriedAt 2 casc24 insMany ≡ 2    -- LOAD-BEARING
_ = refl

_ : rankAt 0 casc24 insMany ≡ 73      -- LOAD-BEARING
_ = refl

daM24₁ : fitAt 1 casc24 insMany
daM24₁ = Below

daM24₂ : fitAt 2 casc24 insMany
daM24₂ = Below

----------------------------------------------------------------------
-- AND THE ONE WHOSE DELIVERIES STAY LIVE.  Each arriving value maps to
-- a flattener over six references to the slot itself, so the six
-- subscriptions one cascade performs are all still registered when it
-- ends.  The registration counter is the witness here — 1, 7, 13 — and
-- the carried reading is flat across all of it.
----------------------------------------------------------------------

fold6 : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
fold6 = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

liveK : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
liveK = strmᵗ (mergeAllᵉ nothing (ofᵉ ( strmᵗ (input zero)
                                      ∷ strmᵗ (input zero)
                                      ∷ strmᵗ (input zero)
                                      ∷ strmᵗ (input zero)
                                      ∷ strmᵗ (input zero)
                                      ∷ strmᵗ (input zero) ∷ [])))

cascLive : Closed Γ₁ (obs natᵗ)
cascLive = scanᵉ fold6 (strmᵗ emptyᵉ)
  (mergeAllᵉ nothing (mapᵉ liveK (input zero)))

_ : mintAt 0 cascLive insMany ≡ 1     -- LOAD-BEARING
_ = refl

_ : mintAt 1 cascLive insMany ≡ 7     -- LOAD-BEARING
_ = refl

_ : mintAt 2 cascLive insMany ≡ 13    -- LOAD-BEARING
_ = refl

_ : nodeAt 1 cascLive insMany ≡ 10    -- LOAD-BEARING
_ = refl

_ : nodeAt 2 cascLive insMany ≡ 18    -- LOAD-BEARING
_ = refl

_ : carriedAt 0 cascLive insMany ≡ 3  -- LOAD-BEARING
_ = refl

_ : carriedAt 1 cascLive insMany ≡ 3  -- LOAD-BEARING
_ = refl

_ : carriedAt 2 cascLive insMany ≡ 3  -- LOAD-BEARING
_ = refl

_ : carriedAt 3 cascLive insMany ≡ 3  -- LOAD-BEARING
_ = refl

_ : rankAt 0 cascLive insMany ≡ 56    -- LOAD-BEARING
_ = refl

daL₁ : fitAt 1 cascLive insMany
daL₁ = Below

daL₂ : fitAt 2 cascLive insMany
daL₂ = Below

daL₃ : fitAt 3 cascLive insMany
daL₃ = Below

----------------------------------------------------------------------
-- THE ROW THE TARGET WRITES.  Everything above reads the fit; this one
-- spends it, at the state the six-delivery cascade produced, and its
-- type comes from `drain-dry-free` rather than from this file.
----------------------------------------------------------------------

daDrain : Confirms (drain-dry-free FUEL 2
            (proj₁ (at 1 casc6 insMany)) (proj₂ (at 1 casc6 insMany)) daM6₁)
daDrain = refl
