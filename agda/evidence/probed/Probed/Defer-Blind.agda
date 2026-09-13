-- A DEFER MOVES THE PAYLOAD BOUND OFF THE TERM AND ONTO THE SCHEDULE.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHAT THE FOUR INSTALL SITES LEAVE OVER.  A subscription writes a node
-- in exactly four places, and three of them read at most the subterm
-- they came from: a take's node is priced at zero, a flattener's is born
-- with an empty queue, and a fold's holds a SEED whose reading the fold
-- clause already folds in at a source delivering nothing.  So a frame
-- cannot write above what it was handed — which is why the store
-- conjunct has never been close to failing, and is a finding about the
-- write rather than about these two rows.  The fourth site is the
-- exception: a defer installs an EMPTY flattener node and puts its body
-- in the SCHEDULE, which no reading in this development reads.

-- WHAT THAT IS AND IS NOT.  It is NOT depth going missing.  The pending
-- body is delivered as an ARRIVAL, and the arrival's own frame
-- subscribes it under a fresh instant, so the four the body is worth is
-- charged in full at that later frame and the seeding rule the store
-- reading is written under is doing exactly what it says.  What moves is
-- WHERE THE ARRIVAL'S BOUND COMES FROM.  Every frame reached from a term
-- takes its payload bound from a subterm of that term, so the shelf's
-- premise is supplied by the syntax the frame descended through.  An
-- arrival off the schedule has no such term: the value it is handed was
-- put there by a frame that was charged one for it, and nothing relates
-- the two figures.

-- AND THE ARRIVAL SUPPLIES IT ITSELF, WHICH IS WHERE THESE ROWS STOP.
-- The obvious reading of the paragraph above is that a bound with no
-- term under it has to be CARRIED to the frame, and that reading is
-- wrong: what arrives is a VALUE rather than a name for one, so it can
-- be read where it lands and the figure does not have to survive the
-- journey.  `Probed.Arrival-Spend` runs this same gated ladder to its
-- arrival and sweeps the rank by hand — dry at nought through four,
-- green at five, against a term reading one and a payload reading four —
-- so the quantity is the payload's and the code already computes it at
-- the only place it is wanted.  These two rows say what the FRAME is
-- charged; they say nothing about what the arrival is owed, and it was
-- the arrival that owed nothing.

-- AND THE ROWS ARE GREEN, WHICH IS THE POINT RATHER THAN A CAVEAT.  A
-- refutation would say the statement is false; these say it is TRUE at
-- a point where it is measuring something the run will be charged for
-- somewhere else, which no refutation can say and which is what makes
-- the arrival the place to look.  The separation is in the BOUNDS
-- rather than in the conjuncts:
-- the same body reads four at both points, and the frame that meets it
-- through a gate is held to one where the frame that meets it openly is
-- held to four.
--
-- SO BOTH ROWS ARE DEGENERATE IN THEIR CONJUNCTS AND LOAD-BEARING IN
-- THEIR BOUNDS, and saying so is what keeps them worth anything.  A
-- source emitting one inner returns nothing and installs nothing that
-- either reading reaches, so the payload out and both store figures come
-- back nought at BOTH points: neither conjunct could have failed here,
-- and nothing about the two of them is being claimed.  What could have
-- failed is the pair of pinned readings, and they are what carries the
-- finding — had the gate's reading tracked its body, the two bounds
-- would have come back equal and there would be no blindness to report.
--
-- TARGET: thru-outer-frame-carried @2de90d
module Probed.Defer-Blind where

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs;
  ofᵉ; mergeAllᵉ; deferᵉ; strmᵗ; nat̂)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; subscribeE;
  rootWitness; rootTri; root; _↠_; sched-init; st-init; mintNode;
  thru-outer; mergeAllᵒ; splitBurst; stepFrame; stHop)
open import Verify-Rank-Sufficient.Carried using (valsHop)
open import Verify-Rank-Sufficient.Push-Carried
  using (thru-outer-frame-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FRAME'S OWN POINT, assembled as the flattener arm assembles it:
-- the outer is SUBSCRIBED under the frame and the frame is handed what
-- the burst hands it.  Nothing is constructed by hand here — the store
-- the conjunct is comparing is the one the run left.
--
-- The rows themselves cannot live here: the decision procedure needs
-- closed numerals, and nothing under a parameter reduces.
----------------------------------------------------------------------

module Ap {n} {Γ : Ctx n} (ins : Slots Γ) (prog : Closed Γ (obs natᵗ))
          (src : Closed Γ (obs (obs natᵗ))) where

  ψ : Fin n → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri prog ins)
  ac = rootWitness prog ins

  nid : NodeId
  nid = proj₁ (mintNode (sched-init prog ins))

  r : Stream Γ (obs (obs natᵗ)) × Sched Γ × EvalSt prog
  r = subscribeE ac src (thru-outer mergeAllᵒ nid ↠ root) 0 0
        (proj₂ (mintNode (sched-init prog ins))) (st-init prog)

  sp : List (Val Γ (obs (obs natᵗ)))
     × List (InstEvent (Val Γ (obs natᵗ))) × Bool
  sp = splitBurst (proj₁ r)

  vals : List (Val Γ (obs (obs natᵗ)))
  vals = proj₁ sp

  fin : Bool
  fin = proj₂ (proj₂ sp)

  sd : Sched Γ
  sd = proj₁ (proj₂ r)

  st : EvalSt prog
  st = proj₂ (proj₂ r)

  sf : List (Val Γ (obs natᵗ)) × List (InstEvent (Val Γ (obs natᵗ)))
     × Bool × Sched Γ × EvalSt prog
  sf = stepFrame ac 0 0 (thru-outer mergeAllᵒ nid) root vals fin sd st

  bound : ℕ
  bound = depthᵉ ψ src

  stIn : ℕ
  stIn = stHop ψ st

  -- the SMALLEST store bound the statement admits at this point
  Rst : ℕ
  Rst = suc bound ⊔ stIn

  -- radix 1000, low digit first: what the frame was handed, the bound
  -- the payload is held to, what it gave back, what the store read going
  -- in, what it reads coming out, and the bound the store half is held
  -- to
  packed : ℕ
  packed = valsHop ψ (obs (obs natᵗ)) vals
         + 1000 * bound
         + 1000000 * valsHop ψ (obs natᵗ) (proj₁ sf)
         + 1000000000 * stIn
         + 1000000000000 * stHop ψ (proj₂ (proj₂ (proj₂ (proj₂ sf))))
         + 1000000000000000 * Rst

----------------------------------------------------------------------
-- THE CLOSED CONTEXT, where the reading of an input cannot enter and
-- every figure is the term's own.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE BODY, at four.  Each layer is one flattening, which is the one
-- clause of the reading that takes a successor, so the ladder's readings
-- are nought through four and nothing else about them differs.
----------------------------------------------------------------------

b0 b1 b2 b3 b4 : Closed Γ₀ (obs natᵗ)
b0 = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])
b1 = ofᵉ (strmᵗ (mergeAllᵉ nothing b0) ∷ [])
b2 = ofᵉ (strmᵗ (mergeAllᵉ nothing b1) ∷ [])
b3 = ofᵉ (strmᵗ (mergeAllᵉ nothing b2) ∷ [])
b4 = ofᵉ (strmᵗ (mergeAllᵉ nothing b3) ∷ [])

----------------------------------------------------------------------
-- THE TWO SOURCES.  Both emit ONE inner and differ in nothing else: the
-- control emits the body itself, the deferred one emits the same body
-- behind a gate.  Everything the frame can see is the same at both; what
-- the run is holding afterwards is not.
----------------------------------------------------------------------

srcOpen : Closed Γ₀ (obs (obs natᵗ))
srcOpen = ofᵉ (strmᵗ b4 ∷ [])

gated4 : Closed Γ₀ (obs natᵗ)
gated4 = deferᵉ b4

srcGated : Closed Γ₀ (obs (obs natᵗ))
srcGated = ofᵉ (strmᵗ gated4 ∷ [])

module Open  = Ap ins₀ (mergeAllᵉ nothing srcOpen)  srcOpen
module Gated = Ap ins₀ (mergeAllᵉ nothing srcGated) srcGated

----------------------------------------------------------------------
-- THE READINGS THAT MAKE THE SEPARATION.  The gate's own reading is a
-- constant: the body under it reads four and the gated value reads one,
-- so the four is a quantity THIS frame is never charged for.
----------------------------------------------------------------------

body-reads : depthᵉ (slotRd ins₀) b4 ≡ 4
body-reads = refl

gate-reads : depthᵉ (slotRd ins₀) gated4 ≡ 1
gate-reads = refl

----------------------------------------------------------------------
-- BOTH POINTS PINNED.  Read low digit first at radix 1000: handed,
-- payload bound, returned, store in, store out, store bound.
----------------------------------------------------------------------

open-is : Open.packed ≡ 5000000000004004
open-is = refl

gated-is : Gated.packed ≡ 2000000000001001
gated-is = refl

----------------------------------------------------------------------
-- THE TARGET, AT BOTH POINTS.  The premise and both hypotheses are
-- DECIDED rather than assumed, and the store bound is the least one they
-- admit — so the gated row passing is the statement holding tightly at
-- a point where the bound it pins is a quarter of what the run goes on
-- to carry.
----------------------------------------------------------------------

openRow : Confirms (thru-outer-frame-carried Open.ac 0 0 mergeAllᵒ Open.nid
  root Open.ψ Open.bound Open.Rst Below Open.vals Open.fin Open.sd Open.st
  Below Below)
openRow = Below , Below

gatedRow : Confirms (thru-outer-frame-carried Gated.ac 0 0 mergeAllᵒ
  Gated.nid root Gated.ψ Gated.bound Gated.Rst Below Gated.vals Gated.fin
  Gated.sd Gated.st Below Below)
gatedRow = Below , Below
