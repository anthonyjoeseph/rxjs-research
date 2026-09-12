------------------------------------------------------------------
-- THE FRAME'S PAYLOAD AXIS, AS A POTENTIAL RATHER THAN AS A GRANT.
--
-- A chain position used to be entered with one number every hypothesis
-- was stated under, and what the frame emitted had to stay under it.
-- That form is refuted at the arm that substitutes: the frame is
-- quantified over and named in none of the hypotheses, so the step
-- function's own body is a term chosen after the number was, and one
-- layer deeper than whatever the other hypotheses admit.  What answers
-- it is a reading that moves with the path -- the payload charged at
-- the factor and summand of what is STILL TO BE WALKED -- which the
-- walk face already carries and already transports across all five
-- arms.  What is left here is one leaf: that the arrival face's own
-- per-position data is enough to pay the walk's frame obligation.
--
-- IT SITS ABOVE THE ARRIVAL FACE RATHER THAN INSIDE IT, because the
-- module that consumes this is at the iteration loop's edge, and a
-- fact put there costs a gate run to check instead of seconds.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Face.Part7.Frame-Vals where

open import Data.Bool using (Bool; true)
open import Data.List using (List)
open import Data.Nat  using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim  using (Gas; Id; Tick)
open import Rx.Exp   using (Ctx; Closed; Val)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; budgetAt)
open import Verify-Budget-Sufficient.Nest-Store using (storeSyncMax)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?; FrameΦHyp)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestΦAt)

-- THE ONE LEAF, AND IT IS A DELIVERY QUESTION RATHER THAN AN
-- ARITHMETIC ONE.  `frameΦ-fit` (.Caps-Face.Part7.Depth-Fit, PROVEN)
-- already produces this from the caps receipt at the position, so what
-- is owed is not the frame's price but the receipt: the arrival face
-- enters a chain holding the potential, the vocabulary and the store,
-- and the walk face asks in addition for the position's size, strat,
-- park and order readings.  Stating it here is what says the gap is
-- THOSE readings and nothing else.
--
-- AND THE SIZE SLOT IS THE ROUND'S OWN CAP RATHER THAN A QUANTIFIED
-- ONE, which costs nothing and is worth a line: every consumer enters
-- at that cap, and the producer concludes at it, so a slot open to an
-- arbitrary number would claim the fit at caps no position is ever
-- read against -- strength nothing spends, on the axis where a cap too
-- small makes the reading it carries false.
--
-- AND THE ROUTE OUT IS A SIGNATURE CHANGE ONE FACE OVER, WHICH IS WHY
-- IT IS STATED HERE RATHER THAN ASSEMBLED.  The walk face already
-- produces this reading for an arbitrary position -- `frameΦ-fit` is
-- what `walk-ΦHyp-go` spends at each frame -- and the arrival face
-- cannot reach it only because that walk is entered through the WHOLE
-- chain's descent bound, which is the statement this leaf serves.  The
-- circle is not real: that premise is spent nowhere except to project
-- a bound on the position's OWN frame out of a join, and per position
-- `frame-depth-fit` delivers exactly that from the potential the
-- motive already carries.  So what discharges this is restating the
-- walk's entry against the ceiling rather than against the fold, after
-- which this becomes a projection.
--
-- AND IT IS ONE LEAF WHERE THE SPLIT WAS FOUR, WHICH IS THE POINT.
-- The four arms differed only in which frame they named, and what
-- kills the fixed form reaches every one of them -- the quantifier is
-- the same in each and the map arm is merely the one that needs no
-- burst count to say so.  So splitting by arm bought nothing: it
-- multiplied a single missing receipt into four statements that each
-- asked the impossible thing separately.
-- REFUTED: `Refuted.Step-Frame-Vals-Map` -- the fixed-grant form these
--   replace, at a step function one layer deeper than whatever grant
--   the three numeric hypotheses admit.  The frame appears in none of
--   them, so the crossing holds at every program rather than at one
--   arithmetic.
-- TWIN: `stepFrame-nest-Φ` (.Regs-Nest-Walk) -- the transport this
--   feeds, PROVEN over all five arms, which is what says the potential
--   is the right shape and the receipt is the whole of what is left.
postulate
  chain-frame-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
    (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) (f ↠ p) vals ≡ true →
    storeSyncMax sched st ≤ S →
    FrameΦHyp sf bid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
              f p vals fin sched st
