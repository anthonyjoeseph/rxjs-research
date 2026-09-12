------------------------------------------------------------------
-- THE FRAME'S PAYLOAD AXIS, ARM BY ARM.
--
-- A chain position is entered with a GRANT -- one number every
-- hypothesis is stated under -- and what the frame emits has to stay
-- under it.  Splitting the obligation by `stepFrame`'s own arms is
-- what makes each remaining price greppable rather than hidden inside
-- one statement over an abstract `Frame`: two of the five substitute
-- and so carry a factor, two graft a burst and carry the walk's, and
-- the fifth carries nothing and is discharged here.
--
-- IT SITS ABOVE THE ARRIVAL FACE RATHER THAN INSIDE IT, because the
-- module that consumes this is at the iteration loop's edge, and a
-- fact put there costs a gate run to check instead of seconds.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Face.Part7.Frame-Vals where

open import Data.Bool using (Bool)
open import Data.List using (List; [])
open import Data.Nat  using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤n⊔m; ⊔-lub)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim  using (Gas; Id; Tick)
open import Rx.Exp   using (Ctx; Closed; Val; Fn; obs; _×ᵗ_)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; AllOp;
  stepFrame; budgetAt; map-f; scan-f; take-f; from-inner; thru-outer)
open import Verify-Budget-Sufficient.Nest-Store using
  (storeSyncMax; storeSync-nodes≤)
open import Verify-Budget-Sufficient.Nest-Walk using
  (nestDᵛˢ; nodesMax; stepFrame-nodes-take)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestΦAt)

-- AND THE PAYLOAD AXIS IS PRICED ARM BY ARM, because only two of the
-- five move it.  `take-f` writes a numeral, sweeps the live set and
-- drops registrations, so what it emits is either what it was handed or
-- what its own node already held -- both already under the grant, which
-- is why that arm is DISCHARGED below rather than postulated.  The
-- remaining four are leaves, and splitting them is what makes each
-- one's price greppable: the map and scan arms substitute and so carry
-- a factor, while the two `*All` arms graft a burst and carry the
-- walk's own.
-- REFUTED: `Refuted.Scan-Phi-Burst` is why no leaf here may be given a
--   charge CONSTANT in the burst.  `scanVals` THREADS, so a burst of
--   sixty-five values folds sixty-five layers onto the accumulator
--   while a premise reading the step function alone clears at
--   sixty-four -- a constant against a linear conclusion.
-- REFUTED: `Refuted.Share-Step-Scan` kills PRESERVATION OF THE CEILING
--   across this very step, and naming it is what says which statement
--   this is not: `sightCeil` is a function of what is in hand and moves
--   with it, where S is a GRANT every hypothesis is stated under and
--   `nestΦ-frame-charge` (.Caps-Face.Nest-Arith, PROVEN) puts a tower
--   in the position's own size cap underneath it.
-- DEAD ROUTE: ASSEMBLING THESE LEAVES OUT OF THAT TWIN, which is the
--   obvious route and the one the split was written for.  The twin's
--   conclusion carries the burst count in an EXPONENT -- a threading
--   frame applies its step function once per value handed to it -- so
--   spending it asks the position's grant to dominate a power in a
--   count, and `Refuted.Walk-Phi-Room` kills exactly that product at a
--   count the caps recurrence admits.  The count is under the NEXT
--   instant's size cap and under nothing smaller (`burst≤size′`), while
--   the grant here is sighted at THIS instant, so the two are one index
--   apart and the width axis towers where the size steps geometrically.
--   The same arithmetic is already a live SHAPE row one module over, at
--   the statement that would have supplied the count; these leaves
--   inherit it rather than adding a second instance of it.
-- TWIN: `stepFrame-nodes` (.Nest-Walk) -- the same quantity over all
--   five arms, PROVEN, in the walk's priced currency.  It is what says
--   the growth is bounded at all rather than only conjectured to be,
--   and the dead route above is what says it is not what closes these.

-- BUT SPENDING IT IS NOT A TRANSPORT, AND THE PREMISE LIST IS WHY.  The
-- twin asks for the OUTPUT's width as a hypothesis and not only the
-- input's, so it prices a burst it is handed rather than bounding one;
-- a chain loop threading it therefore owes that width at every step,
-- and that obligation is the region's open question rather than a
-- bookkeeping detail of this module.  Beside it sit a caps rider and
-- several path readings the fit predicate these leaves are consumed
-- under carries none of -- so the rider is what has to move first, and
-- it moves in the predicate rather than here.  What is left after it
-- moves is NOT arithmetic, which is the finding the split turned up and
-- the dead route below states: the rider carries a count, the twin
-- charges a power in that count, and the grant these leaves are stated
-- against cannot pay for one.

-- AND THE OUTPUT WIDTH IS SPENT AT ONE ARM OF FIVE, which is what says
-- how much a rider carrying it would have to buy.  Read off the twin's
-- own clauses rather than its signature: the two substituting arms and
-- the taking one discard that premise, the arm grafting an inner binds
-- it and never spends it, and only the arm that subscribes an outer
-- uses it -- there, through the park reading it hands its own delivery
-- lemma.  So three of these four leaves are owed the INPUT width alone.
-- The fold around them is the one that owes the output width, at every
-- arm and not at one, because what it carries forward is the predicate
-- at the NEXT position; and that is why the obligation is a leaf of the
-- loop rather than a premise of any leaf here.
postulate
  step-frame-vals-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
    (fn : Fn Γ [] [] [] s u) (p : Path Γ u t) (vals : List (Val Γ s))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    nestDᵛˢ vals ≤ S →
    storeSyncMax sched st ≤ S →
    nestDᵛˢ (proj₁ (stepFrame sf bid now (map-f fn) p vals fin sched st)) ≤ S

  step-frame-vals-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    nestDᵛˢ vals ≤ S →
    storeSyncMax sched st ≤ S →
    nestDᵛˢ (proj₁ (stepFrame sf bid now (scan-f fn nid) p vals fin sched st)) ≤ S

  step-frame-vals-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
    (op : AllOp) (allNid inst : NodeId) (p : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    nestDᵛˢ vals ≤ S →
    storeSyncMax sched st ≤ S →
    nestDᵛˢ (proj₁ (stepFrame sf bid now (from-inner op allNid inst) p vals
                        fin sched st)) ≤ S

  step-frame-vals-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
    (op : AllOp) (nid : NodeId) (p : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    nestDᵛˢ vals ≤ S →
    storeSyncMax sched st ≤ S →
    nestDᵛˢ (proj₁ (stepFrame sf bid now (thru-outer op nid) p vals
                        fin sched st)) ≤ S

step-frame-vals≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
  nestΦAt e sl id ≤ S →
  nestDᵛˢ vals ≤ S →
  storeSyncMax sched st ≤ S →
  nestDᵛˢ (proj₁ (stepFrame sf bid now f p vals fin sched st)) ≤ S
step-frame-vals≤ sl id sf bid now S (map-f fn) p vals fin sched st =
  step-frame-vals-map sl id sf bid now S fn p vals fin sched st
step-frame-vals≤ sl id sf bid now S (scan-f fn nid) p vals fin sched st =
  step-frame-vals-scan sl id sf bid now S fn nid p vals fin sched st
step-frame-vals≤ sl id sf bid now S (take-f nid) p vals fin sched st
  _ _ _ hval hS =
  ≤-trans (m≤n⊔m (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ R))))) (nestDᵛˢ (proj₁ R)))
          (≤-trans (stepFrame-nodes-take sf bid now nid p vals fin sched st)
                   (⊔-lub (≤-trans (storeSync-nodes≤ sched st) hS) hval))
  where
  R = stepFrame sf bid now (take-f nid) p vals fin sched st
step-frame-vals≤ sl id sf bid now S (from-inner op allNid inst) p vals fin sched st =
  step-frame-vals-inner sl id sf bid now S op allNid inst p vals fin sched st
step-frame-vals≤ sl id sf bid now S (thru-outer op nid) p vals fin sched st =
  step-frame-vals-outer sl id sf bid now S op nid p vals fin sched st
