-- THE HOP EDGE AT A STORE THAT IS ALREADY DEEP — the configuration
-- every frame row on this shelf was missing.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THE SHELF NEEDED THIS AND NOTHING ELSE SUPPLIES IT.  Every frame
-- row in this tree is a fresh subscribe at the root, so the store reads
-- ZERO going in at all of them and the store conjunct has only ever
-- said a frame leaves an EMPTY store alone.  That is the weakest thing
-- it could say, and it is the half the tier's open question leans on:
-- if no premise about a state is owed, this conjunct is what carries
-- the obligation instead.  Here the frame's own node is installed
-- already holding observables, so the store reads deep BEFORE the frame
-- runs and the conjunct is comparing two positive numbers.

-- AND THE STORE BOUND IS TAKEN AT ITS SMALLEST LEGAL VALUE, which is
-- what makes these rows able to fail.  The statement quantifies `Rst`
-- over every natural above the premise, so a row is free to pick one
-- large enough to be safe; each row here picks `suc Rin ⊔ store`, the
-- least value satisfying both the premise and the incoming hypothesis.
-- There is then no slack anywhere to absorb a frame that installs
-- deeper than it was handed, and a row would go unsolvable rather than
-- pass.

-- WHAT THE PRE-LOADED QUEUE IS AND IS NOT.  It is the flattener's own
-- node, holding inners a previous instant parked, which is the one
-- place this machine lets a value wait.  It is NOT a second frame's
-- leavings: no row here runs a frame on the output of another, so what
-- is still unreached is a store some earlier frame WROTE, as against
-- one it was handed.

-- THE PARK BRANCH CANNOT CROSS, AND THAT IS BY THE DEFINITIONS RATHER
-- THAN BY THESE ROWS.  An observable VALUE is a closed expression, the
-- value reading at an observable type keeps the hop component of the
-- expression's reading, and the expression reading IS that component —
-- so the two are the same number, pinned below.  Parking appends the
-- arriving value to a queue the store reads by `⊔`, so what a park adds
-- is exactly what the frame was handed, and the premise pays for it
-- with a whole `suc` to spare.  A queue holding something deeper than
-- the source that emitted it does not exist to be built.
--
-- TARGET: thru-outer-frame-carried @134c89
module Probed.Hop-Store where

open import Data.Bool using (Bool; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
  ofᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; depthᵉ; depthᵛ; rdᵉ; ε)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState; subscribeE; rootWitness; rootTri; root; _↠_;
  sched-init; st-init; mintNode; installNode; mergeAll-st; thru-outer; mergeAllᵒ; splitBurst;
  stepFrame; stHop)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Carried using (valsRd)
open import Verify-Rank-Sufficient.Push-Carried
  using (thru-outer-frame-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FRAME'S OWN POINT, assembled as the walk's flattener arm
-- assembles it, except that the node the arm installs is handed in
-- already populated.  Everything downstream of that is the run's: the
-- outer is SUBSCRIBED under the frame and the frame is handed what the
-- burst hands it.
--
-- The rows themselves cannot live here: the decision procedure needs
-- closed numerals, and nothing under a parameter reduces.
----------------------------------------------------------------------

module Ap {n} {Γ : Ctx n} (ins : Slots Γ)
          (node : NodeState Γ) (prog : Closed Γ (obs natᵗ))
          (src : Closed Γ (obs (obs natᵗ))) where

  ψ : Fin n → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri prog ins)
  ac = rootWitness prog ins

  nid : NodeId
  nid = proj₁ (mintNode (sched-init prog ins))

  r : Stream Γ (obs (obs natᵗ)) × Sched Γ × EvalSt prog
  r = subscribeE {lo = n} ac src
        (thru-outer mergeAllᵒ nid ↠ root) 0 0
        (proj₂ (mintNode (sched-init prog ins)))
        (installNode nid node (st-init prog))

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
  sf = stepFrame {lo = n} ac 0 0 (thru-outer mergeAllᵒ nid) root vals fin sd st

  -- the bound the arriving observables are held to — the source's own
  -- payload PAIR, which is what the walk enters this frame at
  Rin : Rd
  Rin = proj₂ (rdᵉ ψ ε src)

  bound : ℕ
  bound = depthᵉ ψ src

  -- what the store reads going IN, which is the quantity no other row
  -- on this shelf moves off zero
  stIn : ℕ
  stIn = stHop ψ st

  -- the SMALLEST store bound the statement admits at this point: the
  -- premise forces `suc bound` and the incoming hypothesis forces the
  -- store's own reading, and nothing forces more
  Rst : ℕ
  Rst = suc bound ⊔ stIn

  -- radix 1000, low digit first: what the frame was handed, the bound
  -- the payload is held to, what it gave back, what the store read
  -- going in, what it reads coming out, and the bound the store half is
  -- held to
  -- and the DELIVERY side of the same pair: handed, the bound, returned
  counts : ℕ
  counts = proj₁ (valsRd ψ (obs (obs natᵗ)) vals)
         + 1000 * proj₁ Rin
         + 1000000 * proj₁ (valsRd ψ (obs natᵗ) (proj₁ sf))

  packed : ℕ
  packed = proj₂ (valsRd ψ (obs (obs natᵗ)) vals)
         + 1000 * bound
         + 1000000 * proj₂ (valsRd ψ (obs natᵗ) (proj₁ sf))
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
-- THE INNER, which is the shelf's own: a fold that re-wraps its
-- accumulator once per delivery, so what the frame hands back climbs
-- with the outer source while the bound it is held to is read off the
-- syntax.  The seed is flattened once so the node a subscription
-- installs for it does not read zero.
----------------------------------------------------------------------

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

src₂ : Closed Γ₀ (obs (obs natᵗ))
src₂ = ofᵉ (strmᵗ (scanᵉ deepen liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))) ∷ [])

----------------------------------------------------------------------
-- THE QUEUES, at three depths.  `q0` is the control the rest of the
-- shelf already covers; `q1` and `q2` read one and two, so the store
-- enters ABOVE what the premise alone would give and the bound the
-- conjunct is held to is the store's reading rather than the rank.
----------------------------------------------------------------------

q0 q1 q2 : Closed Γ₀ (obs natᵗ)
q0 = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])
q1 = ofᵉ (strmᵗ (mergeAllᵉ nothing q0) ∷ [])
q2 = ofᵉ (strmᵗ (mergeAllᵉ nothing q1) ∷ [])

mrg : Closed Γ₀ (obs (obs natᵗ)) → Closed Γ₀ (obs natᵗ)
mrg = mergeAllᵉ nothing

module Q0 = Ap ins₀ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₂) src₂
module Q1 = Ap ins₀ (mergeAll-st {t = obs natᵗ} nothing 0 (q1 ∷ []) false)
              (mrg src₂) src₂
module Q2 = Ap ins₀ (mergeAll-st {t = obs natᵗ} nothing 0 (q2 ∷ []) false)
              (mrg src₂) src₂

----------------------------------------------------------------------
-- THE TWO READINGS COINCIDE AT AN OBSERVABLE, which is what closes the
-- park branch by construction rather than by instantiation.  A value of
-- observable type IS a closed expression, and the two readings differ
-- only in which component of the same triple they project — so no queue
-- can hold something the frame was not already charged for.  Pinned at
-- three depths because a coincidence at zero would be no evidence.
----------------------------------------------------------------------

same₀ : depthᵛ (slotRd ins₀) (obs (obs natᵗ)) q0 ≡ depthᵉ (slotRd ins₀) q0
same₀ = refl

same₁ : depthᵛ (slotRd ins₀) (obs (obs natᵗ)) q1 ≡ depthᵉ (slotRd ins₀) q1
same₁ = refl

same₂ : depthᵛ (slotRd ins₀) (obs (obs natᵗ)) q2 ≡ depthᵉ (slotRd ins₀) q2
same₂ = refl

----------------------------------------------------------------------
-- BOTH SIDES PINNED, so the rows below are green with a margin someone
-- can read rather than merely green.  Read low digit first at radix
-- 1000: handed, payload bound, returned, store in, store out, store
-- bound.  The fourth digit is the one no other row on this shelf moves.
----------------------------------------------------------------------

q0-is : Q0.packed ≡ 4003000003003003
q0-is = refl

q1-is : Q1.packed ≡ 4003001003003003
q1-is = refl

q2-is : Q2.packed ≡ 4003002003003003
q2-is = refl

-- AND THE DELIVERY SIDE, which the hop figures project away.  Read low
-- first: handed, bound, returned.  The hypothesis is SATURATED at every
-- row and the conclusion has a delivery of margin, which the queue's
-- depth does not move — this family varies the STORE and the count side
-- sits where the outer's own reading puts it.
counts₀-is : Q0.counts ≡ 1002002
counts₀-is = refl

counts₁-is : Q1.counts ≡ 1002002
counts₁-is = refl

counts₂-is : Q2.counts ≡ 1002002
counts₂-is = refl


----------------------------------------------------------------------
-- WHAT THE THREE FIGURES SAY.  What the frame is handed equals the
-- source's own reading at every row, so the payload hypothesis is
-- decided at EQUALITY rather than granted with room.  The store enters
-- at nought, one and two — the first rows anywhere on this shelf where
-- it enters positive at all — and comes out reading THREE at all three,
-- which is the frame's own write: subscribing the arriving inner
-- installs a node deeper than anything that was waiting, and the queue
-- that was there is absorbed by the `⊔` the store reading is.  Held to
-- four, so the write has a unit to spare.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- AND THE STORE-IN AXIS CANNOT REFUTE, WHICH IS WORTH MORE THAN THE
-- ROWS.  The queue's reading enters the bound and the outgoing reading
-- through the same `⊔`, so raising it raises both sides by the same
-- amount and no depth of queue can produce a counterexample — a
-- bound-side axis, decidable from the definitions before any harness
-- exists.  What remains falsifiable is the frame's own WRITE, which is
-- what these rows actually exercise: an installation deeper than the
-- payload leaves the conjunct unsolvable at the least legal bound.
-- NOT covered, and it is the same gap the shelf still has: no row runs
-- a frame on a store a DIFFERENT frame wrote, and here the write and
-- the payload coincide at three, so nothing yet separates them.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- THE TARGET, AT THE POINTS THE RUNS REACHED.  The premise and both
-- hypotheses are DECIDED rather than assumed, and the store bound is
-- the least one they admit, so a frame installing deeper than it was
-- handed leaves the row unsolvable rather than passing quietly.
----------------------------------------------------------------------

stRow₀ : Confirms (thru-outer-frame-carried {lo = 0} Q0.ac 0 0 mergeAllᵒ Q0.nid root
  Q0.ψ Q0.Rin Q0.Rst Below Q0.vals Q0.fin Q0.sd Q0.st
  (Below , Below) Below)
stRow₀ = (Below , Below) , Below

stRow₁ : Confirms (thru-outer-frame-carried {lo = 0} Q1.ac 0 0 mergeAllᵒ Q1.nid root
  Q1.ψ Q1.Rin Q1.Rst Below Q1.vals Q1.fin Q1.sd Q1.st
  (Below , Below) Below)
stRow₁ = (Below , Below) , Below

stRow₂ : Confirms (thru-outer-frame-carried {lo = 0} Q2.ac 0 0 mergeAllᵒ Q2.nid root
  Q2.ψ Q2.Rin Q2.Rst Below Q2.vals Q2.fin Q2.sd Q2.st
  (Below , Below) Below)
stRow₂ = (Below , Below) , Below
