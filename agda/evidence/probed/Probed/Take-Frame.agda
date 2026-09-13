-- THE PREFIX FRAME, INSTANTIATED — a take handed real observables and
-- asked what it gives back, held to exactly what it was handed.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THIS STATEMENT AND WHY NOW.  Its neighbour on the same shelf fell
-- to `Refuted.Map-Template`, at a template that drops its argument, and
-- the two were split because the reason they were believed differs: a
-- map evaluates a second term and a take does not.  That is an argument
-- from reading the arm, and an argument from reading the arm is what
-- the killed one also had.  So the surviving half is instantiated
-- rather than inherited, at the shapes that witness could not reach.

-- BOTH CONJUNCTS ARE LOAD-BEARING, AND THE TYPE IS WHAT MAKES THEM SO.
-- A take over a stream of NATS hands back data payloads, which the
-- reading charges zero by construction — a row there would compare zero
-- against zero and could not have failed.  So the source below emits
-- OBSERVABLES, produced by a fold that re-wraps its accumulator as it
-- runs, and every value the frame is handed reads positive.  The store
-- half needs the same care from the other side: a take's own node is
-- priced at zero by the reading, so the store conjunct would be
-- comparing nothing at all if the take's node were the only one there.
-- What makes it comparable is the fold's node, which the subscription
-- installs and which holds a live accumulator.

-- AND THE BOUNDS ARE THE TIGHTEST THE PREDICATE ADMITS.  The statement
-- quantifies `Rv` and `Rst` over every natural and the two hypotheses
-- are the only thing pinning them, so a row taken at a generous bound
-- is a row that could not have failed.  Each row below takes `Rv` to be
-- exactly what the frame was handed and `Rst` exactly what the store
-- read on the way in, which is the strongest instance of the claim
-- there is: any output the take invented, and any node it deepened,
-- crosses immediately.

-- WHAT THE FAMILIES ARE BUILT TO MOVE, AND THE FIGURES SAY WHICH ONES
-- REACHED IT.  The count is varied against what the burst supplies, and the
-- PAYLOAD digit is what separates the outcomes rather than any label:
-- two rows hand back strictly less than they were given, which is the
-- prefix being cut, and two hand back all of it.  Of the latter, one
-- has a count that exactly exhausts the burst and one a count that
-- outruns it.  The fold's rate is varied across two sources as well, so
-- no row is green because the values it compared had stopped moving.

-- THE BOUNDARY, and it is what these rows do NOT buy.  Every row is a
-- SUBSCRIBE at the root: no row reaches an arrival, a drain step, or a
-- take whose node was already spent by an earlier burst, so nothing
-- here says what the frame does to a store some later frame has already
-- written.  The FINISH digit records exactly that and is constant true
-- across all four — every point sits at a burst that completes — so it
-- pins the flag surviving the frame and buys no mid-stream coverage.
-- Which BRANCH of the arm ran is not separated by the figures either:
-- a count that exactly exhausts the burst closes the take while handing
-- back everything, and is indistinguishable here from one that merely
-- decrements.  Source lengths run to three literals, because a row
-- costs a whole walk.
--
-- TARGET: take-frame-carried @d01324
module Probed.Take-Frame where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
  ofᵉ; takeᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId;
  subscribeE; rootWitness; rootTri; root; _↠_; sched-init; st-init;
  mintNode; installNode; take-st; take-f; splitBurst; stepFrame; stHop)
open import Verify-Rank-Sufficient.Carried using (valsHop)
open import Verify-Rank-Sufficient.Push-Carried using (take-frame-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FRAME'S OWN POINT, assembled exactly as the walk's take arm
-- assembles it: mint the node, install the count, subscribe the source
-- under the frame, and hand the frame what the burst hands it.  The
-- values are REACHED BY RUNNING — `splitBurst` of the real burst is
-- what `pushBurst` passes — rather than written down, and the store is
-- the one the subscription left behind.
--
-- The rows themselves cannot live here: the decision procedure needs
-- closed numerals, and nothing under a parameter reduces.
----------------------------------------------------------------------

module Ap {n} {Γ : Ctx n} (ins : Slots Γ) (k : ℕ)
          (prog : Closed Γ (obs natᵗ)) (src : Closed Γ (obs natᵗ)) where

  ψ : Fin n → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri prog ins)
  ac = rootWitness prog ins

  nid : NodeId
  nid = proj₁ (mintNode (sched-init prog ins))

  r : Stream Γ (obs natᵗ) × Sched Γ × EvalSt prog
  r = subscribeE ac src (take-f nid ↠ root) 0 0
        (proj₂ (mintNode (sched-init prog ins)))
        (installNode nid (take-st k) (st-init prog))

  sp : List (Val Γ (obs natᵗ))
     × List (InstEvent (Val Γ (obs natᵗ))) × Bool
  sp = splitBurst (proj₁ r)

  vals : List (Val Γ (obs natᵗ))
  vals = proj₁ sp

  fin : Bool
  fin = proj₂ (proj₂ sp)

  sd : Sched Γ
  sd = proj₁ (proj₂ r)

  st : EvalSt prog
  st = proj₂ (proj₂ r)

  sf : List (Val Γ (obs natᵗ)) × List (InstEvent (Val Γ (obs natᵗ)))
     × Bool × Sched Γ × EvalSt prog
  sf = stepFrame ac 0 0 (take-f nid) root vals fin sd st

  -- the two bounds, each the TIGHTEST the predicate admits: what the
  -- frame was handed, and what the store read on the way in
  Rv : ℕ
  Rv = valsHop ψ (obs natᵗ) vals

  Rst : ℕ
  Rst = stHop ψ st

  -- radix 1000, low digit first: what the frame was handed, what it
  -- gave back, what the store read going in, what it reads coming
  -- out, and whether the take CLOSED — the last because the hop
  -- figures alone cannot separate the arm's two branches, and a row
  -- at the cutting branch that was silently on the passing one is a
  -- row the header lies about
  packed : ℕ
  packed = Rv
         + 1000 * valsHop ψ (obs natᵗ) (proj₁ sf)
         + 1000000 * Rst
         + 1000000000 * stHop ψ (proj₂ (proj₂ (proj₂ (proj₂ sf))))
         + 1000000000000 * (if proj₁ (proj₂ (proj₂ sf)) then 1 else 0)

----------------------------------------------------------------------
-- THE CLOSED CONTEXT, where the reading of an input cannot enter and
-- every figure is the term's own.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE SOURCE: a fold whose accumulator is an OBSERVABLE, so what the
-- take is handed reads positive, and whose node the store can read.
-- `deepen` re-wraps once per delivery and `deepen2` twice, so the
-- values climb at two rates and a row that stalled would say so.
----------------------------------------------------------------------

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

deepen2 : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen2 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

folded : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ) →
         List (Tm Γ₀ [] [] [] natᵗ) → Closed Γ₀ (obs natᵗ)
folded f xs = scanᵉ f liveSeed (ofᵉ xs)

src₂ src₃ : Closed Γ₀ (obs natᵗ)
src₂ = folded deepen (nat̂ 0 ∷ nat̂ 1 ∷ [])
src₃ = folded deepen2 (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

tk : ℕ → Closed Γ₀ (obs natᵗ) → Closed Γ₀ (obs natᵗ)
tk c b = takeᵉ (nat̂ c) b

----------------------------------------------------------------------
-- THE FOUR POINTS, named for what the count does to the burst.  `Cut₁`
-- is the shape in which a prefix that was not a prefix would show up
-- soonest: the cut fires on the first delivery.  `Edge₂` takes exactly
-- what the burst supplies, so the take is spent and nothing is dropped.
-- `Pass` outruns it.  `Deep` cuts a longer burst at the faster fold
-- rate, which is the only point where the figures leave the single
-- digits they otherwise sit in.
----------------------------------------------------------------------

module Cut₁ = Ap ins₀ 1 (tk 1 src₂) src₂
module Edge₂ = Ap ins₀ 2 (tk 2 src₂) src₂
module Pass = Ap ins₀ 5 (tk 5 src₂) src₂
module Deep = Ap ins₀ 2 (tk 2 src₃) src₃

----------------------------------------------------------------------
-- BOTH SIDES PINNED, so the rows below are green with a margin someone
-- can read rather than merely green.  Every figure is LOAD-BEARING: a
-- handed reading that came back zero would say the source is emitting
-- data rather than observables and the payload conjunct is comparing
-- nothing; a store figure of zero would say the same of the second
-- conjunct; and either returned figure overtaking the bound beside it
-- would refute the target outright.
--
-- Read low digit first at radix 1000: handed, returned, store in,
-- store out, finished.  The STORE half is tight at every point — what
-- the frame read going in it reads coming out — which is the cutting
-- arm dropping registry entries and installing nothing.
----------------------------------------------------------------------

cut₁-is : Cut₁.packed ≡ 1003003002003
cut₁-is = refl

edge₂-is : Edge₂.packed ≡ 1003003003003
edge₂-is = refl

pass-is : Pass.packed ≡ 1003003003003
pass-is = refl

deep-is : Deep.packed ≡ 1007007005007
deep-is = refl

----------------------------------------------------------------------
-- THE TARGET, AT THE POINTS THE RUNS REACHED.  Both hypotheses are
-- DECIDED rather than assumed, and at these bounds they hold by
-- construction — which is the point: the row that remains is the
-- conclusion alone, taken where the predicate is strongest.
----------------------------------------------------------------------

takeCut₁ : Confirms (take-frame-carried Cut₁.ac 0 0 Cut₁.nid root
  Cut₁.ψ Cut₁.Rv Cut₁.Rst Cut₁.vals Cut₁.fin Cut₁.sd Cut₁.st Below Below)
takeCut₁ = Below , Below

takeEdge₂ : Confirms (take-frame-carried Edge₂.ac 0 0 Edge₂.nid root
  Edge₂.ψ Edge₂.Rv Edge₂.Rst Edge₂.vals Edge₂.fin Edge₂.sd Edge₂.st
  Below Below)
takeEdge₂ = Below , Below

takePass : Confirms (take-frame-carried Pass.ac 0 0 Pass.nid root
  Pass.ψ Pass.Rv Pass.Rst Pass.vals Pass.fin Pass.sd Pass.st Below Below)
takePass = Below , Below

takeDeep : Confirms (take-frame-carried Deep.ac 0 0 Deep.nid root
  Deep.ψ Deep.Rv Deep.Rst Deep.vals Deep.fin Deep.sd Deep.st Below Below)
takeDeep = Below , Below
