-- THE TEMPLATE FRAME, INSTANTIATED — a map handed what its source
-- really emits and asked what the template makes of it.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THIS STATEMENT AND WHY NOW.  Two witnesses pin this statement's
-- two ends apart, and neither of them instantiates the form that
-- survived: one kills a freely quantified bound, the other kills the
-- symmetric pin, and both do it in a predicate they RESTATE locally.  A
-- locally restated predicate agreeing with a postulate is not the
-- postulate holding — so what the statement says at a point the walk can
-- reach has never been run, and the class it carries rests on two
-- arguments about what is false.

-- THE POINT IS THE WALK'S OWN, AND THE PAYLOAD IS REACHED BY RUNNING.
-- Each row subscribes the SOURCE under a map frame, exactly as the map
-- arm does, splits the burst the subscription produced, and hands the
-- frame that.  So the incoming values are ones this source can actually
-- emit rather than the strongest the bound admits — which is the
-- distinction the symmetric form got wrong, and the one a row written
-- from the bound instead of from the run would erase.

-- THE HYPOTHESIS IS DECIDED, WHICH IS WHERE A REFUTATION WOULD SURFACE.
-- `Below` spends the decision procedure at the probe's own numerals, so
-- a source whose emissions overrun its own reading leaves the row
-- unsolvable rather than letting it through.  That is the half worth
-- having: it says the incoming bound is satisfiable by a real run, and
-- not merely that the conclusion holds once someone grants it.

-- WHAT THE FAMILY IS BUILT TO MOVE.  The template is the axis, at the
-- three things one can do to an argument's depth: ADD a layer, DROP the
-- argument for something shallower, and PRESERVE it.  The two ends of
-- the statement coincide at the middle two and come apart at the first,
-- so a bound quietly collapsed onto its neighbour would still pass the
-- preserving rows and fail the growing ones.  The source is the second
-- axis, at three depths, so no row is green because the reading it
-- compared was zero on both sides.

-- AND THE STORE IS THE THIRD, WHICH IS WHAT THE DEEPEST SOURCE IS FOR.
-- The statement's store conjunct compares against a bound quantified
-- over every natural, so a row must take it TIGHT to say anything — and
-- a tight bound at ZERO is still nothing being compared.  A map mints no
-- node, so the only way the store reads positive at this frame is for
-- the SOURCE to have installed one, which a literal never does.  The
-- fold below does, and holds an accumulator the reading prices at three.

-- THE BOUNDARY, and it is what these rows do NOT buy.  Every row is a
-- SUBSCRIBE at the root under an empty context: no row reaches an
-- arrival or a drain step, so nothing here says what the frame does to a
-- store a LATER frame wrote — only that it leaves alone one its own
-- source did.  One template application per row, so nothing here reaches
-- a template whose own body maps again.  The FINISH flag is whatever the
-- source's burst carried and is not varied.
--
-- TARGET: map-frame-carried @fbcf9c
module Probed.Map-Frame where

open import Data.Bool using (Bool)
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
open import Rx.Exp using (Ctx; Closed; Tm; Val; Fn; natᵗ; obs; _×ᵗ_;
  strmᵗ; ofᵉ; mergeAllᵉ; mapᵉ; scanᵉ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; subscribeE;
  rootWitness; rootTri; root; _↠_; sched-init; st-init; map-f;
  splitBurst; stepFrame; stHop)
open import Verify-Rank-Sufficient.Carried using (valsHop)
open import Verify-Rank-Sufficient.Push-Carried using (map-frame-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FRAME'S OWN POINT, assembled exactly as the walk's map arm
-- assembles it: subscribe the source under the frame and hand the frame
-- what the burst hands it.  A map mints no node, so the store the frame
-- is given is the one the subscription left.
--
-- The rows themselves cannot live here: the decision procedure needs
-- closed numerals, and nothing under a parameter reduces.
----------------------------------------------------------------------

module Ap {n} {Γ : Ctx n} (ins : Slots Γ)
          (fn : Fn Γ [] [] [] (obs natᵗ) (obs natᵗ))
          (b : Closed Γ (obs natᵗ)) where

  prog : Closed Γ (obs natᵗ)
  prog = mapᵉ fn b

  ψ : Fin n → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri prog ins)
  ac = rootWitness prog ins

  r : Stream Γ (obs natᵗ) × Sched Γ × EvalSt prog
  r = subscribeE ac b (map-f fn ↠ root) 0 0 (sched-init prog ins)
        (st-init prog)

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
  sf = stepFrame ac 0 0 (map-f fn) root vals fin sd st

  -- the store bound is quantified over every natural, so it is taken
  -- TIGHT: whatever the store read on the way in.  The two payload
  -- bounds are not ours to choose — the statement pins them at the
  -- source's reading and the map expression's
  Rst : ℕ
  Rst = stHop ψ st

  -- radix 1000, low digit first: the incoming bound, what the frame was
  -- actually handed, the outgoing bound, what it gave back, what the
  -- store read going in and coming out.  The first two say the
  -- hypothesis has margin or none; the middle two say whether the
  -- template moved the reading and whether the bound moved with it
  packed : ℕ
  packed = depthᵉ ψ b
         + 1000 * valsHop ψ (obs natᵗ) vals
         + 1000000 * depthᵉ ψ (mapᵉ fn b)
         + 1000000000 * valsHop ψ (obs natᵗ) (proj₁ sf)
         + 1000000000000 * Rst
         + 1000000000000000 * stHop ψ (proj₂ (proj₂ (proj₂ (proj₂ sf))))

----------------------------------------------------------------------
-- THE CLOSED CONTEXT, where the reading of an input cannot enter and
-- every figure is the term's own.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

----------------------------------------------------------------------
-- THE THREE TEMPLATES, which are the three things a template can do to
-- the depth of what it is handed.  `grow` re-wraps, so one application
-- adds exactly the layer the reading's map clause charges; `shed`
-- ignores its argument entirely and returns a literal, which is the
-- shape that killed the freely quantified form; `keep` hands the
-- argument straight back, where the two ends of the statement coincide.
----------------------------------------------------------------------

grow : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
grow = strmᵗ (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))

shed : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
shed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

keep : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
keep = varᵗ (here refl)

----------------------------------------------------------------------
-- THE SHALLOW SOURCES, so no row compares zero against zero on both
-- sides.  `src₀` emits an observable as shallow as the type allows;
-- `src₁`
-- emits one already carrying a flattener, so its own reading is
-- positive and the incoming bound is a real bound rather than a floor.
----------------------------------------------------------------------

src₀ : Closed Γ₀ (obs natᵗ)
src₀ = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

src₁ : Closed Γ₀ (obs natᵗ)
src₁ = ofᵉ (strmᵗ (mergeAllᵉ nothing
         (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])

----------------------------------------------------------------------
-- AND A THIRD SOURCE WHOSE SUBSCRIPTION LEAVES SOMETHING IN THE STORE,
-- which is what the two above cannot do.  A map mints no node, so the
-- store the frame is handed is whatever its SOURCE installed — and a
-- literal installs nothing, which is why the store conjunct reads zero
-- on both sides at every point above and compares nothing.  A fold does
-- install one, and an accumulator that is an OBSERVABLE is what the
-- reading prices above zero, so `srcS` is the shape in which the store
-- half of this statement is a comparison at all.
----------------------------------------------------------------------

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

srcS : Closed Γ₀ (obs natᵗ)
srcS = scanᵉ deepen liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))

----------------------------------------------------------------------
-- THE NINE POINTS — every template at every source, because which rows
-- can fail is not decidable from the template alone: a template that
-- DROPS depth is unfalsifiable at a source reading zero and load-bearing
-- one layer up, where it must return a payload under a bound its own
-- body no longer justifies.
----------------------------------------------------------------------

module Grow₀ = Ap ins₀ grow src₀
module Shed₀ = Ap ins₀ shed src₀
module Keep₀ = Ap ins₀ keep src₀
module Grow₁ = Ap ins₀ grow src₁
module Shed₁ = Ap ins₀ shed src₁
module Keep₁ = Ap ins₀ keep src₁

module GrowS = Ap ins₀ grow srcS
module ShedS = Ap ins₀ shed srcS
module KeepS = Ap ins₀ keep srcS

----------------------------------------------------------------------
-- BOTH SIDES PINNED, so the rows below are green with a margin someone
-- can read rather than merely green.  Read low digit first at radix
-- 1000: incoming bound, handed, outgoing bound, returned, store in,
-- store out.
--
-- WHICH ROWS COULD HAVE FAILED, since three of the six could not.  The
-- GROWING rows are the load-bearing ones and they are TIGHT — returned
-- equals the outgoing bound at both sources, so one extra layer anywhere
-- in the template's body would have taken the conclusion out.  The
-- DROPPING row is load-bearing only at the deeper source, where the
-- payload falls to zero under a bound that stays at one; at the shallow
-- source it and the PRESERVING row read zero in every digit and are
-- DEGENERATE, kept as the floor and buying nothing.
--
-- AND THE HYPOTHESIS IS SATURATED, WHICH IS THE HALF THAT SURPRISES.
-- What the frame is handed equals the source's own reading at both
-- sources, so the incoming bound has NO margin at any point here: the
-- decision procedure discharging it is deciding an equality, and a source
-- emitting one layer more than its reading admits would have left every
-- row unsolvable rather than merely loose.
--
-- AND A DROPPING TEMPLATE'S OUTGOING BOUND DOES NOT DROP WITH IT: the
-- map expression reads one where its template returns a literal, so the
-- statement's right-hand end tracks the SOURCE and not the body.  That is
-- slack in the reading rather than in this statement, and it is owed to
-- the reading's own map clause.
----------------------------------------------------------------------

grow₀-is : Grow₀.packed ≡ 1001000000
grow₀-is = refl

shed₀-is : Shed₀.packed ≡ 0
shed₀-is = refl

keep₀-is : Keep₀.packed ≡ 0
keep₀-is = refl

grow₁-is : Grow₁.packed ≡ 2002001001
grow₁-is = refl

shed₁-is : Shed₁.packed ≡ 1001001
shed₁-is = refl

keep₁-is : Keep₁.packed ≡ 1001001001
keep₁-is = refl

----------------------------------------------------------------------
-- AND THE THREE OVER A STORE THAT READS POSITIVE, which is where the
-- second conjunct stops being a comparison of nothing.  The store reads
-- THREE going in and three coming out at all three templates, so it is
-- TIGHT at a figure that could have moved: a map that deepened any node
-- would overrun a bound taken at exactly what it was handed, and the
-- rows above could not have said so at zero.
--
-- The payload digits repeat the finding the shallow rows already carry,
-- at a source three layers deep rather than one: the GROWING row is
-- tight at four against four, the PRESERVING row tight at three against
-- three, and the DROPPING row returns ZERO under a bound of three —
-- which is the same slack in the reading's own map clause, now three
-- layers wide instead of one.  So the slack tracks the SOURCE's depth,
-- which one source could not have shown.
----------------------------------------------------------------------

growS-is : GrowS.packed ≡ 3003004004003003
growS-is = refl

shedS-is : ShedS.packed ≡ 3003000003003003
shedS-is = refl

keepS-is : KeepS.packed ≡ 3003003003003003
keepS-is = refl

----------------------------------------------------------------------
-- THE TARGET, AT THE POINTS THE RUNS REACHED.  The hypotheses are
-- DECIDED rather than assumed, so a point where the source overruns its
-- own reading leaves the row unsolvable; what remains is the conclusion
-- at the two bounds the statement itself fixes.
----------------------------------------------------------------------

mapGrow₀ : Confirms (map-frame-carried Grow₀.ac 0 0 grow src₀ root
  Grow₀.ψ Grow₀.Rst Grow₀.vals Grow₀.fin Grow₀.sd Grow₀.st Below Below)
mapGrow₀ = Below , Below

mapShed₀ : Confirms (map-frame-carried Shed₀.ac 0 0 shed src₀ root
  Shed₀.ψ Shed₀.Rst Shed₀.vals Shed₀.fin Shed₀.sd Shed₀.st Below Below)
mapShed₀ = Below , Below

mapKeep₀ : Confirms (map-frame-carried Keep₀.ac 0 0 keep src₀ root
  Keep₀.ψ Keep₀.Rst Keep₀.vals Keep₀.fin Keep₀.sd Keep₀.st Below Below)
mapKeep₀ = Below , Below

mapGrow₁ : Confirms (map-frame-carried Grow₁.ac 0 0 grow src₁ root
  Grow₁.ψ Grow₁.Rst Grow₁.vals Grow₁.fin Grow₁.sd Grow₁.st Below Below)
mapGrow₁ = Below , Below

mapShed₁ : Confirms (map-frame-carried Shed₁.ac 0 0 shed src₁ root
  Shed₁.ψ Shed₁.Rst Shed₁.vals Shed₁.fin Shed₁.sd Shed₁.st Below Below)
mapShed₁ = Below , Below

mapKeep₁ : Confirms (map-frame-carried Keep₁.ac 0 0 keep src₁ root
  Keep₁.ψ Keep₁.Rst Keep₁.vals Keep₁.fin Keep₁.sd Keep₁.st Below Below)
mapKeep₁ = Below , Below

mapGrowS : Confirms (map-frame-carried GrowS.ac 0 0 grow srcS root
  GrowS.ψ GrowS.Rst GrowS.vals GrowS.fin GrowS.sd GrowS.st Below Below)
mapGrowS = Below , Below

mapShedS : Confirms (map-frame-carried ShedS.ac 0 0 shed srcS root
  ShedS.ψ ShedS.Rst ShedS.vals ShedS.fin ShedS.sd ShedS.st Below Below)
mapShedS = Below , Below

mapKeepS : Confirms (map-frame-carried KeepS.ac 0 0 keep srcS root
  KeepS.ψ KeepS.Rst KeepS.vals KeepS.fin KeepS.sd KeepS.st Below Below)
mapKeepS = Below , Below
