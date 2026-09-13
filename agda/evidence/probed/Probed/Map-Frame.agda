-- THE TEMPLATE FRAME, INSTANTIATED — a map handed what its source
-- really emits and asked what the template makes of it.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THIS STATEMENT AND WHY NOW.  Three witnesses pin this statement's
-- ends apart, and none of them instantiates the form that survived: two
-- kill candidate residues in a predicate they RESTATE locally, and the
-- third killed the CURRENCY the whole family was denominated in.  A
-- locally restated predicate agreeing with a postulate is not the
-- postulate holding — so what the statement says at a point the walk can
-- reach has never been run, and the class it carries rests on arguments
-- about what is false.

-- THE POINT IS THE WALK'S OWN, AND THE PAYLOAD IS REACHED BY RUNNING.
-- Each row subscribes the SOURCE under a map frame, exactly as the map
-- arm does, splits the burst the subscription produced, and hands the
-- frame that.  The incoming bound is the source's own payload pair,
-- which is what the walk has at this arm — so the incoming values are
-- ones this source can actually emit rather than the strongest the bound
-- admits.

-- THE HYPOTHESIS IS DECIDED, WHICH IS WHERE A REFUTATION WOULD SURFACE.
-- `Below` spends the decision procedure at the probe's own numerals, and
-- the payload hypothesis is now a PAIR of them — so a source whose
-- emissions overrun its own reading on EITHER component leaves the row
-- unsolvable rather than letting it through.

-- WHAT THE FAMILY IS BUILT TO MOVE.  The template is the first axis, at
-- the three things one can do to an argument's depth: ADD a layer, DROP
-- the argument for something shallower, and PRESERVE it.  The two ends
-- of the statement coincide at the middle two and come apart at the
-- first, so a bound quietly collapsed onto its neighbour would still
-- pass the preserving rows and fail the growing ones.  The source is the
-- second axis, at three depths, so no row is green because the reading
-- it compared was zero on both sides.

-- AND THE DELIVERY COUNT IS THE THIRD, WHICH IS THE AXIS THAT KILLED THE
-- PREDECESSOR.  A template may FOLD over its argument, and then what it
-- hands back rises one layer per DELIVERY the payload carries — a
-- quantity the earlier currency projected away, so one bound admitted
-- payloads delivering one, three and five alike while the outputs came
-- back three figures apart.  The folding rows below run exactly that
-- family against the pair, where the count is half the bound: they are
-- the rows that say the widening reached the region that killed the
-- predecessor, and not merely that it typechecks.

-- AND THE STORE IS THE FOURTH, WHICH IS WHAT THE DEEPEST SOURCE IS FOR.
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
-- TARGET: map-frame-carried @5c8de1
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
open import Rx.Hop-Depth using (Rd; Rd₃; rdᵉ; ε)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; subscribeE;
  rootWitness; rootTri; root; _↠_; sched-init; st-init; map-f;
  splitBurst; stepFrame; stHop)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Carried using (valsRd)
open import Verify-Rank-Sufficient.Push-Carried using (map-frame-carried;
  mapRd)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FRAME'S OWN POINT, assembled exactly as the walk's map arm
-- assembles it: subscribe the source under the frame and hand the frame
-- what the burst hands it.  A map mints no node, so the store the frame
-- is given is the one the subscription left, and the incoming bound is
-- the source's own payload pair — the expression the walk spends.
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
  r = subscribeE {lo = n} ac b {below-ctx b} (map-f fn ↠ root) 0 0
        (sched-init prog ins) (st-init prog)

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
  sf = stepFrame {lo = n} ac 0 0 (map-f fn) root vals fin sd st

  -- the incoming bound is not ours to choose: the walk enters this frame
  -- at the source's own payload pair, and the outgoing one is the
  -- residue the statement spells from it
  Rin : Rd
  Rin = proj₂ (rdᵉ ψ ε b)

  Rout : Rd
  Rout = mapRd ψ Rin fn

  -- the store bound is quantified over every natural, so it is taken
  -- TIGHT: whatever the store read on the way in
  Rst : ℕ
  Rst = stHop ψ st

  -- radix 1000, low digit first: the incoming bound, what the frame was
  -- actually handed, the outgoing bound, what it gave back.  The first
  -- two say the hypothesis has margin or none; the last two say whether
  -- the template moved the reading and whether the bound moved with it.
  -- Both halves of the pair are packed, since the whole finding behind
  -- this statement is that ONE of them is not enough
  counts : ℕ
  counts = proj₁ Rin
         + 1000 * proj₁ (valsRd ψ (obs natᵗ) vals)
         + 1000000 * proj₁ Rout
         + 1000000000 * proj₁ (valsRd ψ (obs natᵗ) (proj₁ sf))

  hops : ℕ
  hops = proj₂ Rin
       + 1000 * proj₂ (valsRd ψ (obs natᵗ) vals)
       + 1000000 * proj₂ Rout
       + 1000000000 * proj₂ (valsRd ψ (obs natᵗ) (proj₁ sf))

  -- the store on the way in and on the way out, which a map must leave
  -- alone
  stores : ℕ
  stores = Rst + 1000 * stHop ψ (proj₂ (proj₂ (proj₂ (proj₂ sf))))

----------------------------------------------------------------------
-- THE CLOSED CONTEXT, where the reading of an input cannot enter and
-- every figure is the term's own.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

----------------------------------------------------------------------
-- THE FOUR TEMPLATES, which are the four things a template can do to
-- what it is handed.  `grow` re-wraps, so one application adds exactly
-- the layer the reading's map clause charges; `shed` ignores its
-- argument entirely and returns a literal, which is the shape that
-- killed the freely quantified form; `keep` hands the argument straight
-- back, where the two ends of the statement coincide.  `fold` is the
-- fourth and the one the predecessor could not see: it scans over the
-- DELIVERIES of its argument, so what it returns rises with a quantity
-- the earlier currency projected away.
----------------------------------------------------------------------

grow : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
grow = strmᵗ (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))

shed : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
shed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

keep : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
keep = varᵗ (here refl)

deepen : ∀ {Δᵍ Δ Θ} → Fn Γ₀ Δᵍ Δ Θ (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

seed₀ : ∀ {Δᵍ Δ Θ} → Tm Γ₀ Δᵍ Δ Θ (obs natᵗ)
seed₀ = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

fold : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
fold = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen seed₀
         (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))))

----------------------------------------------------------------------
-- THE SHALLOW SOURCES, so no row compares zero against zero on both
-- sides.  `src₀` emits an observable as shallow as the type allows;
-- `src₁` emits one already carrying a flattener, so its own reading is
-- positive and the incoming bound is a real bound rather than a floor.
----------------------------------------------------------------------

src₀ : Closed Γ₀ (obs natᵗ)
src₀ = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

src₁ : Closed Γ₀ (obs natᵗ)
src₁ = ofᵉ (strmᵗ (mergeAllᵉ nothing
         (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])

----------------------------------------------------------------------
-- AND THE THREE THAT DIFFER ONLY IN HOW MANY DELIVERIES THE PAYLOAD
-- CARRIES, which is the axis the predecessor currency was blind to.
-- Each emits ONE observable, and that observable delivers one, three
-- and five values — so the hop side of the incoming pair is identical
-- across all three and only the count side moves.
----------------------------------------------------------------------

srcD₁ : Closed Γ₀ (obs natᵗ)
srcD₁ = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

srcD₃ : Closed Γ₀ (obs natᵗ)
srcD₃ = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ [])

srcD₅ : Closed Γ₀ (obs natᵗ)
srcD₅ = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ []))
          ∷ [])

----------------------------------------------------------------------
-- AND A SOURCE WHOSE SUBSCRIPTION LEAVES SOMETHING IN THE STORE, which
-- the ones above cannot do.  A map mints no node, so the store the frame
-- is handed is whatever its SOURCE installed — and a literal installs
-- nothing, which is why the store conjunct reads zero on both sides at
-- every point above and compares nothing.  A fold does install one, and
-- an accumulator that is an OBSERVABLE is what the reading prices above
-- zero, so `srcS` is the shape in which the store half of this statement
-- is a comparison at all.
----------------------------------------------------------------------

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

srcS : Closed Γ₀ (obs natᵗ)
srcS = scanᵉ deepen liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))

----------------------------------------------------------------------
-- THE POINTS.  Every template at every source, because which rows can
-- fail is not decidable from the template alone: a template that DROPS
-- depth is unfalsifiable at a source reading zero and load-bearing one
-- layer up, where it must return a payload under a bound its own body no
-- longer justifies.
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

module Fold₁ = Ap ins₀ fold srcD₁
module Fold₃ = Ap ins₀ fold srcD₃
module Fold₅ = Ap ins₀ fold srcD₅

----------------------------------------------------------------------
-- BOTH SIDES PINNED, so the rows below are green with a margin someone
-- can read rather than merely green.  Read low digit first at radix
-- 1000: incoming bound, handed, outgoing bound, returned.
--
-- WHICH ROWS COULD HAVE FAILED, since two of the twelve could not.  The
-- GROWING rows are load-bearing and TIGHT — returned equals the outgoing
-- bound at all three sources, so one extra layer anywhere in the
-- template's body would have taken the conclusion out.  The DROPPING row
-- is load-bearing at the two deeper sources, where the payload falls to
-- zero under a bound that stays where the source left it; at the shallow
-- source it and the PRESERVING row read zero in every hop digit and are
-- DEGENERATE there, kept as the floor and buying nothing.
--
-- AND THE HYPOTHESIS IS SATURATED, WHICH IS THE HALF THAT SURPRISES.
-- What the frame is handed equals the source's own reading at both
-- sources and on BOTH components, so the incoming bound has no margin at
-- any point here: the decision procedure discharging it is deciding two
-- equalities, and a source emitting one layer or one delivery more than
-- its reading admits would have left every row unsolvable rather than
-- merely loose.
--
-- AND A DROPPING TEMPLATE'S OUTGOING BOUND DOES NOT DROP WITH IT: the
-- residue reads the template under an environment binding the incoming
-- pair and JOINS the incoming hop back in, so the statement's right-hand
-- end tracks the SOURCE as well as the body.  That is slack in the
-- reading's own map clause rather than in this statement.
----------------------------------------------------------------------

grow₀-counts : Grow₀.counts ≡ 1001001001
grow₀-counts = refl

grow₀-hops : Grow₀.hops ≡ 1001000000
grow₀-hops = refl

grow₀-stores : Grow₀.stores ≡ 0
grow₀-stores = refl

shed₀-counts : Shed₀.counts ≡ 1001001001
shed₀-counts = refl

shed₀-hops : Shed₀.hops ≡ 0
shed₀-hops = refl

keep₀-counts : Keep₀.counts ≡ 1001001001
keep₀-counts = refl

keep₀-hops : Keep₀.hops ≡ 0
keep₀-hops = refl

grow₁-counts : Grow₁.counts ≡ 1001001001
grow₁-counts = refl

grow₁-hops : Grow₁.hops ≡ 2002001001
grow₁-hops = refl

shed₁-counts : Shed₁.counts ≡ 1001001001
shed₁-counts = refl

shed₁-hops : Shed₁.hops ≡ 1001001
shed₁-hops = refl

keep₁-counts : Keep₁.counts ≡ 1001001001
keep₁-counts = refl

keep₁-hops : Keep₁.hops ≡ 1001001001
keep₁-hops = refl

----------------------------------------------------------------------
-- AND THE THREE OVER A STORE THAT READS POSITIVE, which is where the
-- second conjunct stops being a comparison of nothing.  A map that
-- deepened any node would overrun a bound taken at exactly what it was
-- handed, and the rows above could not have said so at zero.
----------------------------------------------------------------------

growS-counts : GrowS.counts ≡ 1001001001
growS-counts = refl

growS-hops : GrowS.hops ≡ 4004003003
growS-hops = refl

growS-stores : GrowS.stores ≡ 3003
growS-stores = refl

shedS-counts : ShedS.counts ≡ 1001001001
shedS-counts = refl

shedS-hops : ShedS.hops ≡ 3003003
shedS-hops = refl

keepS-counts : KeepS.counts ≡ 1001001001
keepS-counts = refl

keepS-hops : KeepS.hops ≡ 3003003003
keepS-hops = refl

----------------------------------------------------------------------
-- AND THE DELIVERY FAMILY, WHICH IS WHAT SAYS THE WIDENING REACHED THE
-- REGION THAT KILLED ITS PREDECESSOR.  Three sources whose payloads
-- differ ONLY in how many values the delivered observable carries, under
-- a template that folds over exactly that.  LOAD-BEARING as a TRIPLE:
-- one figure is a height and two are a direction, and three are what say
-- the residue tracks the deliveries rather than saturating.  Under the
-- earlier currency a single bound admitted all three payloads while the
-- outputs came back three figures apart; here the count digit of the
-- incoming bound moves with the source, which is the whole repair.  It
-- is TIGHT on both components at all three: the counts go one, three,
-- five in and one, nine, twenty-five out, and the hops three, five,
-- seven — so the residue tracks the deliveries QUADRATICALLY, and a
-- bound that merely saturated would have shown as a figure standing
-- still across the triple.
----------------------------------------------------------------------

fold₁-counts : Fold₁.counts ≡ 1001001001
fold₁-counts = refl

fold₁-hops : Fold₁.hops ≡ 3003000000
fold₁-hops = refl

fold₃-counts : Fold₃.counts ≡ 9009003003
fold₃-counts = refl

fold₃-hops : Fold₃.hops ≡ 5005000000
fold₃-hops = refl

fold₅-counts : Fold₅.counts ≡ 25025005005
fold₅-counts = refl

fold₅-hops : Fold₅.hops ≡ 7007000000
fold₅-hops = refl

----------------------------------------------------------------------
-- THE TARGET, AT THE POINTS THE RUNS REACHED.  The hypotheses are
-- DECIDED rather than assumed, so a point where the source overruns its
-- own reading on either component leaves the row unsolvable; what
-- remains is the conclusion at the two bounds the statement itself
-- fixes.
----------------------------------------------------------------------

mapGrow₀ : Confirms (map-frame-carried {lo = 0} Grow₀.ac 0 0 grow root
  Grow₀.ψ Grow₀.Rin Grow₀.Rst Grow₀.vals Grow₀.fin Grow₀.sd Grow₀.st
  (Below , Below) Below)
mapGrow₀ = (Below , Below) , Below

mapShed₀ : Confirms (map-frame-carried {lo = 0} Shed₀.ac 0 0 shed root
  Shed₀.ψ Shed₀.Rin Shed₀.Rst Shed₀.vals Shed₀.fin Shed₀.sd Shed₀.st
  (Below , Below) Below)
mapShed₀ = (Below , Below) , Below

mapKeep₀ : Confirms (map-frame-carried {lo = 0} Keep₀.ac 0 0 keep root
  Keep₀.ψ Keep₀.Rin Keep₀.Rst Keep₀.vals Keep₀.fin Keep₀.sd Keep₀.st
  (Below , Below) Below)
mapKeep₀ = (Below , Below) , Below

mapGrow₁ : Confirms (map-frame-carried {lo = 0} Grow₁.ac 0 0 grow root
  Grow₁.ψ Grow₁.Rin Grow₁.Rst Grow₁.vals Grow₁.fin Grow₁.sd Grow₁.st
  (Below , Below) Below)
mapGrow₁ = (Below , Below) , Below

mapShed₁ : Confirms (map-frame-carried {lo = 0} Shed₁.ac 0 0 shed root
  Shed₁.ψ Shed₁.Rin Shed₁.Rst Shed₁.vals Shed₁.fin Shed₁.sd Shed₁.st
  (Below , Below) Below)
mapShed₁ = (Below , Below) , Below

mapKeep₁ : Confirms (map-frame-carried {lo = 0} Keep₁.ac 0 0 keep root
  Keep₁.ψ Keep₁.Rin Keep₁.Rst Keep₁.vals Keep₁.fin Keep₁.sd Keep₁.st
  (Below , Below) Below)
mapKeep₁ = (Below , Below) , Below

mapGrowS : Confirms (map-frame-carried {lo = 0} GrowS.ac 0 0 grow root
  GrowS.ψ GrowS.Rin GrowS.Rst GrowS.vals GrowS.fin GrowS.sd GrowS.st
  (Below , Below) Below)
mapGrowS = (Below , Below) , Below

mapShedS : Confirms (map-frame-carried {lo = 0} ShedS.ac 0 0 shed root
  ShedS.ψ ShedS.Rin ShedS.Rst ShedS.vals ShedS.fin ShedS.sd ShedS.st
  (Below , Below) Below)
mapShedS = (Below , Below) , Below

mapKeepS : Confirms (map-frame-carried {lo = 0} KeepS.ac 0 0 keep root
  KeepS.ψ KeepS.Rin KeepS.Rst KeepS.vals KeepS.fin KeepS.sd KeepS.st
  (Below , Below) Below)
mapKeepS = (Below , Below) , Below

mapFold₁ : Confirms (map-frame-carried {lo = 0} Fold₁.ac 0 0 fold root
  Fold₁.ψ Fold₁.Rin Fold₁.Rst Fold₁.vals Fold₁.fin Fold₁.sd Fold₁.st
  (Below , Below) Below)
mapFold₁ = (Below , Below) , Below

mapFold₃ : Confirms (map-frame-carried {lo = 0} Fold₃.ac 0 0 fold root
  Fold₃.ψ Fold₃.Rin Fold₃.Rst Fold₃.vals Fold₃.fin Fold₃.sd Fold₃.st
  (Below , Below) Below)
mapFold₃ = (Below , Below) , Below

mapFold₅ : Confirms (map-frame-carried {lo = 0} Fold₅.ac 0 0 fold root
  Fold₅.ψ Fold₅.Rin Fold₅.Rst Fold₅.vals Fold₅.fin Fold₅.sd Fold₅.st
  (Below , Below) Below)
mapFold₅ = (Below , Below) , Below
