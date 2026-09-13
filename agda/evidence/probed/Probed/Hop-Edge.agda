-- THE HOP EDGE, INSTANTIATED — a flattener's frame handed real
-- observables and asked what it gives back, read one `suc` above what
-- it was handed.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THIS IS THE FIRST FORM OF THE CLAIM THAT CAN BE INSTANTIATED AT
-- ALL.  The flattener's obligation used to be a whole CLAUSE of the
-- walk, quantified over every program the arm admits, with no concrete
-- point to take it at.  Stated at the frame it is an ordinary
-- application: three literal arguments, a store the run built, and two
-- comparisons that compute.  So the region carrying the exchange
-- between the two currencies has coverage for the first time.

-- BOTH CONJUNCTS ARE LOAD-BEARING, AND ONLY BECAUSE OF THE TYPE AND THE
-- SEED.  A flattener over a stream of NATS hands back data payloads,
-- which the reading charges zero by construction — a row there would
-- compare zero against a successor and could not have failed.  So the
-- frame here flattens a stream of streams of streams, where what it
-- gives back is itself an observable and reads what that observable
-- reads.  The store half needs the same care from the other side: what
-- a subscribed inner installs is its fold's SEED, so a seed of depth
-- zero would leave the store conjunct comparing zero as well.  The seed
-- below is flattened once for exactly that reason, and every figure the
-- pins report is positive.

-- WHAT THE FAMILIES ARE BUILT TO MOVE.  The inner is a fold that
-- re-wraps its accumulator as it runs, so the values the frame hands
-- back read DEEPER the longer the inner's source runs, while the bound
-- it is held to is read off the OUTER source and has no term-level
-- reason to follow them.  That is the one shape in which the exchange
-- could cost more than the `suc` the entry invariant pays, and it is
-- the shape that refuted two earlier readings of this measure.  The
-- third family doubles the step's wrapping per refold, which is the
-- rate no coefficient reached when the fold clause was a closed form.

-- WHAT THE ROWS SAY, AND THE MARGIN IS EXACTLY ONE, EVERYWHERE.  The
-- frame gives back precisely what it was handed and not one more — two
-- against two, three against three, five against five at the doubling
-- step, one at the park — so the claim holds with a whole unit of slack
-- at every point reached, and the slack is CONSTANT rather than
-- closing, which is the shape a crossing would have shown up in.  Both
-- rates move together besides: the handed reading, the returned
-- reading, what the store reads afterwards and the rank all climb
-- exactly one per source literal, so no row is green because something
-- stalled.

-- AND THE CONSTANT IS THE FINDING THAT COSTS SOMETHING.  Nothing here
-- SPENDS the `suc` the target is stated at; every run affords it.  So
-- the statement has a whole unit of room in it, and the stronger form
-- holding the frame to what it was handed is what these rows are
-- evidence for — worth knowing if the proof of the weaker one stalls,
-- since the arm consuming it needs only `Rin ≤ suc Rin` and would take
-- either.

-- THE BOUNDARY, and there are two.  No row reaches a frame whose rank
-- is SPENT: the witness is taken at a root, and a flattener's own
-- reading is a successor by construction, so the dry clause of
-- `subscribeInner` is unreachable from a root and nothing here says
-- what the frame hands back once the descent has run out.  And every
-- fold family below completes inside its own subscribe frame; only the
-- park family holds an inner open, and it does so through a scripted
-- slot rather than through the program, so the queue is reached at one
-- shape and one limit.
--
-- TARGET: thru-outer-frame-carried @260099
module Probed.Hop-Edge where

open import Data.Bool using (Bool; false)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
  ofᵉ; mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; strmᵗ; nat̂; fstᵗ;
  varᵗ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; depthᵉ; rdᵉ; ε)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState;
  AllOp; subscribeE; rootWitness; rootTri; root; _↠_; sched-init; st-init;
  mintNode; installNode; mergeAll-st; switch-st; exhaust-st; thru-outer;
  mergeAllᵒ; switchᵒ; exhaustᵒ; splitBurst; stepFrame; stHop)
open import Verify-Rank-Sufficient.Carried using (valsRd)
open import Verify-Rank-Sufficient.Push-Carried
  using (thru-outer-frame-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FRAME'S OWN POINT, assembled exactly as the walk's flattener arm
-- assembles it: mint the node, install the merge state, subscribe the
-- outer under the frame, and hand the frame what the burst hands it.
-- The values are REACHED BY RUNNING — `splitBurst` of the real burst is
-- what `pushBurst` passes — rather than written down, and the store is
-- the one the subscription left behind.
--
-- The rows themselves cannot live here: the decision procedure needs
-- closed numerals, and nothing under a parameter reduces.
----------------------------------------------------------------------

module Ap {n} {Γ : Ctx n} (ins : Slots Γ) (op : AllOp)
          (node : NodeState Γ) (prog : Closed Γ (obs natᵗ))
          (src : Closed Γ (obs (obs natᵗ))) where

  ψ : Fin n → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri prog ins)
  ac = rootWitness prog ins

  nid : NodeId
  nid = proj₁ (mintNode (sched-init prog ins))

  r : Stream Γ (obs (obs natᵗ)) × Sched Γ × EvalSt prog
  r = subscribeE ac src (thru-outer op nid ↠ root) 0 0
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
  sf = stepFrame ac 0 0 (thru-outer op nid) root vals fin sd st

  -- the bound the arriving observables are held to — the source's own
  -- payload PAIR, which is what the walk enters this frame at — and the
  -- rank the machine entered at
  Rin : Rd
  Rin = proj₂ (rdᵉ ψ ε src)

  bound : ℕ
  bound = depthᵉ ψ src

  rank : ℕ
  rank = proj₁ (proj₂ (rootTri prog ins))

  -- radix 1000, low digit first: what the frame was handed, the bound,
  -- what it gave back, what its store reads afterwards, the rank
  packed : ℕ
  packed = proj₂ (valsRd ψ (obs (obs natᵗ)) vals)
         + 1000 * bound
         + 1000000 * proj₂ (valsRd ψ (obs natᵗ) (proj₁ sf))
         + 1000000000 * stHop ψ (proj₂ (proj₂ (proj₂ (proj₂ sf))))
         + 1000000000000 * rank

  -- and the DELIVERY side of the same pair, which the hop figure
  -- projects away: handed, the bound, returned
  counts : ℕ
  counts = proj₁ (valsRd ψ (obs (obs natᵗ)) vals)
         + 1000 * proj₁ Rin
         + 1000000 * proj₁ (valsRd ψ (obs natᵗ) (proj₁ sf))

----------------------------------------------------------------------
-- THE CLOSED CONTEXT, where the reading of an input cannot enter and
-- every figure is the term's own.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE INNER: a fold that deepens what it hands out, seeded with
-- something the store can read.  `deepen` wraps its accumulator once
-- per delivery and `deepen2` twice, so the values they emit climb with
-- the source at two different rates; the seed is flattened once so the
-- node a subscription installs for it does not read zero.
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

----------------------------------------------------------------------
-- THE OUTER, at two lengths and two rates.  The frame's arriving
-- observables are the literals of this source; its OUTPUTS are what
-- those observables deliver, which is where the exchange is made.
----------------------------------------------------------------------

src₁ src₂ src₃ : Closed Γ₀ (obs (obs natᵗ))
src₁ = ofᵉ (strmᵗ (folded deepen (nat̂ 0 ∷ [])) ∷ [])
src₂ = ofᵉ (strmᵗ (folded deepen (nat̂ 0 ∷ nat̂ 1 ∷ [])) ∷ [])
src₃ = ofᵉ (strmᵗ (folded deepen2 (nat̂ 0 ∷ nat̂ 1 ∷ [])) ∷ [])

mrg : Closed Γ₀ (obs (obs natᵗ)) → Closed Γ₀ (obs natᵗ)
mrg = mergeAllᵉ nothing

module A₁ = Ap ins₀ mergeAllᵒ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₁) src₁
module A₂ = Ap ins₀ mergeAllᵒ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₂) src₂
module A₃ = Ap ins₀ mergeAllᵒ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₃) src₃

----------------------------------------------------------------------
-- THE OTHER TWO OPERATORS, at the second family's program.  The
-- statement quantifies over the operator and the three consume an
-- arriving inner by three different rules — merge keeps every one,
-- switch kills what it already holds, exhaust drops while busy — so a
-- row at merge alone would leave two thirds of the quantifier with no
-- coverage.  The rank the machine enters at is the same, because the
-- reading charges the three flatteners identically.
----------------------------------------------------------------------

module AS = Ap ins₀ switchᵒ (switch-st nothing false)
              (switchAllᵉ src₂) src₂
module AE = Ap ins₀ exhaustᵒ (exhaust-st false false)
              (exhaustAllᵉ src₂) src₂

----------------------------------------------------------------------
-- THE PARK FAMILY, which is the only one whose store holds a QUEUE.
-- An inner over a scripted slot with an asynchronous tail does not
-- finish inside its own subscribe frame, so the limit below refuses the
-- second arrival and the frame writes it into the node instead of
-- subscribing it.  The map's template drops its argument and emits a
-- flattened literal, so the queued observable reads positive and the
-- store conjunct is comparing something.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insA : Slots Γ₁
insA zero = scripted (cold (7 ∷ []) (after 0 , 9 ∷ []))

wrap : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
wrap = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])))

innerLive : Closed Γ₁ (obs natᵗ)
innerLive = mapᵉ wrap (input zero)

srcP : Closed Γ₁ (obs (obs natᵗ))
srcP = ofᵉ (strmᵗ innerLive ∷ strmᵗ innerLive ∷ [])

module AP = Ap insA mergeAllᵒ (mergeAll-st {t = obs natᵗ} (just 1) 0 [] false)
              (mergeAllᵉ (just 1) srcP) srcP

----------------------------------------------------------------------
-- BOTH SIDES PINNED, so the rows below are green with a margin someone
-- can read rather than merely green.  Every figure is LOAD-BEARING: a
-- handed reading that stalled across the first two would say the fold
-- clause is blind to what it folds over, a third that failed to track
-- the doubling step would say the clause is a closed form again, and
-- either returned figure overtaking the bound it is compared against
-- would refute the target outright.
----------------------------------------------------------------------

packed₁-is : A₁.packed ≡ 3002002002002
packed₁-is = refl

packed₂-is : A₂.packed ≡ 4003003003003
packed₂-is = refl

packed₃-is : A₃.packed ≡ 6005005005005
packed₃-is = refl

packedP-is : AP.packed ≡ 2001001001001
packedP-is = refl

packedS-is : AS.packed ≡ 4003003003003
packedS-is = refl

packedE-is : AE.packed ≡ 4003003003003
packedE-is = refl

-- AND THE DELIVERY SIDE, which the hop figures project away.  Read low
-- first: handed, bound, returned.  The hypothesis is SATURATED at every
-- row — what the frame is handed equals the source's own count exactly,
-- so a source delivering one more than its reading admits leaves the row
-- unsolvable — and the conclusion has margin, the flattener handing back
-- a single delivery under a bound of two wherever the outer carries two.
counts₁-is : A₁.counts ≡ 1001001
counts₁-is = refl

counts₂-is : A₂.counts ≡ 1002002
counts₂-is = refl

counts₃-is : A₃.counts ≡ 1002002
counts₃-is = refl

countsP-is : AP.counts ≡ 1002002
countsP-is = refl

countsS-is : AS.counts ≡ 1002002
countsS-is = refl

countsE-is : AE.counts ≡ 1002002
countsE-is = refl


----------------------------------------------------------------------
-- THE TARGET, AT THE POINTS THE RUNS REACHED.  The premise is the entry
-- invariant's rank conjunct and the two hypotheses are the walk's own
-- conclusion at the source; all three are DECIDED rather than assumed,
-- so a point the machine could not have entered fails here rather than
-- passing quietly.
----------------------------------------------------------------------

hopRow₁ : Confirms (thru-outer-frame-carried A₁.ac 0 0 mergeAllᵒ A₁.nid root
  A₁.ψ A₁.Rin A₁.rank Below A₁.vals A₁.fin A₁.sd A₁.st
  (Below , Below) Below)
hopRow₁ = (Below , Below) , Below

hopRow₂ : Confirms (thru-outer-frame-carried A₂.ac 0 0 mergeAllᵒ A₂.nid root
  A₂.ψ A₂.Rin A₂.rank Below A₂.vals A₂.fin A₂.sd A₂.st
  (Below , Below) Below)
hopRow₂ = (Below , Below) , Below

hopRow₃ : Confirms (thru-outer-frame-carried A₃.ac 0 0 mergeAllᵒ A₃.nid root
  A₃.ψ A₃.Rin A₃.rank Below A₃.vals A₃.fin A₃.sd A₃.st
  (Below , Below) Below)
hopRow₃ = (Below , Below) , Below

hopRowP : Confirms (thru-outer-frame-carried AP.ac 0 0 mergeAllᵒ AP.nid root
  AP.ψ AP.Rin AP.rank Below AP.vals AP.fin AP.sd AP.st
  (Below , Below) Below)
hopRowP = (Below , Below) , Below

hopRowS : Confirms (thru-outer-frame-carried AS.ac 0 0 switchᵒ AS.nid root
  AS.ψ AS.Rin AS.rank Below AS.vals AS.fin AS.sd AS.st
  (Below , Below) Below)
hopRowS = (Below , Below) , Below

hopRowE : Confirms (thru-outer-frame-carried AE.ac 0 0 exhaustᵒ AE.nid root
  AE.ψ AE.Rin AE.rank Below AE.vals AE.fin AE.sd AE.st
  (Below , Below) Below)
hopRowE = (Below , Below) , Below
