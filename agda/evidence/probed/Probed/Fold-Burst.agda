-- WHAT A FOLD'S BURST LEAVES BEHIND, INSTANTIATED — the statement that
-- replaced the frame-local one, at the machine's own seed.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THIS ONE IS PROBEABLE despite being stated over a store: every
-- quantity in it computes.  The seed is NAMED by the statement, so the
-- store the burst is pushed into is built here exactly as the walk's
-- own scan arm builds it — mint, install the evaluated seed, subscribe
-- the source under `scan-f … ↠ κ`, push.  Nothing is a record written
-- by hand, and the two premises are arithmetic comparisons the decision
-- procedure discharges at each point.
--
-- THE AXES THAT COULD HAVE CROSSED, AND THE TWO THAT COULD NOT.  A
-- fold's only measure-side quantity is the accumulator it writes: the
-- step iterated once per delivered value, against a reading whose fold
-- clause iterates the same step over the source's TOP COUNT from the
-- seed's own reading.  So the rows move what feeds that count — step
-- depth at one, two and three layers per refold; source length to four;
-- a source whose every delivery is itself a flattened pair, which is
-- where the reading spends a PRODUCT rather than a literal count; a
-- limited flattener, which queues inners into a node the run mints; a
-- fold under a fold; and a seed that reads above the floor.  The margin
-- is CONSTANT along every family and never closes, which is the shape a
-- crossing would have shown up in.
--
-- AND THE CONTINUATION IS INERT, which is a finding rather than a gap:
-- `stepFrame` at a `scan-f` dispatches on the stored node and names
-- neither `κ` nor the witness nor the clock, and the only events a fold
-- re-emits are its own values — so the rows below, all taken at the
-- root, are evidence at EVERY continuation rather than at one.  The
-- store's other nodes are inert for the same kind of reason: a fold
-- writes one node and carries the rest through untouched, so a deeper
-- foreign node raises the incoming reading the premise already bounds
-- by exactly what it raises the outgoing one, and no instantiation of
-- that axis could have refuted anything.
--
-- THE BOUNDARY.  Every row is a SUBSCRIBE burst; no row reaches an
-- arrival or a drain step, so nothing here says what the loop preserves
-- once the fold is live — that is the drain row's subject.  Lengths run
-- to four and layers to three, because a row costs a whole walk.
--
-- TARGET: scan-burst-carried @c66599
module Probed.Fold-Burst where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ; input; evalTm)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; root; scan-f;
  scan-st; _↠_; mintNode; installNode; subscribeE; pushBurst; stHop;
  rootWitness; sched-init; st-init)
open import Verify-Rank-Sufficient.Carried using (burstHop)
open import Verify-Rank-Sufficient.Push-Carried using (scan-burst-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- ONE COLD INPUT WHOSE SYNCHRONOUS PART LENGTHENS ROW BY ROW.  That
-- length is the delivery count the fold refolds against, and it is the
-- axis the reading's fold clause has to price.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insAt : List ℕ → Slots Γ₁
insAt xs zero = scripted (cold xs (after 0 , 9 ∷ []))

Step : Set
Step = Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)

Seed : Set
Seed = Tm Γ₁ [] [] [] (obs natᵗ)

Src : Set
Src = Closed Γ₁ natᵗ

----------------------------------------------------------------------
-- THE STEPS: one, two and three fresh layers per refold.  A step that
-- did not deepen could not have failed, so none is offered.
----------------------------------------------------------------------

step1 : Step
step1 = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

step2 : Step
step2 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
          (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

step3 : Step
step3 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
          (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ []))) ∷ [])))

----------------------------------------------------------------------
-- THE SOURCES, each feeding the refold count a different way.
----------------------------------------------------------------------

burst6 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst6 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))

src : Src
src = mergeAllᵉ nothing (mapᵉ burst6 (input zero))

-- every delivery is itself a flattened pair, so the count the reading
-- spends is a PRODUCT rather than a literal list length
burstDeep : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burstDeep = strmᵗ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))
       ∷ strmᵗ (ofᵉ (nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))
       ∷ [])))

srcDeep : Src
srcDeep = mergeAllᵉ nothing (mapᵉ burstDeep (input zero))

-- a limit queues inners into the flattener's own node, which is the one
-- store quantity the run mints rather than inherits
srcLim : Src
srcLim = mergeAllᵉ (just 1) (mapᵉ burstDeep (input zero))

idStep : Fn Γ₁ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ
idStep = fstᵗ (varᵗ (here refl))

srcScan : Src
srcScan = scanᵉ idStep (nat̂ 0) (mergeAllᵉ nothing (mapᵉ burst6 (input zero)))

seed0 : Seed
seed0 = strmᵗ emptyᵉ

seedLive : Seed
seedLive = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ [])))

----------------------------------------------------------------------
-- THE POINT, BUILT AS THE WALK BUILDS IT.  `nid` and the schedule come
-- off `mintNode`, the store off `installNode` at the evaluated seed,
-- and the burst off a real subscribe — so the tie the statement rests
-- on is the machine's and not this file's.
----------------------------------------------------------------------

prog : Step → Seed → Src → Closed Γ₁ (obs natᵗ)
prog f z b = scanᵉ f z b

nidOf : (f : Step) (z : Seed) (b : Src) (xs : List ℕ) → NodeId
nidOf f z b xs = proj₁ (mintNode (sched-init (prog f z b) (insAt xs)))

sdOf : (f : Step) (z : Seed) (b : Src) (xs : List ℕ) → Sched Γ₁
sdOf f z b xs = proj₂ (mintNode (sched-init (prog f z b) (insAt xs)))

stOf : (f : Step) (z : Seed) (b : Src) → EvalSt (prog f z b)
stOf f z b = st-init (prog f z b)

inner : (f : Step) (z : Seed) (b : Src) (xs : List ℕ)
      → Stream Γ₁ natᵗ × Sched Γ₁ × EvalSt (prog f z b)
inner f z b xs =
  subscribeE (rootWitness (prog f z b) (insAt xs)) b
    (scan-f f (nidOf f z b xs) ↠ root) 0 0 (sdOf f z b xs)
    (installNode (nidOf f z b xs) (scan-st {t = obs natᵗ} (evalTm z))
      (stOf f z b))

out : (f : Step) (z : Seed) (b : Src) (xs : List ℕ)
    → Stream Γ₁ (obs natᵗ) × Sched Γ₁ × EvalSt (prog f z b)
out f z b xs =
  pushBurst (rootWitness (prog f z b) (insAt xs)) 0 0
    (scan-f f (nidOf f z b xs)) root
    (proj₁ (inner f z b xs)) (proj₁ (proj₂ (inner f z b xs)))
    (proj₂ (proj₂ (inner f z b xs)))

outHop : (f : Step) (z : Seed) (b : Src) (xs : List ℕ) → ℕ
outHop f z b xs =
  burstHop (slotRd (insAt xs)) (obs natᵗ) (proj₁ (out f z b xs))

outSt : (f : Step) (z : Seed) (b : Src) (xs : List ℕ) → ℕ
outSt f z b xs = stHop (slotRd (insAt xs)) (proj₂ (proj₂ (out f z b xs)))

term : (f : Step) (z : Seed) (b : Src) (xs : List ℕ) → ℕ
term f z b xs = depthᵉ (slotRd (insAt xs)) (prog f z b)

----------------------------------------------------------------------
-- THE ROWS.  Each is the target applied at its own point, so Agda
-- generates the claim from the statement as it reads and this file
-- chooses only where it is asked.  Every one is LOAD-BEARING: the
-- accumulator deepens once per delivered value at every point, so a
-- reading that charged the fold a bound flat in the delivery count
-- would cross at the second row of the first family.
----------------------------------------------------------------------

rate₁ : Confirms (scan-burst-carried
  (rootWitness (prog step1 seed0 src) (insAt (7 ∷ []))) 0 0
  step1 seed0 src (nidOf step1 seed0 src (7 ∷ [])) root
  (sdOf step1 seed0 src (7 ∷ [])) (stOf step1 seed0 src)
  (slotRd (insAt (7 ∷ []))) (term step1 seed0 src (7 ∷ []))
  Below Below Below)
rate₁ = Below , Below

rate₄ : Confirms (scan-burst-carried
  (rootWitness (prog step1 seed0 src) (insAt (7 ∷ 8 ∷ 9 ∷ 10 ∷ []))) 0 0
  step1 seed0 src (nidOf step1 seed0 src (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])) root
  (sdOf step1 seed0 src (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])) (stOf step1 seed0 src)
  (slotRd (insAt (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])))
  (term step1 seed0 src (7 ∷ 8 ∷ 9 ∷ 10 ∷ []))
  Below Below Below)
rate₄ = Below , Below

layers₃ : Confirms (scan-burst-carried
  (rootWitness (prog step3 seed0 src) (insAt (7 ∷ 8 ∷ []))) 0 0
  step3 seed0 src (nidOf step3 seed0 src (7 ∷ 8 ∷ [])) root
  (sdOf step3 seed0 src (7 ∷ 8 ∷ [])) (stOf step3 seed0 src)
  (slotRd (insAt (7 ∷ 8 ∷ []))) (term step3 seed0 src (7 ∷ 8 ∷ []))
  Below Below Below)
layers₃ = Below , Below

product : Confirms (scan-burst-carried
  (rootWitness (prog step2 seed0 srcDeep) (insAt (7 ∷ 8 ∷ []))) 0 0
  step2 seed0 srcDeep (nidOf step2 seed0 srcDeep (7 ∷ 8 ∷ [])) root
  (sdOf step2 seed0 srcDeep (7 ∷ 8 ∷ [])) (stOf step2 seed0 srcDeep)
  (slotRd (insAt (7 ∷ 8 ∷ []))) (term step2 seed0 srcDeep (7 ∷ 8 ∷ []))
  Below Below Below)
product = Below , Below

queued : Confirms (scan-burst-carried
  (rootWitness (prog step2 seed0 srcLim) (insAt (7 ∷ 8 ∷ []))) 0 0
  step2 seed0 srcLim (nidOf step2 seed0 srcLim (7 ∷ 8 ∷ [])) root
  (sdOf step2 seed0 srcLim (7 ∷ 8 ∷ [])) (stOf step2 seed0 srcLim)
  (slotRd (insAt (7 ∷ 8 ∷ []))) (term step2 seed0 srcLim (7 ∷ 8 ∷ []))
  Below Below Below)
queued = Below , Below

nested : Confirms (scan-burst-carried
  (rootWitness (prog step2 seedLive srcScan) (insAt (7 ∷ 8 ∷ []))) 0 0
  step2 seedLive srcScan (nidOf step2 seedLive srcScan (7 ∷ 8 ∷ [])) root
  (sdOf step2 seedLive srcScan (7 ∷ 8 ∷ [])) (stOf step2 seedLive srcScan)
  (slotRd (insAt (7 ∷ 8 ∷ [])))
  (term step2 seedLive srcScan (7 ∷ 8 ∷ []))
  Below Below Below)
nested = Below , Below

----------------------------------------------------------------------
-- BOTH SIDES PINNED, so the rows above are green with a margin someone
-- can read.  Radix 100: the burst's reading, the store's, and the
-- term's, at the first and last length of each family.  The store
-- figure EQUALS the burst figure at every point, which is the statement
-- of this whole restatement in a number: a fold's store is its last
-- output, so the two conjuncts are one fact.
----------------------------------------------------------------------

packedAt : (f : Step) (z : Seed) (b : Src) (xs : List ℕ) → ℕ
packedAt f z b xs = outHop f z b xs + 100 * outSt f z b xs
                  + 10000 * term f z b xs

oneLayer : ℕ
oneLayer = packedAt step1 seed0 src (7 ∷ [])
         + 1000000 * packedAt step1 seed0 src (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])

oneLayer-is : oneLayer ≡ 312424130606
oneLayer-is = refl

twoLayer : ℕ
twoLayer = packedAt step2 seed0 src (7 ∷ [])
         + 1000000 * packedAt step2 seed0 src (7 ∷ 8 ∷ [])

twoLayer-is : twoLayer ≡ 372424251212
twoLayer-is = refl
