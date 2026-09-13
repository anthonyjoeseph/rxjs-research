-- THE DOOR'S PREMISE, INSTANTIATED — and the region it reaches is the
-- one its predecessor recorded as unreachable.  The statement here used
-- to be a whole fit certificate, so a row could only stand where every
-- constructor it needed was already proven: the chains with no frame on
-- them, and nothing else.  The premise is now a WALK, comparing the
-- payload the chain is carrying against the program's own reading at
-- each re-entering frame in turn, and it computes at every chain — so
-- the two-frame chain that was pinned as a boundary is a row.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- THE LOAD-BEARING ROW IS THE FLATTENED ONE, AND IT COMES BACK TIGHT.
-- Its chain carries one flattener and the program reads one, so the
-- premise holds with NO MARGIN — a reading that charged the flattener
-- anything more, or a program reading that charged it anything less,
-- crosses here.  That is what says the count and the reading are in the
-- same currency rather than merely both being small.

-- THE BARE ROW IS DEGENERATE IN EVERY COMPONENT AND IS CLAIMED AS A
-- CONTROL RATHER THAN AS COVERAGE.  Its chain is the root, so the
-- count is nought, the payload is a number and reads nought, and the
-- rank it is held under is nought too — the conjunct could not have
-- failed.  What it pins is that the allowance serves an arrival at all
-- and that the arrival reaches a chain, which is how the flattened
-- row's own reduction is known to be asking for something.

-- THE LADDER IS WHERE THE TWO CURRENCIES COULD DIVERGE AND DO NOT, AND
-- THE WALK SAYS SO ONE FRAME AT A TIME.  A chain carrying two and then
-- three flatteners is paid by a program whose own reading grows by one
-- at each rung, and because the walk compares at every frame rather
-- than once at the end, the DEEPEST frame of each rung comes back with
-- no margin at all — one against one, two against two, three against
-- three.  A single tight row cannot say that, and neither could a sum:
-- a reading that charged a flattener once for the whole ladder, or a
-- payload that grew faster than the reading, crosses at the first rung
-- where the two disagree.

-- THE FORKED ROWS WERE BUILT TO REACH THE PREMISE'S RECURSION AND DO
-- NOT, WHICH IS THE FINDING THEY CARRY.  Two consumers standing over
-- one source — once through a SHARE, once over the SCRIPTED slot — give
-- byte-identical figures, and both report the arrival reaching ONE
-- chain carrying nought flatteners.  So the cons case of the chain
-- recursion is not a shape the door has; whatever fan-out a program
-- has is registered on the sink and entered from there, not threaded
-- through a tail at this arrival.  A repair that made the door see a
-- second chain would move both of these rows at once.
--
-- AND THE WALK SEPARATES THEM WHERE THE FIGURES CANNOT, WHICH IS WHY
-- BOTH ARE KEPT.  The shared chain ends at the SINK and the raw one at
-- the ROOT, so the first has a conjunct to discharge and the second is
-- the vacuous arm — two rows whose six figures agree in every digit and
-- whose bodies do not.  That is the distinction the predecessor's
-- single end-of-chain comparison could not draw at all.

-- AND THE SINK ROWS MEASURE THE HALF THE DOOR HANDS ON, WHICH IS WHERE
-- THE REMAINING RISK OF THIS FACE SITS.  What a chain has made of its
-- payload by the time it reaches its own sink is not a function of what
-- entered the dispatch — that is the refuted reading — so the three
-- rows below read the sink's own figure and the admitted registry's
-- beside the rank the door supplies.  At the three points the sink
-- payload and the widest admitted chain sum to one BELOW the rank, and
-- the two halves move independently of each other: the payload goes
-- nought, one, one while the registry figure goes one, one, two.  A
-- margin that were an artifact of one axis would not survive the other
-- moving, and a bound denominated in the store rather than the rank
-- crosses at the first row, where the store reads one against a rank of
-- two.

-- NOT COVERED, AND ONE ENTRY OF THIS LIST IS NOW A BOUNDARY RATHER
-- THAN A GAP.  Every row stands at ONE arrival and at the allowance's
-- FIRST step, so nothing here reaches a second arrival or the
-- allowance's second conjunct; the ladder stops at three rungs, which
-- is where the reading and the count were seen to keep step and not
-- where they were shown to.  The recursion's cons case is not missing
-- coverage — the two forked rows are the evidence that it is not
-- reachable at this point at all, and a probe cannot be written for it
-- here.  The sink rows stand at two telescopes and three programs, so
-- the constant margin is where the two currencies were seen to keep
-- step and not where they were shown to; and nothing here reaches a
-- registry admitting more than two chains.
-- TARGET: entry-drain-hop @5b9789
module Probed.Door-Fits where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; map; foldr)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂;
  ofᵉ; mapᵉ; mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Hop-Depth using (Rd; Rd₃; rdᵛ; depthᵛ; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink;
  _↠_; map-f; scan-f; take-f; from-inner; thru-outer; subscribeE;
  rootWitness; sched-init; st-init; sched-next; chainsOf; cascadeLatch;
  shareAdmit; arrTy; arrVal; RegId)
open import Verify-Rank-Sufficient using (entry-drain-hop)
open import Verify-Rank-Sufficient.Fits using (arrivalRank)
open import Verify-Rank-Sufficient.Push-Carried using (mapRd)
open import Probed.Apparatus using (Below; Confirms)

----------------------------------------------------------------------
-- THE FLATTENER COUNT, COUNTED HERE.  It is a reporting figure and not
-- a restatement: the rows that instantiate the target are generated by
-- Agda from `entry-drain-hop` further down, and this only says how many
-- re-entering frames the chain the arrival reached is carrying, which
-- is what makes a rank figure beside it readable as tight or slack.
----------------------------------------------------------------------

chainHops : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
chainHops root             = 0
chainHops (share-sink _)   = 0
chainHops (thru-outer _ _ ↠ κ) = suc (chainHops κ)
chainHops (_ ↠ κ)          = chainHops κ

----------------------------------------------------------------------
-- THE SLOT.  One input, cold, nothing in the subscribe frame and a
-- single value one tick out — so the door returns before anything is
-- delivered and the allowance is what serves it.
----------------------------------------------------------------------

Γ₁ : Ctx 2
Γ₁ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero       = scripted (cold [] (after 0 , 9 ∷ []))
insLate (suc zero) = shared (input zero)

bare : Closed Γ₁ natᵗ
bare = input zero

lit : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
lit = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

flat : Closed Γ₁ natᵗ
flat = mergeAllᵉ nothing (mapᵉ lit (input zero))

-- THE LADDER.  Each rung is one more flattener between the slot and
-- the root, so the chain's count rises by one a rung and the program's
-- own reading has to rise with it
flat₂ : Closed Γ₁ natᵗ
flat₂ = mergeAllᵉ nothing (mapᵉ lit flat)

flat₃ : Closed Γ₁ natᵗ
flat₃ = mergeAllᵉ nothing (mapᵉ lit flat₂)

-- THE GATE over the ladder: the body is subscribed a tick out, so the
-- door returns with whatever the gate has registered by then
gated : Closed Γ₁ natᵗ
gated = deferᵉ flat₂

-- TWO CHAINS ON ONE ARRIVAL, carrying different counts.  It has to be
-- the SHARE that both consumers read: two subscriptions to a scripted
-- slot are two arrivals, one chain each, which is what the registry
-- records when there is nothing to share
shd : Closed Γ₁ natᵗ
shd = input (suc zero)

forked : Closed Γ₁ natᵗ
forked = mergeAllᵉ nothing
           (ofᵉ (strmᵗ shd ∷ strmᵗ (mergeAllᵉ nothing (mapᵉ lit shd)) ∷ []))

-- the same fan-out over the SCRIPTED slot rather than the share, which
-- is the other way two consumers could have come to stand under one
-- arrival
forkedRaw : Closed Γ₁ natᵗ
forkedRaw = mergeAllᵉ nothing
              (ofᵉ (strmᵗ bare ∷ strmᵗ (mergeAllᵉ nothing (mapᵉ lit bare)) ∷ []))

-- THE SECOND TELESCOPE, WHERE THE SHARE'S OWN SOURCE FLATTENS.  Under
-- `insLate` the share reads the slot itself, so an arrival meets the
-- sink with nothing above it and the sink's conjunct is taken at the
-- floor.  Here the share reads a FLATTENED slot, so the chain carries
-- a frame BEFORE the sink while the consumers registered on the share
-- carry frames after it — the one shape where both halves of the
-- sink's comparison are positive, and the shape the refutation stands
-- at with the door's own rank removed
insDeep : Slots Γ₁
insDeep zero       = scripted (cold [] (after 0 , 9 ∷ []))
insDeep (suc zero) = shared (mergeAllᵉ nothing (mapᵉ lit (input zero)))

----------------------------------------------------------------------
-- THE ENTRY, AND IT IS THE STATEMENT'S OWN.  `entry-drain-hop` names
-- the pair `subscribeE` returns at the root; nothing here is written by
-- hand, which is what makes the figures below about a REACHED state.
----------------------------------------------------------------------

entOf : (ins : Slots Γ₁) (e : Closed Γ₁ natᵗ) → Sched Γ₁
entOf ins e = proj₁ (proj₂ (subscribeE (rootWitness e ins) e root 0 0
                (sched-init e ins) (st-init e)))

stOf : (ins : Slots Γ₁) (e : Closed Γ₁ natᵗ) → EvalSt e
stOf ins e = proj₂ (proj₂ (subscribeE (rootWitness e ins) e root 0 0
               (sched-init e ins) (st-init e)))

----------------------------------------------------------------------
-- THE FIGURES, TAKEN AT THE OBLIGATION'S OWN POINT.  The state is the
-- latched one with this registration marked delivered, which is the
-- state the premise's first conjunct is stated against — so a row that
-- read the entry state instead would be comparing against a rank the
-- statement never mentions.
----------------------------------------------------------------------

atArrival : (ins : Slots Γ₁) (e : Closed Γ₁ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
atArrival ins e with sched-next (entOf ins e)
... | inj₁ _        = 0 , 0 , 0 , 0 , 0 , 0
... | inj₂ (a , sd) = go (chainsOf a (stOf ins e))
  where
  lat : EvalSt e
  lat = cascadeLatch a (stOf ins e)

  tailHops : List (RegId × Path Γ₁ (arrTy a) natᵗ) → ℕ
  tailHops []             = 0
  tailHops ((_ , c) ∷ _)  = chainHops c

  go : List (RegId × Path Γ₁ (arrTy a) natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  go []               = 0 , 0 , 0 , 0 , 0 , 0
  go ((rid , c) ∷ cs) =
    let st′ = record lat { delivered = rid ∷ EvalSt.delivered lat }
        ψ   = slotRd (Sched.slots sd)
    in depthᵛ ψ (arrTy a) (arrVal a) , chainHops c , arrivalRank a sd st′
     , depthᵉ ψ e , suc (length cs) , tailHops cs

pay hops rank term reach hops₂ : (ins : Slots Γ₁) (e : Closed Γ₁ natᵗ) → ℕ
pay   ins e = proj₁ (atArrival ins e)
hops  ins e = proj₁ (proj₂ (atArrival ins e))
rank  ins e = proj₁ (proj₂ (proj₂ (atArrival ins e)))
term  ins e = proj₁ (proj₂ (proj₂ (proj₂ (atArrival ins e))))
reach ins e = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (atArrival ins e)))))
hops₂ ins e = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (atArrival ins e)))))

----------------------------------------------------------------------
-- THE ROWS.  Six figures per program, packed so one error reports all
-- of them: payload, flattener count, the rank the chain is held under,
-- the program's own reading, how many chains the arrival reached, and
-- the count on the SECOND of them.  The rank gets two digits because a
-- ladder's does not stay under ten.
----------------------------------------------------------------------

packOf : Slots Γ₁ → Closed Γ₁ natᵗ → ℕ
packOf ins e = pay ins e + 10 * hops ins e + 100 * rank ins e
             + 10000 * term ins e + 1000000 * reach ins e
             + 10000000 * hops₂ ins e

-- DEGENERATE in all four of its comparing components, and pinned so
-- that the rows below cannot be read as covering what this one does
-- not: the arrival is served and reaches one chain, and everything the
-- premise compares there is nought
bareRow : packOf insLate bare ≡ 1000000
bareRow = refl

-- LOAD-BEARING, and TIGHT: the chain's one flattener is paid by the
-- program's reading of one, with the payload contributing nothing, so
-- the premise holds by equality.  A flattener priced at more than one,
-- or a program reading that did not charge for its own, crosses here
flatRow : packOf insLate flat ≡ 1010110
flatRow = refl

-- LOAD-BEARING, and the first rung where a per-ladder reading would
-- differ from a per-rung one: two flatteners on the chain against a
-- reading that has to have grown twice
flat₂Row : packOf insLate flat₂ ≡ 1020220
flat₂Row = refl

-- LOAD-BEARING: the third rung says the margin is CONSTANT rather than
-- merely non-negative, which two rows cannot distinguish
flat₃Row : packOf insLate flat₃ ≡ 1030330
flat₃Row = refl

-- LOAD-BEARING, and the only row where the PAYLOAD carries weight: the
-- gate's body is subscribed a tick out, so what the arrival hands over
-- is itself an observable and reads two.  Two and one against a rank of
-- three is tight in all three terms at once, which no row above it is
gatedRow : packOf insLate gated ≡ 1010312
gatedRow = refl

-- THE FINDING, and it is a NEGATIVE one: the arrival reaches ONE
-- chain, carrying nought flatteners, however the fan-out was built.
-- The two rows are byte-identical, so the share is not what is missing
forkedRow : packOf insLate forked ≡ 1020200
forkedRow = refl

forkedRawRow : packOf insLate forkedRaw ≡ 1020200
forkedRawRow = refl

----------------------------------------------------------------------
-- THE SINK'S OWN TWO QUANTITIES, WHICH ARE WHAT THE FAN-OUT'S PREMISE
-- COMPARES AND WHAT NO ROW ABOVE REPORTS.  `sinkRd` carries the payload
-- rootward by the SAME `mapRd` the walk itself steps with, so what it
-- reports is where the walk stands when it reaches the sink; it is a
-- reporting figure like `chainHops`, and the rows that instantiate the
-- target are still generated by Agda from `entry-drain-hop`.
--
-- AND THE REGISTERED COUNT IS TAKEN OFF `shareAdmit`, which is the list
-- the fan-out's own premise walks — not `chainsOf`, which is the door's.
-- The two being different lists is the whole distinction between the
-- door's claim and the sink's, so reading the sink's figure off the
-- door's list would report agreement that nothing had checked.
----------------------------------------------------------------------

sinkRd : ∀ {n} {Γ : Ctx n} {s t} → (Fin n → Rd₃) → Path Γ s t → Rd → Rd
sinkRd ψ root                    Rin = Rin
sinkRd ψ (share-sink _)          Rin = Rin
sinkRd ψ (map-f fn ↠ κ)          Rin = sinkRd ψ κ (mapRd ψ Rin fn)
sinkRd ψ (scan-f fn nid ↠ κ)     Rin = sinkRd ψ κ (mapRd ψ Rin fn)
sinkRd ψ (take-f nid ↠ κ)        Rin = sinkRd ψ κ Rin
sinkRd ψ (from-inner o a i ↠ κ)  Rin = sinkRd ψ κ Rin
sinkRd ψ (thru-outer op nid ↠ κ) Rin = sinkRd ψ κ (proj₁ Rin , suc (proj₂ Rin))

atSink : (ins : Slots Γ₁) (e : Closed Γ₁ natᵗ) → ℕ × ℕ × ℕ
atSink ins e with sched-next (entOf ins e)
... | inj₁ _        = 0 , 0 , 0
... | inj₂ (a , sd) = go (chainsOf a (stOf ins e))
  where
  regs : List ℕ
  regs = map (λ p → chainHops (proj₂ p))
             (shareAdmit (suc zero) (EvalSt.registry (stOf ins e)))

  go : List (RegId × Path Γ₁ (arrTy a) natᵗ) → ℕ × ℕ × ℕ
  go []              = 0 , 0 , 0
  go ((rid , c) ∷ _) =
    let ψ = slotRd (Sched.slots sd)
    in proj₂ (sinkRd ψ c (rdᵛ ψ (arrTy a) (arrVal a)))
     , foldr _⊔_ 0 regs , length regs

sinkPay regMax regLen : (ins : Slots Γ₁) (e : Closed Γ₁ natᵗ) → ℕ
sinkPay ins e = proj₁ (atSink ins e)
regMax  ins e = proj₁ (proj₂ (atSink ins e))
regLen  ins e = proj₂ (proj₂ (atSink ins e))

-- payload AT the sink, the deepest registered chain, how many chains
-- are registered, and the rank the whole dispatch is entered under —
-- the four the restatement has to be denominated in
sinkPack : Slots Γ₁ → Closed Γ₁ natᵗ → ℕ
sinkPack ins e = sinkPay ins e + 10 * regMax ins e + 100 * regLen ins e
               + 1000 * rank ins e + 100000 * term ins e

-- THE CONTROL, and it is the refutation's own shape: the share reads
-- the slot, so the payload reaches the sink at the FLOOR and the two
-- registered chains are the fan-out's.  This is where the free-standing
-- leaf is false, and the row says why it is not false here — the rank
-- the dispatch is entered under is two, not the store's one
shallowRow : sinkPack insLate forked ≡ 202210
shallowRow = refl

-- LOAD-BEARING, and the one row where both halves are positive: a
-- frame above the sink and a flattener below it, so the sum the
-- restatement needs is compared against a rank that had to grow with
-- both
deepRow : sinkPack insDeep forked ≡ 303211
deepRow = refl

-- AND THE THIRD POINT MOVES THE REGISTERED HALF ON ITS OWN, which is
-- what makes the pair a DIRECTION rather than a height: the share's
-- source is unchanged and the deepest consumer gains a flattener, so a
-- rank that tracked only the chain above the sink would stand still
-- here while the sum it has to cover went up
forked₂ : Closed Γ₁ natᵗ
forked₂ = mergeAllᵉ nothing
            (ofᵉ (strmᵗ shd
                ∷ strmᵗ (mergeAllᵉ nothing (mapᵉ lit
                          (mergeAllᵉ nothing (mapᵉ lit shd)))) ∷ []))

widerRow : sinkPack insDeep forked₂ ≡ 404221
widerRow = refl

----------------------------------------------------------------------
-- AND THE STATEMENT ITSELF, at both points.  The type is generated by
-- Agda from `entry-drain-hop` as it now reads, so the probe chooses the
-- program and nothing else; a restatement changes what these rows have
-- to inhabit.
----------------------------------------------------------------------

doorBare : Confirms (entry-drain-hop 1 bare insLate)
doorBare = (tt , tt) , tt

doorFlat : Confirms (entry-drain-hop 1 flat insLate)
doorFlat = ((Below , tt) , tt) , tt

doorFlat₂ : Confirms (entry-drain-hop 1 flat₂ insLate)
doorFlat₂ = ((Below , Below , tt) , tt) , tt

doorFlat₃ : Confirms (entry-drain-hop 1 flat₃ insLate)
doorFlat₃ = ((Below , Below , Below , tt) , tt) , tt

doorGated : Confirms (entry-drain-hop 1 gated insLate)
doorGated = ((Below , tt) , tt) , tt

doorForked : Confirms (entry-drain-hop 1 forked insLate)
doorForked = (Below , tt) , tt

doorForkedRaw : Confirms (entry-drain-hop 1 forkedRaw insLate)
doorForkedRaw = (tt , tt) , tt

-- and at the SECOND telescope, where the arrival's own chain carries a
-- frame before it sinks: the door's walk has a conjunct to discharge
-- above the share, which is the half no row at the first telescope has
doorDeep : Confirms (entry-drain-hop 1 forked insDeep)
doorDeep = ((Below , Below) , tt) , tt

doorDeep₂ : Confirms (entry-drain-hop 1 forked₂ insDeep)
doorDeep₂ = ((Below , Below) , tt) , tt
