-- THE DOOR'S PREMISE, INSTANTIATED — and the region it reaches is the
-- one its predecessor recorded as unreachable.  The statement here used
-- to be a whole fit certificate, so a row could only stand where every
-- constructor it needed was already proven: the chains with no frame on
-- them, and nothing else.  The premise is now a COUNT of flatteners
-- against the program's own reading, which computes at every chain, so
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

-- THE LADDER IS WHERE THE TWO CURRENCIES COULD DIVERGE AND DO NOT.  A
-- chain carrying two and then three flatteners is paid by a program
-- whose own reading grows by one at each rung, so the margin is
-- constant rather than shrinking — which is the thing a single tight
-- row cannot say.  Had the reading charged a flattener once for the
-- whole ladder, or the count charged per rung against a reading that
-- did not, the three-rung row is where the two readings cross.

-- THE FORKED ROWS WERE BUILT TO REACH THE PREMISE'S RECURSION AND DO
-- NOT, WHICH IS THE FINDING THEY CARRY.  Two consumers standing over
-- one source — once through a SHARE, once over the SCRIPTED slot — give
-- byte-identical figures, and both report the arrival reaching ONE
-- chain carrying nought flatteners.  So the cons case of the chain
-- recursion is not a shape the door has; whatever fan-out a program
-- has is registered on the sink and entered from there, not threaded
-- through a tail at this arrival.  A repair that made the door see a
-- second chain would move both of these rows at once.

-- NOT COVERED, AND ONE ENTRY OF THIS LIST IS NOW A BOUNDARY RATHER
-- THAN A GAP.  Every row stands at ONE arrival and at the allowance's
-- FIRST step, so nothing here reaches a second arrival or the
-- allowance's second conjunct; the ladder stops at three rungs, which
-- is where the reading and the count were seen to keep step and not
-- where they were shown to.  The recursion's cons case is not missing
-- coverage — the two forked rows are the evidence that it is not
-- reachable at this point at all, and a probe cannot be written for it
-- here.
-- TARGET: entry-drain-hop @5b9789
module Probed.Door-Fits where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂;
  ofᵉ; mapᵉ; mergeAllᵉ; deferᵉ; input)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Hop-Depth using (depthᵛ; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; subscribeE;
  rootWitness; sched-init; st-init; sched-next; chainsOf; cascadeLatch;
  arrTy; arrVal; RegId)
open import Verify-Rank-Sufficient using (entry-drain-hop)
open import Verify-Rank-Sufficient.Fits using (arrivalRank)
open import Verify-Rank-Sufficient.Path-Fits using (pathHops)
open import Probed.Apparatus using (Confirms)

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

----------------------------------------------------------------------
-- THE ENTRY, AND IT IS THE STATEMENT'S OWN.  `entry-drain-hop` names
-- the pair `subscribeE` returns at the root; nothing here is written by
-- hand, which is what makes the figures below about a REACHED state.
----------------------------------------------------------------------

entOf : (e : Closed Γ₁ natᵗ) → Sched Γ₁
entOf e = proj₁ (proj₂ (subscribeE (rootWitness e insLate) e root 0 0
            (sched-init e insLate) (st-init e)))

stOf : (e : Closed Γ₁ natᵗ) → EvalSt e
stOf e = proj₂ (proj₂ (subscribeE (rootWitness e insLate) e root 0 0
           (sched-init e insLate) (st-init e)))

----------------------------------------------------------------------
-- THE FIGURES, TAKEN AT THE OBLIGATION'S OWN POINT.  The state is the
-- latched one with this registration marked delivered, which is the
-- state the premise's first conjunct is stated against — so a row that
-- read the entry state instead would be comparing against a rank the
-- statement never mentions.
----------------------------------------------------------------------

atArrival : (e : Closed Γ₁ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
atArrival e with sched-next (entOf e)
... | inj₁ _        = 0 , 0 , 0 , 0 , 0 , 0
... | inj₂ (a , sd) = go (chainsOf a (stOf e))
  where
  lat : EvalSt e
  lat = cascadeLatch a (stOf e)

  tailHops : List (RegId × Path Γ₁ (arrTy a) natᵗ) → ℕ
  tailHops []             = 0
  tailHops ((_ , c) ∷ _)  = pathHops c

  go : List (RegId × Path Γ₁ (arrTy a) natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  go []               = 0 , 0 , 0 , 0 , 0 , 0
  go ((rid , c) ∷ cs) =
    let st′ = record lat { delivered = rid ∷ EvalSt.delivered lat }
        ψ   = slotRd (Sched.slots sd)
    in depthᵛ ψ (arrTy a) (arrVal a) , pathHops c , arrivalRank a sd st′
     , depthᵉ ψ e , suc (length cs) , tailHops cs

pay hops rank term reach hops₂ : (e : Closed Γ₁ natᵗ) → ℕ
pay   e = proj₁ (atArrival e)
hops  e = proj₁ (proj₂ (atArrival e))
rank  e = proj₁ (proj₂ (proj₂ (atArrival e)))
term  e = proj₁ (proj₂ (proj₂ (proj₂ (atArrival e))))
reach e = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (atArrival e)))))
hops₂ e = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (atArrival e)))))

----------------------------------------------------------------------
-- THE ROWS.  Six figures per program, packed so one error reports all
-- of them: payload, flattener count, the rank the chain is held under,
-- the program's own reading, how many chains the arrival reached, and
-- the count on the SECOND of them.  The rank gets two digits because a
-- ladder's does not stay under ten.
----------------------------------------------------------------------

packOf : Closed Γ₁ natᵗ → ℕ
packOf e = pay e + 10 * hops e + 100 * rank e
         + 10000 * term e + 1000000 * reach e + 10000000 * hops₂ e

-- DEGENERATE in all four of its comparing components, and pinned so
-- that the rows below cannot be read as covering what this one does
-- not: the arrival is served and reaches one chain, and everything the
-- premise compares there is nought
bareRow : packOf bare ≡ 1000000
bareRow = refl

-- LOAD-BEARING, and TIGHT: the chain's one flattener is paid by the
-- program's reading of one, with the payload contributing nothing, so
-- the premise holds by equality.  A flattener priced at more than one,
-- or a program reading that did not charge for its own, crosses here
flatRow : packOf flat ≡ 1010110
flatRow = refl

-- LOAD-BEARING, and the first rung where a per-ladder reading would
-- differ from a per-rung one: two flatteners on the chain against a
-- reading that has to have grown twice
flat₂Row : packOf flat₂ ≡ 1020220
flat₂Row = refl

-- LOAD-BEARING: the third rung says the margin is CONSTANT rather than
-- merely non-negative, which two rows cannot distinguish
flat₃Row : packOf flat₃ ≡ 1030330
flat₃Row = refl

-- LOAD-BEARING, and the only row where the PAYLOAD carries weight: the
-- gate's body is subscribed a tick out, so what the arrival hands over
-- is itself an observable and reads two.  Two and one against a rank of
-- three is tight in all three terms at once, which no row above it is
gatedRow : packOf gated ≡ 1010312
gatedRow = refl

-- THE FINDING, and it is a NEGATIVE one: the arrival reaches ONE
-- chain, carrying nought flatteners, however the fan-out was built.
-- The two rows are byte-identical, so the share is not what is missing
forkedRow : packOf forked ≡ 1020200
forkedRow = refl

forkedRawRow : packOf forkedRaw ≡ 1020200
forkedRawRow = refl

----------------------------------------------------------------------
-- AND THE STATEMENT ITSELF, at both points.  The type is generated by
-- Agda from `entry-drain-hop` as it now reads, so the probe chooses the
-- program and nothing else; a restatement changes what these rows have
-- to inhabit.
----------------------------------------------------------------------

doorBare : Confirms (entry-drain-hop 1 bare insLate)
doorBare = (z≤n , tt) , tt

doorFlat : Confirms (entry-drain-hop 1 flat insLate)
doorFlat = (s≤s z≤n , tt) , tt

doorFlat₂ : Confirms (entry-drain-hop 1 flat₂ insLate)
doorFlat₂ = (s≤s (s≤s z≤n) , tt) , tt

doorFlat₃ : Confirms (entry-drain-hop 1 flat₃ insLate)
doorFlat₃ = (s≤s (s≤s (s≤s z≤n)) , tt) , tt

doorGated : Confirms (entry-drain-hop 1 gated insLate)
doorGated = (s≤s (s≤s (s≤s z≤n)) , tt) , tt

doorForked : Confirms (entry-drain-hop 1 forked insLate)
doorForked = (z≤n , tt) , tt

doorForkedRaw : Confirms (entry-drain-hop 1 forkedRaw insLate)
doorForkedRaw = (z≤n , tt) , tt
