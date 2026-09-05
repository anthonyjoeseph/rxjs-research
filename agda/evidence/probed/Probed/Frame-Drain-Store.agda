-- ══════════════════════════════════════════════════════════════════
-- WHAT A DRAIN FRAME LEAVES IN THE TWO STORES, at the one arrival
-- shape that could make either climb.
--
-- TARGET: stepFrame-nest-nodes-inner @9acb55
-- TARGET: stepFrame-nest-regs-inner @9de932
--
-- WHY THE DRAIN IS THE HARD DIRECTION.  A `from-inner` is handed
-- NOTHING: its burst is empty by construction, so the value premise is
-- vacuous and the budget the statement licenses carries no term in the
-- arrivals at all.  Whatever the frame writes therefore has to be paid
-- for by the entry table alone.  The frame does two things to that
-- table -- it POPS the parent *All's queue, and it SUBSCRIBES what it
-- popped -- and only the second could add.
--
-- WHY THE QUEUE IS REACHED AND NOT WRITTEN.  A queue installed by hand
-- is not one the evaluator put there, and the whole question is what
-- the evaluator does to a queue it made.  So the state is built by
-- subscribing a capacity-ONE merge and then stepping an outer frame
-- with THREE arrivals: the first subscribes and stays active, and the
-- other two have nowhere to go but the queue.  The drain then runs
-- against that.

-- WHAT WOULD HAVE FAILED.  A queue of two is what makes the row read
-- something: the pop takes the deeper term and leaves the shallower,
-- so the entry reading climbs with the ladder while the exit reading
-- does not, and at the bottom rung the two coincide and the row stands
-- at margin ZERO.
--
-- AND THE SUBSCRIBE DOES WRITE, WHICH IS THE FINDING.  The second
-- family's popped term is itself a capacity-one merge over a
-- SYNCHRONOUS source, and its subscription DELIVERS inside the very
-- frame that made it: the first element takes the lane and the second
-- parks, so the drain leaves a cell that did not exist on entry.  It
-- is covered anyway, and not by the budget, which is zero here.  A
-- `*All` layer costs one `suc` in the measure and the thing it parks
-- is what was UNDER that layer, so the fresh cell is strictly
-- shallower than the popped term -- and the popped term was in the
-- entry table.  The bound is the entry reading, one rung up.
--
-- AND BEHIND THE GATE IT WRITES NOTHING, which is the other half of
-- the same argument and the one that could have broken it.  A gated
-- queued term is priced at ZERO by the measure however deep it is, so
-- the entry reading no longer dominates it and the strictness above
-- has nothing to stand on.  The evaluator honours the gate it is
-- measured by: the drain registers the deferred term and unfolds
-- none of it, and the table is unmoved at two rungs of a shape whose
-- ungated twin parks three layers.

-- AND THE REGISTRY IS WHERE THE GRANT EARNS ITS KEEP.  The drain
-- SUBSCRIBES what it pops, so that store does grow, and it grows by
-- exactly the popped term's own depth -- one, two, three against an
-- entry registry that stands at one throughout.  The number covering
-- it is not chosen: the frame grant's `G` is at least the node's own
-- reading and the budget is at least `G`, so the rows stand at the
-- node reading, which is a floor the hypothesis cannot go under.  At
-- that floor every rung clears by exactly ZERO.  This is what the
-- walk's values could never have paid for, the burst being empty.
--
-- AND THE PREMISES ARE LEFT STANDING.  The frame grant is a Σ, so no
-- row could discharge it; what each row asserts is the conclusion with
-- the grant unasked, which is stronger than the instance rather than
-- weaker.

-- NOT COVERED: the switch and exhaust ops, which keep no queue to
-- drain; a drain whose parent queue is EMPTY, where the pop has
-- nothing to take and the frame is the identity on the table; and a
-- nonempty path under the frame, `root` being what holds the budget at
-- its floor.
-- ══════════════════════════════════════════════════════════════════
module Probed.Frame-Drain-Store where

open import Data.Bool using (true; false)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Ctx; Closed; natᵗ; ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ; nat̂; input;
         deferᵉ; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; stepFrame;
         thru-outer; from-inner; mergeAllᵒ; NodeId; NodeState; mergeAll-st;
         Path; _↠_)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Nest-Store using (regsNestMax)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nodeNestAt; nestDᵛˢ)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Nodes-Nest-Walk
  using (stepFrame-nest-nodes-inner)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (stepFrame-nest-regs-inner)
open import Probed.Apparatus using (Confirms)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the one value arrives LATER, so every subscription this file makes
-- is still active when the frames run
slots : Slots Γ₁
slots fzero = scripted (cold [] ((after 1 , 7) ∷ []))

-- one flatten layer, so a ladder of these is a ladder of nesting
feed : Closed Γ₁ natᵗ → Closed Γ₁ natᵗ
feed src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

ladder : ℕ → Closed Γ₁ natᵗ
ladder 0       = input fzero
ladder (suc k) = feed (ladder k)

-- capacity ONE over a SYNCHRONOUS source: the one term whose own
-- subscription would park, if a subscribe delivered
parky : ℕ → Closed Γ₁ natᵗ
parky k = mergeAllᵉ (just 1)
  (ofᵉ (strmᵗ (input fzero) ∷ strmᵗ (ladder k) ∷ []))

-- capacity ONE, which is what makes a second arrival park rather than
-- subscribe
prog : Closed Γ₁ natᵗ
prog = mergeAllᵉ (just 1) (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) (input fzero))

sucG : ℕ
sucG = suc (syncSizeᵉ prog + hopDᵉ 0 (slotHop 0 slots) prog)

sub : Sched Γ₁ × EvalSt prog
sub = let r = subscribeE (gasPad sucG g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- THE NODE ID COMES FROM THE RUN, and it has to: a frame at a nid the
-- table does not hold is the IDENTITY, so a row at an invented one
-- would report preservation for a step that did nothing
mergeNid : List (NodeId × NodeState Γ₁) → NodeId
mergeNid []                              = 0
mergeNid ((k , mergeAll-st _ _ _ _) ∷ _) = k
mergeNid (_ ∷ ns)                        = mergeNid ns

tieNid : NodeId
tieNid = mergeNid (EvalSt.nodes (proj₂ sub))

-- the ladder outruns the root program's own gas, which is sized to the
-- program and not to what a frame is handed
gas : ℕ
gas = sucG + 40

-- ONE SUBSCRIBES AND TWO PARK, so the queue the drain reads is one the
-- evaluator wrote
park : List (Closed Γ₁ natᵗ) → Sched Γ₁ × EvalSt prog
park vs =
  let r = stepFrame (gasPad gas g0) 1 0 (thru-outer mergeAllᵒ tieNid)
            root vs false (proj₁ sub) (proj₂ sub)
  in proj₁ (proj₂ (proj₂ (proj₂ r))) , proj₂ (proj₂ (proj₂ (proj₂ r)))

-- the deeper term is the one the pop takes; the shallower stays
qs : ℕ → Sched Γ₁ × EvalSt prog
qs k = park (ladder 1 ∷ ladder k ∷ ladder 1 ∷ [])

-- same, with the popped term replaced by the would-park shape
qsP : ℕ → Sched Γ₁ × EvalSt prog
qsP k = park (ladder 1 ∷ parky k ∷ ladder 1 ∷ [])

-- and again behind the GATE, which is where the measure reads zero for
-- a term that is not shallow
qsD : ℕ → Sched Γ₁ × EvalSt prog
qsD k = park (ladder 1 ∷ deferᵉ (parky k) ∷ ladder 1 ∷ [])

-- an instance no registration is alive through, which is what a
-- completed inner looks like to the drain check
instId : NodeId
instId = 9

drain : Sched Γ₁ × EvalSt prog → EvalSt prog
drain (sc , st) = proj₂ (proj₂ (proj₂ (proj₂
  (stepFrame (gasPad gas g0) 1 0 (from-inner mergeAllᵒ tieNid instId)
     root [] true sc st))))

----------------------------------------------------------------------
-- THE BUDGET, READ OFF THE PREMISE RATHER THAN CHOSEN -- and this is
-- where a drain differs from an arrival.  The value conjunct is `all`
-- over the burst, and a drain's burst is EMPTY, so the number the
-- premise licenses carries no term in the arrivals at all.
----------------------------------------------------------------------
B : ℕ
B = 0

κ₀ : Path Γ₁ natᵗ natᵗ
κ₀ = from-inner mergeAllᵒ tieNid instId ↠ root

Uof : ℕ
Uof = pathΦF B κ₀ * (nestDᵛˢ {Γ = Γ₁} {u = natᵗ} [] + pathΦD B κ₀)

----------------------------------------------------------------------
-- THE TABLE EITHER SIDE OF THE FRAME, at three rungs, with the budget
-- beside it.  The entry reading is the queue's deeper term and the
-- exit reading is its shallower one, so the pair is what says the pop
-- is a shrink and the subscribe adds nothing.
----------------------------------------------------------------------
figs : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
figs = nodesMax (proj₂ (qs 1)) , nodesMax (proj₂ (qs 2))
     , nodesMax (proj₂ (qs 3))
     , nodesMax (drain (qs 1)) , nodesMax (drain (qs 2))
     , nodesMax (drain (qs 3))
     , nodesMax (proj₂ (qsP 3)) , nodesMax (drain (qsP 3))
     , nodeNestAt tieNid (drain (qs 3)) , Uof

packed : ℕ
packed = let (a , b , c , d , e , f , g , h , i , j) = figs in
  a + 100 * b + 10000 * c + 1000000 * d + 100000000 * e
    + 10000000000 * f + 1000000000000 * g + 100000000000000 * h
    + 10000000000000000 * i + 1000000000000000000 * j

packed≡ : packed ≡ 10304010101030201
packed≡ = refl

gated : ℕ × ℕ × ℕ × ℕ
gated = nodesMax (proj₂ (qsD 3)) , nodesMax (drain (qsD 3))
      , nodesMax (proj₂ (qsD 4)) , nodesMax (drain (qsD 4))

gatedPacked : ℕ
gatedPacked = let (a , b , c , d) = gated in
  a + 100 * b + 10000 * c + 1000000 * d

gated≡ : gatedPacked ≡ 1010101
gated≡ = refl

----------------------------------------------------------------------
-- THE REGISTRY, ON THE SAME RUNS.  The drain SUBSCRIBES what it pops,
-- so this is the store that grows, and the number that has to cover it
-- is the one the frame grant already carries: the grant's `G` is at
-- least the node's own reading, and the budget is at least `G`.  So
-- the floor below is a number the statement's own hypothesis can never
-- go under.
----------------------------------------------------------------------
floorU : ℕ → ℕ
floorU k = nodeNestAt tieNid (proj₂ (qs k))

regsFigs : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
regsFigs = regsNestMax (EvalSt.registry (proj₂ (qs 1)))
         , regsNestMax (EvalSt.registry (proj₂ (qs 2)))
         , regsNestMax (EvalSt.registry (proj₂ (qs 3)))
         , regsNestMax (EvalSt.registry (drain (qs 1)))
         , regsNestMax (EvalSt.registry (drain (qs 2)))
         , regsNestMax (EvalSt.registry (drain (qs 3)))
         , floorU 3
         , regsNestMax (EvalSt.registry (drain (qsD 3)))

regsPacked : ℕ
regsPacked = let (a , b , c , d , e , f , g , h) = regsFigs in
  a + 100 * b + 10000 * c + 1000000 * d + 100000000 * e
    + 10000000000 * f + 1000000000000 * g + 100000000000000 * h

regsPacked≡ : regsPacked ≡ 103030201010101
regsPacked≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The type is generated from the statement as it now reads,
-- so a restatement changes every row underneath rather than leaving a
-- component reading kept beside it by hand.
--
-- LOAD-BEARING, and the budget carries none of it: `Uof` is zero, so
-- every row is the entry table alone covering the exit table.  The
-- first would fail at margin zero if the pop left the deeper term
-- rather than taking it; the fourth would fail if the fresh cell a
-- subscribe parks into were charged at the popped term's own depth
-- rather than one below it; the fifth would fail if the gate the
-- measure trusts were not the gate the evaluator keeps.
----------------------------------------------------------------------
tieDrain1 : Confirms
  (stepFrame-nest-nodes-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qs 1)) (proj₂ (qs 1)) B Uof)
tieDrain1 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrain2 : Confirms
  (stepFrame-nest-nodes-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qs 2)) (proj₂ (qs 2)) B Uof)
tieDrain2 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrain3 : Confirms
  (stepFrame-nest-nodes-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qs 3)) (proj₂ (qs 3)) B Uof)
tieDrain3 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrainPark : Confirms
  (stepFrame-nest-nodes-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qsP 3)) (proj₂ (qsP 3)) B Uof)
tieDrainPark = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrainGated : Confirms
  (stepFrame-nest-nodes-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qsD 3)) (proj₂ (qsD 3)) B Uof)
tieDrainGated = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrainRegs1 : Confirms
  (stepFrame-nest-regs-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qs 1)) (proj₂ (qs 1)) B (floorU 1))
tieDrainRegs1 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrainRegs2 : Confirms
  (stepFrame-nest-regs-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qs 2)) (proj₂ (qs 2)) B (floorU 2))
tieDrainRegs2 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrainRegs3 : Confirms
  (stepFrame-nest-regs-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qs 3)) (proj₂ (qs 3)) B (floorU 3))
tieDrainRegs3 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieDrainRegsGated : Confirms
  (stepFrame-nest-regs-inner (gasPad gas g0) 1 0 mergeAllᵒ tieNid instId
     root [] true (proj₁ (qsD 3)) (proj₂ (qsD 3)) B (floorU 1))
tieDrainRegsGated = λ _ _ → ≤ᵇ⇒≤ _ _ tt
