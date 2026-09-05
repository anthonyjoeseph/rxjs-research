-- ══════════════════════════════════════════════════════════════════
-- WHAT AN OUTER FRAME LEAVES IN THE TWO STORES, at the one arrival
-- shape that writes to BOTH of them in a single step.
--
-- TARGET: stepFrame-nest-nodes-outer @492db2
-- TARGET: stepFrame-nest-regs-outer @0e9b79
--
-- WHY ONE FRAME MOVES TWO STORES.  A `thru-outer` receives observables
-- and does one of two things with each: SUBSCRIBE it, which appends a
-- registration whose chain carries the frame plus everything the
-- subscribed term itself pushes, or PARK it in the *All node's queue,
-- which is the one write that makes a node's nesting reading nonzero.
-- Which of the two happens is decided by the merge's capacity, so a
-- merge of capacity ONE handed TWO arrivals does both at once: the
-- first subscribes and stays active, and the second has nowhere to go
-- but the queue.  Every other arrangement leaves one of the two
-- statements reading its entry state back unchanged.
--
-- WHY THE ARRIVALS ARE A LADDER AND THE PROGRAM IS FLAT.  The values a
-- frame steps are quantified over, so they need not appear in the
-- program's own syntax -- and where they do, the entry registry
-- already reads the nesting the step is supposed to introduce and the
-- row cannot move.  So the program is a bare capacity-one merge over
-- the async slot, fixing the entry readings at zero and one, and the
-- arrivals are `k` flatten layers deep.  Both stores then climb with
-- `k` against entry readings that do not.
--
-- WHAT IS LOAD-BEARING.  The budget is not chosen: it is the potential
-- the frame's OWN value premise licenses at burst zero -- the path
-- factor times the arrivals' depth plus the path's depth -- so each
-- row stands at the smallest number that premise would ever hand over.
-- Against it both mints clear by exactly ONE at every rung, so a mint
-- charging one layer more than the potential accounts for would sit at
-- zero margin here and cross at the next rung.  A three-rung ladder is
-- what makes that visible; a single row cannot tell a constant margin
-- from a closing one.
--
-- AND THE PREMISES ARE LEFT STANDING.  Both statements' second
-- hypothesis is a Σ, so it does not compute and no row could discharge
-- it; what each row asserts is therefore the conclusion with the
-- potential and the frame grant unasked, which is stronger than the
-- instance rather than weaker.
--
-- NOT COVERED: the switch and exhaust ops, which never park -- their
-- arms kill or drop rather than queue, so the nodes mint has no
-- counterpart there; a nonzero entry queue, where the park compounds
-- rather than starting from zero; and a nonempty path under the frame,
-- since `root` is what holds the potential at the premise's floor.
-- ══════════════════════════════════════════════════════════════════
module Probed.Thru-Outer-Store where

open import Data.Bool using (false)
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
  using (Ctx; Closed; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ; nat̂; input;
         syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; stepFrame;
         thru-outer; mergeAllᵒ; NodeId; NodeState; mergeAll-st; Path; _↠_)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Nest-Store using (regsNestMax)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nodeNestAt; nestDᵛˢ)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Nodes-Nest-Walk
  using (stepFrame-nest-nodes-outer)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (stepFrame-nest-regs-outer)
open import Probed.Apparatus using (Confirms)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the one value arrives LATER, so every subscription this file makes
-- is still active when the frame runs
slots : Slots Γ₁
slots fzero = scripted (cold [] ((after 1 , 7) ∷ []))

-- one flatten layer, which is what makes a hop REGISTER rather than
-- merely pass a value along -- so a ladder of these is a ladder of
-- registered chain depth
feed : Closed Γ₁ natᵗ → Closed Γ₁ natᵗ
feed src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

ladder : ℕ → Closed Γ₁ natᵗ
ladder 0       = input fzero
ladder (suc k) = feed (ladder k)

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

-- THE NODE ID COMES FROM THE RUN, and it has to: a `thru-outer` at a
-- nid the table does not hold is the IDENTITY, so a row at an invented
-- one would report preservation for a step that did nothing
mergeNid : List (NodeId × NodeState Γ₁) → NodeId
mergeNid []                              = 0
mergeNid ((k , mergeAll-st _ _ _ _) ∷ _) = k
mergeNid (_ ∷ ns)                        = mergeNid ns

tieNid : NodeId
tieNid = mergeNid (EvalSt.nodes (proj₂ sub))

-- the first entry SUBSCRIBES and stays active, so the second one has
-- nowhere to go but the queue: one frame moves both stores at once
vals : ℕ → List (Closed Γ₁ natᵗ)
vals k = ladder k ∷ ladder k ∷ []

-- the ladder outruns the root program's own gas, which is sized to the
-- program and not to what a frame is handed
gas : ℕ
gas = sucG + 40

stepSt : ℕ → EvalSt prog
stepSt k = proj₂ (proj₂ (proj₂ (proj₂
  (stepFrame (gasPad gas g0) 1 0 (thru-outer mergeAllᵒ tieNid)
     root (vals k) false (proj₁ sub) (proj₂ sub)))))

----------------------------------------------------------------------
-- THE BUDGET, READ OFF THE PREMISE RATHER THAN CHOSEN.  The value
-- conjunct admits exactly this number at burst zero, so a row standing
-- at it stands at the tightest budget the statement's own hypothesis
-- would ever supply.
----------------------------------------------------------------------
B : ℕ
B = 0

κ₀ : Path Γ₁ (obs natᵗ) natᵗ
κ₀ = thru-outer mergeAllᵒ tieNid ↠ root

Uof : ℕ → ℕ
Uof k = pathΦF B κ₀ * (nestDᵛˢ (vals k) + pathΦD B κ₀)

----------------------------------------------------------------------
-- BOTH STORES EITHER SIDE OF THE FRAME, at three rungs, with the
-- budget beside them.  The node's own cell is pinned as well as the
-- whole-table fold, so a table reading carried by some OTHER node
-- would be visible as one rather than read as this frame's mint.
----------------------------------------------------------------------
figs : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
figs = nodesMax (proj₂ sub) , regsNestMax (EvalSt.registry (proj₂ sub))
     , nodesMax (stepSt 1) , nodesMax (stepSt 2) , nodesMax (stepSt 3)
     , regsNestMax (EvalSt.registry (stepSt 1))
     , regsNestMax (EvalSt.registry (stepSt 2))
     , regsNestMax (EvalSt.registry (stepSt 3))
     , Uof 1 , Uof 3

packed : ℕ
packed = let (a , b , c , d , e , f , g , h , i , j) = figs in
  a + 100 * b + 10000 * c + 1000000 * d + 100000000 * e
    + 10000000000 * f + 1000000000000 * g + 100000000000000 * h
    + 10000000000000000 * i + 1000000000000000000 * j

packed≡ : packed ≡ 4020302010302010100
packed≡ = refl

-- AND THE MINT IS THE QUEUE PARK AND NOT THE FRESH NODE, which the
-- cell pin is what says: the table's whole-fold reading above is
-- carried by the very cell the frame parked into, at every rung.
cells : ℕ × ℕ × ℕ × ℕ
cells = nodeNestAt tieNid (proj₂ sub) , nodeNestAt tieNid (stepSt 1)
      , nodeNestAt tieNid (stepSt 2) , nodeNestAt tieNid (stepSt 3)

cells≡ : cells ≡ (0 , 1 , 2 , 3)
cells≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The type is generated from each statement as it now
-- reads, so a restatement changes every row underneath rather than
-- leaving a component reading kept beside it by hand.
--
-- LOAD-BEARING at all three rungs and on both axes: the mint climbs
-- with the ladder while the entry reading does not, so the budget is
-- what carries every row.  Each would fail if the frame charged one
-- layer more than the arrivals' own depth.
----------------------------------------------------------------------
tieNodes1 : Confirms
  (stepFrame-nest-nodes-outer (gasPad gas g0) 1 0 mergeAllᵒ tieNid
     root (vals 1) false (proj₁ sub) (proj₂ sub) B (Uof 1))
tieNodes1 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieNodes2 : Confirms
  (stepFrame-nest-nodes-outer (gasPad gas g0) 1 0 mergeAllᵒ tieNid
     root (vals 2) false (proj₁ sub) (proj₂ sub) B (Uof 2))
tieNodes2 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieNodes3 : Confirms
  (stepFrame-nest-nodes-outer (gasPad gas g0) 1 0 mergeAllᵒ tieNid
     root (vals 3) false (proj₁ sub) (proj₂ sub) B (Uof 3))
tieNodes3 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieRegs1 : Confirms
  (stepFrame-nest-regs-outer (gasPad gas g0) 1 0 mergeAllᵒ tieNid
     root (vals 1) false (proj₁ sub) (proj₂ sub) B (Uof 1))
tieRegs1 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieRegs2 : Confirms
  (stepFrame-nest-regs-outer (gasPad gas g0) 1 0 mergeAllᵒ tieNid
     root (vals 2) false (proj₁ sub) (proj₂ sub) B (Uof 2))
tieRegs2 = λ _ _ → ≤ᵇ⇒≤ _ _ tt

tieRegs3 : Confirms
  (stepFrame-nest-regs-outer (gasPad gas g0) 1 0 mergeAllᵒ tieNid
     root (vals 3) false (proj₁ sub) (proj₂ sub) B (Uof 3))
tieRegs3 = λ _ _ → ≤ᵇ⇒≤ _ _ tt
