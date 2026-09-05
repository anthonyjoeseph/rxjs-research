-- ══════════════════════════════════════════════════════════════════
-- THE PARKED QUEUE A SUBSCRIPTION STANDS BESIDE AND NEVER READS.
--
-- TARGET: subscribeE-sz-store @f8b804
--
-- WHAT WAS UNTESTED, AND WHY NO READING OF THE DELIVERED LIST COULD
-- REACH IT.  A `*All` node holds programs it could not admit, and the
-- table reading prices them by their own syntax -- so they are the one
-- part of the table that is not a trace of anything the frame handed
-- on.  Every other witness at this half installs exactly ONE node and
-- enters at an EMPTY queue.
--
-- AND THE ARRIVAL'S LEVEL IS NOT BOUGHT FOR THEM, which is the
-- finding.  A crossing subscription never looks at the queue: the
-- level it is held to is the arrival's own layers and the telescope,
-- and entries standing beside the arrival move neither -- so they have
-- to survive a level nothing about them paid for.  The row is read at
-- the frame, which at ONE arrival, a door with room and no close is
-- the subscription itself.
--
-- WHAT THE ROWS DO NOT BUY.  One queue depth and the merging door
-- alone -- a switch holds a node id and an exhaust two bits, so
-- neither has a queue at all and the shape does not arise there.  And
-- nothing about a queue whose entries name a SHARED slot each, where
-- one definition would run once for the several entries reaching it.
-- ══════════════════════════════════════════════════════════════════
module Probed.Parked-Queue-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Closed; Fn; obs; emptyᵉ; ofᵉ; mapᵉ;
  varᵗ; strmᵗ)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; from-inner; _↠_;
  thru-outer; mergeAll-st; installNode; st-init; stepFrame; sched-init;
  iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (szCount; subscribeE-sz-store)
open import Refuted.Frame-Step-Size-Cross-Store
  using (Γ₁; sl₁; Pow; K; inner; e₀; vals₀)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE ENTRIES.  Three programs of the one type a queue at this node
-- can hold, chosen so their layer counts differ and so the largest
-- count is not the entry a queue walk would reach first.
----------------------------------------------------------------------

-- carries no layer and installs nothing: a queue entry the charge is
-- blind to, standing where a walk of the queue would begin
tiny : Closed Γ₁ (obs (Pow K))
tiny = ofᵉ (strmᵗ emptyᵉ ∷ [])

idO : Fn Γ₁ [] [] [] (obs (Pow K)) (obs (Pow K))
idO = varᵗ (here refl)

-- the reifying scan under one more layer, so it stores what `inner`
-- stores and charges one rung more for it
wrapped : Closed Γ₁ (obs (Pow K))
wrapped = mapᵉ idO inner

----------------------------------------------------------------------
-- THE ARRIVAL, ADMITTING.  The door has room, so the arrival is
-- subscribed and its reifying scan lands in the table -- beside a
-- queue of two the count never reads.
----------------------------------------------------------------------
stRun : EvalSt e₀
stRun = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} nothing 0
                        (tiny ∷ wrapped ∷ []) false)
          (st-init e₀)

postRun : EvalSt e₀
postRun = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
            (thru-outer mergeAllᵒ 0) root vals₀ false (sched-init e₀ sl₁) stRun))))

outerCharge : ℕ
outerCharge = szCount sl₁ (EvalSt.nodes stRun)
                (thru-outer {Γ = Γ₁} {u = obs (Pow K)} mergeAllᵒ 0) vals₀

-- LOAD-BEARING: the charge is the ARRIVAL's, so it does not move when
-- the queue beside it does -- fifteen here and fifteen at an empty
-- queue.  A count that had joined the parked entries in would report
-- sixteen.
outerCharge≡ : outerCharge ≡ 15
outerCharge≡ = refl

-- LOAD-BEARING: the first is the rung the refutation killed, so a
-- charge that had not grown would repeat it in the second.  The
-- second could fail for a queue entry the step had rewritten.
outerRows : List Bool
outerRows = all (λ kv → boundedNode (iterSize 65 1 65) (proj₂ kv))
                (EvalSt.nodes postRun)
          ∷ all (λ kv → boundedNode (iterSize 65 outerCharge 65) (proj₂ kv))
                (EvalSt.nodes postRun)
          ∷ []

outerRows≡ : outerRows ≡ false ∷ true ∷ []
outerRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied out
-- beside a claim.  The premises are left as arguments: the row asserts
-- the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: the reading whose level never counts the queue it must
-- nonetheless leave bounded.  The point is the one the merging door
-- hands the descent -- the caller's path under a `from-inner`
-- decoration, one gas spent, the minted instance counted -- so the row
-- computes what a crossing at this state computes.
tieParkedOuterRun : Confirms
  (subscribeE-sz-store {e = e₀} sl₁ (gasPad 7 g0) inner
     (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init e₀ sl₁) { nextNode = 1 }) stRun 65 65
     (iterSize 65 (layᵉ inner + slotsSize sl₁) 65))
tieParkedOuterRun = λ _ _ _ _ _ → refl
