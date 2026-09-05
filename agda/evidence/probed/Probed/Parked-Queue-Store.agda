-- ══════════════════════════════════════════════════════════════════
-- THE PARKED QUEUE, WHICH NO ROW AT EITHER STORE HALF HAD REACHED.
--
-- TARGET: stepFrame-sz-store-inner @b7ce7a
-- TARGET: subscribeInner-sz-store @b27028
--
-- WHAT WAS UNTESTED, AND WHY NO READING OF THE DELIVERED LIST COULD
-- REACH IT.  A `*All` node holds programs it could not admit, and the
-- table reading prices them by their own syntax -- so they are the one
-- part of the table that is not a trace of anything the frame handed
-- on.  Every witness at either half so far installs exactly ONE node
-- and enters at an EMPTY queue, so what a queue of several buys was
-- open at both arms at once.
--
-- THE TWO ARMS TREAT IT AS DIFFERENT OBJECTS, which is the finding.
-- The inner arm RUNS the queue: the drain subscribes every entry in
-- turn, threading one table through all of them, so the charge reads
-- the queue and joins its entries by max.  A crossing subscription
-- never looks at it: the level it is held to is the arrival's own
-- layers and the telescope, and a queue standing beside the arrival
-- moves neither of those, so the entries have to survive a level that
-- was never bought for them.  That row is read at the frame, which at
-- ONE arrival, a door with room and no close is the subscription
-- itself.
--
-- WHERE THE MAX COULD HAVE FAILED AND DID NOT.  Three parked entries,
-- of nought, fourteen and fifteen layers, drained through one door
-- into one table: a later subscription reads what an earlier one left,
-- so a run whose stored cells compounded would need the entries added
-- rather than joined, and the max would be short.  It is not.  The two
-- rival readings beside it are: the queue read as the frame LEAVES it,
-- which a full drain empties, and the outer arm's own count carried
-- across, which at an empty arrival list is the telescope alone.
--
-- WHAT THE ROWS DO NOT BUY.  One queue depth at each arm, and one door
-- -- a switch holds a node id and an exhaust two bits, so neither has
-- a queue at all and the shape does not arise there.  Nothing
-- about a queue whose entries name a SHARED slot each, where one
-- definition would run once for the several entries reaching it.  And
-- the entries here are drained to exhaustion, so the queue as ENTERED
-- and the queue as LEFT are not separated by any row here, which is
-- what `Probed.Partial-Drain-Store` reads.
-- ══════════════════════════════════════════════════════════════════
module Probed.Parked-Queue-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Closed; Fn; obs; emptyᵉ; ofᵉ; mapᵉ;
  varᵗ; strmᵗ; sizeᵉ)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; from-inner;
  thru-outer; mergeAll-st; installNode; st-init; stepFrame; sched-init;
  iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (parkedLayAt; szCount; stepFrame-sz-store-inner;
         subscribeInner-sz-store)
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
-- THE INNER ARM: a queue of three, drained through the door in one
-- step, so one table carries every subscription the drain makes.
----------------------------------------------------------------------
stQ3 : EvalSt e₀
stQ3 = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} nothing 1
                       (tiny ∷ inner ∷ wrapped ∷ []) false)
         (st-init e₀)

postQ3 : EvalSt e₀
postQ3 = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
           (from-inner mergeAllᵒ 0 7) root [] true (sched-init e₀ sl₁) stQ3))))

innerCharge : ℕ
innerCharge = parkedLayAt 0 (EvalSt.nodes stQ3) + slotsSize sl₁

-- LOAD-BEARING: the three entries' counts are distinct and the queue's
-- own reading is their max, so a charge that had read the head, the
-- last, or a sum would not report fifteen here.  The sizes say the
-- premise is met at sixty-five and not by the entries being small.
parkFigures : List ℕ
parkFigures = layᵉ tiny ∷ layᵉ inner ∷ layᵉ wrapped
            ∷ parkedLayAt 0 (EvalSt.nodes stQ3) ∷ innerCharge
            ∷ sizeᵉ tiny ∷ sizeᵉ wrapped ∷ []

parkFigures≡ : parkFigures ≡ 0 ∷ 14 ∷ 15 ∷ 15 ∷ 16 ∷ 4 ∷ 65 ∷ []
parkFigures≡ = refl

-- LOAD-BEARING: the drain ran EVERY entry rather than the first.  A
-- door that had stopped at one would leave the table one node wider,
-- and a door that had refused the queue would leave it as it was.
drainNodes≡ : length (EvalSt.nodes stQ3) ∷ length (EvalSt.nodes postQ3) ∷ []
            ≡ 1 ∷ 3 ∷ []
drainNodes≡ = refl

-- LOAD-BEARING, and this file's product at this arm: the third row is
-- the stated charge and it holds, so three subscriptions threading one
-- table do not compound past the max of what they were charged for.
-- The first rival reads the queue the step LEAVES, which a full drain
-- empties; the second is the outer arm's own count carried across,
-- which at an empty arrival list is the telescope alone.
innerRows : List Bool
innerRows = all (λ kv → boundedNode
                          (iterSize 65 (parkedLayAt 0 (EvalSt.nodes postQ3)
                                         + slotsSize sl₁) 65)
                          (proj₂ kv))
                (EvalSt.nodes postQ3)
          ∷ all (λ kv → boundedNode (iterSize 65 (slotsSize sl₁) 65) (proj₂ kv))
                (EvalSt.nodes postQ3)
          ∷ all (λ kv → boundedNode (iterSize 65 innerCharge 65) (proj₂ kv))
                (EvalSt.nodes postQ3)
          ∷ []

innerRows≡ : innerRows ≡ false ∷ false ∷ true ∷ []
innerRows≡ = refl

----------------------------------------------------------------------
-- THE OUTER ARM, ADMITTING.  The door has room, so the arrival is
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
-- THE TIES.  The types are generated from the statements as they read,
-- so a restatement changes them rather than leaving the rungs above
-- copied out beside a claim.  The premises are left as arguments: each
-- row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: the queue is the statement's own, reached through the
-- state argument, so this is the claim at a drained queue of three.
tieParkedInner : Confirms
  (stepFrame-sz-store-inner {e = e₀} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root []
     true (sched-init e₀ sl₁) stQ3 65 65)
tieParkedInner = λ _ _ _ → refl

-- LOAD-BEARING: same, at the reading whose level never counts the
-- queue it must nonetheless leave bounded.
tieParkedOuterRun : Confirms
  (subscribeInner-sz-store {e = e₀} sl₁ (gasPad 8 g0) mergeAllᵒ 0 root 0 0
     inner (sched-init e₀ sl₁) stRun 65 65
     (iterSize 65 (layᵉ inner + slotsSize sl₁) 65))
tieParkedOuterRun = λ _ _ _ _ _ → refl
