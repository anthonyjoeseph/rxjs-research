-- ══════════════════════════════════════════════════════════════════
-- THE JOIN ACROSS A BURST: whether several observables reaching one
-- node owe their SUM or their MAX.  The currency is settled and the
-- CROSSING's own fold now carries the max by proof; where the join is
-- still a mechanism choice is the queue a drain reads, which joins its
-- parked entries the same way and against the same rung.

-- WHY IT IS A REAL QUESTION AND NOT A CHOICE OF SLACK.  The conclusion
-- the arm must establish is PER VALUE -- every delivered value under
-- one cap -- and each delivered value comes out of ONE arrival's run.
-- So a sum is honest only if a burst can compound: if one arrival's
-- emission can feed another's inside the same frame, or if the shared
-- `*All` node the burst drains into carries a quantity neither arrival
-- produced alone.

-- FORK: stepFrame-sz-store-inner

-- THE ROWS.  A `thru-outer` frame is run on a burst of three twelve-rung
-- duplication chains -- the same arrival the single-value refutation is
-- built on, three times over -- where the two joins read thirty-seven
-- and thirteen.  What the frame delivers is covered by the MAX reading,
-- and the rung the refutation kills is read beside it so the row cannot
-- be bought by a generous cap.  The node table the burst drains into is
-- read at the same rung, which is the half a compounding burst would
-- break first: three arrivals park into one queue.

-- ALL THREE SINKS ARE RUN, since a merging sink is the one where the
-- arrivals plainly do not interact and would be the weakest of the
-- three to stand on alone.  A switching sink cancels the inner it holds
-- as each new arrival lands and an exhausting one drops what arrives
-- while it is busy, so the burst is entered under admission rules that
-- differ across the pair, against the same rung.

-- WHAT THE ROWS DO NOT BUY.  One burst width and one arrival shape, so
-- nothing about a burst whose members differ; nothing about the SCAN
-- residue, since a threading operator inside an arrival is what the
-- layer count reads at one layer however wide it runs; and no row here
-- discharges the store conclusion this fork names -- the table is read
-- at the same rung, but what reaches that statement is the SEPARATION,
-- the join being one choice across both halves of the arm.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Burst where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (nothing)
open import Data.List using (List; []; _∷_; foldr; length)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Val; obs)
open import Rx.Layer-Count using (layᵛ)
open import Rx.Slots using (slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; switchᵒ; exhaustᵒ;
  thru-outer; switch-st; exhaust-st; installNode; st-init; stepFrame;
  sched-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?; szCount)
open import Refuted.Frame-Step-Size-Cross
  using (Γ₁; sl₁; Pow; chain; e₂; st₂)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE TWO JOINS, of one signature so the fork's separation is a value.
-- The second is `src`'s own arm, applied at this file's slots, so a
-- restatement of the arm moves it.  The node table is the witness's
-- own: this arm reads no node, since what it prices arrived in its own
-- list, and handing it the real table is what says so.
----------------------------------------------------------------------
Burst : Set
Burst = List (Val Γ₁ (obs (Pow 12)))

sumJ : Burst → ℕ
sumJ vals = foldr (λ v a → layᵛ (obs (Pow 12)) v + a) 0 vals + slotsSize sl₁

maxJ : Burst → ℕ
maxJ vals = szCount sl₁ (EvalSt.nodes st₂)
              (thru-outer {Γ = Γ₁} {u = Pow 12} mergeAllᵒ 0) vals

----------------------------------------------------------------------
-- THE BURST.  Three of the arrival the single-value refutation is built
-- on, which is as wide as a burst whose members the level admits can be
-- at this cap.
----------------------------------------------------------------------
vals₃ : Burst
vals₃ = chain 12 ∷ chain 12 ∷ chain 12 ∷ []

-- LOAD-BEARING, and it is this file's product: the two joins part on a
-- burst the walk admits.  `apart` cannot be written where the frame is
-- handed one arrival, which is where every earlier row stood.
separates : Separates sumJ maxJ
separates = separates-at vals₃ (λ ())

-- LOAD-BEARING: it says how far apart, and it is what the rows below
-- are read against.  A burst of one would report the two equal.
joins : List ℕ
joins = sumJ vals₃ ∷ maxJ vals₃ ∷ length vals₃ ∷ []

joins≡ : joins ≡ 37 ∷ 13 ∷ 3 ∷ []
joins≡ = refl

----------------------------------------------------------------------
-- WHAT THE FRAME DOES WITH THE BURST.  The run is the evidence: a
-- delivered list read out of a hand-written state would say nothing
-- about what the walk can reach.
----------------------------------------------------------------------
step₃ : _
step₃ = stepFrame {e = e₂} (gasPad 8 g0) 0 0
          (thru-outer mergeAllᵒ 0) root vals₃ false
          (sched-init e₂ sl₁) st₂

out₃ : List (Val Γ₁ (Pow 12))
out₃ = proj₁ step₃

post₃ : EvalSt e₂
post₃ = proj₂ (proj₂ (proj₂ (proj₂ step₃)))

-- LOAD-BEARING: the first entry is the rung the single-arrival
-- refutation kills, so a row bought by a generous cap would report
-- `true` twice.  The second is the MAX join, and it holds -- three
-- arrivals deliver three values and none of them is larger than what
-- one delivers.
valRows : List Bool
valRows = valsSz? {Γ = Γ₁} {s = Pow 12} (iterSize 51 1 51) out₃
        ∷ valsSz? {Γ = Γ₁} {s = Pow 12} (iterSize 51 (maxJ vals₃) 51) out₃
        ∷ []

valRows≡ : valRows ≡ false ∷ true ∷ []
valRows≡ = refl

-- LOAD-BEARING: this is the half a compounding burst breaks first,
-- since all three arrivals drain into ONE queue and a table holding
-- their sum would outrun a rung bought for the largest of them.
storeRow : all (λ kv → boundedNode (iterSize 51 (maxJ vals₃) 51) (proj₂ kv))
             (EvalSt.nodes post₃) ≡ true
storeRow = refl

----------------------------------------------------------------------
-- THE OTHER TWO SINKS, at the same burst and the same rung.  Each is
-- entered at its own idle state, so the admission rule is the live one
-- rather than one the burst has already exhausted.
----------------------------------------------------------------------
stSw : EvalSt e₂
stSw = installNode 0 (switch-st {Γ = Γ₁} nothing false) (st-init e₂)

stEx : EvalSt e₂
stEx = installNode 0 (exhaust-st {Γ = Γ₁} false false) (st-init e₂)

stepSw : _
stepSw = stepFrame {e = e₂} (gasPad 8 g0) 0 0
           (thru-outer switchᵒ 0) root vals₃ false
           (sched-init e₂ sl₁) stSw

stepEx : _
stepEx = stepFrame {e = e₂} (gasPad 8 g0) 0 0
           (thru-outer exhaustᵒ 0) root vals₃ false
           (sched-init e₂ sl₁) stEx

-- LOAD-BEARING: the two halves at each of the two remaining sinks, so
-- the MAX reading is not held up by the one admission rule that lets
-- every arrival through.
sinkRows : List Bool
sinkRows = valsSz? {Γ = Γ₁} {s = Pow 12}
             (iterSize 51 (maxJ vals₃) 51) (proj₁ stepSw)
         ∷ all (λ kv → boundedNode (iterSize 51 (maxJ vals₃) 51) (proj₂ kv))
               (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ stepSw)))))
         ∷ valsSz? {Γ = Γ₁} {s = Pow 12}
             (iterSize 51 (maxJ vals₃) 51) (proj₁ stepEx)
         ∷ all (λ kv → boundedNode (iterSize 51 (maxJ vals₃) 51) (proj₂ kv))
               (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ stepEx)))))
         ∷ []

sinkRows≡ : sinkRows ≡ true ∷ true ∷ true ∷ true ∷ []
sinkRows≡ = refl
