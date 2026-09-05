-- ══════════════════════════════════════════════════════════════════
-- THE LIVE ARM, AT THE ONLY SHAPE THAT CAN MOVE IT — AND REACHED BY
-- RUNNING RATHER THAN BY BUILDING THE PATH.
--
-- TARGET: stepFrame-nest-live-outer @2d49ae
--
-- WHY THIS PROGRAM.  A live source's nesting is the nesting of its
-- PENDING values, and the evaluator mints a live carrying a nested
-- value in one clause only: subscribing a `deferᵉ`, whose pending entry
-- is the body at observable type.  A scripted slot cannot deliver one,
-- since scripts are data-typed by construction, so the body has to be
-- produced by the program mid-chain.  `progL` does exactly that: a
-- `mapᵉ` over the async input hands the outer *All a deferred nest per
-- arrival, so the chain the evaluator presents subscribes it and the
-- fold moves.  Every other family here reads zero on both sides, which
-- is a fact about their syntax and not about the arm.
--
-- WHAT IS LOAD-BEARING.  The left side is the evaluator's own live fold
-- after a real `chainStep`, the right names the program and the slot
-- vocabulary alone, and the depth axis is swept — the fold moves with
-- the nest and the charge moves with the syntax, so the ordering is a
-- race between two growing quantities rather than a constant against
-- zero.  Both sides are pinned before the ordering is taken.  The
-- charge is the syntactic surrogate the tree proves the arms' increment
-- dominates, so green here implies the arm at this program and red here
-- does not refute it.  The arm's FRAME GRANT is read by the TIE at the
-- foot of this file and by nothing above it: the rows here run the
-- composite, which never states the leaf's premises.  The REGISTRY rows beside it are pins rather than
-- evidence: that fold's whole-chain statement is a definition now, and
-- they hold the evaluator to the reading it was written from.
-- ══════════════════════════════════════════════════════════════════
module Probed.Chain-Step-Live-Deferred where

open import Data.Bool using (true; false; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; foldr; length)
open import Data.Maybe using (nothing)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Exp; natᵗ; sizeᵉ; syncSizeᵉ; ofᵉ; mapᵉ; mergeAllᵉ;
         switchAllᵉ; deferᵉ; strmᵗ; nat̂; input)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next; cascadeLatch; chainStep;
  chainsOf; NodeId; NodeState; mergeAll-st; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; stepFrame;
  thru-outer)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; nestUnit; regsNestMax; slotsNestSum)
open import Refuted.Demand-Programs using (Γ₂; insF)
open import Verify-Budget-Sufficient.Live-Nest-Walk
  using (stepFrame-nest-live-outer)
open import Probed.Apparatus using (Confirms)

slots : Slots Γ₂
slots = insF 1 1 2

-- a nest the depth measure reads all the way down
deepE : ∀ {Θ} → ℕ → Exp Γ₂ [] [] Θ natᵗ
deepE 0       = ofᵉ (nat̂ 0 ∷ [])
deepE (suc m) = switchAllᵉ (ofᵉ (strmᵗ (deepE m) ∷ []))

-- one deferred nest per arrival on the async input
progL : ℕ → Closed Γ₂ natᵗ
progL m = mergeAllᵉ nothing (mapᵉ (strmᵗ (deferᵉ (deepE m))) (input (fsuc fzero)))

sucGL : ℕ → ℕ
sucGL m = suc (syncSizeᵉ (progL m) + hopDᵉ 0 (slotHop 0 slots) (progL m))

sub : (m : ℕ) → Sched Γ₂ × EvalSt (progL m)
sub m = let r = subscribeE (gasPad (sucGL m) g0) (progL m) root 0 0
                           (sched-init (progL m) slots) (st-init (progL m))
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

charge : ℕ → ℕ
charge m = nestUnit (progL m) slots + (2 + sizeᵉ (progL m))

-- the two components before and after the first chain of the first
-- arrival's cascade, taken off states the evaluator reached
reading : (m : ℕ) → (ℕ × ℕ) × (ℕ × ℕ)
reading m with sched-next (proj₁ (sub m))
... | inj₁ _        = (0 , 0) , (0 , 0)
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub m))
...   | []            = (0 , 0) , (0 , 0)
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub m))
            r   = chainStep 1 a c sd st₀
        in (liveMax sd , liveMax (proj₁ (proj₂ r)))
         , (regsNestMax (EvalSt.registry st₀)
           , regsNestMax (EvalSt.registry (proj₂ (proj₂ r))))

row : (m : ℕ) → ℕ × ℕ
row m = proj₁ (reading m)

regsRow : (m : ℕ) → ℕ × ℕ
regsRow m = proj₂ (reading m)

packed : ℕ
packed = proj₁ (row 1) + 100 * proj₂ (row 1) + 10000 * charge 1
       + 1000000 * proj₁ (row 3) + 100000000 * proj₂ (row 3)
       + 10000000000 * charge 3
       + 1000000000000 * proj₁ (regsRow 1) + 100000000000000 * proj₂ (regsRow 1)
       + 10000000000000000 * proj₁ (regsRow 3)
       + 1000000000000000000 * proj₂ (regsRow 3)

figures≡ : packed ≡ 1010101260300180100
figures≡ = refl

fits : (proj₂ (row 1) ≤ᵇ proj₁ (row 1) ⊔ charge 1)
     ∧ (proj₂ (row 3) ≤ᵇ proj₁ (row 3) ⊔ charge 3)
     ∧ (proj₂ (regsRow 1) ≤ᵇ proj₁ (regsRow 1) ⊔ charge 1)
     ∧ (proj₂ (regsRow 3) ≤ᵇ proj₁ (regsRow 3) ⊔ charge 3) ≡ true
fits = refl

----------------------------------------------------------------------
-- THE TIE, at the deferred family's own entry state.  The type is
-- generated from the statement, so the row reports the arm as it now
-- reads rather than a component reading kept beside it by hand.
--
-- THE NODE ID COMES FROM THE RUN, and it has to: `thruConsume` is the
-- IDENTITY at a nid the table does not hold, so a row at an invented
-- one would read the arm against a step that did nothing and report
-- preservation for free.
--
-- THE THREE PREMISES ARE LEFT STANDING, so what each row asserts is
-- the arm with the potential and the value bound unasked -- a stronger
-- claim than the instance rather than a weaker one.
--
-- AND THE DEPTH AXIS SEPARATES THE TWO NUMBERS, which is what these
-- rows are for.  At depth ONE the frame leaves a live fold of 1 under
-- a slot vocabulary of 2, so nothing else is asked.  At depth THREE
-- the fold is 3 against the same vocabulary, so the vocabulary no
-- longer covers it and something must -- and BOTH rows stand at a
-- potential grant of ZERO, with the size budget carrying the depth-3
-- reading alone.  The budget is not a number chosen to clear the fold:
-- it is the value's OWN size, which is why `valsV` computes it rather
-- than stating it.  The figures pin the fold and the size at both
-- depths, so the crossing is arithmetic: what the vocabulary covers
-- does not grow with the nest, the fold does, and the size stays above
-- it because depth truncates at the defer the size counts through.
----------------------------------------------------------------------

mergeNid : List (NodeId × NodeState Γ₂) → NodeId
mergeNid []                              = 0
mergeNid ((k , mergeAll-st _ _ _ _) ∷ _) = k
mergeNid (_ ∷ ns)                        = mergeNid ns

tieNid : (m : ℕ) → NodeId
tieNid m = mergeNid (EvalSt.nodes (proj₂ (sub m)))

-- the smallest size budget the value admits, so the rows below are
-- stated at the tightest V there is rather than at a number chosen to
-- clear the fold
valsV : (m : ℕ) → ℕ
valsV m = sizeᵉ (defL m)
  where defL : ℕ → Closed Γ₂ natᵗ
        defL k = deferᵉ (deepE k)

tieLive1 : Confirms
  (stepFrame-nest-live-outer (gasPad (sucGL 1) g0) 1 0 mergeAllᵒ (tieNid 1)
     root (deferᵉ (deepE 1) ∷ []) false (proj₁ (sub 1)) (proj₂ (sub 1)) 0 0
     (valsV 1))
tieLive1 = λ _ _ _ → ≤ᵇ⇒≤ _ _ tt

tieLive3 : Confirms
  (stepFrame-nest-live-outer (gasPad (sucGL 3) g0) 1 0 mergeAllᵒ (tieNid 3)
     root (deferᵉ (deepE 3) ∷ []) false (proj₁ (sub 3)) (proj₂ (sub 3)) 0 0
     (valsV 3))
tieLive3 = λ _ _ _ → ≤ᵇ⇒≤ _ _ tt

-- the nid the run allocated, the vocabulary the join offers, and the
-- fold either side of the frame -- so a row carried by a no-op step
-- or by an absent node is visible as one rather than green
hasMerge : List (NodeId × NodeState Γ₂) → ℕ
hasMerge []                              = 0
hasMerge ((_ , mergeAll-st _ _ _ _) ∷ _) = 1
hasMerge (_ ∷ ns)                        = hasMerge ns

stepLive : (m : ℕ) → ℕ
stepLive m =
  liveMax (proj₁ (proj₂ (proj₂ (proj₂
    (stepFrame (gasPad (sucGL m) g0) 1 0 (thru-outer mergeAllᵒ (tieNid m))
       root (deferᵉ (deepE m) ∷ []) false (proj₁ (sub m)) (proj₂ (sub m)))))))

tieFigs : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
tieFigs = length (EvalSt.nodes (proj₂ (sub 1)))
        , hasMerge (EvalSt.nodes (proj₂ (sub 1)))
        , tieNid 1
        , slotsNestSum slots
        , liveMax (proj₁ (sub 1))
        , stepLive 1
        , stepLive 3
        , valsV 1
        , valsV 3

tieFigs≡ : tieFigs ≡ (1 , 1 , 0 , 2 , 0 , 1 , 3 , 8 , 16)
tieFigs≡ = refl

----------------------------------------------------------------------
-- THE ONE REGION THE ROWS ABOVE LEAVE OPEN: AN ENTRY FOLD ALREADY
-- NONZERO.  Every row above enters at a fold of ZERO, so what they pin
-- is the mint and not the way a mint COMBINES with what is already
-- live.  Both sides of the conclusion carry the entry fold -- the left
-- through whatever survives the step, the right as a summand of the
-- join -- so the region is safe only if the two readings combine by
-- MAX.  A frame that deepened a standing live source, or one whose
-- mint stacked on the fold rather than joining it, reads one past the
-- join here and these rows go red.
--
-- AND THE STATE IS REACHED BY RUNNING, NOT BUILT.  The first frame is
-- the one the rows above take, and its OUTPUT schedule and state are
-- what the second frame is handed, so the entry fold is a fold the
-- evaluator actually left rather than one written into a record.  The
-- two depths are crossed in BOTH directions, because a mint that
-- stacked would be invisible in the direction where the deeper value
-- arrives second.
----------------------------------------------------------------------

frameOn : (m : ℕ) → Closed Γ₂ natᵗ → Sched Γ₂ → EvalSt (progL m)
        → Sched Γ₂ × EvalSt (progL m)
frameOn m v sc st =
  let r = stepFrame (gasPad (sucGL m) g0) 1 0 (thru-outer mergeAllᵒ (tieNid m))
                    root (v ∷ []) false sc st
  in proj₁ (proj₂ (proj₂ (proj₂ r))) , proj₂ (proj₂ (proj₂ (proj₂ r)))

after₁ : (m : ℕ) → Sched Γ₂ × EvalSt (progL m)
after₁ m = frameOn m (deferᵉ (deepE m)) (proj₁ (sub m)) (proj₂ (sub m))

-- (the fold entering the second frame , the fold leaving it)
twice : (m m' : ℕ) → ℕ × ℕ
twice m m' = liveMax (proj₁ (after₁ m))
           , liveMax (proj₁ (frameOn m (deferᵉ (deepE m'))
                              (proj₁ (after₁ m)) (proj₂ (after₁ m))))

-- LOAD-BEARING in both directions: shallow-onto-deep would rise off
-- the entry fold if the mint stacked, and deep-onto-shallow would rise
-- past the deeper value's own reading.
twicePacked : ℕ
twicePacked = proj₁ (twice 3 1) + 100 * proj₂ (twice 3 1)
            + 10000 * proj₁ (twice 1 3) + 1000000 * proj₂ (twice 1 3)

-- deep-then-shallow reads 3 -> 3 and shallow-then-deep 1 -> 3: the
-- second frame's mint JOINS the standing fold rather than adding to
-- it, and a standing fold is not deepened by a frame that steps past
-- it.  A stacking mint would read 4 in both directions.
twicePacked≡ : twicePacked ≡ 3010303
twicePacked≡ = refl

-- and the statement itself at those two entry states, at the size
-- budget the ARRIVING value admits and no more -- so the row is asked
-- to cover the mint out of the second value alone, with the standing
-- fold carried by the join's own summand and by nothing else
tieLiveOn3 : Confirms
  (stepFrame-nest-live-outer (gasPad (sucGL 3) g0) 1 0 mergeAllᵒ (tieNid 3)
     root (deferᵉ (deepE 1) ∷ []) false (proj₁ (after₁ 3)) (proj₂ (after₁ 3))
     0 0 (valsV 1))
tieLiveOn3 = λ _ _ _ → ≤ᵇ⇒≤ _ _ tt

tieLiveOn1 : Confirms
  (stepFrame-nest-live-outer (gasPad (sucGL 1) g0) 1 0 mergeAllᵒ (tieNid 1)
     root (deferᵉ (deepE 3) ∷ []) false (proj₁ (after₁ 1)) (proj₂ (after₁ 1))
     0 0 (valsV 3))
tieLiveOn1 = λ _ _ _ → ≤ᵇ⇒≤ _ _ tt

----------------------------------------------------------------------
-- AND THE TWO AXES A FRAME HAS THAT A SUBSCRIBE DOES NOT.  An ARRIVAL
-- takes the operator's arm -- switch KILLS the standing inner, exhaust
-- DROPS the arrival while one is active -- so unlike at a subscribe
-- the operator is LIVE here and a row over it can genuinely fail.  And
-- a frame steps a LIST: two values in one step mint twice against a
-- single `V`, which the premise bounds each value by rather than their
-- sum, so a pair of mints that stacked would read past it.  Both are
-- taken at the compounded entry state, where a standing fold is there
-- to be stacked on.
----------------------------------------------------------------------

opLive : AllOp → (m m' : ℕ) → ℕ
opLive op m m' = liveMax (proj₁ (proj₂ (proj₂ (proj₂
  (stepFrame (gasPad (sucGL m) g0) 1 0 (thru-outer op (tieNid m))
     root (deferᵉ (deepE m') ∷ []) false
     (proj₁ (after₁ m)) (proj₂ (after₁ m)))))))

pairLive : (m a b : ℕ) → ℕ
pairLive m a b = liveMax (proj₁ (proj₂ (proj₂ (proj₂
  (stepFrame (gasPad (sucGL m) g0) 1 0 (thru-outer mergeAllᵒ (tieNid m))
     root (deferᵉ (deepE a) ∷ deferᵉ (deepE b) ∷ []) false
     (proj₁ (after₁ m)) (proj₂ (after₁ m)))))))

widePacked : ℕ
widePacked = opLive switchᵒ 3 1 + 100 * opLive exhaustᵒ 3 1
           + 10000 * pairLive 1 1 3 + 1000000 * pairLive 1 3 1

-- every one of the four reads 3, which is the STANDING fold and not a
-- sum with it: switch kills without deepening, exhaust drops the
-- arrival outright, and a pair of arrivals in one step joins whichever
-- direction the deeper one comes in.  A stacking mint reads 4 in three
-- of the four.
widePacked≡ : widePacked ≡ 3030303
widePacked≡ = refl

tieLiveOuterSwitch : Confirms
  (stepFrame-nest-live-outer (gasPad (sucGL 3) g0) 1 0 switchᵒ (tieNid 3)
     root (deferᵉ (deepE 1) ∷ []) false (proj₁ (after₁ 3)) (proj₂ (after₁ 3))
     0 0 (valsV 1))
tieLiveOuterSwitch = λ _ _ _ → ≤ᵇ⇒≤ _ _ tt

tieLiveOuterPair : Confirms
  (stepFrame-nest-live-outer (gasPad (sucGL 1) g0) 1 0 mergeAllᵒ (tieNid 1)
     root (deferᵉ (deepE 1) ∷ deferᵉ (deepE 3) ∷ []) false
     (proj₁ (after₁ 1)) (proj₂ (after₁ 1)) 0 0 (valsV 3))
tieLiveOuterPair = λ _ _ _ → ≤ᵇ⇒≤ _ _ tt
