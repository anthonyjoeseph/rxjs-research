-- THE FLATTENER REDUCIBILITY ARMS ASSERT NOTHING, AND THIS FILE
-- INHABITS THEM WITHOUT READING A HYPOTHESIS.  `RedStep` is a Σ over
-- the run the frame produces, and its witness is the prover's to
-- choose: it asks only that SOME derivation exist whose value column
-- is reducible.  The domain relation offers a premise-free arm at each
-- of these frames -- an inner reaction that hands its batch back, a
-- walk that consumes nothing -- and each of those arms has an EMPTY or
-- a PASSED-THROUGH value column, so the reducibility conjunct is
-- discharged by `[]` or by the hypothesis the statement was handed
-- anyway.
--
-- WHY THAT IS A REFUTATION AND NOT A SHORTCUT.  The premise-free arms
-- are deliberate: they are the machine's type-mismatch and missing-node
-- fallbacks, and the relation is written to be BUILT from the
-- evaluator's own result, where a constructor whose result index is
-- fixed admits no run the machine did not take.  That argument holds in
-- the builder's direction and fails in this one, because a prover
-- choosing its own witness is not the machine.  So the store carrier
-- these statements were held open for is not what they were waiting on:
-- as written they never demanded the store be read at all, and a proof
-- of the whole face could land while proving nothing about what a
-- flattener forwards.
--
-- The repair is to pin the witness rather than to weaken the arms:
-- either the fallbacks carry the side conditions that distinguish them,
-- making the relation functional at these frames, or the statements
-- take the derivation rather than producing it.  Both are restatements,
-- and this file goes red the day either lands -- which is the point.
module Refuted.Red-Step-Vacuous where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.Product using (_,_)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Val; obs)
open import Rx.Evaluator using (Sched; EvalSt; Path; NodeId; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; from-inner; thru-outer;
  aliveThroughᶠ)
open import Rx.Evaluator.Domain using (step-from-inner; step-thru-outer; react-false; react-alive; react-dead; finish-nil;
  thruWalk⇓; walk-nil; walk-cons; consume-all-nil; consume-switch-nil; consume-exhaust-nil)
open import Rx.Evaluator.Reducible using (Red; RedStep)

-- AN INNER REACTION HANDS ITS OWN BATCH BACK, at both settings of the
-- finished flag: unfinished is `react-false` outright, and finished is
-- a case on liveness whose live arm passes through and whose dead arm
-- reaches `finish-nil`, which passes through too.  So the conjunct is
-- discharged by the hypothesis the statement already carries, and no
-- queue is ever drained.
from-inner-vacuous : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                     (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
                     (κ : Path Γ lo s t)
                     {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
                     (sched : Sched Γ) (st : EvalSt e)
                   → RedStep {e = e} id now (from-inner op allNid inst) κ vals fin sched st
from-inner-vacuous id now op allNid inst κ rv false sched st =
  _ , step-from-inner react-false , rv
from-inner-vacuous id now op allNid inst κ rv true sched st
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eq
... | true  = _ , step-from-inner (react-alive eq) , rv
... | false = _ , step-from-inner (react-dead eq finish-nil) , rv

-- A FLATTENING WALK CAN CONSUME NOTHING.  Each operator's own
-- `consume-*-nil` is premise-free, so a walk over any batch produces an
-- empty value column and the conjunct is `[]`.
walk-nothing : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
               (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t) (id : Id) (now : Tick)
               (vals : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e)
             → thruWalk⇓ {e = e} op nid κ id now vals sched st ([] , [] , sched , st)
walk-nothing op nid κ id now [] sched st = walk-nil
walk-nothing mergeAllᵒ nid κ id now (o ∷ os) sched st =
  walk-cons consume-all-nil (walk-nothing mergeAllᵒ nid κ id now os sched st)
walk-nothing switchᵒ nid κ id now (o ∷ os) sched st =
  walk-cons consume-switch-nil (walk-nothing switchᵒ nid κ id now os sched st)
walk-nothing exhaustᵒ nid κ id now (o ∷ os) sched st =
  walk-cons consume-exhaust-nil (walk-nothing exhaustᵒ nid κ id now os sched st)

-- AND THAT WALK DISCHARGES THE STATEMENT at the unfinished setting,
-- which is every step of a source that has not completed.  The finished
-- setting adds only the wrap's node rewrite, and the wrap forwards the
-- value column it is handed rather than reading one.
thru-vacuous : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
               (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
               (κ : Path Γ lo u t)
               {vals : List (Val Γ (obs u))} → All (Red (obs u)) vals →
               (sched : Sched Γ) (st : EvalSt e)
             → RedStep {e = e} id now (thru-outer op nid) κ vals false sched st
thru-vacuous id now op nid κ {vals} rv sched st =
  _ , step-thru-outer (walk-nothing op nid κ id now vals sched st) , []
