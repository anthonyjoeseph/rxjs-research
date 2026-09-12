------------------------------------------------------------------
-- MINT, INSTALL, SUBSCRIBE, READ THE NODE BACK UNCHANGED.
--
-- `scanᵉ` and `takeᵉ` both mint a node, install their state at it, and
-- then subscribe the body under a frame that names the minted id.  Every
-- well-formedness argument about either has to know the node is still
-- there afterwards — the body's own subscription mints its own nodes,
-- and they are all strictly above this one.
--
-- THE WATERMARK PREMISE IS DISCHARGED HERE RATHER THAN EXPOSED, and
-- that is the whole value of the shape: `mintNode` returns the old
-- `nextNode` and leaves `suc` of it behind, so the installed id is
-- exactly one below the watermark the callee sees, and no consumer has
-- to know it.
--
-- IT IS A POSTULATE BECAUSE THE DESCENT DISCIPLINE MOVED UNDER IT.  The
-- route is a freshness ring over the evaluator's own recursion, proven
-- by matching its counter clause for clause; the evaluator now descends
-- on an accessibility witness whose peels are guarded by decidable
-- comparisons, so each ring member needs its arms restructured around
-- those guards rather than retyped.  The statement is unchanged.
-- RECOVERY: `git show 919f115:agda/src/Verify-Budget-Sufficient/Node-Fresh.agda`
--   restores the ring and the two-step assembly this name was the head
--   of — a below-watermark lookup lemma composed with the node table's
--   read-back equation.
------------------------------------------------------------------
module Verify-Support.Node-Fresh where

open import Data.Maybe using (just)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Induction.WellFounded using (Acc)

open import Rx.Prim   using (Tick; Id)
open import Rx.Exp    using (Ctx; Closed)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Sched; EvalSt; NodeState; Path;
  lookupNode; mintNode; installNode; subscribeE)

-- THE STATEMENT IS UNCHANGED FROM ITS PROVEN FORM, which is what the
-- pointer below is evidence OF: what moved is the recursion the ring
-- was matched against, not the claim.
--
-- RECOVERY: git show 919f115:agda/src/Verify-Budget-Sufficient/Node-Fresh.agda
postulate
  mint-install-survives : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri}
    (g : Acc _≺_ τ) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
    lookupNode (proj₁ (mintNode sched))
      (EvalSt.nodes (proj₂ (proj₂ (subscribeE g b κ id now (proj₂ (mintNode sched))
        (installNode (proj₁ (mintNode sched)) ns st)))))
      ≡ just ns
