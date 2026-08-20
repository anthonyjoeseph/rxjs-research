------------------------------------------------------------------
-- FRESHNESS OF THE NODE TABLE ACROSS ONE SUBSCRIBE — one leaf, where
-- three separate postulates were each asserting a corner of it.
--
-- THE FACT.  `subscribeE` never writes a node BELOW the `nextNode`
-- watermark it was handed.  Everything it writes, it minted.  So a node
-- the CALLER installed — at an id the caller minted, hence strictly
-- below the watermark the callee receives — comes back untouched, and
-- the caller can read it back by `lookupNode-setNode` (.Node-Table).
--
-- WHY IT IS TRUE, from the evaluator (Rx/Evaluator.agda, read
-- 2026-08-20).  The only writers to a node are `stepFrame`'s scan-f and
-- take-f clauses (`setNode` / `takeDispatch`), and both fire only out of
-- `pushBurst`.  `pushBurst` applies `stepFrame` for ONE frame and RETURNS
-- the transformed burst — it does not walk the rest of the path — so a
-- subscribe pushes only through the frame it just built, over a nid it
-- just minted.  The share path does not break this: `sharedConnect`
-- lets the connect burst flow up the FIRST subscriber's own frames (the
-- burst it returns), while the other registered chains are served by
-- dispatch on later ARRIVALS, not by the connect.
--
-- WHAT IT IS NOT, and the alignment is the trap: the caps face.
-- `capsOK?` BOUNDS every node and IDENTIFIES none, so no strengthening of
-- a caps receipt reaches a statement that a particular nid holds a
-- particular value — the difference is in KIND, not in a quantifier.
--
-- ⚠ THE LEAF IS OPEN, and it is the whole of the missing structure: a
-- clause-by-clause induction over `subscribeE`, mutual with `pushBurst`,
-- `stepFrame`, `dispatch` and `subscribeInner`, carrying monotonicity of
-- `Sched.nextNode` alongside.  `.Keeps-Ring` is the shape to copy — it
-- runs the same induction for SLOTS and `connectedShares` — but it cannot
-- host this one: `thruConsume`'s concat-park writes a node minted BEFORE
-- the reaction, so node-freshness is false at a `KeepsC` boundary and
-- true at a `subscribeE` one.  The watermark is what distinguishes them,
-- which is why it is an argument here and not a field there.
--
-- PROBED 2026-08-20 (.Scan-Node-Probe, a MODULE_ROOT under `make
-- bug-cache`): twelve green rows on the scan consumer's composite, which
-- is this leaf's conclusion at `k` the freshly minted scan node —
-- including a nested scan, take-under-scan, all four *All operators, and
-- a SHARED slot with two subscribers pinning `connectedShares` non-empty
-- so the connect demonstrably happened.  Not covered: a `κ` ending in
-- `share-sink`, which needs a mid-run state.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Node-Fresh where

open import Data.Nat     using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Maybe   using (just)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import Rx.Prim      using (Gas; Tick; Id)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Sched; EvalSt; Path; NodeId; NodeState;
                                lookupNode; mintNode; installNode; subscribeE)

open import Verify-Budget-Sufficient.Node-Table using (lookupNode-setNode)

-- THE LEAF.  Below the watermark, the node table is frozen by a subscribe.
postulate
  subscribeE-nodes-below : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (k : NodeId) →
    suc k ≤ Sched.nextNode sched →
    lookupNode k (EvalSt.nodes (proj₂ (proj₂ (subscribeE g b κ id now sched st))))
      ≡ lookupNode k (EvalSt.nodes st)

-- THE SHAPE EVERY CONSUMER WANTS: mint, install, subscribe under a frame
-- that mentions the minted nid, read the node back unchanged.  The
-- watermark premise is `≤-refl` here and nowhere else has to know that —
-- `mintNode` returns the old `nextNode` and leaves `suc` of it behind, so
-- the installed id is exactly one below the watermark the callee sees.
mint-install-survives : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode (proj₁ (mintNode sched))
    (EvalSt.nodes (proj₂ (proj₂ (subscribeE g b κ id now (proj₂ (mintNode sched))
      (installNode (proj₁ (mintNode sched)) ns st)))))
    ≡ just ns
mint-install-survives g b κ id now ns sched st =
  trans (subscribeE-nodes-below g b κ id now (proj₂ (mintNode sched))
           (installNode (proj₁ (mintNode sched)) ns st)
           (proj₁ (mintNode sched)) ≤-refl)
        (lookupNode-setNode (proj₁ (mintNode sched)) ns (EvalSt.nodes st))
