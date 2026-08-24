-- THE UNBOUNDED QUEUE, instantiated.  Tier 0's one remaining claim says a
-- node at limit `nothing` whose queue starts empty still has an empty queue
-- after a whole subscribe burst; it had never been instantiated.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library layout
-- makes the name unresolvable there) and nothing in the proof may rest on
-- it.  Checked by `make probed`, claimed by `Probed.Main`.
-- TARGET: pushBurst-queue-dead
--
-- WHY IT IS TESTABLE AT ALL, and which SIDE.  The conclusion is a predicate
-- on a node LOOKUP after a run, so it computes end to end at a closed
-- program: subscribe, read the node the wrap minted, ask whether its queue
-- is null.  The hypothesis computes too — the node is installed by the wrap
-- clause itself, so it is discharged by the same run rather than assumed.
--
-- EVERY ROW IS PAIRED WITH ITS NEGATIVE CONTROL, and that is the whole
-- design.  A green `queueNull?` proves nothing on its own: a program whose
-- inners all COMPLETE synchronously never parks at any limit, so it reports
-- an empty queue at `just 1` too, and the row could not have failed.  Each
-- program is therefore run at `nothing` AND at `just 1`, and the `just 1`
-- row is pinned FALSE.  That is what makes the pair evidence: the same
-- program, the same burst, the same node, and the only difference is the
-- limit the claim is about.
module Probed.MergeAll-Queue where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; null)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat  using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin  using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp  using (Ctx; Closed; natᵗ; strmᵗ; input; ofᵉ; mergeAllᵉ)
open import Rx.Evaluator using (EvalSt; NodeState; mergeAll-st; mergeAllᵒ;
  subscribeE; sched-init; st-init; budgetAt; root; lookupNode; mintNode;
  installNode; thru-outer; _↠_)
open import Rx.Slots using (scripted; Slots)

----------------------------------------------------------------------
-- Two OPEN inners.  `ofᵉ` completes inside its own subscribe, so a
-- program built from those cannot park at any limit and cannot tell the
-- two limits apart; a cold source with an async tail stays live, which
-- is what makes the lane count climb and the gate shut.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

ins : Slots Γ₂
ins zero             = scripted {ok = tt} (cold [] ((after 0 , 7) ∷ []))
ins (suc zero)       = scripted {ok = tt} (cold [] ((after 0 , 8) ∷ []))
ins (suc (suc ()))

-- the queue predicate, as a Bool so a row is a `refl`.  `false` on a
-- missing node too, so a row that loses the node reads as a failure
-- rather than as a vacuous pass
queueNull? : Maybe (NodeState Γ₂) → Bool
queueNull? (just (mergeAll-st lim act q od)) = null q
queueNull? _                                 = false

-- TWO open inners, which is the smallest shape that can park at all
P2 : Maybe ℕ → Closed Γ₂ natᵗ
P2 lim = mergeAllᵉ lim (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input (suc zero)) ∷ []))

-- THREE, the second inner repeated: at `just 1` two of them park, so the
-- row separates "the gate shuts" from "the queue holds exactly one"
P3 : Maybe ℕ → Closed Γ₂ natᵗ
P3 lim = mergeAllᵉ lim (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input (suc zero))
                             ∷ strmᵗ (input (suc zero)) ∷ []))

-- the node the wrap minted, after the whole subscribe burst
NODE : (e : Closed Γ₂ natᵗ) → Maybe (NodeState Γ₂)
NODE e =
  lookupNode (proj₁ (mintNode (sched-init e ins)))
    (EvalSt.nodes (proj₂ (proj₂
      (subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)))))

----------------------------------------------------------------------
-- LOAD-BEARING: the claim's own limit.
----------------------------------------------------------------------

_ : queueNull? (NODE (P2 nothing)) ≡ true
_ = refl

_ : queueNull? (NODE (P3 nothing)) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE CONTROLS.  Same programs, same burst, limit `just 1` — and the
-- rows above are worth something exactly because these are FALSE.
----------------------------------------------------------------------

_ : queueNull? (NODE (P2 (just 1))) ≡ false
_ = refl

_ : queueNull? (NODE (P3 (just 1))) ≡ false
_ = refl

----------------------------------------------------------------------
-- AND THE NODE IS THERE.  `queueNull?` is `false` on a missing node,
-- so the two controls would read the same way if the lookup had failed
-- outright; these pin that the state really is a `mergeAll-st`.
----------------------------------------------------------------------

nodeThere? : Maybe (NodeState Γ₂) → Bool
nodeThere? (just (mergeAll-st lim act q od)) = true
nodeThere? _                                 = false

_ : nodeThere? (NODE (P2 (just 1))) ≡ true
_ = refl

_ : nodeThere? (NODE (P3 (just 1))) ≡ true
_ = refl

----------------------------------------------------------------------
-- WHERE THE CLAIM IS PINNED, which is not where its consumer reads.
-- `subscribeAll` is mint, then `subscribeE` on the OUTER under a
-- `thru-outer` frame, then `pushBurst` of that burst through the frame
-- -- and `pushBurst` is the only thing that reaches `thruConsume`, so
-- it is the only thing that can ever park.  These rows run the outer
-- subscribe ALONE, at the limit where parking is known to happen.
----------------------------------------------------------------------

-- the node after the OUTER subscribe only -- the earlier instant, kept
-- because the rows below are what rule it out as a place to pin
INTER : Maybe ℕ → Maybe (NodeState Γ₂)
INTER lim =
  let e   = P2 lim
      sd  = sched-init e ins
      nid = proj₁ (mintNode sd)
  in lookupNode nid (EvalSt.nodes (proj₂ (proj₂
       (subscribeE (budgetAt e ins 0) (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input (suc zero)) ∷ []))
         (thru-outer mergeAllᵒ nid ↠ root) 0 0 (proj₂ (mintNode sd))
         (installNode nid (mergeAll-st {t = natᵗ} lim 0 [] false) (st-init e))))))

-- DEGENERATE BY CONSTRUCTION, and pinning it is the finding: at `just 1`
-- the finished wrap parks (the control above is FALSE) while the same
-- program at the same limit reports an EMPTY queue here.  So the
-- difference between the two limits is invisible at this instant, and a
-- statement pinned here cannot be the one its consumer spends.
_ : queueNull? (INTER (just 1)) ≡ true
_ = refl

_ : queueNull? (INTER nothing) ≡ true
_ = refl
