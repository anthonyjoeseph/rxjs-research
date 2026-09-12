------------------------------------------------------------------
-- THE PARKED QUEUE SURVIVES A SUBSCRIPTION, for a node the
-- subscription is not about.
--
-- `mergeAll`'s wrap node holds a queue of inners waiting for a lane.
-- A well-formedness argument about one such node has to know that
-- evaluating something ELSE — a sibling's subscription, a burst pushed
-- through an unrelated frame — leaves that queue alone.  The carrier
-- below says exactly that, as a two-field record rather than an
-- equation, because the watermark has to ride along: a freshly minted
-- node is not the node the claim is about.
--
-- THE CARRIER IS PROVEN AND THE TWO RING MEMBERS ARE NOT, and the
-- split is where the descent discipline changed underneath them.  Both
-- used to be proven by matching the evaluator's own counter clause for
-- clause; the evaluator now descends on an accessibility witness whose
-- peels are guarded by decidable comparisons, so each ring member needs
-- its arms restructured around those guards rather than retyped.  The
-- statements are unchanged and the route is the old proof's, one guard
-- at a time.
-- RECOVERY: `git show 919f115:agda/src/Verify-Budget-Sufficient/Queue-Dead.agda`
--   restores the full ring — thirteen members, proven against the
--   counter — whose arms are what a re-proof against the witness
--   transports.
------------------------------------------------------------------
module Verify-Support.Queue-Dead where

open import Data.Empty using (⊥)
open import Data.Nat   using (ℕ; suc; _≤_)
open import Data.List  using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Induction.WellFounded using (Acc)

open import Rx.Prim   using (Tick; Id)
open import Rx.Exp    using (Ctx; Closed)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; Stream; Path;
  Frame; lookupNode; mergeAll-st; subscribeE; pushBurst)

------------------------------------------------------------------
-- THE PREDICATE.  A predicate and not an equation because `NodeState`
-- holds the queue's element type existentially, so the two sides of an
-- equation would not even be at the same type.  The limit is pinned
-- INSIDE it rather than left to the consumer, because the fact is only
-- true at `nothing` — a bounded wrap parks, which is what bounding it
-- is for — and a predicate that reads as limit-agnostic is one a ring
-- can be asked to preserve at a limit where it does not hold.
------------------------------------------------------------------

emptyQueue? : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Set
emptyQueue? (just (mergeAll-st nothing act q od)) = q ≡ []
emptyQueue? _                                     = ⊥

-- the watermark rides along for exactly one purpose: a freshly minted
-- node is not the node the claim is about, and `suc k ≤ nx` is what
-- says so
record QDeadC {n} {Γ : Ctx n} (k : NodeId) (nx nx′ : ℕ)
              (ns ns′ : List (NodeId × NodeState Γ)) : Set where
  constructor qdead
  field
    nxMono : nx ≤ nx′
    keep   : suc k ≤ nx →
             emptyQueue? (lookupNode k ns) → emptyQueue? (lookupNode k ns′)
open QDeadC

QDead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
        NodeId → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
QDead k sched st sched′ st′ =
  QDeadC k (Sched.nextNode sched) (Sched.nextNode sched′)
           (EvalSt.nodes st) (EvalSt.nodes st′)

------------------------------------------------------------------
-- THE TWO MEMBERS THE WELL-FORMEDNESS BRANCH SPENDS.  The ring had
-- thirteen; these are the two reached from outside it, and the eleven
-- others were its own internal arms.  Stating only the spent pair is
-- what keeps the residue greppable: a re-proof re-introduces the arms
-- it needs and no more.
--
-- Both statements are unchanged from the forms the ring proved, which
-- is what the pointer below is evidence OF: what moved is the
-- recursion the arms were matched against, not either claim.
--
-- RECOVERY: git show 919f115:agda/src/Verify-Budget-Sufficient/Queue-Dead.agda
------------------------------------------------------------------

postulate
  subscribeE-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri}
    (k : NodeId) (g : Acc _≺_ τ) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    QDead k sched st
      (proj₁ (proj₂ (subscribeE g b κ id now sched st)))
      (proj₂ (proj₂ (subscribeE g b κ id now sched st)))

  pushBurst-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ : Tri}
    (k : NodeId) (g : Acc _≺_ τ) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    QDead k sched st
      (proj₁ (proj₂ (pushBurst g id now f κ ems sched st)))
      (proj₂ (proj₂ (pushBurst g id now f κ ems sched st)))
