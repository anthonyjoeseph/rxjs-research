-- ══════════════════════════════════════════════════════════════════
-- WHAT BOUNDED CONCURRENCY NEWLY OWES.
--
-- `mergeAllᵉ` replaced two primitives whose union it is: unbounded merge
-- (`nothing`) and concat (`just 1`).  Almost nothing in the machine is
-- new — the counter was merge's, the queue was concat's, and every
-- width measure was already textually identical across the two faces,
-- so the merge bound was what the concat face already paid.  ONE thing
-- is new, and it is the whole risk surface of the change: the DRAIN
-- GATE.  Unbounded merge never queued, so it never drained; concat's
-- drain could stop at the first inner that stayed open, because its
-- capacity was one.  A drain at limit k must refill SEVERAL lanes in
-- one instant and stop on a count rather than on a flag, and that is
-- the only place a proof about the old two faces does not transfer.
--
-- These are the facts the two verification trees draw on.  They are
-- stated here rather than at their consumers because both consumers
-- need them and neither can import the other, which is the
-- lowest-module rule `make dup-check` exists to enforce.  Three of the
-- four turn out to be structural rather than semantic: the drain
-- scrutinises the GATE and nothing else, so shrinkage, saturation and
-- the lane bound all fall out of the same walk, and the queue bound the
-- caps face had proven under its own name is one of them.
--
-- WHAT IS DELIBERATELY NOT HERE.  A bound on the QUEUE's length.  A
-- parked inner is retained state that no width measure reads, which
-- looks like a new unbounded object — but concat already carried
-- exactly that list, so whatever the budget face pays for it, it is
-- already paying.  Stating a fresh queue bound here would re-derive a
-- fact the caps face owns, at a module that cannot see the syntax the
-- bound must be stated over.
-- ══════════════════════════════════════════════════════════════════
module Rx.MergeAll-Laws where

open import Data.Bool  using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List  using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat   using (ℕ; suc; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; Id; Tick)
open import Rx.Exp  using (Ctx; Closed; obs)
open import Rx.Evaluator using (EvalSt; NodeId; NodeState; Path; Sched; _↠_;
  mergeAll-st; mergeAllDrain; mergeAllᵒ; hasRoom; installNode; lookupNode;
  setNode; subscribeE; subscribeInner; thru-outer)
open import Decide using (≡ᵇ-refl)

-- `hasRoom` says a lane is FREE; this says the count is LEGAL.  They
-- are not negations of each other at the boundary — at `just m` with
-- `act ≡ m` there is no room and the count is still legal — and the
-- boundary is exactly where a saturated mergeAll sits, so conflating
-- them makes the invariant unprovable at the only state that matters
withinLimit : Maybe ℕ → ℕ → Bool
withinLimit nothing  act = true
withinLimit (just m) act = act ≤ᵇ m

-- the parked queue of whatever state sits at a node, as the claim that
-- it is EMPTY.  A predicate and not an equation because `NodeState`
-- holds the queue's element type existentially, so the two sides of an
-- equation would not even be at the same type
emptyQueue? : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Set
emptyQueue? (just (mergeAll-st lim act q od)) = q ≡ []
emptyQueue? _                                = ⊥

-- A FREE LANE MAKES THE NEXT COUNT LEGAL, and that is the whole
-- content of the two predicates being different: `hasRoom` is `<`
-- against the limit and `withinLimit` is `≤`, so the step from one to
-- the other is where the bump is paid for
room⇒legal : ∀ (lim : Maybe ℕ) (act : ℕ) →
  hasRoom lim act ≡ true → withinLimit lim (suc act) ≡ true
room⇒legal nothing  act h = refl
room⇒legal (just m) act h = h

-- THE DRAIN GATE, stated and walked.  A drain stops for exactly one of
-- two reasons and never for a third: it ran out of parked inners, or it
-- ran out of lanes.  Every completion argument downstream reads this —
-- `thruWrap` and `innerFinish` both report done on
-- `active ≡ 0 ∧ null queue`, and without saturation a mergeAll could
-- report not-done while holding a queue nothing will ever drain
drain-saturates :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
    (sched : Sched Γ) (st : EvalSt e) →
  let r    = mergeAllDrain g allNid κ id now lim act q sched st
      act′ = proj₁ (proj₂ (proj₂ r))
      q′   = proj₁ (proj₂ (proj₂ (proj₂ r)))
  in (q′ ≡ []) ⊎ (hasRoom lim act′ ≡ false)
drain-saturates g allNid κ id now lim act []      sched st = inj₁ refl
drain-saturates g allNid κ id now lim act (o ∷ q) sched st
  with hasRoom lim act in eq
... | false = inj₂ eq
... | true  with subscribeInner g mergeAllᵒ allNid κ id now o sched st
...   | _ , vs , bs , done , sched₁ , st₁ =
      drain-saturates g allNid κ id now lim
        (if done then act else suc act) q sched₁ st₁

-- THE LANE BOUND.  A legal count stays legal across a drain.  This is
-- what makes the limit MEAN anything: without it, `mergeAllᵉ (just 2)`
-- is a merge with a decoration.  It is also the conjunct that pins the
-- drain's Σ-shaped receipts — `act′` is otherwise upward-closed in
-- every statement that mentions it, which is the vacuity shape
drain-within-limit :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
    (sched : Sched Γ) (st : EvalSt e) →
  withinLimit lim act ≡ true →
  let r    = mergeAllDrain g allNid κ id now lim act q sched st
      act′ = proj₁ (proj₂ (proj₂ r))
  in withinLimit lim act′ ≡ true
drain-within-limit g allNid κ id now lim act []      sched st h = h
drain-within-limit g allNid κ id now lim act (o ∷ q) sched st h
  with hasRoom lim act in eq
... | false = h
... | true  with subscribeInner g mergeAllᵒ allNid κ id now o sched st
...   | _ , vs , bs , false , sched₁ , st₁ =
      drain-within-limit g allNid κ id now lim (suc act) q sched₁ st₁
        (room⇒legal lim act eq)
...   | _ , vs , bs , true  , sched₁ , st₁ =
      drain-within-limit g allNid κ id now lim act q sched₁ st₁ h

-- INSTALLING A NODE MAKES IT FINDABLE.  The one step between a caller
-- holding a node it just minted and a law stated over a LOOKUP, and
-- the reason the law can be stated over a lookup at all
lookup-installNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (s : NodeState Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes (installNode nid s st)) ≡ just s
lookup-installNode {Γ = Γ} nid s st = go (EvalSt.nodes st)
  where
  go : ∀ (ns : List (NodeId × NodeState Γ)) →
       lookupNode nid (setNode nid s ns) ≡ just s
  go []             rewrite ≡ᵇ-refl nid = refl
  go ((k , s′) ∷ r) with k ≡ᵇ nid in eq
  ... | true  rewrite ≡ᵇ-refl nid = refl
  ... | false rewrite eq          = go r

postulate

  -- CONSERVATIVITY AT INFINITY.  At `nothing` the queue is dead: every
  -- arriving inner is subscribed on the spot, so a node that starts
  -- with an empty queue keeps one forever.  Note the shape: the
  -- hypothesis is a LOOKUP and not a `mergeAll-st` pattern, because the
  -- caller holds a node table and not a state.
  --
  -- IT IS THE ONE OF THE FOUR THAT IS NOT LOCAL, and that is why it is
  -- the tier's risk row rather than a walk like its siblings.  The
  -- `nothing` gate is open, so every consume subscribes, and the queue
  -- the statement must report on is the one in the state the INNERS
  -- left — each inner's synchronous burst free to route back through
  -- this very node.  Nothing about that re-entry is bounded by these
  -- hypotheses, so a proof is a clause of an induction over the
  -- evaluator.  What IS local, and is why the claim is credible at
  -- all: `hasRoom nothing act` is `true` by its first clause, so the
  -- single syntactic site that appends to a queue — `thruConsume`'s
  -- capacity-shut branch — is unreachable at this limit, and the only
  -- other writer reinstalls a queue that `drain-queue-shrinks` bounds
  -- by the one it was given.
  --
  -- STATED OVER THE BURST AND NOT OVER ONE CONSUME, which is what its
  -- consumer can actually spend: `mergeAll-node` reports on the node a
  -- whole `subscribeE` left, so a per-`thruConsume` law would have to
  -- be iterated by the caller over emissions the caller cannot see.
  -- The predicate is a predicate for the reason its own definition
  -- gives, and that costs the consumer nothing: the shape conjunct
  -- pins the lookup, and `emptyQueue?` at a pinned `mergeAll-st`
  -- reduces to the equation.
  --
  -- DEAD ROUTE: it was minted to transport the merge face, and the
  --   transport did not need it — every proof written against a queueless
  --   merge state migrated to `mergeAllᵉ` by taking the CONCAT clause as the
  --   general one, which reasons about the queue rather than assuming it
  --   away.  So its consumer is not the budget tree; it is the well-formed
  --   tree's mergeAll clause, which reads a node's completion off
  --   `active ≡ 0 ∧ null queue`.
  --
  -- PROBED: `Probed.MergeAll-Queue`, at two and three OPEN inners, each
  --   row paired with the same program at `just 1` pinned FALSE — so the
  --   greens are not the vacuous kind a family of synchronously-completing
  --   inners would give, where no limit parks and every row passes.
  --   NOT REACHED, and it is the region the statement is actually about:
  --   RE-ENTRY.  Every inner in these programs is a plain scripted source,
  --   so no inner's burst routes back through the wrap's own node, and the
  --   consumes stay sequential.  The rows therefore cover the shape where
  --   the claim is easy and say nothing about the shape where it is hard.
  --   The class stands at DIFFICULTY on exactly that ground.
  --
  unbounded-never-parks :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (fuel : Gas) (nid : NodeId) (b : Closed Γ (obs u)) (κ : Path Γ u t)
      (id : Id) (now : Tick) (act : ℕ) (od : Bool)
      (sched : Sched Γ) (st : EvalSt e) →
    lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = u} nothing act [] od) →
    let r   = subscribeE fuel b (thru-outer mergeAllᵒ nid ↠ κ) id now sched st
        st′ = proj₂ (proj₂ r)
    in emptyQueue? (lookupNode nid (EvalSt.nodes st′))

-- THE RESIDUE SHRINKS, in the one form the caps face needs: a drain
-- never lengthens the queue.  `mergeAllDrain` returns `[]` when it runs
-- the queue out, the recursive residue while lanes remain free, and the
-- QUEUE IT WAS GIVEN when the capacity gate shuts — never anything
-- longer than that, so a cardinality conjunct survives a reinstall by
-- widening alone.  The claim was drafted as a postulate on the reading
-- that above limit 1 the loop shifts several elements per instant and
-- so could not be read off the recursion; it can, because the gate and
-- not the lane count is what the recursion scrutinises
drain-queue-shrinks :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
    (sched : Sched Γ) (st : EvalSt e) →
  let r  = mergeAllDrain g allNid κ id now lim act q sched st
      q′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
  in length q′ ≤ length q
drain-queue-shrinks g allNid κ id now lim act []      sched st = z≤n
drain-queue-shrinks g allNid κ id now lim act (o ∷ q) sched st
  with hasRoom lim act
... | false = ≤-refl
... | true  with subscribeInner g mergeAllᵒ allNid κ id now o sched st
...   | _ , vs , bs , done , sched₁ , st₁ =
      ≤-trans (drain-queue-shrinks g allNid κ id now lim
                 (if done then act else suc act) q sched₁ st₁)
              (n≤1+n (length q))
