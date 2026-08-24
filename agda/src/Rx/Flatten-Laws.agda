-- ══════════════════════════════════════════════════════════════════
-- WHAT BOUNDED CONCURRENCY NEWLY OWES.
--
-- `flattenᵉ` replaced two primitives whose union it is: unbounded merge
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
-- These are the facts the two verification trees will draw on.  They
-- are stated here rather than at their consumers because both
-- consumers need them and neither can import the other, which is the
-- lowest-module rule `make dup-check` exists to enforce.
--
-- WHAT IS DELIBERATELY NOT HERE.  A bound on the QUEUE's length.  A
-- parked inner is retained state that no width measure reads, which
-- looks like a new unbounded object — but concat already carried
-- exactly that list, so whatever the budget face pays for it, it is
-- already paying.  Stating a fresh queue bound here would re-derive a
-- fact the caps face owns, at a module that cannot see the syntax the
-- bound must be stated over.
-- ══════════════════════════════════════════════════════════════════
module Rx.Flatten-Laws where

open import Data.Bool  using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List  using (List; []; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat   using (ℕ; _≤_; _≤ᵇ_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum   using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Gas; Id; Tick)
open import Rx.Exp  using (Ctx; Closed; obs; Val)
open import Rx.Evaluator using (EvalSt; NodeId; NodeState; Path; Sched;
  flatten-st; flattenDrain; flattenᵒ; hasRoom; lookupNode; thruConsume)

-- `hasRoom` says a lane is FREE; this says the count is LEGAL.  They
-- are not negations of each other at the boundary — at `just m` with
-- `act ≡ m` there is no room and the count is still legal — and the
-- boundary is exactly where a saturated flatten sits, so conflating
-- them makes the invariant unprovable at the only state that matters
withinLimit : Maybe ℕ → ℕ → Bool
withinLimit nothing  act = true
withinLimit (just m) act = act ≤ᵇ m

-- the parked queue of whatever state sits at a node, as the claim that
-- it is EMPTY.  A predicate and not an equation because `NodeState`
-- holds the queue's element type existentially, so the two sides of an
-- equation would not even be at the same type
emptyQueue? : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Set
emptyQueue? (just (flatten-st lim act q od)) = q ≡ []
emptyQueue? _                                = ⊥

postulate

  -- THE DRAIN GATE, stated.  A drain stops for exactly one of two
  -- reasons and never for a third: it ran out of parked inners, or it
  -- ran out of lanes.  Every completion argument downstream reads this
  -- — `thruWrap` and `innerFinish` both report done on
  -- `active ≡ 0 ∧ null queue`, and without saturation a flatten could
  -- report not-done while holding a queue nothing will ever drain.
  -- The concat face got this for free: at limit 1 the two disjuncts
  -- are the loop's own two exits, so nobody had to name it
  drain-saturates :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
      (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
      (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
      (sched : Sched Γ) (st : EvalSt e) →
    let r    = flattenDrain g allNid κ id now lim act q sched st
        act′ = proj₁ (proj₂ (proj₂ r))
        q′   = proj₁ (proj₂ (proj₂ (proj₂ r)))
    in (q′ ≡ []) ⊎ (hasRoom lim act′ ≡ false)

  -- THE LANE BOUND.  A legal count stays legal across a drain.  This is
  -- what makes the limit MEAN anything: without it, `flattenᵉ (just 2)`
  -- is a merge with a decoration.  It is also the conjunct that pins
  -- the drain's Σ-shaped receipts — `act′` is otherwise upward-closed
  -- in every statement that mentions it, which is the vacuity shape.
  -- At `just 1` this specialises to concat's `innerActive` boolean,
  -- which is what transports the well-formed tree's concat clauses
  drain-within-limit :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
      (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
      (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
      (sched : Sched Γ) (st : EvalSt e) →
    withinLimit lim act ≡ true →
    let r    = flattenDrain g allNid κ id now lim act q sched st
        act′ = proj₁ (proj₂ (proj₂ r))
    in withinLimit lim act′ ≡ true

  -- THE RESIDUE SHRINKS, in the one form the caps face needs: a drain
  -- never lengthens the queue.  Anything the budget tree already proves
  -- by walking concat's queue is stated over its LENGTH, and at limit 1
  -- this reduces to the suffix fact `concatDrain` had structurally.
  -- Above 1 it does not — the loop shifts several elements in one
  -- instant — so the fact has to be claimed rather than read off the
  -- recursion
  drain-queue-shrinks :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
      (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
      (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
      (sched : Sched Γ) (st : EvalSt e) →
    let r  = flattenDrain g allNid κ id now lim act q sched st
        q′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
    in length q′ ≤ length q

  -- CONSERVATIVITY AT INFINITY.  At `nothing` the queue is dead: every
  -- arriving inner is subscribed on the spot, so a node that starts
  -- with an empty queue keeps one forever.  This is what transports the
  -- whole merge face — every proof there was written against a state
  -- with no queue at all, and this says the field it now carries is
  -- never populated.  Note the shape: the hypothesis is a LOOKUP and
  -- not a `flatten-st` pattern, because the caller holds a node table
  -- and not a state, and threading the table is what made the merge
  -- face's clauses read the way they do
  unbounded-never-parks :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (g : Gas) (nid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
      (o : Val Γ (obs u)) (act : ℕ) (od : Bool)
      (sched : Sched Γ) (st : EvalSt e) →
    lookupNode nid (EvalSt.nodes st) ≡ just (flatten-st {t = u} nothing act [] od) →
    let r   = thruConsume g flattenᵒ nid κ id now o sched st
        st′ = proj₂ (proj₂ (proj₂ r))
    in emptyQueue? (lookupNode nid (EvalSt.nodes st′))
