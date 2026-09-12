------------------------------------------------------------------
-- THE EVALUATOR NEVER GETS STUCK: no run of any program emits the dry
-- marker.
--
-- `evaluate` descends on an accessibility witness, and three of its
-- clauses are guarded by a decidable comparison that can fail — the
-- share connect's unconnected count, the inner subscribe's rank, the μ
-- unfold's syncSize.  A failing guard is not an error: the clause
-- returns a `dry` emit and the run continues, so exhaustion is VISIBLE
-- in the output rather than fatal.  This says the guards never fail at
-- the triple the evaluator actually enters at, which is what makes the
-- descent discipline invisible to every statement above it.
--
-- IT IS THE WHOLE OF WHAT THE DESCENT COSTS, and stating it in one line
-- is the point.  Its type mentions no witness, no triple and no order:
-- `evaluate` seeds its own entry, so every consumer sees a total
-- function on `Fuel`, and this is the only place the seeding has to be
-- shown adequate.  A statement anywhere above that had to know which
-- triple a subterm runs at would be a statement the descent had leaked
-- into.
--
-- WHAT IS OWED, and it is three separate readings rather than one
-- arithmetic.  The μ guard is the easy one: `syncSizeᵉ` is strictly
-- monotone on subterms, so an unfolded body is strictly under its own
-- redex and the entry seeds the whole program's reading.  The connect
-- guard is the next: a connect moves one shared slot out of the
-- unconnected count and nothing puts one back, so the count the entry
-- seeds bounds the connects any run can make.  THE RANK GUARD IS THE
-- OPEN ONE — the claim that an emitted inner's nesting is strictly
-- under its emitter's — and it is this development's nesting face
-- restated at the one place it is actually spent.
------------------------------------------------------------------
module Verify-Rank-Sufficient where

open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim  using (Fuel)
open import Rx.Exp   using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (evaluate; hasDry)

postulate
  rank-sufficient :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (evaluate fuel e ins) ≡ false
