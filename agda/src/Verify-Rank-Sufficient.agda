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

-- TWO OF THE THREE GUARDS HAVE THEIR CURRENCY ALREADY PROVEN, and it is
-- deleted rather than absent — a different starting position from the one
-- this row's class describes, and the class is still right, because a
-- measure is not an instantiation.  What is recoverable is postulate-free
-- and, for the μ guard, stated in this evaluator's own order rather than in
-- the grant the tower spent it on, so it transports as a CLAIM and not
-- merely as a harness.  The `≺` it is stated over is the live one,
-- constructor for constructor.  None of it needs this header to be FOUND:
-- the sha is in `scripts/attic.txt`, so `make find` and `make find-prose`
-- already reach the statements and the dead routes on their own.
--
-- PROBED: `Probed.Descent` — twelve recursive programs, every one green, and
--   they are the first rows ever run against this statement.  What they cover,
--   guard by guard: the μ peel at every program, since all twelve are `μᵉ`;
--   the connect peel at the five carrying a slot, `shared` and `scripted`
--   both, one of them a diamond reaching the share twice in an instant; and
--   the RANK peel at the recursive self-reference, which is an emitted inner
--   that unfolds to its own emitter, at μ nested directly in μ, and at a share
--   holding a recursion — the shape whose nesting the guard cannot read off
--   the term it compares.  Each row pins its run's EVENT COUNT beside it, so
--   none is `false` by an empty stream.  THE BOUNDARY, and it is the whole of
--   what is left: one fuel, hand-written programs, μ nested two deep and no
--   deeper.  Nothing random has ever reached here, because the generator this
--   repo sweeps cannot produce `μᵉ` at all.
-- RECOVERY: `git show 919f115:agda/src/Verify-Budget-Sufficient/Measures.agda`
--   restores the μ guard's whole reading: `unfoldμ-shrinks` is two lines over
--   `syncSize-unfoldμ`, which is one line over a `syncSize-elimG` whose
--   clauses run over the constructors this `Exp` still has.  The sibling
--   `Wet/Part6.agda` then carries `mu-edge≺`, which is that inequality under
--   `ltS` — the guard's obligation verbatim.
-- RECOVERY: `git show 919f115:agda/src/Rx/Layer-Count.agda` restores a
--   payload-blind layer count and a μ depth, BOTH POSTULATE-FREE, whose two
--   unfold equations are the rank guard's currency proven at the operation
--   the guard is about: the layer count is INVARIANT under `unfoldμ`, and
--   the μ depth drops exactly one.  A measure surviving the unfold is the
--   half of a nesting descent that is not bookkeeping.
-- RECOVERY: `git show 919f115:agda/src/Rx/Clos-Size.agda` restores
--   `syncSizeᵉ` with the slot telescope substituted in, also postulate-free
--   — the μ guard reads the UNSUBSTITUTED size, and a slot reference is one
--   symbol standing for a definition of any size, so this is where that gap
--   was already measured.
postulate
  rank-sufficient :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (evaluate fuel e ins) ≡ false
