------------------------------------------------------------------
-- THE ORDER `Gas` STANDS IN FOR.

-- The evaluator peels gas at exactly three edges and holds it fixed at
-- every other clause, because every other clause stays at one nesting
-- level.  Each of the three is an edge at which a lexicographic triple
-- strictly drops — the unconnected shares outermost, then the current
-- value's rank, then the current expression's syncSize — so the counter
-- buys structural VISIBILITY for the termination checker and nothing
-- else mathematical.

-- WHAT THIS MODULE EXISTS TO SAY IS THAT THE ORDER NEEDS NO CAPS.  The
-- same triple already has a flattening into one natural, and that
-- flattening is where every size and rank ceiling in this development's
-- descent argument comes from: packing (U , r , s) into a single number
-- requires multipliers that dominate r and s, so a step that drops U
-- has to be told r and s stayed under theirs.  A lexicographic order
-- packs nothing, and so asks for neither.  Stating it separately is
-- what makes that a checkable claim rather than an observation: the
-- three constructors below carry one inequality each and no ceiling
-- anywhere, and the edges that inhabit them are proven in exactly that
-- form.

-- IT IS IN `Rx` RATHER THAN BESIDE THE MEASURES because it mentions
-- nothing of this development — it is a relation on ℕ × ℕ × ℕ, and the
-- evaluator is where it is ultimately spent.  Nothing here may grow a
-- dependency on the measures; a fact that needs one belongs where that
-- measure lives.

-- WELL-FOUNDEDNESS IS NOT STATED HERE, AND THAT IS THE WIRING LAW
-- RATHER THAN A DOUBT.  It is five lines of nested `Acc` recursion over
-- the naturals' own well-foundedness, and it was written and checked
-- before being taken back out: nothing consumes an accessibility
-- witness until a recursion descends on one, so today it has ZERO
-- consumers and a piece that cannot be plugged in is not progress.  It
-- lands in the commit that first recurses on this order, which is where
-- its fit is tested rather than asserted — and the trap that version
-- cost is recorded in `docs/agda-traps.md`, not here, since it is a
-- fact about Agda and not about this order.
------------------------------------------------------------------
module Rx.Strat-Order where

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------
-- THE CARRIER.  A named synonym rather than a record, because every
-- producer of one of these builds it from three measures that are
-- already separately named, and a record would put a constructor
-- between the edge lemmas and the arithmetic they are proven from.
------------------------------------------------------------------

Tri : Set
Tri = ℕ × ℕ × ℕ

------------------------------------------------------------------
-- THE ORDER.  Lexicographic, outermost component first.  One
-- constructor per gas edge, and that correspondence is the whole
-- design: `ltU` is the connect edge, `ltR` the hop edge, `ltS` the μ
-- edge.  Read the other way it is a coverage claim — a fourth
-- constructor here would mean a fourth edge in the evaluator, and a
-- re-entry site inhabiting none of the three is a site this order does
-- not yet cover.

-- AND THAT COVERAGE CLAIM IS HELD BY A MACHINE RATHER THAN BY THIS
-- PARAGRAPH: `make recursion-cover` cuts the evaluator's three declared
-- peels and fails on any cycle left standing the source does not declare
-- structural.  Today it cuts both of the evaluator's multi-member
-- recursions down to singletons and leaves exactly one pair, which walks
-- the expression — so the three constructors here are not a guess at
-- which sites matter, and a fourth site would go red rather than compile
-- quietly.  Two of that check's readings decided this type's shape: the
-- merge join's drain wants no component of its own, since it rides its
-- own queue and its one outward call peels inside the callee; and the
-- share hop's counter is a separate component reached one way, so it
-- composes without sharing a measure and buys no fourth field here.

-- AND THE RESIDUE OF THAT CENSUS IS EXACTLY ONE SITE, WHICH IS WHY THE
-- COVERAGE CLAIM ABOVE IS NARROWER THAN IT READS.  Three peels are
-- declared and only two of them are edges of this order — the
-- subscribe-inner peel is `ltR` and the shared-connect peel is `ltU`,
-- while the μ peel is a self-edge the component check cannot see and
-- `ltS` covers.  The third declared peel, the share fan-out's, inhabits
-- NONE of the three, and the reason it needs none is the one-way
-- composition: the fan-out's clique calls into the subscribe clique and
-- is never called back, so the two are separate strata rather than one
-- recursion, and a stratum above another is ordered by nothing they
-- share.  Read the constructor count that way and it is a claim about
-- ONE stratum: a fourth constructor would mean a fourth edge inside the
-- subscribe clique, and a fan-out edge is not one.
------------------------------------------------------------------

infix 4 _≺_

data _≺_ : Tri → Tri → Set where
  ltU : ∀ {U′ U r′ r s′ s} → U′ < U → (U′ , r′ , s′) ≺ (U , r , s)
  ltR : ∀ {U r′ r s′ s}    → r′ < r → (U  , r′ , s′) ≺ (U , r , s)
  ltS : ∀ {U r s′ s}       → s′ < s → (U  , r  , s′) ≺ (U , r , s)
