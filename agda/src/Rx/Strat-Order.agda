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
------------------------------------------------------------------

infix 4 _≺_

data _≺_ : Tri → Tri → Set where
  ltU : ∀ {U′ U r′ r s′ s} → U′ < U → (U′ , r′ , s′) ≺ (U , r , s)
  ltR : ∀ {U r′ r s′ s}    → r′ < r → (U  , r′ , s′) ≺ (U , r , s)
  ltS : ∀ {U r s′ s}       → s′ < s → (U  , r  , s′) ≺ (U , r , s)
