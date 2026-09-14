------------------------------------------------------------------
-- THE ORDER THE EVALUATOR DESCENDS ON.

-- The evaluator peels at exactly three edges and holds its witness fixed
-- at every other clause, because every other clause stays at one nesting
-- level.  Each of the three is an edge at which a lexicographic triple
-- strictly drops — the unconnected shares outermost, then the current
-- value's rank, then the current expression's syncSize — so the descent
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

-- WELL-FOUNDEDNESS IS STATED HERE AND PROVEN, and its shape is not a
-- matter of taste: the proof NESTS one `where` level per component,
-- each binding its own accessibility witness in an enclosing pattern,
-- because a flat helper taking all three at once cannot work — its
-- off-component arms have to hand the outer witnesses back, and a
-- witness handed back is REBUILT rather than passed on, so nothing is
-- structurally smaller and the checker names every recursive call.
-- The trap itself is a fact about Agda rather than about this order,
-- so it is recorded in `docs/agda-traps.md`.
------------------------------------------------------------------
module Rx.Strat-Order where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Product using (_×_; _,_)
open import Induction.WellFounded using (Acc; acc; WellFounded)

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
-- constructor per RE-ENTRY edge, and that correspondence is the whole
-- design: `ltU` is the connect edge, `ltR` the hop edge, `ltS` the μ
-- edge.  Read the other way it is a coverage claim — a fourth
-- constructor here would mean a fourth edge in the evaluator, and a
-- re-entry site inhabiting none of the three is a site this order does
-- not yet cover.

-- AND THAT COVERAGE CLAIM IS HELD BY A MACHINE RATHER THAN BY THIS
-- PARAGRAPH, IN TWO PLACES.  The builder takes an `Acc` over this order
-- as an ARGUMENT, so Agda's own termination check holds every member of
-- its cycle to descending on something it carries -- per call site,
-- rather than on a declaration's word.  What that cannot see is a cycle
-- re-entering the block from OUTSIDE it, so `make recursion-cover` cuts
-- the builder's call graph and fails on any cycle the source does not
-- declare; today it leaves exactly the one the builder declares
-- structural.  So the three constructors here are not a guess at which
-- sites matter, and a fourth site goes red rather than compiling
-- quietly.
------------------------------------------------------------------

infix 4 _≺_

data _≺_ : Tri → Tri → Set where
  ltU : ∀ {U′ U r′ r s′ s} → U′ < U → (U′ , r′ , s′) ≺ (U , r , s)
  ltR : ∀ {U r′ r s′ s}    → r′ < r → (U  , r′ , s′) ≺ (U , r , s)
  ltS : ∀ {U r s′ s}       → s′ < s → (U  , r  , s′) ≺ (U , r , s)

------------------------------------------------------------------
-- WELL-FOUNDEDNESS.  Three nested levels, one per component: the
-- outermost binds `U`'s witness, and a drop in `U` restarts the two
-- below it at the naturals' own well-foundedness, since neither is
-- constrained when the component above them moves.

-- IT IS BUILT ON THE SKIPPING WITNESS, AND THAT IS A REDUCTION
-- REQUIREMENT RATHER THAN A TASTE.  The evaluator RUNS on this proof —
-- the bug cache and the oracle both normalise a subscription — so every
-- component's accessibility is unfolded at every edge.  The ordinary
-- witness is structural in the proof it is handed, so it walks the
-- whole component per step; the skipping one hands back an accessor
-- that reads nothing, and the components here are seeded from program
-- size.
------------------------------------------------------------------

≺-wellFounded : WellFounded _≺_
≺-wellFounded (U , r , s) =
  goU (<-wellFounded-fast U) (<-wellFounded-fast r) (<-wellFounded-fast s)
  where
  goU : ∀ {U} → Acc _<_ U → ∀ {r} → Acc _<_ r → ∀ {s} → Acc _<_ s →
        Acc _≺_ (U , r , s)
  goU {U} (acc fU) = goR
    where
    goR : ∀ {r} → Acc _<_ r → ∀ {s} → Acc _<_ s → Acc _≺_ (U , r , s)
    goR {r} (acc fr) = goS
      where
      goS : ∀ {s} → Acc _<_ s → Acc _≺_ (U , r , s)
      goS (acc fs) = acc λ
        { (ltU u) → goU (fU u) (<-wellFounded-fast _) (<-wellFounded-fast _)
        ; (ltR p) → goR (fr p) (<-wellFounded-fast _)
        ; (ltS p) → goS (fs p) }
