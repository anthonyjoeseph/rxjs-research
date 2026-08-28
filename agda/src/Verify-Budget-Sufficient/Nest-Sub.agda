------------------------------------------------------------------
-- THE CEILING AN ARRIVAL CANNOT LEAVE, AND WHY IT LIVES INSIDE THE
-- GRANT RATHER THAN BESIDE THE CAP.
--
-- The nest walk reads every arrival at the head's own written cap,
-- and that reading is false: an arrival is the head's syntax with the
-- payload SUBSTITUTED IN, so a step function naming its payload twice
-- hands back about twice the payload while contributing a constant to
-- the head.  One substitution is the caps face's own size step, and a
-- descent performs at most the head's size of them, so a cap stepped
-- that many times dominates everything one hop can reach.
--
-- WHAT MAKES IT COST NOTHING IS THE GAS.  A substituting re-entry is
-- exactly where the evaluator spends a unit of gas -- that is why the
-- subscription terminates -- so the hop budget is already threaded
-- through every statement on this face.  Indexing the tower by it
-- makes the re-entry read off definitionally: the child runs at the
-- stepped cap with one less gas, and `tow` of that is `tow` of the
-- parent's, the same numeral rather than a bound to re-establish.
-- The alternative devices both cost an index -- a second cap tied by
-- a premise every predicate in the walk would have to carry, or the
-- caps face's existential level in every conclusion.
--
-- AND IT IS SEALED, because it lands in the grant, which is what the
-- walk's conclusions are stated against.  The interface is the two
-- monotonicities plus the step equation.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Sub where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Evaluator using (iterSize)
open import Verify-Budget-Sufficient.Caps using
  (Caps; caps; iterSize-infl; iterSize-mono-count; iterSize-mono-base)

-- THE ARRIVAL-SIDE CAP, which is the walk's own cap with its size
-- field replaced.  The width and the registration count are left
-- alone deliberately: a widened width would weaken the room record's
-- queue conjunct, and only the size premise is the one a substitution
-- breaks.
subCaps : ℕ → Caps → Caps
subCaps Ŝ c = caps Ŝ (Caps.cWid c) (Caps.cReg c)

abstract
  towStep : ℕ → ℕ
  towStep s = iterSize s s s

  tow : Gas → ℕ → ℕ
  tow g0     s = s
  tow (gs g) s = tow g (towStep s)

  tow-step : ∀ (g : Gas) (s : ℕ) → tow (gs g) s ≡ tow g (towStep s)
  tow-step g s = refl

  towStep-infl : ∀ (s : ℕ) → s ≤ towStep s
  towStep-infl zero    = z≤n
  towStep-infl (suc s) = iterSize-infl (suc s) (s≤s z≤n) (suc s) (suc s)

  towStep-mono : ∀ {s s′ : ℕ} → s ≤ s′ → towStep s ≤ towStep s′
  towStep-mono {zero}          le = z≤n
  towStep-mono {suc s} {suc s′} le =
    ≤-trans (iterSize-mono-base (suc s) le le)
            (iterSize-mono-count (suc s′) (suc s′) (s≤s z≤n) le)

  tow-infl : ∀ (g : Gas) (s : ℕ) → s ≤ tow g s
  tow-infl g0     s = ≤-refl
  tow-infl (gs g) s = ≤-trans (towStep-infl s) (tow-infl g (towStep s))

  tow-mono-s : ∀ (g : Gas) {s s′ : ℕ} → s ≤ s′ → tow g s ≤ tow g s′
  tow-mono-s g0     le = le
  tow-mono-s (gs g) le = tow-mono-s g (towStep-mono le)

  -- THE GAS DROP, which is what a re-entry that does NOT substitute
  -- needs: one less hop can only reach a smaller ceiling.
  tow-drop : ∀ (g : Gas) (s : ℕ) → tow g s ≤ tow (gs g) s
  tow-drop g s = tow-mono-s g (towStep-infl s)

  -- THE SAME INFLATION WITH ITS GAS LEFT TO INFERENCE, which is what
  -- the walk's clauses spend: the hop budget there is a pattern rather
  -- than a name, and every clause would otherwise repeat it.
  tow-infl′ : ∀ {g : Gas} {s : ℕ} → s ≤ tow g s
  tow-infl′ {g} {s} = tow-infl g s
