-- THE INPUT BOUND DOES NOT HOLD OF A RUNTIME OBSERVABLE AT AN ARBITRARY
-- FLOOR, AND THE LEAF ASSERTING IT AT ONE IS FALSE AS WRITTEN.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- WHAT IS REFUTED IS THE QUANTIFIER, NOT THE MACHINE.  A value of
-- observable type IS a closed expression over the same context, so it
-- may name any input the context has; the predicate reads that input's
-- position against the floor it is handed.  Take the floor to be zero
-- and the value to be the context's own first input, and the two
-- disagree at the smallest instance the syntax admits.  Nothing subtle
-- happens here and that is the finding: the statement quantifies over
-- every floor while the fact it wants is about the floors a RUN
-- produces, so no proof was ever going to close the gap.
--
-- AND IT IS CONSUMED BY THE EVALUATOR ITSELF, WHICH IS WHY DELETING IT
-- IS NOT THE REPAIR.  The inner-subscription clause needs an inhabitant
-- to hand the walk it re-enters, so the leaf is load-bearing for the
-- machine to be WELL-TYPED and not merely for a proof above it.  The
-- sound form relates the value to the chain it arrived on — a fact
-- about the run state rather than about the term — so the repair is a
-- restatement carrying that relation, and until it lands every
-- statement proven over this leaf stands on a false hypothesis.
module Refuted.Inner-Floor where

open import Data.Bool using (T)
open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Nat using (ℕ)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)

open import Rx.Exp using (Ctx; Val; natᵗ; obs; inputsBelowᵉ; input)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT HERE RATHER THAN IMPORTED, so that this is
-- evidence about the form it was taken against and not about whatever
-- the postulate says today.  A floor conditioned on the value's
-- provenance makes the witness below fail to typecheck rather than
-- quietly agree with it, which is the answer this file is here to give.
----------------------------------------------------------------------

InnerBelow : Set
InnerBelow = ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (o : Val Γ (obs t))
           → T (inputsBelowᵉ k o)

----------------------------------------------------------------------
-- THE ADVERSARIAL PAIR.  One slot, so the context has an input to name;
-- the floor at zero, which is the value the predicate compares against
-- and which no hypothesis forbids.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the smallest runtime observable that reads its own context
o₀ : Val Γ₁ (obs natᵗ)
o₀ = input zero

----------------------------------------------------------------------
-- THE CROSSING.  `inputsBelowᵉ 0 (input zero)` is `0 <ᵇ 0`, so the
-- predicate is `false` and `T` of it is empty — the statement hands
-- back an inhabitant of the empty type directly, with no comparison to
-- pin.
----------------------------------------------------------------------

inner-below-false : InnerBelow → ⊥
inner-below-false h = h 0 o₀
