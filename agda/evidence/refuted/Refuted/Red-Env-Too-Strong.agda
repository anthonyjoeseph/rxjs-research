-- THE ENVIRONMENT LEAF IS THE THEOREM, NOT A LEAF.  The reducibility
-- block states a fundamental theorem at TERMS -- every term evaluated
-- in a reducible environment is reducible -- and treats it as one of
-- six statements the candidate's body stands on.  It is not one of
-- six.  It proves the candidate at EVERY value of EVERY type, the
-- observables included, so the body's whole induction is redundant
-- given it and the five statements beside it assert nothing the leaf
-- does not already hand back.
--
-- WHY IT LEAKS, AND IT IS ONE CONSTRUCTOR.  The term language carries
-- `strmᵗ`, which embeds an arbitrary EXPRESSION as a term of
-- observable type, and `reify` uses it to send every runtime value
-- back into a CLOSED term.  A closed term is evaluated in the empty
-- environment, whose reducibility hypothesis is `⊤`.  So "closed
-- term" buys no smallness whatever: the leaf is applied at a term
-- containing the very expression whose subscribability was the
-- question, and it answers it for free.
--
-- WHAT THIS DOES NOT SAY.  The statement is not FALSE -- it is what
-- the whole development is trying to prove, which is exactly the
-- complaint.  A leaf is meant to be a gap smaller than its consumer.
-- This one is strictly larger, so no grind under it reduces anything
-- and its risk class understates the tier by five rows.  The repair is
-- a restatement that recurses on the TERM with `strmᵗ` appealing to
-- the expression induction under the guarded size, rather than a
-- postulate quantified over all terms at once.
module Refuted.Red-Env-Too-Strong where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂)

open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Ctx; Val; evalTm; reify)
open import Rx.Evaluator.Reducible using (Red; red-env)

-- Reflection round-trips definitionally at every former, `obs`
-- included -- that arm is where the leak lives and it is `refl`.
reify-eval : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → evalTm (reify v) ≡ v
reify-eval unitᵗ    v        = refl
reify-eval boolᵗ    v        = refl
reify-eval natᵗ     v        = refl
reify-eval (s ×ᵗ t) (a , b)  = cong₂ _,_ (reify-eval s a) (reify-eval t b)
reify-eval (s +ᵗ t) (inj₁ a) = cong inj₁ (reify-eval s a)
reify-eval (s +ᵗ t) (inj₂ b) = cong inj₂ (reify-eval t b)
reify-eval (obs u)  v        = refl

-- THE WITNESS.  The candidate, at every type and every value, out of
-- the environment leaf alone.  At `obs` this IS the top-line
-- subscription result the module's well-founded body exists to
-- produce.
red-env-proves-everything : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → Red {Γ = Γ} t v
red-env-proves-everything t v =
  subst (Red t) (reify-eval t v) (red-env (reify v) tt)
