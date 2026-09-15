------------------------------------------------------------------
-- THE MEASURE A μ UNFOLDING DOES NOT MOVE.
------------------------------------------------------------------

-- WHY A FIXPOINT AT ONE TYPE IS STILL A DESCENT.  The reducibility
-- candidate recurses on the TYPE, which the flatteners move strictly
-- down and the term-structural formers leave alone; a μ moves neither,
-- since its unfolding sits at the same type and is no subterm of the
-- fixpoint.  That reads as the one edge nothing can pay for, and it is
-- not, because the SYNTAX has already paid: `μᵉ` binds its variable
-- into the guarded context and `varᵉ` reads only from the usable one,
-- so a synchronous self-reference does not typecheck at all and every
-- recursive occurrence sits under a `deferᵉ`.
--
-- WHAT MAKES THAT A MEASURE RATHER THAN AN OBSERVATION.  The gate is
-- visible in the ELIMINATOR: the guarded-context elimination never
-- substitutes anything, its variable clause is the identity, and its
-- single route to the clause that DOES substitute is its `deferᵉ`
-- clause.  So a size that stops at a `deferᵉ` cannot see any inserted
-- copy, and the unfolding has exactly the size the body had.  The μ
-- former is the one thing that spends a unit, which is what makes the
-- peel a strict decrease.
--
-- AND IT IGNORES TERMS DELIBERATELY, WHICH IS WHAT KEEPS IT ONE
-- FUNCTION.  A term can carry an expression, so counting terms would
-- make this mutual with the whole of the syntax and oblige the
-- preservation lemma to be mutual too.  Nothing needs it: the only
-- consumer recurses into an operator's SOURCE and reaches a term's own
-- expressions through a separate leaf, so every source of a recursive
-- call is an `Exp` subterm and the sizes of the terms beside it are
-- never asked for.
module Rx.Exp.Guarded where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Exp using (Ctx; Closed; Exp; elimGExp; unfoldμ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)

-- The size, counting the formers a subscription actually descends
-- through and stopping at the gate.
gsizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
gsizeᵉ (input i)         = zero
gsizeᵉ (ofᵉ ts)          = zero
gsizeᵉ emptyᵉ            = zero
gsizeᵉ (mapᵉ f e)        = suc (gsizeᵉ e)
gsizeᵉ (takeᵉ c e)       = suc (gsizeᵉ e)
gsizeᵉ (scanᵉ f z e)     = suc (gsizeᵉ e)
gsizeᵉ (mergeAllᵉ lim e) = suc (gsizeᵉ e)
gsizeᵉ (switchAllᵉ e)    = suc (gsizeᵉ e)
gsizeᵉ (exhaustAllᵉ e)   = suc (gsizeᵉ e)
gsizeᵉ (μᵉ e)            = suc (gsizeᵉ e)
gsizeᵉ (varᵉ x)          = zero
gsizeᵉ (deferᵉ e)        = zero

-- THE WHOLE CONTENT, AND IT IS ONE LINE PER FORMER.  The two clauses
-- that carry the argument are the variable and the gate, and both are
-- constant: the variable is untouched by this elimination and the gate
-- is where the size stops looking.  Everything else is a congruence.
gsize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
              (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u)
            → gsizeᵉ (elimGExp x cl e) ≡ gsizeᵉ e
gsize-elimG x cl (input i)         = refl
gsize-elimG x cl (ofᵉ ts)          = refl
gsize-elimG x cl emptyᵉ            = refl
gsize-elimG x cl (mapᵉ f e)        = cong suc (gsize-elimG x cl e)
gsize-elimG x cl (takeᵉ c e)       = cong suc (gsize-elimG x cl e)
gsize-elimG x cl (scanᵉ f z e)     = cong suc (gsize-elimG x cl e)
gsize-elimG x cl (mergeAllᵉ lim e) = cong suc (gsize-elimG x cl e)
gsize-elimG x cl (switchAllᵉ e)    = cong suc (gsize-elimG x cl e)
gsize-elimG x cl (exhaustAllᵉ e)   = cong suc (gsize-elimG x cl e)
gsize-elimG x cl (μᵉ e)            = cong suc (gsize-elimG (there x) cl e)
gsize-elimG x cl (varᵉ y)          = refl
gsize-elimG x cl (deferᵉ e)        = refl

-- THE PEEL, WHICH IS THE LEMMA ABOVE AT THE ONE POSITION THAT MATTERS.
gsize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
              → gsizeᵉ (unfoldμ body) ≡ gsizeᵉ body
gsize-unfoldμ body = gsize-elimG (here refl) (μᵉ body) body
