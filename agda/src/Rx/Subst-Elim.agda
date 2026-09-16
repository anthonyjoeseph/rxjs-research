------------------------------------------------------------------
-- PEELING A FIXPOINT AND CLOSING AGAINST AN ENVIRONMENT COMMUTE.
------------------------------------------------------------------

-- WHY THE GENERAL FORM IS THE ONLY ONE THAT CAN BE PROVEN.  The peel
-- is `elimGExp` at the empty local telescope, and that is where the
-- consumer wants it -- but the eliminator walks under binders by
-- EXTENDING the local telescope, so a statement pinned at the empty
-- one cannot be its own induction hypothesis.  Generalising it
-- immediately costs a transport, because the eliminator's target
-- telescope is `Θloc ++ Θsub` and substituting away `Θsub` leaves the
-- RIGHT side at `Θloc ++ []` while the LEFT is already at `Θloc`.  A
-- list append with a variable on the left does not reduce, so that
-- gap cannot be closed by computation and the equation cannot be
-- STATED without moving one side.  At the consumer's instance the
-- transport is `refl` and both `subst`s vanish definitionally, which
-- is what makes the peel fall out of the general statement rather
-- than out of a second one.
--
-- THE CLOSED COPY IS SUBSTITUTED TOO, and that is the part that has
-- to be said rather than assumed: the eliminator inserts `cl` renamed
-- into the substituted half, so the copy the left side closes is the
-- copy the right side has already closed, and the statement carries
-- `subΘExp [] σ cl` on the right rather than `cl`.
module Rx.Subst-Elim where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Rx.Exp using (Ty; Ctx; Val; Exp; subΘExp; elimGExp; _⊟_)
open import Rx.Subst-Transport using (Cᵉ)

private
  variable
    n         : ℕ
    Γ         : Ctx n
    Δᵍ Δ Θsub : List Ty
    t u       : Ty

postulate
  -- THE EXPRESSION FACE OF THE COMMUTATION, which is the whole of it:
  -- the term and list faces are mutual with this one and are reached
  -- through it, and nothing outside asks for them.
  -- PROBED: `Probed.Substitution-Leaves`, at the consumer's instance
  --   only -- a body whose μ variable is really referenced through the
  --   gate; with that gate met under a BINDER, so the inserted copy
  --   crosses a non-empty local telescope and reads the environment
  --   from under it; and through TWO gates, where the eliminator
  --   shuffles the deferred context and carries a transport on the Δ
  --   index.  Not reached: a nested fixpoint, a local telescope longer
  --   than one entry, and every instance where `Θloc` is not empty, so
  --   nothing covers the transport itself.
  sub-elimGᵉ : (Θloc : List Ty) (x : t ∈ Δᵍ)
               (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
               (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) u)
             → subΘExp Θloc σ (elimGExp Θloc x cl e)
                 ≡ subst (Cᵉ Γ (Δᵍ ⊟ x) Δ u) (++-identityʳ Θloc)
                     (elimGExp Θloc x (subΘExp [] σ cl)
                       (subst (Cᵉ Γ Δᵍ Δ u) (sym (++-identityʳ Θloc))
                         (subΘExp Θloc σ e)))
