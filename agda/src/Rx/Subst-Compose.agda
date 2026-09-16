------------------------------------------------------------------
-- SUBSTITUTING TWICE IS SUBSTITUTING ONCE WITH THE CONCATENATION.
------------------------------------------------------------------

-- WHAT THE EMBEDDING ARM ACTUALLY OWES.  Reading a stream literal
-- does not descend into it -- it CLOSES the expression against the
-- ambient environment -- so the arm where the term face hands back
-- to the expression face is not an induction hypothesis about terms
-- at all.  It is a claim about two substitutions in sequence.  The
-- degenerate end of it, where the ambient environment is EMPTY and
-- the outer substitution must do nothing, is already proven on the
-- identity face; what is left is the composition proper.
--
-- WHY IT LIVES IN A MODULE OF ITS OWN rather than beside the
-- identity walk it mirrors or the renaming shelf it will spend.  It
-- is a walk over the whole expression grammar, so discharging it
-- grows a mutual block that every consumer of either would then be
-- rebuilt behind; nothing but the evaluation agreement needs it, and
-- this is the shallowest module that reaches it.
module Rx.Subst-Compose where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _++_)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp using (Ty; Ctx; Exp; Val; subΘExp)

private
  variable
    n           : ℕ
    Γ           : Ctx n
    Δᵍ Δ        : List Ty
    Θloc Θsub   : List Ty
    t           : Ty

postulate
  -- TWO SUBSTITUTIONS COMPOSE.  The inner one owns the tail of the
  -- telescope and reifies what it takes; the outer one owns what is
  -- left and must leave those reified copies alone, which is the
  -- renaming shelf's inertness claim arriving at its real consumer.
  -- TWIN: `Rx.Subst-Identity`'s `subΘ-idᵉ` walks the same grammar
  --   under the same cast, at the degenerate environment.
  -- PROBED: `Probed.Substitution-Leaves`, at a one-entry local
  --   telescope whose expression reads BOTH halves of the split, at a
  --   three-variable telescope reading every position of it, under a
  --   non-binding former combining two of them, under a `mapᵉ` that
  --   grows the telescope by the element type, and under a `scanᵉ`
  --   that grows it by the accumulator PAIR over a two-entry
  --   environment.  Not reached: a `caseᵗ`, whose two arms extend the
  --   telescope by DIFFERENT types under one former; and the
  --   statement's inductive content, since every row is a single
  --   closed point.
  subΘ-compᵉ : (ρ : All (Val Γ) Θloc) (σ : All (Val Γ) Θsub)
               (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t)
             → subΘExp [] ρ (subΘExp Θloc σ e) ≡ subΘExp [] (++⁺ ρ σ) e
