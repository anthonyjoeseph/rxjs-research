----------------------------------------------------------------------
-- THE PRICE OF CARRYING THE ENVIRONMENT, INSTANTIATED.
----------------------------------------------------------------------

-- WHY THESE FOUR ARE WORTH A ROW EACH THOUGH THEY READ AS BOOKKEEPING.
-- The fundamental theorem recurses on RAW syntax under a carried
-- environment, because a size may not be shown a substitution; the
-- four statements below are what that choice costs, and each is a
-- claim about WHERE a telescope is split rather than about
-- substitution in general.  A split written one entry off typechecks
-- at every one of them -- the indices are inferred, not stated -- so
-- the rows are LOAD-BEARING in the one way a substitution lemma can
-- be: they fail if the local telescope handed to the substituter is
-- not the one the binder actually introduces.  What they do NOT cover
-- is any statement's inductive content, since every row is a single
-- closed point.

-- TARGET: sub-unfoldμ @314410
-- TARGET: sub-evalTm @688109
-- TARGET: sub-applyFn @87e1fd
-- TARGET: subΘ-idExp @3ee7cc
module Probed.Substitution-Leaves where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; Exp; Tm; Fn; Val; ofᵉ; mapᵉ; μᵉ; varᵉ; deferᵉ; nat̂; varᵗ; pairᵗ; fstᵗ)
open import Rx.Evaluator.Reducible using (sub-unfoldμ; sub-evalTm; sub-applyFn; subΘ-idExp)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- ONE TELESCOPE ENTRY, which is the smallest shape that can tell a
-- right split from a wrong one; the environment supplies it.
σ₀ : All (Val Γ₀) (natᵗ ∷ [])
σ₀ = 7 ∷ []

----------------------------------------------------------------------
-- 1.  THE PEEL UNDER AN ENVIRONMENT.  LOAD-BEARING: the body's μ
-- variable is really referenced, through the gate, so a peel that
-- inserted the wrong expression changes the left side and not the
-- right.
----------------------------------------------------------------------

bodyμ : Exp Γ₀ (natᵗ ∷ []) [] (natᵗ ∷ []) natᵗ
bodyμ = mapᵉ (varᵗ (here refl)) (deferᵉ (varᵉ (here refl)))

row-unfoldμ : Confirms (sub-unfoldμ bodyμ σ₀)
row-unfoldμ = refl

----------------------------------------------------------------------
-- 2.  A TERM'S VALUE.  LOAD-BEARING at a variable, which is the one
-- clause that reads the environment at all; the pair around it is
-- there so the row is not a bare lookup.
----------------------------------------------------------------------

tm₀ : Tm Γ₀ [] [] (natᵗ ∷ []) natᵗ
tm₀ = fstᵗ (pairᵗ (varᵗ (here refl)) (nat̂ 3))

row-evalTm : Confirms (sub-evalTm tm₀ σ₀)
row-evalTm = refl

----------------------------------------------------------------------
-- 3.  A FRAME'S FUNCTION.  LOAD-BEARING in exactly the way the others
-- are not: the substituter must SKIP the slot the function binds and
-- reach past it into the environment, so a split one entry off sends
-- the argument where the environment entry should go.  The body reads
-- both positions, which is what makes the two distinguishable.
----------------------------------------------------------------------

fn₀ : Fn Γ₀ [] [] (natᵗ ∷ []) natᵗ natᵗ
fn₀ = fstᵗ (pairᵗ (varᵗ (here refl)) (varᵗ (there (here refl))))

row-applyFn : Confirms (sub-applyFn fn₀ σ₀ 5)
row-applyFn = refl

----------------------------------------------------------------------
-- 4.  THE EMPTY SUBSTITUTION.  DEGENERATE by construction -- nothing
-- can be substituted -- and stated anyway because it is what makes the
-- top line a corollary of the partner at the empty environment, and
-- because it fails outright if the identity is not definitional at
-- some former.  The expression reaches a term, a list and a nested
-- expression, which is where a non-definitional clause would sit.
----------------------------------------------------------------------

exp₀ : Exp Γ₀ [] [] [] natᵗ
exp₀ = mapᵉ (varᵗ (here refl)) (μᵉ (ofᵉ (nat̂ 7 ∷ [])))

row-idExp : Confirms (subΘ-idExp exp₀)
row-idExp = refl
