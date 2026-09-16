----------------------------------------------------------------------
-- THE PRICE OF CARRYING THE ENVIRONMENT, INSTANTIATED.
----------------------------------------------------------------------

-- WHY THESE ARE WORTH A ROW EACH THOUGH THEY READ AS BOOKKEEPING.
-- The fundamental theorem recurses on RAW syntax under a carried
-- environment, because a size may not be shown a substitution; the
-- statements below are what that choice costs, and each is a
-- claim about WHERE a telescope is split rather than about
-- substitution in general.  A split written one entry off typechecks
-- at every one of them -- the indices are inferred, not stated -- so
-- the rows are LOAD-BEARING in the one way a substitution lemma can
-- be: they fail if the local telescope handed to the substituter is
-- not the one the binder actually introduces.  What they do NOT cover
-- is any statement's inductive content, since every row is a single
-- closed point.

-- TARGET: sub-unfoldμ @314410
-- TARGET: evalWith-wkReify @d9e5a9
-- TARGET: sub-evalStrm @350562
-- TARGET: subΘ-idExp @3ee7cc
module Probed.Substitution-Leaves where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; obs; Exp; Val; ofᵉ; mapᵉ; μᵉ; varᵉ; deferᵉ; nat̂; varᵗ)
open import Rx.Evaluator.Reducible using (sub-unfoldμ; subΘ-idExp)
open import Rx.Subst-Eval using (evalWith-wkReify; sub-evalStrm)

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
-- 2.  REIFY-THEN-READ, AT THE ONE TYPE WHERE IT CAN FAIL.  At a data
-- type the literal is a numeral and the row is DEGENERATE.  At an
-- OBSERVABLE the literal carries a whole expression, and reading it
-- back CLOSES that expression against the ambient environment -- so
-- the row is LOAD-BEARING exactly there: it fails if closing an
-- already-closed expression against a NON-EMPTY environment is not the
-- identity.  The environment supplied is non-empty for that reason.
--
-- NOT REACHED: an expression with a real local telescope under the
-- literal, and the product and sum arms, whose reified literals are
-- built from the arms below them.
----------------------------------------------------------------------

obs₀ : Val Γ₀ (obs natᵗ)
obs₀ = ofᵉ (nat̂ 7 ∷ [])

row-wkReify-obs : Confirms (evalWith-wkReify obs₀ σ₀)
row-wkReify-obs = refl

row-wkReify-nat : Confirms (evalWith-wkReify {Γ = Γ₀} 4 σ₀)
row-wkReify-nat = refl

----------------------------------------------------------------------
-- 3.  THE TERM FACE HANDING BACK TO THE EXPRESSION FACE.
-- LOAD-BEARING on the split, which is the whole content: the local
-- telescope is non-empty and the embedded expression reads BOTH
-- halves, so a substituter that took one entry too many or too few
-- sends the local value where the environment entry belongs and the
-- two sides come apart.
--
-- NOT REACHED: a local telescope longer than one entry, and any
-- former between the embedding and the variables that reads them.
----------------------------------------------------------------------

strm₀ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ []) natᵗ
strm₀ = ofᵉ (varᵗ (here refl) ∷ varᵗ (there (here refl)) ∷ [])

row-evalStrm : Confirms (sub-evalStrm strm₀ σ₀ (5 ∷ []))
row-evalStrm = refl

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
