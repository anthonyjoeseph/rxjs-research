----------------------------------------------------------------------
-- THE PRICE OF CARRYING THE ENVIRONMENT, INSTANTIATED.
----------------------------------------------------------------------

-- WHY THIS IS WORTH A ROW THOUGH IT READS AS BOOKKEEPING.
-- The fundamental theorem recurses on RAW syntax under a carried
-- environment, because a size may not be shown a substitution; the
-- statement below is what that choice costs, and it is a
-- claim about WHERE a telescope is split rather than about
-- substitution in general.  A split written one entry off typechecks
-- at every one of them -- the indices are inferred, not stated -- so
-- the row is LOAD-BEARING in the one way a substitution lemma can
-- be: it fails if the local telescope handed to the substituter is
-- not the one the binder actually introduces.  What it does NOT cover
-- is the statement's inductive content, since the row is a single
-- closed point.

-- TARGET: sub-evalStrm @350562
module Probed.Substitution-Leaves where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp
  using (Ctx; natᵗ; Exp; Val; ofᵉ; varᵗ)
open import Rx.Subst-Eval using (sub-evalStrm)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- ONE TELESCOPE ENTRY, which is the smallest shape that can tell a
-- right split from a wrong one; the environment supplies it.
σ₀ : All (Val Γ₀) (natᵗ ∷ [])
σ₀ = 7 ∷ []

----------------------------------------------------------------------
-- 1.  THE TERM FACE HANDING BACK TO THE EXPRESSION FACE.
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
