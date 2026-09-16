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
  using (Ctx; natᵗ; Exp; Val; ofᵉ; varᵗ; primᵗ; pairᵗ; add)
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

----------------------------------------------------------------------
-- 2.  THE SPLIT AT A LOCAL TELESCOPE OF MORE THAN ONE ENTRY.
-- The one-entry row above cannot separate a splitter that walks the
-- local telescope from one that merely tests whether it is empty:
-- both agree at length one.  Here the walk has to take its inductive
-- step TWICE before it reaches the boundary, so a splitter that
-- descended once and then handed the rest over sends the second local
-- value where the environment entry belongs.
--
-- NOT REACHED: an environment of more than one entry, and a local
-- telescope mixing types.
----------------------------------------------------------------------

strm₁ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ natᵗ ∷ []) natᵗ
strm₁ = ofᵉ (varᵗ (here refl)
           ∷ varᵗ (there (here refl))
           ∷ varᵗ (there (there (here refl)))
           ∷ [])

row-evalStrm-deep : Confirms (sub-evalStrm strm₁ σ₀ (5 ∷ 6 ∷ []))
row-evalStrm-deep = refl

----------------------------------------------------------------------
-- 3.  A FORMER BETWEEN THE EMBEDDING AND THE VARIABLES.
-- Every row above reads its telescope through a bare variable sitting
-- directly under the embedding, so the substitution reaches the split
-- point without passing through anything.  Here an arithmetic former
-- sits in between and CONSUMES BOTH HALVES at once, so the equation
-- holds only if the substituter commutes through the congruence arm
-- rather than merely agreeing at the leaves.
--
-- NOT REACHED: a former that BINDS -- a map, a scan or a case, each of
-- which grows the local telescope under itself, which is the arm where
-- a split can go wrong without either half being misread.
----------------------------------------------------------------------

strm₂ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ []) natᵗ
strm₂ = ofᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (varᵗ (there (here refl)))) ∷ [])

row-evalStrm-former : Confirms (sub-evalStrm strm₂ σ₀ (5 ∷ []))
row-evalStrm-former = refl
