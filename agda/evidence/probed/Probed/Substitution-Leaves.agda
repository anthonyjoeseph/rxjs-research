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

-- TARGET: sub-elimGᵉ @0cd8ca
-- TARGET: sub-evalStrm @350562
module Probed.Substitution-Leaves where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; Exp; Val; ofᵉ; mapᵉ; varᵉ; deferᵉ; μᵉ; strmᵗ; varᵗ; fstᵗ; pairᵗ)
open import Rx.Subst-Elim using (sub-elimGᵉ)
open import Rx.Subst-Eval using (sub-evalStrm)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- ONE TELESCOPE ENTRY, which is the smallest shape that can tell a
-- right split from a wrong one; the environment supplies it.
σ₀ : All (Val Γ₀) (natᵗ ∷ [])
σ₀ = 7 ∷ []

----------------------------------------------------------------------
-- 1.  THE PEEL UNDER AN ENVIRONMENT, taken at the general
-- eliminator the peel is defined as -- at the EMPTY local telescope,
-- where the general statement's transport is `refl` and the two sides
-- are the peel's own.  LOAD-BEARING: the body's μ variable is really
-- referenced, through the gate, so a peel that inserted the wrong
-- expression changes the left side and not the right.  DEGENERATE in
-- the transport, which an empty local telescope cannot exercise.
----------------------------------------------------------------------

bodyμ : Exp Γ₀ (natᵗ ∷ []) [] (natᵗ ∷ []) natᵗ
bodyμ = mapᵉ (varᵗ (here refl)) (deferᵉ (varᵉ (here refl)))

row-unfoldμ : Confirms (sub-elimGᵉ [] (here refl) (μᵉ bodyμ) σ₀ bodyμ)
row-unfoldμ = refl

-- AND THE SAME PEEL MET UNDER A BINDER, which is the one shape the
-- row above cannot reach: there the gate sits in the SOURCE of a
-- former, where nothing is bound, so the inserted copy is weakened
-- past an EMPTY local telescope and a split written one entry off
-- still lands.  Here the gate sits inside the former's FUNCTION, so
-- the walk meets it with one thing bound and the copy has to cross
-- that binder on both sides; and the copy itself reads the
-- environment, so a copy substituted at the wrong telescope emits a
-- different literal.  LOAD-BEARING on exactly that.
bodyμ-deep : Exp Γ₀ (natᵗ ∷ []) [] (natᵗ ∷ []) natᵗ
bodyμ-deep =
  mapᵉ (fstᵗ (pairᵗ (varᵗ (there (here refl)))
                    (strmᵗ (deferᵉ (varᵉ (here refl))))))
       (ofᵉ (varᵗ (here refl) ∷ []))

row-unfoldμ-deep : Confirms (sub-elimGᵉ [] (here refl) (μᵉ bodyμ-deep) σ₀ bodyμ-deep)
row-unfoldμ-deep = refl

-- AND THROUGH TWO GATES, which is the arm where the eliminator stops
-- shuffling the GUARD context and starts shuffling the deferred one:
-- crossing the second gate re-splits the two halves and carries a
-- transport on the Δ index that the substituter has to be pushed
-- past.  LOAD-BEARING there: a transport pushed the wrong way round
-- lands the inserted copy in the other half.
bodyμ-gates : Exp Γ₀ (natᵗ ∷ []) [] (natᵗ ∷ []) natᵗ
bodyμ-gates =
  mapᵉ (fstᵗ (pairᵗ (varᵗ (there (here refl)))
                    (strmᵗ (deferᵉ (deferᵉ (varᵉ (here refl)))))))
       (ofᵉ (varᵗ (here refl) ∷ []))

row-unfoldμ-gates : Confirms (sub-elimGᵉ [] (here refl) (μᵉ bodyμ-gates) σ₀ bodyμ-gates)
row-unfoldμ-gates = refl

----------------------------------------------------------------------
-- 2.  THE TERM FACE HANDING BACK TO THE EXPRESSION FACE.
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

