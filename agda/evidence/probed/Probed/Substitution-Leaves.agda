----------------------------------------------------------------------
-- THE PRICE OF CARRYING THE ENVIRONMENT, INSTANTIATED.
----------------------------------------------------------------------

-- WHY THIS IS WORTH A ROW THOUGH IT READS AS BOOKKEEPING.
-- The fundamental theorem recurses on RAW syntax under a carried
-- environment, because a size may not be shown a substitution; the
-- statement below is what that choice costs, and it is
-- a claim about WHERE a telescope is split rather than about
-- substitution in general.  A split written one entry off typechecks
-- at every one of them -- the indices are inferred, not stated -- so
-- these rows are LOAD-BEARING in the one way a substitution lemma can
-- be: they fail if the local telescope handed to the substituter is
-- not the one the binder actually introduces.  What they do NOT cover
-- is the statement's inductive content, since every row is a
-- single closed point.

-- TARGET: subΘ-compᵉ @22846e
module Probed.Substitution-Leaves where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp
  using (Ctx; natᵗ; Exp; Val; ofᵉ; varᵗ; primᵗ; pairᵗ; fstᵗ; mapᵉ; scanᵉ; add)
open import Rx.Subst-Compose using (subΘ-compᵉ)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- ONE TELESCOPE ENTRY, which is the smallest shape that can tell a
-- right split from a wrong one; the environment supplies it.
σ₀ : All (Val Γ₀) (natᵗ ∷ [])
σ₀ = 7 ∷ []

----------------------------------------------------------------------
-- 1.  THE COMPOSITION, AT A TELESCOPE THE EXPRESSION READS BOTH
-- HALVES OF.  LOAD-BEARING on the split: the inner substitution owns
-- the tail and reifies what it takes, the outer owns the head, so a
-- substituter that took one entry too many or too few sends the local
-- value where the environment entry belongs and the two sides come
-- apart at distinct numerals.
--
-- NOT REACHED: a local telescope longer than one entry, and any
-- former between the two halves that reads them.
----------------------------------------------------------------------

strm₀ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ []) natᵗ
strm₀ = ofᵉ (varᵗ (here refl) ∷ varᵗ (there (here refl)) ∷ [])

row-compᵉ : Confirms (subΘ-compᵉ (5 ∷ []) σ₀ strm₀)
row-compᵉ = refl

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

row-compᵉ-deep : Confirms (subΘ-compᵉ (5 ∷ 6 ∷ []) σ₀ strm₁)
row-compᵉ-deep = refl

----------------------------------------------------------------------
-- 3.  A FORMER BETWEEN THE EMBEDDING AND THE VARIABLES.
-- Every row above reads its telescope through a bare variable sitting
-- directly under the head former, so the substitution reaches the
-- split point without passing through anything.  Here an arithmetic
-- former sits in between and CONSUMES BOTH HALVES at once, so the
-- equation holds only if the substituter commutes through the
-- congruence arm rather than merely agreeing at the leaves.
--
-- NOT REACHED: a former that BINDS -- a map, a scan or a case, each of
-- which grows the local telescope under itself, which is the arm where
-- a split can go wrong without either half being misread.
----------------------------------------------------------------------

strm₂ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ []) natᵗ
strm₂ = ofᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (varᵗ (there (here refl)))) ∷ [])

row-compᵉ-former : Confirms (subΘ-compᵉ (5 ∷ []) σ₀ strm₂)
row-compᵉ-former = refl

----------------------------------------------------------------------
-- 4.  A FORMER THAT BINDS, which is the arm the split's arithmetic
-- actually turns on.  Every row above keeps the local telescope FIXED
-- all the way down, so a substituter that ignored its telescope
-- argument entirely and split at a remembered length would pass them
-- all.  A `mapᵉ` grows the telescope under itself by exactly the
-- element type, and the function below reads all three positions --
-- the bound element, the local value and the environment's -- so the
-- equation holds only if the inner substitution is handed the
-- EXTENDED telescope and the split lands one entry further along on
-- the inside than on the outside.
--
-- LOAD-BEARING on the extension: off by one either way, the bound
-- element is read as the local value or the local value as the
-- environment's, and both sides come apart at distinct numerals.
----------------------------------------------------------------------

strm₃ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ []) natᵗ
strm₃ = mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl))
                               (primᵗ add (pairᵗ (varᵗ (there (here refl)))
                                                 (varᵗ (there (there (here refl))))))))
             (ofᵉ (varᵗ (here refl) ∷ []))

row-compᵉ-binder : Confirms (subΘ-compᵉ (5 ∷ []) σ₀ strm₃)
row-compᵉ-binder = refl

----------------------------------------------------------------------
-- 5.  A BINDER AT A PRODUCT TYPE, OVER AN ENVIRONMENT OF MORE THAN
-- ONE ENTRY.  A `scanᵉ` extends the telescope by the accumulator
-- PAIR rather than by the element, so the entry the split steps over
-- is not the type of anything the expression carries -- and its
-- initial term sits at the UNEXTENDED telescope beside a function at
-- the extended one, which is the one place a single former uses both
-- splits at once.  The environment has two entries, so a substituter
-- reaching the boundary still has to pick the right one of them.
--
-- LOAD-BEARING on both: the accumulator and the two environment
-- entries are distinct numerals, so any confusion among them is a
-- different value.
--
-- NOT REACHED STILL: a `caseᵗ`, whose two arms extend the telescope
-- by DIFFERENT types under one former; and the statement's
-- inductive content, since every row here is a single closed point.
----------------------------------------------------------------------

σ₁ : All (Val Γ₀) (natᵗ ∷ natᵗ ∷ [])
σ₁ = 7 ∷ 9 ∷ []

strm₄ : Exp Γ₀ [] [] (natᵗ ∷ natᵗ ∷ natᵗ ∷ []) natᵗ
strm₄ = scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl)))
                                (varᵗ (there (there (here refl))))))
              (varᵗ (here refl))
              (ofᵉ (varᵗ (there (there (here refl))) ∷ []))

row-compᵉ-scan : Confirms (subΘ-compᵉ (5 ∷ []) σ₁ strm₄)
row-compᵉ-scan = refl
