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

-- TARGET: gWk @670218
-- TARGET: dWk @522702
-- TARGET: sub-ren-gate @5cd7ea
-- TARGET: sub-evalStrm @350562
module Probed.Substitution-Leaves where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp
  using (Ctx; natᵗ; obs; _×ᵗ_; Exp; Tm; Val; ofᵉ; nat̂; varᵗ; pairᵗ; strmᵗ)
open import Rx.Subst-Elim using (gWk; dWk; sub-ren-gate)
open import Rx.Subst-Eval using (sub-evalStrm)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- ONE TELESCOPE ENTRY, which is the smallest shape that can tell a
-- right split from a wrong one; the environment supplies it.
σ₀ : All (Val Γ₀) (natᵗ ∷ [])
σ₀ = 7 ∷ []

----------------------------------------------------------------------
-- 1.  A CLOSED LITERAL IS UNTOUCHED BY EITHER WALK, taken at a
-- NON-EMPTY local telescope, which is where the eliminator's own
-- index arithmetic could go wrong and where nothing before covered
-- it.  LOAD-BEARING on the walk being the identity on a term with
-- structure: the rows recurse through a pair and through an embedded
-- expression, so a walk that renumbered anything inside a weakened
-- literal changes the left side and not the right.
--
-- NOT REACHED: the transport, which a CONCRETE local telescope can
-- never exercise -- fixing `Θl` forces the equation to `refl`, so
-- every row here is at the identity transport and the general
-- `Θl ++ [] ≡ Θ` is uninstantiable away from it.
----------------------------------------------------------------------

clos : Exp Γ₀ [] [] [] natᵗ
clos = ofᵉ (nat̂ 3 ∷ [])

gate : natᵗ ∈ (natᵗ ∷ [])
gate = here refl

lit : Tm Γ₀ [] [] [] (natᵗ ×ᵗ natᵗ)
lit = pairᵗ (nat̂ 1) (nat̂ 2)

deep : Tm Γ₀ [] [] [] (obs natᵗ)
deep = strmᵗ (ofᵉ (nat̂ 5 ∷ []))

row-gWk : Confirms (gWk {Δ = []} (natᵗ ∷ []) refl gate clos lit)
row-gWk = refl

row-gWk-deep : Confirms (gWk {Δ = []} (natᵗ ∷ []) refl gate clos deep)
row-gWk-deep = refl

row-dWk : Confirms (dWk {Δᵍ = []} (natᵗ ∷ []) refl gate clos lit)
row-dWk = refl

row-dWk-deep : Confirms (dWk {Δᵍ = []} (natᵗ ∷ []) refl gate clos deep)
row-dWk-deep = refl

----------------------------------------------------------------------
-- 2.  THE INSERTED COPY LANDS IN THE HALF THE SUBSTITUTER CONSUMES.
-- LOAD-BEARING on exactly that: the copy reads the environment, and
-- the local telescope is non-empty, so a rename that sent the copy's
-- variable to the LOCAL half would leave a `varᵗ` on the left where
-- the right side emits the literal.
--
-- NOT REACHED: a local telescope longer than one entry, and an
-- environment supplying more than one value.
----------------------------------------------------------------------

gated : Exp Γ₀ [] [] (natᵗ ∷ []) natᵗ
gated = ofᵉ (varᵗ (here refl) ∷ [])

row-gate : Confirms (sub-ren-gate {Δᵍ′ = []} {Δ′ = []} (natᵗ ∷ []) gated σ₀)
row-gate = refl

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
