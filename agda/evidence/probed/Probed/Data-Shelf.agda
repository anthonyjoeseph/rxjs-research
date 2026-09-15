-- THE SHELF THE SUBSTITUTION LEMMA STANDS ON, INSTANTIATED.
--
-- WHAT IS AT RISK AND WHAT IS NOT.  The weakening equates a reading
-- taken at an ARBITRARY bound with one taken at the closed bound, so
-- both sides move: the left is read at `k` and the right at `0`, and a
-- term reaching any variable clause would separate them.  That is
-- exactly why the rows come in pairs — the same term read at `0` and
-- at a positive bound — since a clause that leaked the bound would be
-- invisible at `0` alone.
--
-- COVERAGE: a term with no head and a term whose head is `strmᵗ`, the
-- only head the reading counts, each at the closed bound and at a
-- positive one.
-- NOT reached: a term with a binder under the weakened context.
--
-- TARGET: dep-wkTm @594716
module Probed.Data-Shelf where

open import Data.List using ([]; _∷_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; nat̂; strmᵗ; ofᵉ)
open import Rx.Obs-Depth.Substitution using (dep-wkTm)

open import Probed.Apparatus using (Confirms; zeroη)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

----------------------------------------------------------------------
-- 1.  WEAKENING MOVES NO READING, AT THE CLOSED BOUND.  The second row
-- is the load-bearing one: `strmᵗ` is the only head the reading
-- counts, so a renaming that rebuilt it at a different index would
-- fail here and nowhere above.
----------------------------------------------------------------------

row-wk-leaf : Confirms (dep-wkTm {Γ = Γ₀} zeroη 0 {Δᵍ = []} {Δ = []} {Θ = []}
                         (nat̂ 7))
row-wk-leaf = refl

row-wk-strm : Confirms
  (dep-wkTm {Γ = Γ₀} zeroη 0 {Δᵍ = []} {Δ = []} {Θ = natᵗ ∷ []}
    (strmᵗ (ofᵉ (nat̂ 7 ∷ []))))
row-wk-strm = refl

----------------------------------------------------------------------
-- 2.  AND AT A POSITIVE BOUND, WHICH IS THE HALF THE CLOSED ROWS
-- CANNOT SEE.  The bound is a parameter of the reading now, so the two
-- sides are read at DIFFERENT bounds and a clause that let `k` through
-- would separate them here while agreeing at zero.
----------------------------------------------------------------------

row-wk-leaf-open : Confirms
  (dep-wkTm {Γ = Γ₀} zeroη 3 {Δᵍ = []} {Δ = []} {Θ = []} (nat̂ 7))
row-wk-leaf-open = refl

row-wk-strm-open : Confirms
  (dep-wkTm {Γ = Γ₀} zeroη 3 {Δᵍ = []} {Δ = []} {Θ = natᵗ ∷ []}
    (strmᵗ (ofᵉ (nat̂ 7 ∷ []))))
row-wk-strm-open = refl
