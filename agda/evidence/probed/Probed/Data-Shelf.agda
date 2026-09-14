-- THE SHELF THE SUBSTITUTION LEMMA STANDS ON, INSTANTIATED.
--
-- WHAT IS AT RISK AND WHAT IS NOT.  The membership reads a `Bool` the
-- type alone decides, so its conclusion is `true ≡ true` at every
-- point that satisfies its premise and no row can make it fail.  That
-- row is DEGENERATE as an inequality and LOAD-BEARING as non-vacuity:
-- what it buys is that the premise is satisfiable at a nested
-- telescope at all, which is how a projection off an `if`-shaped
-- predicate goes quietly empty.  The weakening row is the one with
-- content on both sides.
--
-- COVERAGE: a membership at the head of the telescope and past it, and
-- a weakening of a term with no head and of one whose head is the only
-- head that carries a reading.
-- NOT reached: the size axis, which this shelf no longer prices.
--
-- TARGET: data-of @6d56e8
-- TARGET: dep-wkTm @537866
module Probed.Data-Shelf where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ty; Ctx; boolᵗ; natᵗ; nat̂; strmᵗ; ofᵉ)
open import Rx.Obs-Depth.Substitution using (AllData; []ᵈ; _∷ᵈ_;
  data-of; dep-wkTm)

open import Probed.Apparatus using (Confirms; zeroη)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

----------------------------------------------------------------------
-- 1.  THE MEMBERSHIP.  The row is the target applied at a telescope
-- the premise actually admits, so what it pins is that the premise is
-- inhabited there.
----------------------------------------------------------------------

Θ₂ : List Ty
Θ₂ = natᵗ ∷ boolᵗ ∷ []

dd₂ : AllData Θ₂
dd₂ = refl ∷ᵈ (refl ∷ᵈ []ᵈ)

row-of-head : Confirms (data-of {Θ = Θ₂} dd₂ (here refl))
row-of-head = refl

-- past the head, which is the clause that recurses
row-of-tail : Confirms (data-of {Θ = Θ₂} dd₂ (there (here refl)))
row-of-tail = refl

----------------------------------------------------------------------
-- 2.  WEAKENING MOVES NO READING.  The second row is the load-bearing
-- one: `strmᵗ` is the only head the reading counts, so a renaming that
-- rebuilt it at a different index would fail here and nowhere above.
----------------------------------------------------------------------

row-wk-leaf : Confirms (dep-wkTm {Γ = Γ₀} zeroη {Δᵍ = []} {Δ = []} {Θ = []} (nat̂ 7))
row-wk-leaf = refl

row-wk-strm : Confirms
  (dep-wkTm {Γ = Γ₀} zeroη {Δᵍ = []} {Δ = []} {Θ = natᵗ ∷ []}
    (strmᵗ (ofᵉ (nat̂ 7 ∷ []))))
row-wk-strm = refl
