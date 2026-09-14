-- THE SHELF THE SUBSTITUTION LEMMA STANDS ON, INSTANTIATED — AND ONE
-- FINDING THAT CAME OUT OF INSTANTIATING IT.
--
-- WHAT IS AT RISK AND WHAT IS NOT.  The membership reads a `Bool` the
-- type alone decides, so its conclusion is `true ≡ true` at every
-- point that satisfies its premise and no row can make it fail.  That
-- row is DEGENERATE as an inequality and LOAD-BEARING as non-vacuity:
-- what it buys is that the premise is satisfiable at a nested
-- telescope at all, which is how a projection off an `if`-shaped
-- predicate goes quietly empty.  The weakening row is the one with
-- content on both sides, and the size row is the one that found
-- something.
--
-- COVERAGE: a membership at the head of the telescope and past it, a
-- weakening of a term with no head and of one whose head is the only
-- head that carries a reading, and the size bound at an argument whose
-- reified form is one node.
-- NOT reached: the size bound at any argument whose reified form is
-- LARGER than one node, and that gap is not an omission — see below.
--
-- TARGET: data-of @6d56e8
-- TARGET: dep-wkTm @537866
-- TARGET: syncSize-applyFn @b81a9c
module Probed.Data-Shelf where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m+n)
open import Data.Product using (_,_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ty; Ctx; Tm; Val; Fn; boolᵗ; natᵗ; _×ᵗ_;
  obs; varᵗ; nat̂; fstᵗ; strmᵗ; ofᵉ; applyFn; syncSizeᵉ; syncSizeᵗ)
open import Rx.Obs-Depth.Substitution using (AllData; []ᵈ; _∷ᵈ_;
  data-of; dep-wkTm; syncSize-applyFn)

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

----------------------------------------------------------------------
-- 3.  THE SIZE BOUND, AND THE FINDING.
--
-- The row that closes is at an argument whose reified form is a single
-- node: substitution then replaces a `varᵗ` by something the same size,
-- the bound holds with the `dataSize` term unspent, and the body is a
-- proven weakening rather than a numeral — which is what `Confirms`
-- asks for.
----------------------------------------------------------------------

fn-nat : Fn Γ₀ [] [] [] natᵗ (obs natᵗ)
fn-nat = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

row-sync-one-node : Confirms (syncSize-applyFn {Γ = Γ₀} {s = natᵗ} refl fn-nat 5)
row-sync-one-node = ≤-trans base (m≤m+n _ _)
  where
  base : syncSizeᵉ (applyFn fn-nat 5) ≤ syncSizeᵗ fn-nat
  base = s≤s (s≤s (s≤s z≤n))

----------------------------------------------------------------------
-- AND THE PAIR THAT SAYS THE BOUND IS NOT ENOUGH.  `dataSize` is a
-- function of the TYPE, so at a fixed argument type it is one number
-- however the template is written.  These two templates share that
-- type and differ only in how many times they read the argument: the
-- reified pair is two nodes bigger than the `varᵗ` it replaces, so the
-- gap between the two sides grows with the count and nothing on the
-- right grows with it.  Three occurrences already need five, and the
-- family goes on.
--
-- The rows are pins rather than `Confirms` rows deliberately: the
-- target cannot be instantiated at either point, since closing it
-- would need a LOWER bound on a postulate that has no equations.  That
-- is the coverage boundary, and it is also the finding — recorded in
-- the statement's own header, where it constrains rather than here.
----------------------------------------------------------------------

Pair : Ty
Pair = natᵗ ×ᵗ natᵗ

v-pair : Val Γ₀ Pair
v-pair = 3 , 4

fst-arg : Tm Γ₀ [] [] (Pair ∷ []) natᵗ
fst-arg = fstᵗ (varᵗ (here refl))

fn-once : Fn Γ₀ [] [] [] Pair (obs natᵗ)
fn-once = strmᵗ (ofᵉ (fst-arg ∷ []))

fn-thrice : Fn Γ₀ [] [] [] Pair (obs natᵗ)
fn-thrice = strmᵗ (ofᵉ (fst-arg ∷ fst-arg ∷ fst-arg ∷ []))

gap-once-template : syncSizeᵗ fn-once ≡ 5
gap-once-template = refl

gap-once-applied : syncSizeᵉ (applyFn fn-once v-pair) ≡ 6
gap-once-applied = refl

gap-thrice-template : syncSizeᵗ fn-thrice ≡ 9
gap-thrice-template = refl

gap-thrice-applied : syncSizeᵉ (applyFn fn-thrice v-pair) ≡ 14
gap-thrice-applied = refl
