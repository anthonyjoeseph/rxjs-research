-- ══════════════════════════════════════════════════════════════════
-- SUBSTITUTION IS NOT ADDITIVE IN THE NESTING CURRENCY, and one map
-- frame is enough to say so.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  Applying a step function to a payload wraps
-- the payload by at most the step function's OWN nesting:
-- `nestDᵛ (applyFn fn v) ≤ nestDᵗ fn + nestDᵛ v`.  It is the nesting
-- face of a substitution lemma this development already has twice, on
-- the size face and on the width face, and it is what the map frame's
-- charge -- `pathNestD`'s `nestDᵗ f` -- asserts.
--
-- WHY IT LOOKED RIGHT.  A variable weighs nothing, so substituting a
-- payload into one appears to cost exactly the payload; and the two
-- proven faces both compose their per-occurrence bound into a single
-- factor, so the third face reads as the easy one.
--
-- WHERE IT BREAKS.  `nestDᵉ` is ADDITIVE at `mapᵉ` and at `scanᵉ`, and
-- a step function may name its payload on BOTH sides of such a sum.
-- Then one substitution installs the payload's nesting twice while the
-- unsubstituted term weighs zero on both sides, because a variable
-- weighs zero.  The proven faces are immune only because they are
-- multiplicative: a size bound already carries the occurrence count.
--
-- THE WITNESS is the smallest term of that shape -- a `mapᵉ` whose
-- source list and whose step function are the SAME outer variable --
-- applied to a payload one `switchAllᵉ` deep.  Two against a charge of
-- one, and the gap is the number of occurrences, so it grows without
-- bound in a term the charge does not move with at all.
--
-- WHAT DIES AND WHAT DOES NOT.  The additive form dies, and with it the
-- map arm of the walk's per-frame charge as currently stated.  What
-- survives is the shape the other two faces have: the payload's nesting
-- must be charged once per OCCURRENCE, so the repair is a factor the
-- syntax can see -- the step function's size -- and not a tighter
-- argument about the same sum.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Apply-Fn-Nest where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (natᵗ; obs; Fn; Val; applyFn;
         ofᵉ; mapᵉ; switchAllᵉ; varᵗ; nat̂; strmᵗ)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

-- a payload one `*All` layer deep
v : Val Γ₂ (obs natᵗ)
v = switchAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- the step function names its payload TWICE, once on each side of the
-- `mapᵉ` sum: as the list the source emits, and as the mapped result
fn : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fn = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

row : ℕ × ℕ
row = nestDᵛ (obs (obs natᵗ)) (applyFn fn v)
    , nestDᵗ fn + nestDᵛ (obs natᵗ) v

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
subbed≡2 : proj₁ row ≡ 2
subbed≡2 = refl

oneWrap≡1 : proj₂ row ≡ 1
oneWrap≡1 = refl

applyFn-nest-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `2 ≤ᵇ 1` reduces to `false`, so `T` of it IS the empty type
applyFn-nest-absurd h = ≤⇒≤ᵇ h
