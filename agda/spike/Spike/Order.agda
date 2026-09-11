------------------------------------------------------------------
-- THE ORDER, and the one clause that will not fit in it.
--
-- `Spike.Mini` established that Agda accepts the domain predicate.
-- That says the RECURSION can be expressed; it says nothing about
-- whether the recursion TERMINATES, which is a separate question with
-- a separate answer, and this file is where the two come apart.
--
-- The candidate is the lexicographic triple the real development
-- already carries, positionally encoded inside `dBound`:
--
--     (unconn cs , hopD e , syncSize e)
--
-- Read as a genuine lex order rather than as a number, the carry
-- conditions vanish: `dBound-hop` needs `s′ ≤ V` and `dBound-connect`
-- needs `r′ ≤ R` and `s′ ≤ V` only because a positional encoding must
-- stop a lower digit from overflowing into a higher one.  A lex order
-- has no digits and needs only the strict component.
--
-- What does NOT vanish is `hopD`'s own `V`, and this file refutes the
-- hope that it does.  The refold separation below exhibits two
-- programs agreeing on every quantity a syntax-directed scan clause
-- can read, whose deepest emissions differ — so the clause must read
-- something else, and the something else is how many values the source
-- delivers.
------------------------------------------------------------------
module Spike.Order where

open import Spike.Mini
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Run []

------------------------------------------------------------------
-- THE INNERMOST COMPONENT: synchronous size, truncated at the gate.
-- `deferᵉ` reads 1 because its body does not run in this instant,
-- which is exactly what makes the μ unfold a decrease.
------------------------------------------------------------------

syncSize : Exp → ℕ
syncSize (ofᵉ vs)      = 1
syncSize (mapᵉ f e)    = suc (syncSize e)
syncSize (scanᵉ f z e) = suc (syncSize e)
syncSize (allᵉ e)      = suc (syncSize e)
syncSize (μᵉ b)        = suc (syncSize b)
syncSize varᵉ          = 1
syncSize (deferᵉ b)    = 1
syncSize (slotᵉ i)     = 1

------------------------------------------------------------------
-- THE MIDDLE COMPONENT: remaining hop depth, with the scan clause
-- written NAIVELY — every quantity a syntax-directed clause could read
-- about `scanᵉ f z e`, and nothing about what `e` will deliver.  The
-- `⊔ 1` on the multiplier is not decoration: without it a template
-- that drops its argument prices the source at zero, and `hopD e ≤
-- hopD (mapᵉ f e)` — the descent edge's own non-increase — is false.
------------------------------------------------------------------

hopDv : Val → ℕ
hopD  : Exp → ℕ
hopDt : Tm  → ℕ
pm    : Tm  → ℕ
hopDl : List Val → ℕ

hopDv (natᵛ n) = 0
hopDv (obsᵛ e) = hopD e

hopDl []       = 0
hopDl (v ∷ vs) = hopDv v ⊔ hopDl vs

hopDt inᵗ        = 0
hopDt accᵗ       = 0
hopDt (konstᵗ k) = hopDv k
hopDt (nestᵗ t)  = suc (hopDt t)

pm inᵗ        = 1
pm accᵗ       = 1
pm (konstᵗ k) = 0
pm (nestᵗ t)  = pm t

hopD (ofᵉ vs)      = hopDl vs
hopD (mapᵉ f e)    = hopDt f + (pm f ⊔ 1) * hopD e
hopD (scanᵉ f z e) = hopDt f + hopDv z + (pm f ⊔ 1) * hopD e
hopD (allᵉ e)      = suc (hopD e)
hopD (μᵉ b)        = hopD b
hopD varᵉ          = 0
hopD (deferᵉ b)    = 0
hopD (slotᵉ i)     = 0

------------------------------------------------------------------
-- THE REFOLD SEPARATION.
--
-- Two scans differing only in how many values the source delivers.
-- Every quantity the naive clause reads is EQUAL across the pair —
-- same template, same seed, same source hop — and the deepest emitted
-- value's hop is 3 against 5.  So no clause of the form
-- `F (hopDt f , pm f , hopDv z , hopD e)` can dominate an emission,
-- whatever `F` is, and the emitted-value invariant `hopD o ≤ hopD e`
-- that the inner-hop edge needs is FALSE under any such clause.
--
-- The witness is `nestᵗ accᵗ`, which reifies the accumulator behind a
-- hop frame: fold it k times and the accumulator nests k deep.  That
-- is the real `hopDᵉ`'s scan clause in miniature, and it is why that
-- clause is priced `(2 + pm)^V` — the exponent is a bound on the fold
-- count, and this pair shows the fold count cannot be read off the
-- syntax at all.
------------------------------------------------------------------

step : Tm
step = nestᵗ accᵗ

seed : Val
seed = natᵛ 0

src3 src5 : Exp
src3 = ofᵉ (natᵛ 1 ∷ natᵛ 2 ∷ natᵛ 3 ∷ [])
src5 = ofᵉ (natᵛ 1 ∷ natᵛ 2 ∷ natᵛ 3 ∷ natᵛ 4 ∷ natᵛ 5 ∷ [])

prog3 prog5 : Exp
prog3 = scanᵉ step seed src3
prog5 = scanᵉ step seed src5

burst3 burst5 : List Val
burst3 = proj₁ (run prog3 [] (dScan dOf))
burst5 = proj₁ (run prog5 [] (dScan dOf))

-- LOAD-BEARING: the four readable quantities coincide
readable : Exp → ℕ × ℕ × ℕ × ℕ
readable e = hopDt step , pm step , hopDv seed , hopD e

readable-agree : readable src3 ≡ readable src5
readable-agree = refl

-- LOAD-BEARING: the deepest emission does not
deepest-3 : hopDl burst3 ≡ 3
deepest-3 = refl

deepest-5 : hopDl burst5 ≡ 5
deepest-5 = refl

-- and the naive clause reads the same number for both, under both
naive-3 : hopD prog3 ≡ 1
naive-3 = refl

naive-5 : hopD prog5 ≡ 1
naive-5 = refl

------------------------------------------------------------------
-- THE SAME EDGE, WITH NO REFOLD, IS FINE — which is what localises
-- the finding to `scanᵉ` rather than to the order.  A `mapᵉ` under the
-- same template nests every emission exactly once regardless of how
-- many values arrive, because nothing is carried between them, and the
-- clause's own `suc` pays for it at both lengths.
------------------------------------------------------------------

mprog3 mprog5 : Exp
mprog3 = mapᵉ step src3
mprog5 = mapᵉ step src5

mburst3 mburst5 : List Val
mburst3 = proj₁ (run mprog3 [] (dMap dOf))
mburst5 = proj₁ (run mprog5 [] (dMap dOf))

map-deepest-3 : hopDl mburst3 ≡ 1
map-deepest-3 = refl

map-deepest-5 : hopDl mburst5 ≡ 1
map-deepest-5 = refl

map-bound-3 : hopD mprog3 ≡ 1
map-bound-3 = refl

map-bound-5 : hopD mprog5 ≡ 1
map-bound-5 = refl
