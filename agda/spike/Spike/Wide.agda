------------------------------------------------------------------
-- THE PLUG CAN LAND IN THE EXPONENT, AND THEN NO AFFINE PLUG LAW
-- EXISTS.
--
-- `Spike.Scan` prices the scan clause by `blE`, a burst-length bound
-- it calls syntactic, and its whole claim rests on two AFFINE template
-- laws: an emitted value's depth and width are each bounded by
-- `constant + slope * the plugged value's`.  That is what lets a
-- coefficient be a MULTIPLIER at all.
--
-- `blE` IS NOT INVARIANT UNDER PLUGGING.  Its `allᵉ` clause reads
-- `blE (allᵉ e) = blE e * H e`, so a value substituted into an `allᵉ`'s
-- source contributes its own WIDTH to the burst length — and a `scanᵉ`
-- over that `allᵉ` therefore takes its fold count from the plugged
-- value rather than from the program text.  The plug lands in `iter`'s
-- EXPONENT, and the transport is exponential rather than affine.
--
-- `F` below is that template, written as a function on values because
-- `Spike.Scan`'s `Tm` cannot express it — which is precisely the
-- silence this file is about.  The real language's `strmᵗ` can: `F` is
--
--     map(v => v.pipe(mergeAll(), scan((acc, x) => <acc twice>)))
--
-- in plain rxjs, with nothing exotic in it.
--
-- `template-affine` IS WHAT MAKES THIS A REFUTATION RATHER THAN A
-- STRAWMAN.  Every template the fragment CAN express satisfies the law
-- as stated here, with the constant and slope read straight off
-- `evalTm-hop` — so the law is the fragment's own, and `F` is outside
-- it by a property of `F` and not by a choice of phrasing.
--
-- THE WITNESS IS A FAMILY RATHER THAN A PAIR, and it has to be: the
-- claim quantifies a constant and a slope BEFORE the value, so any
-- finite set of points is satisfied by a large enough constant.  The
-- family plugs a WIDE, SHALLOW observable — `wide k` has width k and
-- hop depth 0 — so the affine bound collapses onto its constant while
-- the image's depth reads `2 ^ k`.
--
-- WHAT IT DOES AND DOES NOT KILL.  It kills the reading in which the
-- scan clause's exponent is carried by the program text, and with it
-- the coefficient as a multiplier — both of which `Spike.Scan`'s
-- header claims.  It says nothing about the LEX ORDER, which is
-- `Spike.Order`'s and `Spike.Total`'s subject and never mentions
-- `blE`; and it says nothing about whether some OTHER syntactic
-- quantity works.
------------------------------------------------------------------
module Spike.Wide where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _<_)
open import Data.Nat.Properties using
  ( ≤-refl; ≤-trans; ≤-reflexive; <-irrefl
  ; +-mono-≤; +-monoʳ-≤; *-monoʳ-≤; ⊔-lub
  ; +-assoc; +-identityʳ; *-zeroʳ; *-distribˡ-+; ⊔-identityʳ
  ; m≤m+n; m≤n+m )
open import Data.List using (List; []; _∷_; length)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import Spike.Scan using
  ( Val; natᵛ; obsᵛ; ofᵉ; scanᵉ; allᵉ; Tm; accᵗ; dupᵗ
  ; evalTm; pm; iter; module M )

-- no slots in anything below, so both environments are constantly 0
-- and neither measure can be reading anything off them
z0 : ℕ → ℕ
z0 _ = 0

open M z0 z0

------------------------------------------------------------------
-- THE LAW.  A coefficient is a MULTIPLIER exactly when a plug
-- transports affinely, with the constant and the slope quantified
-- BEFORE the value — which is what a clause of a syntax-directed
-- measure is.
------------------------------------------------------------------

AffinePlug : (Val → Val) → Set
AffinePlug G = Σ ℕ λ c → Σ ℕ λ p → ∀ v → hopDv (G v) ≤ c + p * hopDv v

-- the fragment's own templates all satisfy it, so the law is not a
-- phrasing chosen to fail
template-affine : ∀ f a → AffinePlug (evalTm f a)
template-affine f a = hopDt f + pm f * hopDv a , pm f , bound
  where
    -- the ⊔ the fragment's law is stated over, traded for the + an
    -- affine bound needs; stated with both sides explicit because the
    -- target is otherwise only pinned further down the chain
    ⊔→+ : ∀ v → hopDv a ⊔ hopDv v ≤ hopDv a + hopDv v
    ⊔→+ v = ⊔-lub (m≤m+n (hopDv a) (hopDv v)) (m≤n+m (hopDv v) (hopDv a))

    split : ∀ v → hopDt f + pm f * (hopDv a + hopDv v)
                ≡ (hopDt f + pm f * hopDv a) + pm f * hopDv v
    split v = trans (cong (hopDt f +_)
                          (*-distribˡ-+ (pm f) (hopDv a) (hopDv v)))
                    (sym (+-assoc (hopDt f) _ _))

    bound : ∀ v → hopDv (evalTm f a v)
                ≤ (hopDt f + pm f * hopDv a) + pm f * hopDv v
    bound v =
      ≤-trans (evalTm-hop f a v)
              (≤-trans (+-monoʳ-≤ (hopDt f) (*-monoʳ-≤ (pm f) (⊔→+ v)))
                       (≤-reflexive (split v)))

------------------------------------------------------------------
-- THE WIDE, SHALLOW FAMILY.  `wide k` is a literal burst of k plain
-- numbers, so its width is k and its hop depth is 0 — the two come
-- apart, which is what pins the affine bound at its constant.
------------------------------------------------------------------

vals : ℕ → List Val
vals zero    = []
vals (suc n) = natᵛ 0 ∷ vals n

wide : ℕ → Val
wide k = obsᵛ (ofᵉ (vals k))

vals-len : ∀ k → length (vals k) ≡ k
vals-len zero    = refl
vals-len (suc n) = cong suc (vals-len n)

vals-hop : ∀ k → hopDl (vals k) ≡ 0
vals-hop zero    = refl
vals-hop (suc n) = vals-hop n

vals-H : ∀ k → Hl (vals k) ≡ 0
vals-H zero    = refl
vals-H (suc n) = vals-H n

-- LOAD-BEARING: width k, depth 0.  If either failed the family would
-- not separate the two quantities and an affine bound could read the
-- width instead.
wide-width : ∀ k → Hv (wide k) ≡ k
wide-width k = trans (cong₂ _⊔_ (vals-len k) (vals-H k)) (⊔-identityʳ k)

wide-hop : ∀ k → hopDv (wide k) ≡ 0
wide-hop k = vals-hop k

------------------------------------------------------------------
-- THE TEMPLATE.  Written as a function on values because no `Tm` of
-- `Spike.Scan` can build it: it puts the plug inside an `allᵉ` that a
-- `scanᵉ` folds over.  The step is `dupᵗ accᵗ`, whose plug slope is 2.
------------------------------------------------------------------

step : Tm
step = dupᵗ accᵗ

F : Val → Val
F v = obsᵛ (scanᵉ step (natᵛ 0) (allᵉ (ofᵉ (v ∷ []))))

-- the exponent the clause reads is the PLUGGED value's width
F-count : ∀ k → blE (allᵉ (ofᵉ (wide k ∷ []))) ≡ k
F-count k = trans (cong (λ w → 1 * (w ⊔ 0)) (wide-width k))
                  (trans (cong (1 *_) (⊔-identityʳ k)) (+-identityʳ k))

iter-pow : ∀ k → iter 0 2 k 1 ≡ 2 ^ k
iter-pow zero    = refl
iter-pow (suc k) = cong (λ x → 2 * x) (iter-pow k)

-- LOAD-BEARING, and the whole finding: the image's depth is
-- exponential in a quantity no affine bound in the plug's DEPTH can
-- see, because the plug's depth is zero all along the family.
F-image : ∀ k → hopDv (F (wide k)) ≡ 2 ^ k
F-image k =
  trans (cong₂ (λ n b → iter 0 2 n (suc (b ⊔ 0))) (F-count k) (wide-hop k))
        (iter-pow k)

------------------------------------------------------------------
-- THE REFUTATION.
------------------------------------------------------------------

1≤2^n : ∀ n → 1 ≤ 2 ^ n
1≤2^n zero    = ≤-refl
1≤2^n (suc n) = ≤-trans (1≤2^n n) (m≤m+n _ _)

-- no constant dominates the family, which is what makes a pair of
-- points insufficient and this induction necessary
n<2^n : ∀ n → n < 2 ^ n
n<2^n zero    = ≤-refl
n<2^n (suc n) = +-mono-≤ (1≤2^n n) (≤-trans (n<2^n n) (m≤m+n _ 0))

affine-plug-law-absurd : AffinePlug F → ⊥
affine-plug-law-absurd (c , p , h) =
  <-irrefl refl (≤-trans (n<2^n c) bound)
  where
    collapse : c + p * hopDv (wide c) ≡ c
    collapse rewrite wide-hop c | *-zeroʳ p = +-identityʳ c

    bound : 2 ^ c ≤ c
    bound = ≤-trans (≤-reflexive (sym (F-image c)))
                    (≤-trans (h (wide c)) (≤-reflexive collapse))
