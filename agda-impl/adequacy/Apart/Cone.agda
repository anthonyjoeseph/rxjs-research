-- WHAT SITS UNDER A POSITION: everything a subscription there can ever
-- make — the positions below it, and every timer cascade a cold
-- subscribed under it fires, at a tick past the one it was subscribed
-- at.  Two children of one stamped position share nothing: a cascade
-- under one is keyed by where it was made, which only that child has.
module adequacy.Apart.Cone where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; <-≤-trans; ≤-<-trans; <-irrefl; m≤m+n; m<m+n; +-assoc; n≤1+n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import denotation.Events using (Pos; Label; ix; last; tick; _<ᵖ_; <ᵖ-below; <ᵖ-part; <ᵖ-trans; <ᵖ-asym; <ᵖ-irrefl; ix-<) renaming (sub to subᴾ)
open import operation.Key using (at; after; _<ᴷ_; after-lt)
open import adequacy.Stamped using (Ix; ix-⊕)

data Cone (r : Pos) : Pos → Set where
  pre : ∀ y → Cone r (r ++ y)
  tag : ∀ {T e} y → tick e < T → Cone r e → Cone r (ix T ∷ subᴾ e ∷ y)

------------------------------------------------------------------------
-- Size: a cone's members are no smaller than its root

mutual
  size : Pos → ℕ
  size []      = 0
  size (a ∷ p) = suc (sizeˡ a + size p)

  sizeˡ : Label → ℕ
  sizeˡ (subᴾ q) = size q
  sizeˡ (ix _)   = 0
  sizeˡ last     = 0

size-++ : ∀ p q → size (p ++ q) ≡ size p + size q
size-++ []      q = refl
size-++ (a ∷ p) q = cong suc (trans (cong (sizeˡ a +_) (size-++ p q)) (sym (+-assoc (sizeˡ a) (size p) (size q))))

private
  grow : ∀ p l y → size p < size (p ++ l ∷ y)
  grow p l y = subst (size p <_) (sym (size-++ p (l ∷ y))) (m<m+n (size p) (s≤s z≤n))

cone-size : ∀ {r x} → Cone r x → size r ≤ size x
cone-size {r} (pre [])      = subst (λ z → size r ≤ size z) (sym (++-identityʳ r)) ≤-refl
cone-size {r} (pre (l ∷ y)) = <⇒≤ (grow r l y)
cone-size (tag {e = e} y lt c) = ≤-trans (cone-size c) (≤-trans (m≤m+n (size e) (size y)) (≤-trans (n≤1+n _) (n≤1+n _)))

-- Nothing strictly under a position holds it.
cone-up : ∀ {p} l y → Cone (p ++ l ∷ y) p → ⊥
cone-up {p} l y c = <-irrefl refl (<-≤-trans (grow p l y) (cone-size c))

------------------------------------------------------------------------
-- A cone is closed downward

cone-ext : ∀ {a b} → Cone a b → ∀ y → Cone a (b ++ y)
cone-ext {a} (pre z)      y = subst (Cone a) (sym (++-assoc a z y)) (pre (z ++ y))
cone-ext (tag z lt c)     y = tag (z ++ y) lt c

cone-trans : ∀ {a b c} → Cone a b → Cone b c → Cone a c
cone-trans h (pre y)      = cone-ext h y
cone-trans h (tag y lt c) = tag y lt (cone-trans h c)

------------------------------------------------------------------------
-- A cone's members come no earlier than its root

cone-tick : ∀ {r x} → Ix r → Cone r x → tick r ≤ tick x
cone-tick {ix t ∷ r} _ (pre y)      = ≤-refl
cone-tick            h (tag y lt c) = <⇒≤ (≤-<-trans (cone-tick h c) lt)

cone-ge : ∀ {r x} → Ix r → Cone r x → r <ᵖ x ≡ true ⊎ r ≡ x
cone-ge {r} h (pre [])      = inj₂ (sym (++-identityʳ r))
cone-ge {r} h (pre (l ∷ y)) = inj₁ (<ᵖ-below r y)
cone-ge {ix t ∷ r} h (tag {T} {e} y lt c) = inj₁ (<ᵖ-part [] {ix t} {ix T} r (subᴾ e ∷ y) (ix-< (≤-<-trans (cone-tick h c) lt)))

-- Before a cone's root, before all of it.
cone-low : ∀ {r x} j → Ix r → j <ᵖ r ≡ true → Cone r x → j <ᵖ x ≡ true
cone-low j h jr c with cone-ge h c
... | inj₁ rx   = <ᵖ-trans j _ _ jr rx
... | inj₂ refl = jr

-- Past a position and not under it: past all of its subtree.
cone-past : ∀ q y → q <ᵖ y ≡ true → (Cone q y → ⊥) → after q <ᴷ at y ≡ true
cone-past q y h ne = after-lt q y h (λ z e → ne (subst (Cone q) (sym e) (pre z)))

------------------------------------------------------------------------
-- Siblings share nothing

private
  strip : ∀ p {a b} y z → (p ++ a ∷ y) ≡ (p ++ b ∷ z) → a ≡ b
  strip []      y z refl = refl
  strip (c ∷ p) y z e    = strip p y z (cong tl e)
    where
      tl : Pos → Pos
      tl []      = []
      tl (_ ∷ x) = x

  snoc : ∀ p (a : Label) y → (p ++ [ a ]) ++ y ≡ p ++ a ∷ y
  snoc p a y = ++-assoc p [ a ] y

  -- A cascade under one child is at a tick the other's root is not.
  cross : ∀ {p a b T e} y z → Ix p → tick e < T → Cone (p ++ [ b ]) e → (p ++ [ a ]) ++ y ≡ ix T ∷ subᴾ e ∷ z → ⊥
  cross {ix t ∷ p} {b = b} {e = e} y z _ lt c eq =
    <-irrefl refl (≤-<-trans (cone-tick {ix t ∷ p ++ [ b ]} _ c) (subst (tick e <_) (sym (cong tick eq)) lt))

  apart : ∀ {p a b x x′} → Ix p → a ≢ b → Cone (p ++ [ a ]) x → Cone (p ++ [ b ]) x′ → x ≡ x′ → ⊥
  apart {p} {a} {b} h ne (pre y) (pre z) eq =
    ne (strip p y z (trans (sym (snoc p a y)) (trans eq (snoc p b z))))
  apart h ne (pre y) (tag z lt c) eq = cross y z h lt c eq
  apart h ne (tag y lt c) (pre z) eq = cross z y h lt c (sym eq)
  apart h ne (tag y lt c) (tag z lt′ c′) refl = apart h ne c c′ refl

cone-apart : ∀ {p a b x} → Ix p → a ≢ b → Cone (p ++ [ a ]) x → Cone (p ++ [ b ]) x → ⊥
cone-apart h ne c c′ = apart h ne c c′ refl

-- A later sibling's subtree is past an earlier one's.
cone-after : ∀ {p a b y} → Ix p → [ a ] <ᵖ [ b ] ≡ true → Cone (p ++ [ b ]) y → after (p ++ [ a ]) <ᴷ at y ≡ true
cone-after {p} {a} {b} {y} h ab c = cone-past (p ++ [ a ]) y lt (λ c′ → cone-apart h ne c′ c)
  where
    ne : a ≢ b
    ne refl = ⊥-elim (clash′ (<ᵖ-irrefl [ a ]) ab)
      where
        clash′ : ∀ {u : Data.Bool.Bool} → u ≡ false → u ≡ true → ⊥
        clash′ refl ()
    ab′ : (p ++ a ∷ []) <ᵖ (p ++ b ∷ []) ≡ true
    ab′ = <ᵖ-part p [] [] ab
    lt : (p ++ [ a ]) <ᵖ y ≡ true
    lt with cone-ge (ix-⊕ p [ b ] h) c
    ... | inj₁ by   = <ᵖ-trans (p ++ [ a ]) (p ++ [ b ]) y ab′ by
    ... | inj₂ refl = ab′
