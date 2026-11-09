-- WHAT SITS UNDER A POSITION: everything a subscription there can ever
-- make — the positions below it, and every timer cascade a cold
-- subscribed under it fires, at a tick past the one it was subscribed
-- at.  Two children of one position share nothing: a cascade under one
-- is keyed by where it was made, which only that child has.
module adequacy.Apart.Cone where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties using (≤-reflexive; <⇒≤; ≤-<-trans; <-irrefl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; Label; ix; last; tick; path; _∙_; cascade; isLt; _<ˡ_; _<ᵖ_; _⊕_)
open import denotation.Events using (<ᵖ-below; <ᵖ-part; <ᵖ-trans; <ᵖ-asym; <ᵖ-irrefl)
open import denotation.Simultaneity using (reflˡ; earlier-tick; effect-tick)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ)
open import operation.Key using (at; after; _<ᴷ_; after-lt)

data Cone (r : Pos) : Pos → Set where
  pre : ∀ y → Cone r (r ⊕ y)
  tag : ∀ {T e} y → tick e < T → Cone r e → Cone r (cascade T e ∙ y)

------------------------------------------------------------------------
-- A cone is closed downward

cone-ext : ∀ {a b} → Cone a b → ∀ y → Cone a (b ⊕ y)
cone-ext {a} (pre z)      y = subst (Cone a) (sym (⊕-assoc a z y)) (pre (z ++ y))
cone-ext (tag z lt c)     y = tag (z ++ y) lt c

cone-trans : ∀ {a b c} → Cone a b → Cone b c → Cone a c
cone-trans h (pre y)      = cone-ext h y
cone-trans h (tag y lt c) = tag y lt (cone-trans h c)

------------------------------------------------------------------------
-- A cone's members come no earlier than its root

cone-tick : ∀ {r x} → Cone r x → tick r ≤ tick x
cone-tick {r} (pre y)    = ≤-reflexive (sym (effect-tick r y))
cone-tick (tag y lt c)   = <⇒≤ (≤-<-trans (cone-tick c) lt)

cone-ge : ∀ {r x} → Cone r x → r <ᵖ x ≡ true ⊎ r ≡ x
cone-ge {r} (pre [])      = inj₂ (sym (⊕-identityʳ r))
cone-ge {r} (pre (l ∷ y)) = inj₁ (<ᵖ-below r y)
cone-ge {r} (tag {e = e} y lt c) = inj₁ (earlier-tick r e y (≤-<-trans (cone-tick c) lt))

-- Before a cone's root, before all of it.
cone-low : ∀ {r x} j → j <ᵖ r ≡ true → Cone r x → j <ᵖ x ≡ true
cone-low j jr c with cone-ge c
... | inj₁ rx   = <ᵖ-trans j _ _ jr rx
... | inj₂ refl = jr

private
  clash : ∀ {u : Bool} → u ≡ false → u ≡ true → ⊥
  clash refl ()

-- Nothing strictly under a position holds it.
cone-up : ∀ {p} l y → Cone (p ⊕ (l ∷ y)) p → ⊥
cone-up {p} l y c with cone-ge c
... | inj₁ h    = clash (<ᵖ-asym p _ (<ᵖ-below p y)) h
... | inj₂ e    = clash (<ᵖ-irrefl p) (subst (λ z → p <ᵖ z ≡ true) e (<ᵖ-below p y))

-- Past a position and not under it: past all of its subtree.
cone-past : ∀ q y → q <ᵖ y ≡ true → (Cone q y → ⊥) → after q <ᴷ at y ≡ true
cone-past q y h ne = after-lt q y h (λ z e → ne (subst (Cone q) (sym e) (pre z)))

------------------------------------------------------------------------
-- Siblings share nothing

private
  stripᵗ : ∀ (x : List Label) {a b} y z → x ++ a ∷ y ≡ x ++ b ∷ z → a ≡ b
  stripᵗ []      y z refl = refl
  stripᵗ (c ∷ x) y z e    = stripᵗ x y z (cong tl e)
    where
      tl : List Label → List Label
      tl []      = []
      tl (_ ∷ w) = w

  strip : ∀ p {a b} y z → (p ⊕ (a ∷ y)) ≡ (p ⊕ (b ∷ z)) → a ≡ b
  strip (_ ∙ x) y z e = stripᵗ x y z (cong path e)

  snoc : ∀ p (a : Label) y → (p ⊕ [ a ]) ⊕ y ≡ p ⊕ (a ∷ y)
  snoc p a y = ⊕-assoc p [ a ] y

  -- A cascade under one child is at a tick the other's instant is not.
  cross : ∀ {p a b T e} y z → tick e < T → Cone (p ⊕ [ b ]) e → (p ⊕ [ a ]) ⊕ y ≡ (cascade T e ∙ z) → ⊥
  cross {p} {a} {b} {T} {e} y z lt c eq =
    <-irrefl refl (≤-<-trans (subst (_≤ tick e) (effect-tick p [ b ]) (cone-tick c)) (subst (tick e <_) tp lt))
    where
      tp : T ≡ tick p
      tp = trans (sym (cong tick eq)) (trans (effect-tick (p ⊕ [ a ]) y) (effect-tick p [ a ]))

  apart : ∀ {p a b x x′} → a ≢ b → Cone (p ⊕ [ a ]) x → Cone (p ⊕ [ b ]) x′ → x ≡ x′ → ⊥
  apart {p} {a} {b} ne (pre y) (pre z) eq =
    ne (strip p y z (trans (sym (snoc p a y)) (trans eq (snoc p b z))))
  apart ne (pre y) (tag z lt c) eq = cross y z lt c eq
  apart ne (tag y lt c) (pre z) eq = cross z y lt c (sym eq)
  apart ne (tag y lt c) (tag z lt′ c′) refl = apart ne c c′ refl

cone-apart : ∀ {p a b x} → a ≢ b → Cone (p ⊕ [ a ]) x → Cone (p ⊕ [ b ]) x → ⊥
cone-apart ne c c′ = apart ne c c′ refl

-- A later sibling's subtree is past an earlier one's.
cone-after : ∀ {p a b y} → a <ˡ b ≡ true → Cone (p ⊕ [ b ]) y → after (p ⊕ [ a ]) <ᴷ at y ≡ true
cone-after {p} {a} {b} {y} ab c = cone-past (p ⊕ [ a ]) y lt (λ c′ → cone-apart ne c′ c)
  where
    ne : a ≢ b
    ne refl = clash (cong isLt (reflˡ a)) ab
    ab′ : (p ⊕ (a ∷ [])) <ᵖ (p ⊕ (b ∷ [])) ≡ true
    ab′ = <ᵖ-part p [] [] ab
    lt : (p ⊕ [ a ]) <ᵖ y ≡ true
    lt with cone-ge c
    ... | inj₁ by   = <ᵖ-trans (p ⊕ [ a ]) (p ⊕ [ b ]) y ab′ by
    ... | inj₂ refl = ab′
