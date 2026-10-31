-- WHEN A PENDING CONTINUATION RUNS: at the position of the event it
-- makes, or, for one that makes none, `after` a position — later than
-- everything under it, earlier than whatever follows it.  Keys compare as
-- positions do, a key `after p` reading as `p` with a label past every
-- other appended.
module operation.Key where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does; yes; no)

open import denotation.Events using (Pos; Label; _<ᵖ_; _≟ˡ_; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-split)

data Key : Set where
  at    : Pos → Key
  after : Pos → Key

private
  data XL : Set where
    lab : Label → XL
    top : XL

  -- A label strictly before another.
  _≺_ : XL → XL → Bool
  lab a ≺ lab b = [ a ] <ᵖ [ b ]
  lab _ ≺ top   = true
  top   ≺ _     = false

  _≐_ : XL → XL → Bool
  lab a ≐ lab b = does (a ≟ˡ b)
  top   ≐ top   = true
  _     ≐ _     = false

  lex : List XL → List XL → Bool
  lex []      []      = false
  lex []      (_ ∷ _) = true
  lex (_ ∷ _) []      = false
  lex (a ∷ p) (b ∷ q) = (a ≺ b) ∨ ((a ≐ b) ∧ lex p q)

  labs : Pos → List XL
  labs []      = []
  labs (a ∷ p) = lab a ∷ labs p

  ext : Key → List XL
  ext (at p)    = labs p
  ext (after p) = labs p ++ [ top ]

-- Strictly earlier.
_<ᴷ_ : Key → Key → Bool
k <ᴷ k′ = lex (ext k) (ext k′)

clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
clash refl ()

private
  ≺-trans : ∀ a b c → a ≺ b ≡ true → b ≺ c ≡ true → a ≺ c ≡ true
  ≺-trans (lab a) (lab b) (lab c) h₁ h₂ = <ᵖ-trans [ a ] [ b ] [ c ] h₁ h₂
  ≺-trans (lab _) _       top     _  _  = refl
  ≺-trans (lab _) top     (lab _) _  ()
  ≺-trans top     _       _       () _

  ≺-irrefl : ∀ a → a ≺ a ≡ false
  ≺-irrefl (lab a) = <ᵖ-irrefl [ a ]
  ≺-irrefl top     = refl

  ≺-asym : ∀ a b → b ≺ a ≡ true → a ≺ b ≡ false
  ≺-asym a b h with a ≺ b in e
  ... | false = refl
  ... | true  = ⊥-elim (clash (≺-trans b a b h e) (≺-irrefl b))

  ≐-eq : ∀ a b → a ≐ b ≡ true → a ≡ b
  ≐-eq (lab a) (lab b) h with a ≟ˡ b
  ... | yes refl = refl
  ... | no _     = ⊥-elim (clash h refl)
  ≐-eq top     top     _  = refl
  ≐-eq (lab _) top     ()
  ≐-eq top     (lab _) ()

  ≐-refl : ∀ a → a ≐ a ≡ true
  ≐-refl (lab a) with a ≟ˡ a
  ... | yes _ = refl
  ... | no n  = ⊥-elim (n refl)
  ≐-refl top = refl

  ≺→≠ : ∀ a b → b ≺ a ≡ true → a ≐ b ≡ false
  ≺→≠ a b h with a ≐ b in e
  ... | false = refl
  ... | true with ≐-eq a b e
  ...   | refl = ⊥-elim (clash h (≺-irrefl a))

  xtri : ∀ a b → a ≺ b ≡ true ⊎ a ≡ b ⊎ b ≺ a ≡ true
  xtri (lab a) (lab b) with [ b ] <ᵖ [ a ] in e
  ... | true  = inj₂ (inj₂ refl)
  ... | false with <ᵖ-split [ a ] [ b ] e
  ...   | inj₁ lt   = inj₁ lt
  ...   | inj₂ refl = inj₂ (inj₁ refl)
  xtri (lab _) top     = inj₁ refl
  xtri top     (lab _) = inj₂ (inj₂ refl)
  xtri top     top     = inj₂ (inj₁ refl)

  -- One step of `lex`, read off its two halves.
  ok₁ : ∀ u v → u ≡ true → u ∨ v ≡ true
  ok₁ _ _ refl = refl

  ok₂ : ∀ u v w → v ≡ true → w ≡ true → u ∨ (v ∧ w) ≡ true
  ok₂ true  _ _ _    _    = refl
  ok₂ false _ _ refl refl = refl

  nope : ∀ u v w → u ≡ false → v ≡ false → u ∨ (v ∧ w) ≡ false
  nope _ _ _ refl refl = refl

  none : ∀ u v w → u ≡ false → w ≡ false → u ∨ (v ∧ w) ≡ false
  none _ true  _ refl refl = refl
  none _ false _ refl refl = refl

  pick : ∀ u v w → u ≡ false → v ≡ true → u ∨ (v ∧ w) ≡ true → w ≡ true
  pick _ _ _ refl refl h = h

  lex-irrefl : ∀ x → lex x x ≡ false
  lex-irrefl []      = refl
  lex-irrefl (a ∷ x) = none (a ≺ a) (a ≐ a) (lex x x) (≺-irrefl a) (lex-irrefl x)

  lex-trans : ∀ x y z → lex x y ≡ true → lex y z ≡ true → lex x z ≡ true
  lex-trans []      (_ ∷ _) (_ ∷ _) _  _  = refl
  lex-trans []      []      _       () _
  lex-trans []      (_ ∷ _) []      _  ()
  lex-trans (_ ∷ _) []      _       () _
  lex-trans (_ ∷ _) (_ ∷ _) []      _  ()
  lex-trans (a ∷ x) (b ∷ y) (c ∷ z) h₁ h₂ with xtri a b | xtri b c
  ... | inj₂ (inj₂ ba)   | _                = ⊥-elim (clash h₁ (nope (a ≺ b) (a ≐ b) (lex x y) (≺-asym a b ba) (≺→≠ a b ba)))
  ... | _                | inj₂ (inj₂ cb)   = ⊥-elim (clash h₂ (nope (b ≺ c) (b ≐ c) (lex y z) (≺-asym b c cb) (≺→≠ b c cb)))
  ... | inj₁ ab          | inj₁ bc          = ok₁ _ _ (≺-trans a b c ab bc)
  ... | inj₁ ab          | inj₂ (inj₁ refl) = ok₁ _ _ ab
  ... | inj₂ (inj₁ refl) | inj₁ bc          = ok₁ _ _ bc
  ... | inj₂ (inj₁ refl) | inj₂ (inj₁ refl) =
    ok₂ (a ≺ a) (a ≐ a) (lex x z) (≐-refl a)
        (lex-trans x y z (pick (a ≺ a) (a ≐ a) (lex x y) (≺-irrefl a) (≐-refl a) h₁)
                         (pick (a ≺ a) (a ≐ a) (lex y z) (≺-irrefl a) (≐-refl a) h₂))

  lex-tot : ∀ x y → lex x y ≡ true ⊎ x ≡ y ⊎ lex y x ≡ true
  lex-tot []      []      = inj₂ (inj₁ refl)
  lex-tot []      (_ ∷ _) = inj₁ refl
  lex-tot (_ ∷ _) []      = inj₂ (inj₂ refl)
  lex-tot (a ∷ x) (b ∷ y) with xtri a b
  ... | inj₁ ab          = inj₁ (ok₁ _ _ ab)
  ... | inj₂ (inj₂ ba)   = inj₂ (inj₂ (ok₁ _ _ ba))
  ... | inj₂ (inj₁ refl) with lex-tot x y
  ...   | inj₁ xy          = inj₁ (ok₂ (a ≺ a) (a ≐ a) (lex x y) (≐-refl a) xy)
  ...   | inj₂ (inj₁ refl) = inj₂ (inj₁ refl)
  ...   | inj₂ (inj₂ yx)   = inj₂ (inj₂ (ok₂ (a ≺ a) (a ≐ a) (lex y x) (≐-refl a) yx))

  lex-≮ : ∀ x y z → lex x y ≡ false → lex y z ≡ false → lex x z ≡ false
  lex-≮ x y z h₁ h₂ with lex x z in e
  ... | false = refl
  ... | true with lex-tot x y | lex-tot y z
  ...   | inj₁ xy          | _                = ⊥-elim (clash xy h₁)
  ...   | _                | inj₁ yz          = ⊥-elim (clash yz h₂)
  ...   | inj₂ (inj₁ refl) | _                = ⊥-elim (clash e h₂)
  ...   | _                | inj₂ (inj₁ refl) = ⊥-elim (clash e h₁)
  ...   | inj₂ (inj₂ yx)   | inj₂ (inj₂ zy)   = ⊥-elim (clash (lex-trans x z x e (lex-trans z y x zy yx)) (lex-irrefl x))

-- Neither strictly before the next, twice: not strictly before the last.
≮ᴷ-trans : ∀ a b c → a <ᴷ b ≡ false → b <ᴷ c ≡ false → a <ᴷ c ≡ false
≮ᴷ-trans a b c = lex-≮ (ext a) (ext b) (ext c)
