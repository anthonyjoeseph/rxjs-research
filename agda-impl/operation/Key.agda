-- WHEN A PENDING CONTINUATION RUNS: at the position of the event it
-- makes, or, for one that makes none, `after` a position — later than
-- everything under it, earlier than whatever follows it.  Keys compare as
-- positions do, a key `after p` reading as `p` with a label past every
-- other appended.
module operation.Key where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (does; yes; no)

open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import denotation.Position using (Pos; Label; Instant; _∙_; _⊕_; ix; sub; last; _<ˡ_; _<ⁱ_; _<ᵖ_; _≟ˡ_; _≟ⁱ_;
  Cmp; lt; eq; gt; cmpℕ; lexi; isLt; isEq; cmpLabel; cmpInstant; cmpPath; cmpPos; instant; path; frame; cascade)
open import denotation.Flat using (FLabel; cmpFL; flat; flatᵗ; Ok; Okᵗ; ok-frame; ok-cascade; []; _∷_; cmp-flatˡ; cmp-flat)
open import denotation.Simultaneity using (eqˡ; eqⁱ; reflˡ; reflⁱ; ltˡ; ltⁱ; gtˡ; gtⁱ; isLt-lt)

data Key : Set where
  at    : Pos → Key
  after : Pos → Key

private
  -- A key reads as a list: its instant, then its path's labels, then for
  -- `after` a label past every other.
  data XL : Set where
    ins : Instant → XL
    lab : Label → XL
    top : XL

  -- Strictly before: instants first, then labels, then the top.
  _≺_ : XL → XL → Bool
  ins i ≺ ins j = i <ⁱ j
  ins _ ≺ lab _ = true
  ins _ ≺ top   = true
  lab _ ≺ ins _ = false
  lab a ≺ lab b = a <ˡ b
  lab _ ≺ top   = true
  top   ≺ _     = false

  _≐_ : XL → XL → Bool
  ins i ≐ ins j = does (i ≟ⁱ j)
  lab a ≐ lab b = does (a ≟ˡ b)
  top   ≐ top   = true
  _     ≐ _     = false

  lex : List XL → List XL → Bool
  lex []      []      = false
  lex []      (_ ∷ _) = true
  lex (_ ∷ _) []      = false
  lex (a ∷ p) (b ∷ q) = (a ≺ b) ∨ ((a ≐ b) ∧ lex p q)

  labs : List Label → List XL
  labs []      = []
  labs (a ∷ p) = lab a ∷ labs p

  ext : Key → List XL
  ext (at (i ∙ p))    = ins i ∷ labs p
  ext (after (i ∙ p)) = ins i ∷ labs p ++ [ top ]

-- Strictly earlier: in an earlier instant, or in the same one and
-- earlier on the path.
_<ᴷ_ : Key → Key → Bool
k <ᴷ k′ = lex (ext k) (ext k′)

clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
clash refl ()

------------------------------------------------------------------------
-- THE KEY ORDER IS THE FLAT ORDER WITH A TOP: a key flattened to its
-- position's flat label list (`denotation.Flat`), with one label past
-- every other appended for `after`, orders lexicographically as that
-- list does.

data FXL : Set where
  flab : FLabel → FXL
  ftop : FXL

flex : List FXL → List FXL → Bool
flex []      []      = false
flex []      (_ ∷ _) = true
flex (_ ∷ _) []      = false
flex (flab a ∷ p) (flab b ∷ q) = isLt (cmpFL a b) ∨ (isEq (cmpFL a b) ∧ flex p q)
flex (flab _ ∷ _) (ftop ∷ _)   = true
flex (ftop ∷ _)   (flab _ ∷ _) = false
flex (ftop ∷ p)   (ftop ∷ q)   = flex p q

-- A key, `after` or not.
keyAt : Bool → Pos → Key
keyAt false p = at p
keyAt true  p = after p

fkey : Bool → Pos → List FXL
fkey b p = map flab (flat p) ++ (if b then [ ftop ] else [])

private
  sfx : Bool → List XL
  sfx b = if b then [ top ] else []

  ext-keyAt : ∀ b i p → ext (keyAt b (i ∙ p)) ≡ ins i ∷ labs p ++ sfx b
  ext-keyAt false i p = cong (ins i ∷_) (sym (++-identityʳ (labs p)))
  ext-keyAt true  i p = refl

  -- A comparison's `eq` is decided equality.
  bridge : ∀ {A : Set} (c : A → A → Cmp) (d : DecidableEquality A) → (∀ a b → c a b ≡ eq → a ≡ b) → (∀ a → c a a ≡ eq)
         → ∀ a b → isEq (c a b) ≡ does (d a b)
  bridge c d e r a b with d a b
  ... | yes refl rewrite r a = refl
  ... | no ne with c a b in h
  ...   | eq = ⊥-elim (ne (e a b h))
  ...   | lt = refl
  ...   | gt = refl

  two : ∀ c₁ c₂ z → isLt c₁ ∨ (isEq c₁ ∧ (isLt c₂ ∨ (isEq c₂ ∧ z))) ≡ isLt (lexi c₁ c₂) ∨ (isEq (lexi c₁ c₂) ∧ z)
  two eq _ _ = refl
  two lt _ _ = refl
  two gt _ _ = refl

  flex-path : ∀ {p q} → Okᵗ p → Okᵗ q → ∀ b b′
            → flex (map flab (flatᵗ p) ++ (if b then [ ftop ] else [])) (map flab (flatᵗ q) ++ (if b′ then [ ftop ] else []))
            ≡ lex (labs p ++ sfx b) (labs q ++ sfx b′)
  flex-path []       []       false false = refl
  flex-path []       []       false true  = refl
  flex-path []       []       true  false = refl
  flex-path []       []       true  true  = refl
  flex-path []       (_ ∷ _)  false _     = refl
  flex-path []       (_ ∷ _)  true  _     = refl
  flex-path (_ ∷ _)  []       _     false = refl
  flex-path (_ ∷ _)  []       _     true  = refl
  flex-path {a ∷ p} {c ∷ q} (x ∷ xs) (y ∷ ys) b b′ =
    trans (cong₂ (λ k z → isLt k ∨ (isEq k ∧ z)) (cmp-flatˡ x y) (flex-path xs ys b b′))
          (cong (λ v → isLt (cmpLabel a c) ∨ (v ∧ lex (labs p ++ sfx b) (labs q ++ sfx b′)))
                (bridge cmpLabel _≟ˡ_ eqˡ reflˡ a c))

  flex-pos : ∀ {a c} → Ok a → Ok c → ∀ b b′
           → flex (fkey b a) (fkey b′ c)
           ≡ (instant a <ⁱ instant c) ∨ (does (instant a ≟ⁱ instant c) ∧ lex (labs (path a) ++ sfx b) (labs (path c) ++ sfx b′))
  flex-pos (ok-frame xs)    (ok-frame ys)    b b′ = flex-path xs ys b b′
  flex-pos (ok-frame _)     (ok-cascade _ _) _ _  = refl
  flex-pos (ok-cascade _ _) (ok-frame _)     _ _  = refl
  flex-pos {cascade (suc t) e ∙ p} {cascade (suc u) d ∙ q} (ok-cascade ex ey′) (ok-cascade dx dy′) b b′ =
    trans (cong₂ (λ k z → isLt (cmpℕ (suc t) (suc u)) ∨ (isEq (cmpℕ (suc t) (suc u)) ∧ (isLt k ∨ (isEq k ∧ z))))
                 (cmp-flat ex dx) (flex-path ey′ dy′ b b′))
    (trans (two (cmpℕ (suc t) (suc u)) (cmpPos e d) (lex (labs p ++ sfx b) (labs q ++ sfx b′)))
           (cong (λ v → isLt (cmpInstant (cascade (suc t) e) (cascade (suc u) d)) ∨ (v ∧ lex (labs p ++ sfx b) (labs q ++ sfx b′)))
                 (bridge cmpInstant _≟ⁱ_ eqⁱ reflⁱ (cascade (suc t) e) (cascade (suc u) d))))

-- THE KEY ORDER IS THE FLAT ORDER WITH A TOP.
flat-key : ∀ b b′ {a c} → Ok a → Ok c → flex (fkey b a) (fkey b′ c) ≡ keyAt b a <ᴷ keyAt b′ c
flat-key b b′ {i ∙ p} {j ∙ q} oa oc = trans (flex-pos oa oc b b′) (sym (cong₂ lex (ext-keyAt b i p) (ext-keyAt b′ j q)))

private
  ≺-trans : ∀ a b c → a ≺ b ≡ true → b ≺ c ≡ true → a ≺ c ≡ true
  ≺-trans (ins i) (ins j) (ins k) h₁ h₂ = cong isLt (ltⁱ i j k (isLt-lt h₁) (isLt-lt h₂))
  ≺-trans (ins _) _       (lab _) _  _  = refl
  ≺-trans (ins _) _       top     _  _  = refl
  ≺-trans (ins _) (lab _) (ins _) _  ()
  ≺-trans (ins _) top     (ins _) _  ()
  ≺-trans (lab a) (lab b) (lab c) h₁ h₂ = cong isLt (ltˡ a b c (isLt-lt h₁) (isLt-lt h₂))
  ≺-trans (lab _) _       top     _  _  = refl
  ≺-trans (lab _) (ins _) _       () _
  ≺-trans (lab _) (lab _) (ins _) _  ()
  ≺-trans (lab _) top     (ins _) _  ()
  ≺-trans (lab _) top     (lab _) _  ()
  ≺-trans top     _       _       () _

  ≺-irrefl : ∀ a → a ≺ a ≡ false
  ≺-irrefl (ins i) = cong isLt (reflⁱ i)
  ≺-irrefl (lab a) = cong isLt (reflˡ a)
  ≺-irrefl top     = refl

  ≺-asym : ∀ a b → b ≺ a ≡ true → a ≺ b ≡ false
  ≺-asym a b h with a ≺ b in e
  ... | false = refl
  ... | true  = ⊥-elim (clash (≺-trans b a b h e) (≺-irrefl b))

  ≐-eq : ∀ a b → a ≐ b ≡ true → a ≡ b
  ≐-eq (ins i) (ins j) h with i ≟ⁱ j
  ... | yes refl = refl
  ... | no _     = ⊥-elim (clash h refl)
  ≐-eq (lab a) (lab b) h with a ≟ˡ b
  ... | yes refl = refl
  ... | no _     = ⊥-elim (clash h refl)
  ≐-eq top     top     _  = refl
  ≐-eq (ins _) (lab _) ()
  ≐-eq (ins _) top     ()
  ≐-eq (lab _) (ins _) ()
  ≐-eq (lab _) top     ()
  ≐-eq top     (ins _) ()
  ≐-eq top     (lab _) ()

  ≐-refl : ∀ a → a ≐ a ≡ true
  ≐-refl (ins i) with i ≟ⁱ i
  ... | yes _ = refl
  ... | no n  = ⊥-elim (n refl)
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
  xtri (ins i) (ins j) with cmpInstant i j in e
  ... | lt = inj₁ refl
  ... | gt = inj₂ (inj₂ (cong isLt (gtⁱ i j e)))
  ... | eq with eqⁱ i j e
  ...   | refl = inj₂ (inj₁ refl)
  xtri (lab a) (lab b) with cmpLabel a b in e
  ... | lt = inj₁ refl
  ... | gt = inj₂ (inj₂ (cong isLt (gtˡ a b e)))
  ... | eq with eqˡ a b e
  ...   | refl = inj₂ (inj₁ refl)
  xtri (ins _) (lab _) = inj₁ refl
  xtri (ins _) top     = inj₁ refl
  xtri (lab _) (ins _) = inj₂ (inj₂ refl)
  xtri (lab _) top     = inj₁ refl
  xtri top     (ins _) = inj₂ (inj₂ refl)
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

  pickf : ∀ u v w → u ≡ false → v ≡ true → u ∨ (v ∧ w) ≡ false → w ≡ false
  pickf _ _ _ refl refl h = h

  same : ∀ u v w {r} → u ≡ false → v ≡ true → w ≡ r → u ∨ (v ∧ w) ≡ r
  same _ _ _ refl refl refl = refl

  -- One step of `lex` is one step of `lexi`.
  one : ∀ c z c₂ → z ≡ isLt c₂ → isLt c ∨ (isEq c ∧ z) ≡ isLt (lexi c c₂)
  one lt _ _ _ = refl
  one eq _ _ h = h
  one gt _ _ _ = refl

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

  lex-at : ∀ p q → lex (labs p) (labs q) ≡ isLt (cmpPath p q)
  lex-at []      []      = refl
  lex-at []      (_ ∷ _) = refl
  lex-at (_ ∷ _) []      = refl
  lex-at (a ∷ p) (b ∷ q) =
    trans (cong (λ v → (a <ˡ b) ∨ (v ∧ lex (labs p) (labs q))) (sym (bridge cmpLabel _≟ˡ_ eqˡ reflˡ a b)))
          (one (cmpLabel a b) _ (cmpPath p q) (lex-at p q))

  tl : List XL → List XL
  tl []      = []
  tl (_ ∷ x) = x

  no-top : ∀ p y → labs p ≡ labs y ++ [ top ] → ⊥
  no-top []      []      ()
  no-top []      (_ ∷ _) ()
  no-top (a ∷ p) []      ()
  no-top (a ∷ p) (b ∷ y) e = no-top p y (cong tl e)

  lex-nil : ∀ x → lex x [] ≡ false
  lex-nil []      = refl
  lex-nil (_ ∷ _) = refl

  lex-top : ∀ y → lex (labs y) [ top ] ≡ true
  lex-top []      = refl
  lex-top (_ ∷ _) = refl

  -- Equal labels at the head: the order of the tails.
  path-cons : ∀ a p q → isLt (cmpPath (a ∷ p) (a ∷ q)) ≡ isLt (cmpPath p q)
  path-cons a p q = cong (λ c → isLt (lexi c (cmpPath p q))) (reflˡ a)

  after-ltᵗ : ∀ q y → isLt (cmpPath q y) ≡ true → (∀ z → y ≡ q ++ z → ⊥) → lex (labs q ++ [ top ]) (labs y) ≡ true
  after-ltᵗ []      y       h ne = ⊥-elim (ne y refl)
  after-ltᵗ (a ∷ q) []      () ne
  after-ltᵗ (a ∷ q) (b ∷ y) h ne with xtri (lab a) (lab b)
  ... | inj₁ ab          = ok₁ _ _ ab
  ... | inj₂ (inj₂ ba)   = ⊥-elim (clash (trans (lex-at (a ∷ q) (b ∷ y)) h)
                                         (nope (lab a ≺ lab b) (lab a ≐ lab b) _ (≺-asym (lab a) (lab b) ba) (≺→≠ (lab a) (lab b) ba)))
  ... | inj₂ (inj₁ refl) =
    ok₂ (lab a ≺ lab a) (lab a ≐ lab a) _ (≐-refl (lab a))
        (after-ltᵗ q y (trans (sym (path-cons a q y)) h) λ z e → ne z (cong (a ∷_) e))

  after-pastᵗ : ∀ y q → lex (labs y ++ [ top ]) (labs q) ≡ false → (∀ z → y ≡ q ++ z → z ≡ []) → lex (labs y ++ [ top ]) (labs q ++ [ top ]) ≡ false
  after-pastᵗ []      []      h ne = lex-irrefl (top ∷ [])
  after-pastᵗ []      (b ∷ q) h ne = refl
  after-pastᵗ (a ∷ y) []      h ne with () ← ne (a ∷ y) refl
  after-pastᵗ (a ∷ y) (b ∷ q) h ne with xtri (lab a) (lab b)
  ... | inj₁ ab          = ⊥-elim (clash (ok₁ _ _ ab) h)
  ... | inj₂ (inj₂ ba)   = nope (lab a ≺ lab b) (lab a ≐ lab b) _ (≺-asym (lab a) (lab b) ba) (≺→≠ (lab a) (lab b) ba)
  ... | inj₂ (inj₁ refl) =
    same (lab a ≺ lab a) (lab a ≐ lab a) _ (≺-irrefl (lab a)) (≐-refl (lab a))
         (after-pastᵗ y q (pickf (lab a ≺ lab a) (lab a ≐ lab a) _ (≺-irrefl (lab a)) (≐-refl (lab a)) h) λ z e → ne z (cong (a ∷_) e))

  attach-nextᵗ : ∀ c → lex (labs (c ++ [ ix 1 ]) ++ [ top ]) (labs (c ++ [ ix 2 ])) ≡ true
  attach-nextᵗ []      = refl
  attach-nextᵗ (a ∷ c) = ok₂ (lab a ≺ lab a) (lab a ≐ lab a) _ (≐-refl (lab a)) (attach-nextᵗ c)

  past-attachᵗ : ∀ c y → lex (labs y) (labs (c ++ [ ix 1 ]) ++ [ top ]) ≡ false → lex (labs y) (labs (c ++ [ ix 2 ])) ≡ false
  past-attachᵗ []      []                            ()
  past-attachᵗ []      (ix zero ∷ y)                 ()
  past-attachᵗ []      (ix (suc zero) ∷ y)           h =
    ⊥-elim (clash (ok₂ (lab (ix 1) ≺ lab (ix 1)) (lab (ix 1) ≐ lab (ix 1)) _ (≐-refl (lab (ix 1))) (lex-top y)) h)
  past-attachᵗ []      (ix (suc (suc zero)) ∷ y)     h = none _ _ _ refl (lex-nil (labs y))
  past-attachᵗ []      (ix (suc (suc (suc n))) ∷ y)  h = none _ _ _ refl (lex-nil (labs y))
  past-attachᵗ []      (sub _ ∷ y)                   h = none _ _ _ refl (lex-nil (labs y))
  past-attachᵗ []      (last ∷ y)                    h = none _ _ _ refl (lex-nil (labs y))
  past-attachᵗ (a ∷ c) []                            ()
  past-attachᵗ (a ∷ c) (b ∷ y) h with xtri (lab b) (lab a)
  ... | inj₁ ba          = ⊥-elim (clash (ok₁ _ _ ba) h)
  ... | inj₂ (inj₂ ab)   = nope (lab b ≺ lab a) (lab b ≐ lab a) _ (≺-asym (lab b) (lab a) ab) (≺→≠ (lab b) (lab a) ab)
  ... | inj₂ (inj₁ refl) =
    same (lab b ≺ lab b) (lab b ≐ lab b) _ (≺-irrefl (lab b)) (≐-refl (lab b))
         (past-attachᵗ c y (pickf (lab b ≺ lab b) (lab b ≐ lab b) _ (≺-irrefl (lab b)) (≐-refl (lab b)) h))

-- A position's key and an after's never tie: one is strictly first.
at-after-≮ : ∀ p y → at p <ᴷ after y ≡ false → after y <ᴷ at p ≡ false → ⊥
at-after-≮ (i ∙ p) (j ∙ y) h₁ h₂ with lex-tot (ins i ∷ labs p) (ins j ∷ labs y ++ [ top ])
... | inj₁ l        = clash l h₁
... | inj₂ (inj₁ e) = no-top p y (cong tl e)
... | inj₂ (inj₂ g) = clash g h₂

-- Neither strictly before the next, twice: not strictly before the last.
≮ᴷ-trans : ∀ a b c → a <ᴷ b ≡ false → b <ᴷ c ≡ false → a <ᴷ c ≡ false
≮ᴷ-trans a b c = lex-≮ (ext a) (ext b) (ext c)

<ᴷ-trans : ∀ a b c → a <ᴷ b ≡ true → b <ᴷ c ≡ true → a <ᴷ c ≡ true
<ᴷ-trans a b c = lex-trans (ext a) (ext b) (ext c)

<ᴷ-irrefl : ∀ a → a <ᴷ a ≡ false
<ᴷ-irrefl a = lex-irrefl (ext a)

-- Positions' keys compare as the positions do.
at-<ᴷ : ∀ p q → at p <ᴷ at q ≡ p <ᵖ q
at-<ᴷ (i ∙ p) (j ∙ q) =
  trans (cong (λ v → (i <ⁱ j) ∨ (v ∧ lex (labs p) (labs q))) (sym (bridge cmpInstant _≟ⁱ_ eqⁱ reflⁱ i j)))
        (one (cmpInstant i j) _ (cmpPath p q) (lex-at p q))

-- Past `q` and not under it: past all of `q`'s subtree.
after-lt : ∀ q y → q <ᵖ y ≡ true → (∀ z → y ≡ q ⊕ z → ⊥) → after q <ᴷ at y ≡ true
after-lt (i ∙ q) (j ∙ y) h ne with xtri (ins i) (ins j)
... | inj₁ ij          = ok₁ _ _ ij
... | inj₂ (inj₂ ji)   = ⊥-elim (clash (trans (at-<ᴷ (i ∙ q) (j ∙ y)) h)
                                       (nope (ins i ≺ ins j) (ins i ≐ ins j) _ (≺-asym (ins i) (ins j) ji) (≺→≠ (ins i) (ins j) ji)))
... | inj₂ (inj₁ refl) =
  ok₂ (ins i ≺ ins i) (ins i ≐ ins i) _ (≐-refl (ins i))
      (after-ltᵗ q y (trans (sym (cong (λ c → isLt (lexi c (cmpPath q y))) (reflⁱ i))) h) λ z e → ne z (cong (i ∙_) e))

-- An after no earlier than `q`, and not strictly under it: no earlier
-- than `q`'s after.
after-past : ∀ y q → after y <ᴷ at q ≡ false → (∀ z → y ≡ q ⊕ z → z ≡ []) → after y <ᴷ after q ≡ false
after-past (i ∙ y) (j ∙ q) h ne with xtri (ins i) (ins j)
... | inj₁ ij          = ⊥-elim (clash (ok₁ _ _ ij) h)
... | inj₂ (inj₂ ji)   = nope (ins i ≺ ins j) (ins i ≐ ins j) _ (≺-asym (ins i) (ins j) ji) (≺→≠ (ins i) (ins j) ji)
... | inj₂ (inj₁ refl) =
  same (ins i ≺ ins i) (ins i ≐ ins i) _ (≺-irrefl (ins i)) (≐-refl (ins i))
       (after-pastᵗ y q (pickf (ins i ≺ ins i) (ins i ≐ ins i) _ (≺-irrefl (ins i)) (≐-refl (ins i)) h) λ z e → ne z (cong (i ∙_) e))

-- A connect's attach is keyed strictly before its next slot.
attach-next : ∀ c → after (c ⊕ [ ix 1 ]) <ᴷ at (c ⊕ [ ix 2 ]) ≡ true
attach-next (i ∙ c) = ok₂ (ins i ≺ ins i) (ins i ≐ ins i) _ (≐-refl (ins i)) (attach-nextᵗ c)

-- No position lies between a connect's attach and its next slot.
past-attach : ∀ c y → at y <ᴷ after (c ⊕ [ ix 1 ]) ≡ false → at y <ᴷ at (c ⊕ [ ix 2 ]) ≡ false
past-attach (i ∙ c) (j ∙ y) h with xtri (ins j) (ins i)
... | inj₁ ji          = ⊥-elim (clash (ok₁ _ _ ji) h)
... | inj₂ (inj₂ ij)   = nope (ins j ≺ ins i) (ins j ≐ ins i) _ (≺-asym (ins j) (ins i) ij) (≺→≠ (ins j) (ins i) ij)
... | inj₂ (inj₁ refl) =
  same (ins j ≺ ins j) (ins j ≐ ins j) _ (≺-irrefl (ins j)) (≐-refl (ins j))
       (past-attachᵗ c y (pickf (ins j ≺ ins j) (ins j ≐ ins j) _ (≺-irrefl (ins j)) (≐-refl (ins j)) h))

-- Strictly before, never the other way too.
<ᴷ-asym : ∀ a b → a <ᴷ b ≡ true → b <ᴷ a ≡ false
<ᴷ-asym a b h with b <ᴷ a in e
... | false = refl
... | true  = ⊥-elim (clash (<ᴷ-trans a b a h e) (<ᴷ-irrefl a))
