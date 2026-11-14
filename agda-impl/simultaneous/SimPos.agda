{-# OPTIONS --guardedness #-}

-- POSITIONS AS A SIMULATION READS THEM: two positions lead one another
-- or lie apart, and apart they keep their order below them; a join's
-- subscription read back from the order of two joins of one row.
module simultaneous.SimPos where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; Path; Label; _∙_; _⊕_; sub; lt; eq; gt; cmpLabel; cmpPath; cmpInstant; isLt)
open import denotation.Simultaneity using (eqˡ; eqⁱ)
open import denotation.Events using (<ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-trans; ≺-absurd; ≺-ext; ≼-or-≻; ≼-split; ≺→≼; ≺-≼-≺; ≼-≺-≺)
open import denotation.Laws.Worlds using (_⊑_; ⊕-assoc; ⊕-identityʳ; ⊕-cancelˡ; ⊕-injˡ; ⊕-injʳ; ⊑-refl; ⊑-trans; ⊑-≼; ⊑-cmp; ⊑-snoc)
open import denotation.Laws.Count using (⊑?)

private
  lt-of : ∀ {c} → T (isLt c) → c ≡ lt
  lt-of {lt} _ = refl

  path-apart : ∀ p q σ σ′ → cmpPath p q ≡ lt → (∀ zs → q ≡ p ++ zs → ⊥) → cmpPath (p ++ σ) (q ++ σ′) ≡ lt
  path-apart []      q       σ σ′ h  np = ⊥-elim (np q refl)
  path-apart (a ∷ p) (b ∷ q) σ σ′ h  np with cmpLabel a b in c
  ... | lt = refl
  ... | eq with eqˡ a b c
  ...   | refl = path-apart p q σ σ′ h (λ zs e → np zs (cong (a ∷_) e))
  path-apart (a ∷ p) (b ∷ q) σ σ′ () np | gt

-- TWO POSITIONS APART keep their order below them.
apart : ∀ {y y′} → y ≺ y′ → ¬ (y ⊑ y′) → ∀ σ σ′ → (y ⊕ σ) ≺ (y′ ⊕ σ′)
apart {i ∙ p} {j ∙ q} h np σ σ′ with cmpInstant i j in c
... | lt = tt
... | eq with eqⁱ i j c
...   | refl = subst (λ x → T (isLt x)) (sym (path-apart p q σ σ′ (lt-of h) (λ zs e → np (zs , cong (i ∙_) e)))) tt
apart {i ∙ p} {j ∙ q} () np σ σ′ | gt

-- Apart, below on one side.
apart₁ : ∀ {y y′} → y ≺ y′ → ¬ (y ⊑ y′) → ∀ σ → (y ⊕ σ) ≺ y′
apart₁ {y} {y′} h np σ = subst ((y ⊕ σ) ≺_) (⊕-identityʳ y′) (apart h np σ [])

apart₂ : ∀ {y y′} → y ≺ y′ → ¬ (y ⊑ y′) → ∀ σ → y ≺ (y′ ⊕ σ)
apart₂ {y} {y′} h np σ = subst (_≺ (y′ ⊕ σ)) (⊕-identityʳ y) (apart h np [] σ)

-- Leading: at, or before.
⊑-split : ∀ {x y} → x ⊑ y → x ≡ y ⊎ x ≺ y
⊑-split {x} ([] , refl)     = inj₁ (sym (⊕-identityʳ x))
⊑-split {x} (l ∷ zs , refl) = inj₂ (≺-ext x zs)

⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
⊑-antisym {x} {y} xy yx with ⊑-split xy | ⊑-split yx
... | inj₁ e  | _      = e
... | inj₂ _  | inj₁ e = sym e
... | inj₂ a  | inj₂ b = ⊥-elim (≺-absurd {x} {y} a b)

-- HOW TWO POSITIONS LIE: one leads the other, or they lie apart.
data Lie (x y : Pos) : Set where
  above : x ⊑ y → Lie x y
  below : y ⊑ x → Lie x y
  left  : x ≺ y → ¬ (x ⊑ y) → ¬ (y ⊑ x) → Lie x y
  right : y ≺ x → ¬ (x ⊑ y) → ¬ (y ⊑ x) → Lie x y

lie : ∀ x y → Lie x y
lie x y with ⊑? x y | ⊑? y x
... | yes xy | _      = above xy
... | no _   | yes yx = below yx
... | no nxy | no nyx with ≼-or-≻ x y
...   | inj₂ yx = right yx nxy nyx
...   | inj₁ xy with ≼-split {x} {y} xy
...     | inj₁ x<y = left x<y nxy nyx
...     | inj₂ refl = ⊥-elim (nxy (⊑-refl x))

-- Between a position and one below it: below the first.
between : ∀ {x y} σ → x ≺ y → y ≺ (x ⊕ σ) → x ⊑ y
between {x} {y} σ xy yx with lie x y
... | above a       = a
... | below b       = ⊥-elim (⊑-≼ b xy)
... | left _ n _    = ⊥-elim (≺-absurd {y} {x ⊕ σ} yx (apart₁ xy n σ))
... | right yx′ _ _ = ⊥-elim (≺-absurd {x} {y} xy yx′)

-- Up to an image: before it, or under it; closed downward.
UpTo : Pos → Pos → Set
UpTo y l = l ≺ y ⊎ y ⊑ l

upto-down : ∀ {y l l′} → l′ ≺ l → UpTo y l → UpTo y l′
upto-down {y} {l} {l′} ll (inj₁ ly) = inj₁ (≺-trans {l′} {l} {y} ll ly)
upto-down {y} {l} {l′} ll (inj₂ (σ , refl)) with lie l′ y
... | above a with ⊑-split a
...   | inj₁ refl = inj₂ (⊑-refl l′)
...   | inj₂ b    = inj₁ b
upto-down {y} {l} {l′} ll (inj₂ (σ , refl)) | below b        = inj₂ b
upto-down {y} {l} {l′} ll (inj₂ (σ , refl)) | left a _ _     = inj₁ a
upto-down {y} {l} {l′} ll (inj₂ (σ , refl)) | right a _ n    = ⊥-elim (≺-absurd {l′} {y ⊕ σ} ll (apart₁ a n σ))

------------------------------------------------------------------------
-- Joins of one row

⊕-cons : ∀ k a σ → k ⊕ (a ∷ σ) ≡ (k ⊕ [ a ]) ⊕ σ
⊕-cons k a σ = sym (⊕-assoc k [ a ] σ)

-- One label down, two labels compared.
label-lt : ∀ k {a b} σ τ → T (isLt (cmpLabel a b)) → (k ⊕ (a ∷ σ)) ≺ (k ⊕ (b ∷ τ))
label-lt k {a} {b} σ τ h = Equivalence.from T-≡ (<ᵖ-part k {a} {b} σ τ (Equivalence.to T-≡ h))

-- Two joins of one row: in their subscriptions' order.
join-lt : ∀ k {e p} σ τ → e ≺ p → (k ⊕ (sub e ∷ σ)) ≺ (k ⊕ (sub p ∷ τ))
join-lt k {e} {p} σ τ h = label-lt k {sub e} {sub p} σ τ h

-- Read back.
join-back : ∀ k {e p} σ → (k ⊕ (sub e ∷ σ)) ≺ (k ⊕ [ sub p ]) → e ≺ p
join-back k {e} {p} σ h with ≼-or-≻ p e
... | inj₂ pe = pe
... | inj₁ pe with ≼-split {p} {e} pe
...   | inj₁ p<e = ⊥-elim (≺-absurd {k ⊕ (sub e ∷ σ)} {k ⊕ [ sub p ]} h (join-lt k {p} {e} [] σ p<e))
...   | inj₂ refl = ⊥-elim (⊑-≼ (σ , ⊕-cons k (sub p) σ) h)

join-fwd : ∀ k {e p} σ → (k ⊕ [ sub p ]) ≺ (k ⊕ (sub e ∷ σ)) → p ≡ e ⊎ p ≺ e
join-fwd k {e} {p} σ h with ≼-or-≻ p e
... | inj₂ ep = ⊥-elim (≺-absurd {k ⊕ [ sub p ]} {k ⊕ (sub e ∷ σ)} h (join-lt k {e} {p} σ [] ep))
... | inj₁ pe with ≼-split {p} {e} pe
...   | inj₁ p<e = inj₂ p<e
...   | inj₂ eq′ = inj₁ eq′
