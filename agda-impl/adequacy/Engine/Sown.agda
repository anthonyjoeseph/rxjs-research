-- WHAT A PLACE CAN CAUSE (`Sown p`): every position an event at `p` can
-- lead to — under `p`, or a timer cascade `ix t ∷ sub e ∷ …` whose timer
-- was created at a place `p` causes.  Causation passes on (`sown-trans`),
-- and two siblings under a proper place cause nothing in common
-- (`sib-apart`): a cascade is tagged by where its timer was made, and no
-- place is tagged by what it causes (`no-self`).
module adequacy.Engine.Sown where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-cancelˡ; ∷-injectiveˡ; ∷-injectiveʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; n≤1+n; ≤-trans; <⇒≱; +-assoc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; trans; cong)

open import denotation.MonotonicList.Events using (Label; Pos; ix; sub; last)
open import operation.Key using (Key; at; after)

------------------------------------------------------------------------
-- Where a place keys

data Sown (p : Pos) : Pos → Set where
  inside : ∀ ys → Sown p (p ++ ys)
  framed : ∀ t e ys → Sown p e → Sown p (ix t ∷ sub e ∷ ys)

-- A position's key: where it is, or the position it is past.
posᴷ : Key → Pos
posᴷ (at p)    = p
posᴷ (after p) = p

Sownᴷ : Pos → Key → Set
Sownᴷ p h = Sown p (posᴷ h)

sown-here : ∀ p → Sown p p
sown-here p = subst (Sown p) (++-identityʳ p) (inside [])

after-sown : ∀ p {h} → h ≡ after p → Sownᴷ p h
after-sown p refl = sown-here p

-- A place under `p` sows only where `p` does.
sown-mono : ∀ p ys {h} → Sown (p ++ ys) h → Sown p h
sown-mono p ys (inside zs)       = subst (Sown p) (sym (++-assoc p ys zs)) (inside (ys ++ zs))
sown-mono p ys (framed t e zs s) = framed t e zs (sown-mono p ys s)

-- What is sown, extended, is sown.
sown-ext : ∀ {p h} zs → Sown p h → Sown p (h ++ zs)
sown-ext {p} zs (inside ys)       = subst (Sown p) (sym (++-assoc p ys zs)) (inside (ys ++ zs))
sown-ext     zs (framed t e ys s) = framed t e (ys ++ zs) s

-- What a sown place sows, its sower sows.
sown-trans : ∀ {p x y} → Sown p x → Sown x y → Sown p y
sown-trans s (inside ys)        = sown-ext ys s
sown-trans s (framed t e ys s′) = framed t e ys (sown-trans s s′)

------------------------------------------------------------------------
-- No place sows a place tagged by what it sows

size : Pos → ℕ
size []           = 0
size (ix _ ∷ xs)  = suc (size xs)
size (sub e ∷ xs) = suc (size e + size xs)
size (last ∷ xs)  = suc (size xs)

size-++ : ∀ xs ys → size (xs ++ ys) ≡ size xs + size ys
size-++ []           ys = refl
size-++ (ix _ ∷ xs)  ys = cong suc (size-++ xs ys)
size-++ (sub e ∷ xs) ys = cong suc (trans (cong (size e +_) (size-++ xs ys)) (sym (+-assoc (size e) (size xs) (size ys))))
size-++ (last ∷ xs)  ys = cong suc (size-++ xs ys)

sown-size : ∀ {p h} → Sown p h → size p ≤ size h
sown-size {p} (inside ys)       = subst (size p ≤_) (sym (size-++ p ys)) (m≤m+n (size p) ys′)
  where ys′ = size ys
sown-size     (framed t e ys s) = ≤-trans (sown-size s) (≤-trans (m≤m+n (size e) (size ys)) (≤-trans (n≤1+n _) (n≤1+n _)))

tag-size : ∀ a e ys → size e < size (a ∷ sub e ∷ ys)
tag-size (ix _)  e ys = s≤s (≤-trans (m≤m+n (size e) (size ys)) (n≤1+n _))
tag-size (sub d) e ys = s≤s (≤-trans (≤-trans (m≤m+n (size e) (size ys)) (n≤1+n _)) (m≤n+m _ (size d)))
tag-size last    e ys = s≤s (≤-trans (m≤m+n (size e) (size ys)) (n≤1+n _))

no-self : ∀ a e ys → Sown (a ∷ sub e ∷ ys) e → ⊥
no-self a e ys s = <⇒≱ (tag-size a e ys) (sown-size s)

------------------------------------------------------------------------
-- Siblings cause nothing in common

-- A place below the run's root; a step an operator takes, not a subject's.
Proper : Pos → Set
Proper []      = ⊥
Proper (_ ∷ _) = ⊤

proper-snoc : ∀ p l → Proper (p ++ [ l ])
proper-snoc []      l = tt
proper-snoc (_ ∷ _) l = tt

Plain : Label → Set
Plain (ix _)  = ⊤
Plain (sub _) = ⊥
Plain last    = ⊤

sib-apart : ∀ p {a b} → Proper p → Plain a → Plain b → a ≢ b → ∀ {y} → Sown (p ++ [ a ]) y → Sown (p ++ [ b ]) y → ⊥
sib-apart p {a} {b} pr pa pb ne s₁ s₂ = go s₁ s₂ refl
  where
    off : ∀ {c d} → Plain c → ∀ ys t e zs → Sown (p ++ [ d ]) e → (p ++ [ c ]) ++ ys ≡ ix t ∷ sub e ∷ zs → ⊥
    off {c} {d} pc ys t e zs s eq = cut p pr eq s
      where
        cut : ∀ q → Proper q → (q ++ [ c ]) ++ ys ≡ ix t ∷ sub e ∷ zs → Sown (q ++ [ d ]) e → ⊥
        cut []           () eq′ s′
        cut (x ∷ [])     pq eq′ s′ = subst Plain (∷-injectiveˡ (∷-injectiveʳ eq′)) pc
        cut (x ∷ y′ ∷ q′) pq eq′ s′ with ∷-injectiveˡ eq′ | ∷-injectiveˡ (∷-injectiveʳ eq′)
        ... | refl | refl = no-self x e (q′ ++ [ d ]) s′
    go : ∀ {y₁ y₂} → Sown (p ++ [ a ]) y₁ → Sown (p ++ [ b ]) y₂ → y₁ ≡ y₂ → ⊥
    go (inside ys) (inside zs) eq =
      ne (∷-injectiveˡ (++-cancelˡ p (a ∷ ys) (b ∷ zs) (trans (sym (++-assoc p [ a ] ys)) (trans eq (++-assoc p [ b ] zs)))))
    go (inside ys) (framed t e zs s) eq = off pa ys t e zs s eq
    go (framed t e ys s) (inside zs) eq = off pb zs t e ys s (sym eq)
    go (framed t e ys s) (framed t′ e′ zs s′) eq with ∷-injectiveˡ (∷-injectiveʳ eq)
    ... | refl = go s s′ refl
