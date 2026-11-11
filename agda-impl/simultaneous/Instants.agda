{-# OPTIONS --guardedness #-}

-- INSTANTS IN ORDER.  A list of instants strictly ascending, built by
-- inserting one at a time; two such lists holding the same instants have
-- one length, and one holding every instant of another and one more is
-- longer.  What a rank counts.
module simultaneous.Instants where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Nat using (suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Instant; frame; cascade; Cmp; lt; eq; gt; isLt; lexi; cmpInstant; cmpPath; _<ⁱ_; _∙_; instant)
open import denotation.EmissionSet using (_≺_)
open import denotation.Simultaneity using (eqⁱ; reflⁱ; ltⁱ; gtⁱ)

-- Instants in order.
record _≺ⁱ_ (i j : Instant) : Set where
  constructor below
  field earlier : T (i <ⁱ j)

-- Strictly ascending.
Sorted : List Instant → Set
Sorted = AllPairs _≺ⁱ_

------------------------------------------------------------------------
-- The order

lt→≺ⁱ : ∀ {i j} → cmpInstant i j ≡ lt → i ≺ⁱ j
lt→≺ⁱ h = below (subst (λ c → T (isLt c)) (sym h) tt)

≺ⁱ→lt : ∀ {i j} → i ≺ⁱ j → cmpInstant i j ≡ lt
≺ⁱ→lt {i} {j} (below h) with cmpInstant i j
... | lt = refl
... | eq = ⊥-elim h
... | gt = ⊥-elim h

irrⁱ : ∀ {i} → i ≺ⁱ i → ⊥
irrⁱ {i} (below h) = subst (λ c → T (isLt c)) (reflⁱ i) h

transⁱ : ∀ {i j k} → i ≺ⁱ j → j ≺ⁱ k → i ≺ⁱ k
transⁱ {i} {j} {k} a b = lt→≺ⁱ (ltⁱ i j k (≺ⁱ→lt a) (≺ⁱ→lt b))

triⁱ : ∀ i j → i ≺ⁱ j ⊎ i ≡ j ⊎ j ≺ⁱ i
triⁱ i j with cmpInstant i j in h
... | lt = inj₁ (lt→≺ⁱ h)
... | eq = inj₂ (inj₁ (eqⁱ i j h))
... | gt = inj₂ (inj₂ (lt→≺ⁱ (gtⁱ i j h)))

-- Nothing comes before the subscribe frame.
frame-least : ∀ {i} → i ≺ⁱ frame → ⊥
frame-least {frame}         h = irrⁱ h
frame-least {cascade _ _ _} (below ())

------------------------------------------------------------------------
-- Insertion

mutual
  insertⁱ : Instant → List Instant → List Instant
  insertⁱ y []       = y ∷ []
  insertⁱ y (x ∷ xs) = place y x xs (cmpInstant y x)

  place : Instant → Instant → List Instant → Cmp → List Instant
  place y x xs lt = y ∷ x ∷ xs
  place y x xs eq = x ∷ xs
  place y x xs gt = x ∷ insertⁱ y xs

all-insert : ∀ {P : Instant → Set} {y} xs → P y → All P xs → All P (insertⁱ y xs)
all-insert []       py []         = py ∷ []
all-insert {y = y} (x ∷ xs) py (px ∷ pxs) with cmpInstant y x
... | lt = py ∷ px ∷ pxs
... | eq = px ∷ pxs
... | gt = px ∷ all-insert xs py pxs

sorted-insert : ∀ {y} xs → Sorted xs → Sorted (insertⁱ y xs)
sorted-insert []       []         = [] ∷ []
sorted-insert {y} (x ∷ xs) (ax ∷ sx) with cmpInstant y x in h
... | lt = (lt→≺ⁱ h ∷ All.map (transⁱ (lt→≺ⁱ h)) ax) ∷ ax ∷ sx
... | eq = ax ∷ sx
... | gt = all-insert xs (lt→≺ⁱ (gtⁱ y x h)) ax ∷ sorted-insert xs sx

∈-insert⁻ : ∀ {z y} xs → z ∈ insertⁱ y xs → z ≡ y ⊎ z ∈ xs
∈-insert⁻ []       (here refl) = inj₁ refl
∈-insert⁻ {y = y} (x ∷ xs) m with cmpInstant y x
∈-insert⁻ (x ∷ xs) (here refl) | lt = inj₁ refl
∈-insert⁻ (x ∷ xs) (there m)   | lt = inj₂ m
∈-insert⁻ (x ∷ xs) m           | eq = inj₂ m
∈-insert⁻ (x ∷ xs) (here refl) | gt = inj₂ (here refl)
∈-insert⁻ (x ∷ xs) (there m)   | gt with ∈-insert⁻ xs m
... | inj₁ z≡y = inj₁ z≡y
... | inj₂ m′  = inj₂ (there m′)

∈-insert⁺ : ∀ {z y} xs → z ≡ y ⊎ z ∈ xs → z ∈ insertⁱ y xs
∈-insert⁺ []       (inj₁ refl) = here refl
∈-insert⁺ {y = y} (x ∷ xs) m with cmpInstant y x in h
∈-insert⁺ (x ∷ xs) (inj₁ refl)         | lt = here refl
∈-insert⁺ (x ∷ xs) (inj₂ m)            | lt = there m
∈-insert⁺ {y = y} (x ∷ xs) (inj₁ refl) | eq = here (eqⁱ y x h)
∈-insert⁺ (x ∷ xs) (inj₂ m)            | eq = m
∈-insert⁺ (x ∷ xs) (inj₁ refl)         | gt = there (∈-insert⁺ xs (inj₁ refl))
∈-insert⁺ (x ∷ xs) (inj₂ (here refl))  | gt = here refl
∈-insert⁺ (x ∷ xs) (inj₂ (there m))    | gt = there (∈-insert⁺ xs (inj₂ m))

length-insert : ∀ {y} xs → ¬ y ∈ xs → length (insertⁱ y xs) ≡ suc (length xs)
length-insert []       _ = refl
length-insert {y} (x ∷ xs) n with cmpInstant y x in h
... | lt = refl
... | eq = ⊥-elim (n (here (eqⁱ y x h)))
... | gt = cong suc (length-insert xs (λ m → n (there m)))

------------------------------------------------------------------------
-- Counting

-- Past the head of an ascending list.
private
  above : ∀ {x z xs} → All (x ≺ⁱ_) xs → z ∈ x ∷ xs → z ≡ x ⊎ x ≺ⁱ z
  above _  (here refl) = inj₁ refl
  above ax (there m)   = inj₂ (All.lookup ax m)

  off-head : ∀ {x y z} → y ≺ⁱ x → z ≡ x ⊎ x ≺ⁱ z → z ≡ y → ⊥
  off-head yx (inj₁ refl) refl = irrⁱ yx
  off-head yx (inj₂ xz)   refl = irrⁱ (transⁱ yx xz)

-- An ascending list holding only instants of another is no longer.
sorted-⊆ : ∀ {xs ys} → Sorted xs → Sorted ys → (∀ {z} → z ∈ xs → z ∈ ys) → length xs ≤ length ys
sorted-⊆ {[]}             _         _         _   = z≤n
sorted-⊆ {x ∷ xs} {[]}     _         _         sub with () ← sub (here refl)
sorted-⊆ {x ∷ xs} {y ∷ ys} (ax ∷ sx) (ay ∷ sy) sub with sub (here refl)
... | here refl = s≤s (sorted-⊆ sx sy λ m → tail m (sub (there m)))
  where
    tail : ∀ {z} → z ∈ xs → z ∈ x ∷ ys → z ∈ ys
    tail _ (there m′)  = m′
    tail m (here refl) = ⊥-elim (irrⁱ (All.lookup ax m))
... | there xm = m≤n⇒m≤1+n (sorted-⊆ (ax ∷ sx) sy λ {z} m → past m (sub m))
  where
    past : ∀ {z} → z ∈ x ∷ xs → z ∈ y ∷ ys → z ∈ ys
    past _ (there m′)            = m′
    past m (here z≡y)            = ⊥-elim (off-head (All.lookup ay xm) (above ax m) z≡y)

-- One holding every instant of another and one more is longer.
sorted-⊂ : ∀ {xs ys w} → Sorted xs → Sorted ys → (∀ {z} → z ∈ xs → z ∈ ys) → w ∈ ys → ¬ w ∈ xs
         → suc (length xs) ≤ length ys
sorted-⊂ {xs} {ys} sx sy sub wy wx =
  subst (_≤ length ys) (length-insert xs wx) (sorted-⊆ (sorted-insert xs sx) sy λ m → [ (λ { refl → wy }) , sub ]′ (∈-insert⁻ xs m))

------------------------------------------------------------------------
-- Positions by instant

-- A row before another and of another instant is of an earlier one.
≺-instant : ∀ k q → k ≺ q → instant k ≢ instant q → instant k ≺ⁱ instant q
≺-instant (a ∙ p) (b ∙ r) h ne with cmpInstant a b in c
... | lt = lt→≺ⁱ c
... | eq = ⊥-elim (ne (eqⁱ a b c))
... | gt = ⊥-elim h

-- A row of an earlier instant is before.
instant-≺ : ∀ k q → instant k ≺ⁱ instant q → k ≺ q
instant-≺ (a ∙ p) (b ∙ r) h = subst (λ x → T (isLt (lexi x (cmpPath p r)))) (sym (≺ⁱ→lt h)) tt
