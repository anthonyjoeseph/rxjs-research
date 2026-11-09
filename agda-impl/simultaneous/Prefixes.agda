-- PREFIXES UNDER EQUALITY, and a list with its last item held back as a
-- prefix of the whole.
module simultaneous.Prefixes where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import simultaneous.Readings using (closed)

------------------------------------------------------------------------
-- Prefixes under equality

prefix-refl : ∀ {X : Set} (xs : List X) → Prefix _≡_ xs xs
prefix-refl []       = []
prefix-refl (x ∷ xs) = refl ∷ prefix-refl xs

prefix-≡ : ∀ {X : Set} {xs ys : List X} → xs ≡ ys → Prefix _≡_ xs ys
prefix-≡ {xs = xs} refl = prefix-refl xs

prefix-trans : ∀ {X : Set} {xs ys zs : List X} → Prefix _≡_ xs ys → Prefix _≡_ ys zs → Prefix _≡_ xs zs
prefix-trans []         _          = []
prefix-trans (refl ∷ p) (refl ∷ q) = refl ∷ prefix-trans p q

prefix-++ : ∀ {X : Set} (zs : List X) {xs ys : List X} → Prefix _≡_ xs ys → Prefix _≡_ (zs ++ xs) (zs ++ ys)
prefix-++ []       p = p
prefix-++ (z ∷ zs) p = refl ∷ prefix-++ zs p

-- Holding the last group back keeps a prefix.
closed-prefix : ∀ {X : Set} ov (xs : List X) → Prefix _≡_ (closed ov xs) xs
closed-prefix true  xs           = prefix-refl xs
closed-prefix false []           = []
closed-prefix false (x ∷ [])     = []
closed-prefix false (x ∷ y ∷ xs) = refl ∷ closed-prefix false (y ∷ xs)
