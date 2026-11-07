-- BATCHES, FLATTENED BACK: joining the spec's grouping gives back the
-- values it grouped, and a prefix of a grouping joins to a prefix of
-- them.  What `left-to-right` needs to pass from batches to values.
open import Relation.Binary.Definitions using (DecidableEquality)

module simultaneous.Flatten {N : Set} (_≟_ : DecidableEquality N) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; concat; map)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

open import simultaneous.Readings using (closed)
import simultaneous.Spec as Spec
open Spec _≟_ using (batchFrom; batchSimultaneousᴰ)

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

prefix-map : ∀ {X Y : Set} (f : X → Y) {xs ys : List X} → Prefix _≡_ xs ys → Prefix _≡_ (map f xs) (map f ys)
prefix-map f []         = []
prefix-map f (refl ∷ p) = refl ∷ prefix-map f p

prefix-++ : ∀ {X : Set} (zs : List X) {xs ys : List X} → Prefix _≡_ xs ys → Prefix _≡_ (zs ++ xs) (zs ++ ys)
prefix-++ []       p = p
prefix-++ (z ∷ zs) p = refl ∷ prefix-++ zs p

prefix-concat : ∀ {X : Set} {xss yss : List (List X)} → Prefix _≡_ xss yss → Prefix _≡_ (concat xss) (concat yss)
prefix-concat []                 = []
prefix-concat {xss = xs ∷ _} (refl ∷ p) = prefix-++ xs (prefix-concat p)

------------------------------------------------------------------------
-- The grouping, joined

private
  joinFrom : ∀ {A : Set} (i : N) (vs : List A) (ys : List (N × A)) →
             concat (map proj₂ (batchFrom i vs ys)) ≡ vs ++ map proj₂ ys
  joinFrom i vs []             = refl
  joinFrom i vs ((j , v) ∷ ys) with i ≟ j
  ... | yes _ rewrite joinFrom i (vs ∷ʳ v) ys = ++-assoc vs (v ∷ []) (map proj₂ ys)
  ... | no  _ = cong (vs ++_) (joinFrom j (v ∷ []) ys)

-- Joining the grouping gives back what was grouped.
joined-batches : ∀ {A : Set} (ys : List (N × A)) → concat (map proj₂ (batchSimultaneousᴰ ys)) ≡ map proj₂ ys
joined-batches []             = refl
joined-batches ((i , v) ∷ ys) = joinFrom i (v ∷ []) ys

-- Holding the last group back keeps a prefix.
closed-prefix : ∀ {X : Set} ov (xs : List X) → Prefix _≡_ (closed ov xs) xs
closed-prefix true  xs           = prefix-refl xs
closed-prefix false []           = []
closed-prefix false (x ∷ [])     = []
closed-prefix false (x ∷ y ∷ xs) = refl ∷ closed-prefix false (y ∷ xs)

-- A grouping, its last group perhaps held back, joins to a prefix of what
-- was grouped.
joined-closed : ∀ {A : Set} ov (ys : List (N × A)) →
                Prefix _≡_ (concat (map proj₂ (closed ov (batchSimultaneousᴰ ys)))) (map proj₂ ys)
joined-closed ov ys =
  prefix-trans (prefix-concat (prefix-map proj₂ (closed-prefix ov (batchSimultaneousᴰ ys))))
               (prefix-≡ (joined-batches ys))
