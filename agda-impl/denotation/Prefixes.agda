-- A POSITION'S ANCESTORS: its instant's root, each step below it, and
-- itself; a position under another has it among them (`self-∈`).
module denotation.Prefixes where

open import Data.List using (List; []; _∷_; [_]; _++_) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.Position using (Pos; Path; _∙_; _⊕_)

-- Each non-empty prefix of a path, itself included.
prefixesᵗ : Path → List Path
prefixesᵗ []      = []
prefixesᵗ (l ∷ q) = [ l ] ∷ mapL (l ∷_) (prefixesᵗ q)

-- Each prefix of a position, its instant's root and itself included: a
-- timer's step is its instant's root.
prefixes : Pos → List Pos
prefixes (i ∙ q) = (i ∙ []) ∷ mapL (i ∙_) (prefixesᵗ q)

self-∈ᵗ : ∀ l q zs → (l ∷ q) ∈ prefixesᵗ ((l ∷ q) ++ zs)
self-∈ᵗ l []      zs = here refl
self-∈ᵗ l (m ∷ q) zs = there (∈-map⁺ (l ∷_) (self-∈ᵗ m q zs))

self-∈ : ∀ y zs → y ∈ prefixes (y ⊕ zs)
self-∈ (i ∙ [])      zs = here refl
self-∈ (i ∙ (l ∷ q)) zs = there (∈-map⁺ (i ∙_) (self-∈ᵗ l q zs))
