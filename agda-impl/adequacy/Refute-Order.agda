{-# OPTIONS --guardedness #-}

-- Witnesses: a rejoin, and a flatMap's merge, of runs merely in order.
module adequacy.Refute-Order where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

import Tree as T
open import denotation.MonotonicList using (Events; Events∞; Pos; ix; skip; out; hush; root)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Placed using (Atop; Ordered; ordered)

open Events∞

-- A run in order stepping to an extension of its last position: rekeyed
-- under `sub p`, the extension's `ix` sorts before the `sub`.
rejoin-run : Events ⊤
rejoin-run = skip (ix 1 ∷ []) λ where .force → skip (ix 1 ∷ ix 0 ∷ []) λ where .force → hush

rejoin-ordered : Ordered rejoin-run
rejoin-ordered = record { ordered = refl , record { ordered = tt , record { ordered = tt } } }

rejoin-refuted : (∀ {A} p (e : Events A) → Ordered e → Ordered (M.rejoin p e)) → ⊥
rejoin-refuted h with ordered (h root rejoin-run rejoin-ordered)
... | () , _

-- An outer value and an outer skip at one position: the value shows as
-- a skip just past it, and the skip after.
src : NEnv (ℕ ∷ [])
src = hush ∷ᴬ []ᴬ

outerᶜ : U.Node (ℕ ∷ []) ℕ
outerᶜ = U.joinᶜ (here refl) root ((root , just 0) ∷ (root , nothing) ∷ []) nothing

laneᶜ : ℕ → Pos → U.Node (ℕ ∷ []) ℕ
laneᶜ a q = U.joinᶜ (here refl) q [] nothing

outer-ordered : Ordered (U.meaning outerᶜ src)
outer-ordered = record { ordered = refl , record { ordered = tt , record { ordered = tt } } }

flat-refuted : (∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (ρ : NEnv Γ) → Ordered (U.meaning o ρ)
               → (∀ a q → Ordered (U.meaning (g a q) ρ) × Atop q (U.meaning (g a q) ρ))
               → Ordered (U.meaning (U.flatMapᶜ op g (just o) [] []) ρ)) → ⊥
flat-refuted h with ordered (h (T.mergeᶠ nothing) laneᶜ outerᶜ src outer-ordered (λ a q → record { ordered = tt } , tt))
... | () , _
