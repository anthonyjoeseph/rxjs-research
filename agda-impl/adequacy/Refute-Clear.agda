{-# OPTIONS --guardedness #-}

-- Witness: a lane a flatMap shows, over sources merely clear of where
-- it subscribes, with a source event inside it.
module adequacy.Refute-Clear where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; empty; flatMap; connected)
import Tree as T
open import denotation.MonotonicList using (Events; Events∞; Timeline; ix; sub; skip; out; hush)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Placed using (Sorted; Clearᴱ; Reaches; skip-here; ext; clear; ordered; steady)

open Events∞

-- A joiner at `[ ix 0 ]` keys A's value under `sub [ ix 0 ]`; B holds an
-- event inside the lane that value admits, and sits clear of `[ ix 0 ]`.
A B : Events ℕ
A = out (ix 1 ∷ []) 0 λ where .force → hush
B = skip (ix 1 ∷ sub (ix 0 ∷ []) ∷ ix 1 ∷ ix 0 ∷ []) λ where .force → hush

ρ : NEnv (ℕ ∷ ℕ ∷ [])
ρ = A ∷ᴬ B ∷ᴬ []ᴬ

sorted : Sorted ρ
sorted = ((record { ordered = tt , record { ordered = tt } } , record { steady = tt , record { steady = tt } })
         , (record { ordered = tt , record { ordered = tt } } , record { steady = tt , record { steady = tt } }) , tt)

clears : Clearᴱ (ix 0 ∷ []) ρ
clears = record { clear = (λ ()) , record { clear = tt } } , record { clear = (λ ()) , record { clear = tt } } , tt

prog : Obs Timeline (ℕ ∷ ℕ ∷ []) ℕ
prog = flatMap (T.mergeᶠ nothing) (λ _ → empty) (connected (here refl))

reaches : Reaches (ix 1 ∷ sub (ix 0 ∷ []) ∷ ix 0 ∷ []) (U.meaning (U.subscribe prog (ix 0 ∷ [])) ρ)
reaches = skip-here

clear-shown-refuted : (∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Clearᴱ p ρ
                       → ∀ x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.subscribe (flatMap op f s) p) ρ) → Clearᴱ (x ++ [ ix 1 ]) ρ) → ⊥
clear-shown-refuted h = proj₁ (clear (proj₁ (proj₂ c))) (ext (ix 0) [])
  where c = h (T.mergeᶠ nothing) (λ _ → empty) (connected (here refl)) (ix 0 ∷ []) ρ sorted clears (ix 1 ∷ sub (ix 0 ∷ []) ∷ []) reaches
