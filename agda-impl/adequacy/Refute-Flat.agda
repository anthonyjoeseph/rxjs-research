{-# OPTIONS --guardedness #-}

-- Witness: a subscription at a position no tick heads, whose lane's
-- timer frame, rooted at a bare tick, sorts before the step that
-- admitted it.
module adequacy.Refute-Flat where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Tree using (Obs; Later; cold; of; flatMap)
import Tree as T
open import denotation.MonotonicList using (From; Timeline; Pos; at; done; last)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Placed using (Sorted; Alienᴱ; Ordered; ordered; Steady; steady)

open M.Frame∞

-- The outer's value at `[ last , ix 0 ]` shows a step just past it;
-- its lane, at `[ last , ix 0 , ix 1 ]`, has a frame at tick 1, rooted
-- at `[ ix 1 , sub … ]`, which `ix` puts before `last`.
lane : From ℕ 0
lane = at 1 z≤n (M.emit 1 λ where .force → M.close λ where .M.From∞.force → done)

ordered-refuted : (∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ
                    → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ)) → ⊥
ordered-refuted h with proj₁ (ordered (h (T.mergeᶠ nothing) (λ (_ : ℕ) → cold (lift lane)) (of (0 ∷ [])) (last ∷ []) []ᴬ tt tt))
... | ()

steady-refuted : (∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ → Steady (U.meaning (U.subscribe o p) ρ)) → ⊥
steady-refuted h with proj₁ (proj₁ (steady (h (flatMap (T.mergeᶠ nothing) (λ (_ : ℕ) → cold (lift lane)) (of (0 ∷ []))) (last ∷ []) []ᴬ (λ ()) tt tt)))
... | ()

-- A cold alone: its subscribe burst at `[ last , ix 0 ]`, its frame at
-- tick 1 rooted at `[ ix 1 , sub … ]`, behind it; and deferred.
twice : From ℕ 0
twice = at 0 z≤n (M.emit 0 λ where .force → M.close λ where .M.From∞.force → at 1 (s≤s z≤n) (M.emit 1 λ where .force → M.close λ where .M.From∞.force → done))

late : Later Timeline [] ℕ
late .Later.force = cold (lift twice)

start-refuted : (∀ {A} p (m : From A 0) → Ordered (M.start p m)) → ⊥
start-refuted h with proj₁ (ordered (proj₂ (ordered (h (last ∷ []) twice))))
... | ()

steady-start-refuted : (∀ {A} p (m : From A 0) → p ≢ [] → Steady (M.start p m)) → ⊥
steady-start-refuted h with proj₁ (proj₁ (steady (proj₂ (steady (h (last ∷ []) twice (λ ()))))))
... | ()

defer-refuted : (∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ → Ordered (U.meaning (U.deferᶜ l p []) ρ)) → ⊥
defer-refuted h with proj₁ (ordered (proj₂ (ordered (proj₂ (ordered (h late (last ∷ []) []ᴬ tt tt))))))
... | ()

steady-defer-refuted : (∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
                         → Steady (U.meaning (U.deferᶜ l p []) ρ)) → ⊥
steady-defer-refuted h with proj₁ (proj₁ (steady (proj₂ (steady (proj₂ (steady (h late (last ∷ []) []ᴬ (λ ()) tt tt)))))))
... | ()
