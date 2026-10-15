{-# OPTIONS --guardedness #-}

-- Witness: a subscription at the empty position, whose steps sit at
-- bare ticks, stepping just inside one of them.
module adequacy.Refute-Steady where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; z≤n)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Level using (lift)

open import Tree using (Obs; cold; flatMap)
import Tree as T
open import denotation.MonotonicList using (From; Timeline; ix; sub; last; at; done)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Placed using (Sorted; Alienᴱ; Steady; steady; ext)

open M.Frame∞

-- The outer's subscribe burst steps at `[ ix 0 ]` and `[ ix 1 ]`; the
-- lane its value admits, at `[ ix 0 , ix 1 ]`, sets a timer for tick 1,
-- whose frame shows under `[ ix 1 ]`, after that step.
outer lane : From ℕ 0
outer = at 0 z≤n (M.emit 0 λ where .force → M.stall λ where .force → M.close λ where .M.From∞.force → done)
lane  = at 1 z≤n (M.emit 1 λ where .force → M.close λ where .M.From∞.force → done)

prog : Obs Timeline [] ℕ
prog = flatMap (T.mergeᶠ nothing) (λ _ → cold (lift lane)) (cold (lift outer))

steady-refuted : (∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ → Steady (U.meaning (U.subscribe o p) ρ)) → ⊥
steady-refuted h = proj₁ (steady (proj₂ (steady (h prog [] []ᴬ tt tt)))) (ext (sub (ix 0 ∷ ix 1 ∷ last ∷ [])) (ix 0 ∷ []))
