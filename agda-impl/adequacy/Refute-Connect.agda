{-# OPTIONS --guardedness #-}

-- Witness: a connect over a lane that is itself a connect, keyed by a
-- timer's frame outside the source's own subscription.  The lane shows
-- its source's step `k` as a skip at `k ++ [ ix 0 ]`, `k` left pinned;
-- the outer connect, its source past its subscription, re-shows that
-- skip at `k ++ [ ix 0 , ix 0 ]` with `k` still pinned in its cut.
module adequacy.Refute-Connect where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; z≤n)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; cold; of; flatMap; connect; connected; mergeᶠ)
open import denotation.MonotonicList using (Timeline; From; at; done; emit; close; root)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import adequacy.Placed using (Headed; Sorted; Alienᴱ; Trailing; trail; everyᵀ)

tick1 : From ℕ 0
tick1 = at 1 z≤n (emit 7 (λ where .M.Frame∞.force → close (λ where .M.From∞.force → done)))

lane : Obs Timeline [] ℕ
lane = connect (of (2 ∷ [])) (connected (here refl))

src : Obs Timeline [] ℕ
src = flatMap (mergeᶠ nothing) (λ _ → lane) (cold (lift tick1))

-- The third event: the re-shown skip, its step `k` still pinned.
connect-refuted : (∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : U.NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                   → Trailing (U.stateᴺ (U.subscribe (connect s b) p) ρ)) → ⊥
connect-refuted t with proj₁ (everyᵀ (proj₁ (proj₂ (trail (proj₂ (proj₂ (trail (proj₂ (proj₂ (trail (t src (connected (here refl)) root []ᴬ tt tt tt)))))))))))
... | inj₁ ()
... | inj₂ ()
