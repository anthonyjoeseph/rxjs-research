{-# OPTIONS --guardedness #-}

-- ALGEBRAIC LAWS OF THE PROGRAM TREE, proven on the denotation and carried
-- to the pure runtime by adequacy.  Each law is stated once on events,
-- lifted to `MonotonicList` at every subscription, then to programs
-- through `compositional`; the runtime form needs only `adequacy` on both
-- sides and the bridge from agreement to the runs it shows.
module denotation.Laws where

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import Tree using (Obs; map)
open import denotation.MonotonicList.Events using (Events; Events∞; Timeline; out; skip; end; hush; root)
open import denotation.MonotonicList using (MonotonicList; Agree; stop; out⁼; skip⁼; end⁼; hush⁼; agreeᵀ-refl; agrees; agree; _≈_; ≈ₖ-sym; ≈ₖ-trans; mapᴱ; mapᴰ; observe; enter; ticks)
open import denotation.Order using (_≃_)
open import denotation.Denote using (DenEnv; ⟦_⟧)
open import denotation.Compositional using (compositional; module Compositional)
open import denotation.NonExpansive using (mapᴰ-ne)
open import operation.PureObservable using (PureObs)
open import adequacy.Adequacy using (run; adequacy)
open Events∞

------------------------------------------------------------------------
-- MAP FUSION

mapᴱ-∘ : ∀ {A B C} (f : B → C) (g : A → B) k (e : Events A)
       → Agree k (mapᴱ (f ∘ g) e) (mapᴱ f (mapᴱ g e))
mapᴱ-∘ f g zero    e           = stop
mapᴱ-∘ f g (suc k) (out p a r) = out⁼ (agreeᵀ-refl k (cut r)) (mapᴱ-∘ f g k (force r))
mapᴱ-∘ f g (suc k) (skip p r)  = skip⁼ (agreeᵀ-refl k (cut r)) (mapᴱ-∘ f g k (force r))
mapᴱ-∘ f g (suc k) (end p)     = end⁼
mapᴱ-∘ f g (suc k) hush        = hush⁼

mapᴰ-∘ : ∀ {A B C} (f : B → C) (g : A → B) (m : MonotonicList A)
       → mapᴰ (f ∘ g) m ≈ mapᴰ f (mapᴰ g m)
mapᴰ-∘ f g m k = agrees (λ p → agreeᵀ-refl k (cut (enter m p))) λ p → mapᴱ-∘ f g k (observe m p)

map-fusion : ∀ {Γ A B C} (f : B → C) (g : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
           → ⟦ map (f ∘ g) s ⟧ ρ ≈ ⟦ map f (map g s) ⟧ ρ
map-fusion f g s ρ k =
  ≈ₖ-trans (mapᶜ (f ∘ g) s ρ k)
    (≈ₖ-trans (mapᴰ-∘ f g (⟦ s ⟧ ρ) k)
      (≈ₖ-sym (≈ₖ-trans (mapᶜ f (map g s) ρ k) (mapᴰ-ne f (mapᶜ g s ρ k)))))
  where open Compositional compositional

------------------------------------------------------------------------
-- TO THE RUNTIME

-- Events agreeing for every number of steps show the same runs.
postulate
  agree-shows : ∀ {A} {x y : Events A} → (∀ k → Agree k x y) → ticks x ≃ ticks y

map-fusionᴾ : ∀ {A B C} (f : B → C) (g : A → B) (s : PureObs [] A)
            → run (map (f ∘ g) s) ≃ run (map f (map g s))
map-fusionᴾ f g s =
  let (l₁ , r₁) = adequacy (map (f ∘ g) s)
      (l₂ , r₂) = adequacy (map f (map g s))
      (l , r)   = agree-shows {x = observe (⟦ map (f ∘ g) s ⟧ []) root} λ k → agree (map-fusion f g s [] k) root
  in (λ sh → r₂ (l (l₁ sh))) , (λ sh → r₁ (r (l₂ sh)))
