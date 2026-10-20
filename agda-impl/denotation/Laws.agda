{-# OPTIONS --guardedness #-}

-- ALGEBRAIC LAWS OF THE PROGRAM TREE, proven on the denotation and carried
-- to the pure runtime by adequacy.  Each law is stated once on events,
-- lifted to `MonotonicList` at every subscription, then to programs
-- through `compositional`; the runtime form needs only `adequacy` on both
-- sides and the bridge from agreement to the runs it shows.
module denotation.Laws where

open import Data.Bool using (true; false)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import Tree using (Obs; map)
open import denotation.MonotonicList.Events using (Events; Events∞; Timeline; out; skip; end; hush; root)
open import denotation.MonotonicList using (MonotonicList; Agree; stop; out⁼; skip⁼; end⁼; hush⁼; agreeᵀ-refl; agree-sym; agrees; agree; _≈_; ≈ₖ-sym; ≈ₖ-trans; mapᴱ; mapᴰ; observe; enter; ticks; inFrame; within)
open import denotation.Order using (_≃_; Shows; ShowsIn; nil; at⁺; emit⁺; stall⁺; close⁺)
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

-- Events agreeing for every number of steps show the same runs: a reader
-- sees finitely many steps, so induction on what it saw.
private
  Alike : ∀ {A} → Events A → Events A → Set
  Alike x y = ∀ k → Agree k x y

  out-tail : ∀ {A k p a} {l r : Events∞ A} → Agree (suc k) (out p a l) (out p a r) → Agree k (force l) (force r)
  out-tail (out⁼ _ a) = a

  skip-tail : ∀ {A k p} {l r : Events∞ A} → Agree (suc k) (skip p l) (skip p r) → Agree k (force l) (force r)
  skip-tail (skip⁼ _ a) = a

  mutual
    shows : ∀ {A is} {x y : Events A} → Alike x y → Shows (ticks x) is → Shows (ticks y) is
    shows h d with h 1
    ... | out⁼ _ _  = shows-out h d
    ... | skip⁼ _ _ = shows-skip h d
    ... | end⁼      = d
    ... | hush⁼     = d

    shows-out : ∀ {A is p a} {l r : Events∞ A} → Alike (out p a l) (out p a r)
              → Shows (ticks (out p a l)) is → Shows (ticks (out p a r)) is
    shows-out h nil             = nil
    shows-out h (at⁺ nil)       = at⁺ nil
    shows-out h (at⁺ (emit⁺ d)) = at⁺ (emit⁺ (showsIn (λ k → out-tail (h (suc k))) d))

    shows-skip : ∀ {A is p} {l r : Events∞ A} → Alike (skip p l) (skip p r)
               → Shows (ticks (skip p l)) is → Shows (ticks (skip p r)) is
    shows-skip h nil              = nil
    shows-skip h (at⁺ nil)        = at⁺ nil
    shows-skip h (at⁺ (stall⁺ d)) = at⁺ (stall⁺ (showsIn (λ k → skip-tail (h (suc k))) d))

    showsIn : ∀ {A t is} {x y : Events A} → Alike x y → ShowsIn t (inFrame t x) is → ShowsIn t (inFrame t y) is
    showsIn h d with h 1
    ... | out⁼ _ _  = within-out h d
    ... | skip⁼ _ _ = within-skip h d
    ... | end⁼      = d
    ... | hush⁼     = d

    within-out : ∀ {A t is p a b} {l r : Events∞ A} → Alike (out p a l) (out p a r)
               → ShowsIn t (within t (out p a l) b) is → ShowsIn t (within t (out p a r) b) is
    within-out {b = true}  h nil        = nil
    within-out {b = true}  h (emit⁺ d)  = emit⁺ (showsIn (λ k → out-tail (h (suc k))) d)
    within-out {b = false} h nil        = nil
    within-out {b = false} h (close⁺ d) = close⁺ (shows h d)

    within-skip : ∀ {A t is p b} {l r : Events∞ A} → Alike (skip p l) (skip p r)
                → ShowsIn t (within t (skip p l) b) is → ShowsIn t (within t (skip p r) b) is
    within-skip {b = true}  h nil        = nil
    within-skip {b = true}  h (stall⁺ d) = stall⁺ (showsIn (λ k → skip-tail (h (suc k))) d)
    within-skip {b = false} h nil        = nil
    within-skip {b = false} h (close⁺ d) = close⁺ (shows h d)

agree-shows : ∀ {A} {x y : Events A} → (∀ k → Agree k x y) → ticks x ≃ ticks y
agree-shows h = shows h , shows λ k → agree-sym (h k)

map-fusionᴾ : ∀ {A B C} (f : B → C) (g : A → B) (s : PureObs [] A)
            → run (map (f ∘ g) s) ≃ run (map f (map g s))
map-fusionᴾ f g s =
  let (l₁ , r₁) = adequacy (map (f ∘ g) s)
      (l₂ , r₂) = adequacy (map f (map g s))
      (l , r)   = agree-shows {x = observe (⟦ map (f ∘ g) s ⟧ []) root} λ k → agree (map-fusion f g s [] k) root
  in (λ sh → r₂ (l (l₁ sh))) , (λ sh → r₁ (r (l₂ sh)))
