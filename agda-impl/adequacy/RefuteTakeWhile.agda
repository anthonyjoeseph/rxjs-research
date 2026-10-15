{-# OPTIONS --guardedness --large-indices #-}

-- `takeWhileᴷ-well` and `connectᴷ-well` refuted.  A well observer's
-- callback may leave the last delivery anywhere in its scope.  An
-- inclusive `takeWhile` failing on its value calls `next`, then completes
-- under `last`, which may then fall before it.  A `connect` whose body
-- completes cuts its source by a `send` to an unsubscribe sink, which
-- `Well` places as a delivery, before what the completion delivered.
module adequacy.RefuteTakeWhile where

open import Data.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (ix; last)
open import operation.AbstractObservable using (module Run; module Heap)
open import operation.PureObservable using (Pureᴾ; fin)
open import adequacy.Sorted using (module Sorting)
open Heap using (same; new; here; slot)

open Run (Pureᴾ ⊤) using (Observer; Subscribe; Subject; done; under; eff; takeWhileᴷ; connectᴷ)
open Sorting ⊤ using (Well; WellObs; WellSub; doneʷ; newRefʷ; readRefʷ; writeRefʷ; underʷ; finʷ; sendʷ)

-- One value delivered, nothing returned.
one : ∀ {w} → Subscribe ⊤ w
one ρ o k = Observer.next o tt

one-well : ∀ {w} → WellSub (one {w})
one-well ρ o k p lo le wo wk = proj₁ wo tt p lo le

-- A `next` that opens a scope under `last` and delivers nothing there.
deep : Observer ⊤ []
deep = record { next = λ _ → under last (done tt) (done tt) ; complete = eff fin (λ _ → done tt) ; closed = done false }

deep-well : WellObs deep
deep-well = (λ a q lo le → underʷ doneʷ (λ _ _ → doneʷ)) , (λ q lo le → finʷ le) , (λ q lo → doneʷ)

refuted : (∀ {A w} i p {s : Subscribe A w} → WellSub s → WellSub (takeWhileᴷ i p s)) → ⊥
refuted tw with tw {⊤} {[]} true (λ _ → false) one-well same deep (λ _ _ → done tt) [] [] (inj₁ refl) deep-well (λ _ _ _ _ → doneʷ)
... | newRefʷ f with f new here
...   | newRefʷ g with g new here
...     | readRefʷ h with h same true
...       | underʷ _ c with c (last ∷ ix 0 ∷ []) (inj₂ refl , inj₂ (ix 0 ∷ [] , refl))
...         | underʷ i _ with i
...           | finʷ (inj₁ ())
...           | finʷ (inj₂ ())

-- A body that completes at once; a source that does nothing.
ends : ∀ {w} → Subscribe ⊤ w
ends ρ o k = Observer.complete o

ends-well : ∀ {w} → WellSub (ends {w})
ends-well ρ o k p lo le wo wk = proj₁ (proj₂ wo) p lo le

idle : ∀ {w} → Subscribe ⊤ w
idle ρ o k = done tt

idle-well : ∀ {w} → WellSub (idle {w})
idle-well ρ o k p lo le wo wk = doneʷ

-- A `complete` that opens a scope under `last` and delivers nothing there.
deeper : Observer ⊤ []
deeper = record { next = λ _ → done tt ; complete = under last (done tt) (done tt) ; closed = done false }

deeper-well : WellObs deeper
deeper-well = (λ a q lo le → doneʷ) , (λ q lo le → underʷ doneʷ (λ _ _ → doneʷ)) , (λ q lo → doneʷ)

connect-refuted : (∀ {A B w} {s : Subscribe A w} {b : ∀ {v} → w Heap.⊑ v → Subject A v → Subscribe B v}
                   → WellSub s → (∀ {v} σ st → WellSub {B} {v} (b σ st)) → WellSub (connectᴷ s b)) → ⊥
connect-refuted cw with cw {⊤} {⊤} {[]} {idle} {λ σ st → ends} idle-well (λ σ st → ends-well) same deeper (λ _ _ → done tt) [] [] (inj₁ refl) deeper-well (λ _ _ _ _ → doneʷ)
... | newRefʷ f₁ with f₁ new here
... | newRefʷ f₂ with f₂ new here
... | newRefʷ f₃ with f₃ new here
... | newRefʷ f₄ with f₄ new here
... | newRefʷ f₅ with f₅ new here
... | underʷ i _ with i
... | underʷ _ c with c (ix 0 ∷ last ∷ []) (inj₂ refl , inj₂ ([] , refl))
... | writeRefʷ w with w
... | readRefʷ h with h (new {slot ⊤}) (just here)
... | sendʷ (inj₁ ()) _
... | sendʷ (inj₂ ()) _
