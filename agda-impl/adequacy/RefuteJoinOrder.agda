{-# OPTIONS --guardedness --large-indices #-}

-- `connectᴷ-well` refuted as stated.  A subject delivers a value to its
-- joiners in the order its cell lists them, each under `sub` of the
-- position it joined at.  `Well`'s read of a cell is well for EVERY
-- content, so a list naming a later joiner first is a counter-instance:
-- its delivery may leave the last under `sub` of the later position,
-- past where the earlier joiner's delivery then runs.
module adequacy.RefuteJoinOrder where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (ix; last; sub)
open import operation.AbstractObservable using (module Run; module Heap)
open import operation.PureObservable using (Pureᴾ; fin)
open import adequacy.Sorted using (module Sorting)
open Heap using (same; new; here; slot)

open Run (Pureᴾ ⊤) using (Observer; Subscribe; Subject; done; under; eff; connectᴷ)
open Sorting ⊤ using (WellObs; WellSub; doneʷ; newRefʷ; readRefʷ; underʷ; finʷ; sendʷ)

-- One value delivered, nothing returned.
one : ∀ {w} → Subscribe ⊤ w
one ρ o k = Observer.next o tt

one-well : ∀ {w} → WellSub (one {w})
one-well ρ o k p lo le wo wk = proj₁ wo tt p lo le

-- A body that does nothing.
idle : ∀ {w} → Subscribe ⊤ w
idle ρ o k = done tt

idle-well : ∀ {w} → WellSub (idle {w})
idle-well ρ o k p lo le wo wk = doneʷ

quiet : Observer ⊤ []
quiet = record { next = λ _ → done tt ; complete = eff fin (λ _ → done tt) ; closed = done false }

quiet-well : WellObs quiet
quiet-well = (λ a q lo le → doneʷ) , (λ q lo le → finʷ le) , (λ q lo → doneʷ)

refuted : (∀ {A B w} {s : Subscribe A w} {b : ∀ {v} → w Heap.⊑ v → Subject A v → Subscribe B v}
           → WellSub s → (∀ {v} σ st → WellSub {B} {v} (b σ st)) → WellSub (connectᴷ s b)) → ⊥
refuted cw with cw {⊤} {⊤} {[]} {one} {λ σ st → idle} one-well (λ σ st → idle-well) same quiet (λ _ _ → done tt) [] [] (inj₁ refl) quiet-well (λ _ _ _ _ _ → doneʷ)
... | newRefʷ f₁ with f₁ new here
... | newRefʷ f₂ with f₂ new here
... | newRefʷ f₃ with f₃ new here
... | newRefʷ f₄ with f₄ new here
... | newRefʷ f₅ with f₅ new here
... | underʷ _ c₀ with c₀ [] (inj₁ refl , inj₁ refl)
... | underʷ i _ with i
... | readRefʷ h with h (new {slot ⊤}) ((here , ix 0 ∷ []) ∷ (here , []) ∷ [])
... | underʷ _ c₁ with c₁ (ix 1 ∷ sub (ix 0 ∷ []) ∷ []) (inj₂ refl , inj₂ ([] , refl))
... | underʷ w _ with w
... | sendʷ (inj₁ ()) _
... | sendʷ (inj₂ ()) _
