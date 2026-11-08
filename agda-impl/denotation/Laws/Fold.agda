{-# OPTIONS --guardedness #-}

-- A SCAN BOUNDS ITS SOURCE: a value with few rows before it has a fold,
-- from the latest value among those rows, or from none.  Which of them
-- holds a value is not decidable, but the bound is, so it is read
-- classically.
module denotation.Laws.Fold where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (¬¬-excluded-middle)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; _≺_; _≼_; Few)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (≼-refl; ≼-or-≻; ≼-trans; ≺→≼; few-ind)

module _ {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) where
  open ES.Scan f z t using (Acc; acc₀; acc)

  Val : Pos → Set
  Val k = Σ A λ a → t k (out a)

  -- The latest value before `w` among `ks`, or none there.
  Latest : Pos → List Pos → Set
  Latest w ks = (∀ {k} → k ∈ ks → Val k → k ≺ w → ⊥)
              ⊎ Σ Pos λ v → Val v × v ≺ w × (∀ {k} → k ∈ ks → Val k → k ≺ w → k ≼ v)

  latest : ∀ w ks → ¬ ¬ Latest w ks
  latest w []       ¬L = ¬L (inj₁ λ ())
  latest w (k ∷ ks) ¬L = latest w ks λ L → ¬¬-excluded-middle {A = Val k × k ≺ w} λ d → ¬L (add L d)
    where
      add : Latest w ks → Dec (Val k × k ≺ w) → Latest w (k ∷ ks)
      add (inj₁ none) (no ¬h) = inj₁ λ { {_} (here refl) vk kw → ¬h (vk , kw) ; {_} (there m) → none m }
      add (inj₂ (v , vv , vw , mx)) (no ¬h) =
        inj₂ (v , vv , vw , λ { {_} (here refl) vk kw → ⊥-elim (¬h (vk , kw)) ; {_} (there m) → mx m })
      add (inj₁ none) (yes (vk , kw)) =
        inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {_} (there m) vk′ k′w → ⊥-elim (none m vk′ k′w) })
      add (inj₂ (v , vv , vw , mx)) (yes (vk , kw)) with ≼-or-≻ v k
      ... | inj₁ vk≼ = inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {k′} (there m) vk′ k′w → ≼-trans {k′} {v} {k} (mx m vk′ k′w) vk≼ })
      ... | inj₂ kv  = inj₂ (v , vv , vw , λ { {_} (here refl) _ _ → ≺→≼ {k} {v} kv ; {_} (there m) → mx m })

  fold : ∀ {w} → Few t w → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)
  fold = few-ind (λ w → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)) step
    where
      step : ∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → ∀ {a} → t v (out a) → ¬ ¬ Σ B (Acc v))
           → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)
      step {w} (ks , h) ih {a} x ¬A = latest w ks λ
        { (inj₁ none) → ¬A (f z a , acc₀ x λ y kw → none (h y kw) (_ , y) kw)
        ; (inj₂ (v , (_ , xv) , vw , mx)) → ih xv vw xv λ
            { (b , av) → ¬A (f b a , acc av x vw λ y vk kw → mx (h y kw) (_ , y) kw vk) } }
