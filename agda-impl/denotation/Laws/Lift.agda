{-# OPTIONS --guardedness #-}

-- A LEVEL THAT SHOWS ITS HANGS PASSES A ROW UP where the reading of it has
-- few rows: the rows before it that reach few rows are the reading's own,
-- so few, and then every row before it is few.  Read top-down, a level
-- has few rows wherever the level reading it does, each of its rows met
-- at most one step down above it.
module denotation.Laws.Lift where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
import Data.List as L
open import Data.List using (_∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (<ᵖ-step)
open import denotation.EmissionSet using (Ev; EmissionSet; Few; Truncate; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-≼-≺; ≺→≼; ≼-split)
open import denotation.Laws.Worlds using (Shows)
open import denotation.Laws.Shows using (∈-stable; few-reach; Step)
open import denotation.Up using (up; up-⊕)

-- A row of a level that shows its hangs, at or before where its reading
-- has few rows: the reading's.
few-lift : ∀ {A} {U : EmissionSet A} {v k e} → Shows U → Few (Truncate U) v → U k e → k ≼ v → ¬ ¬ Truncate U k e
few-lift {U = U} {v} {k} sh (ks , h) u kv ¬t =
  sh {v = k} (ks , λ {k′} x f lt → h (x , few-reach f) (≺-≼-≺ {k′} {k} {v} lt kv)) λ f → ¬t (u , few-reach f)

-- A row one step down from one before `v` is no later than `v`.
step-≼ : ∀ {k z v} → Step k z → k ≺ v → z ≼ v
step-≼ {k} {v = v} (inj₁ refl) kv    = ≺→≼ {k} {v} kv
step-≼ {k} {v = v} (inj₂ refl) kv h′ = subst T (<ᵖ-step k v (Equivalence.to T-≡ kv)) h′

-- Below a level that shows its hangs: as few rows as its reading has,
-- each met at most one step down.
few-below : ∀ {A B} {U : EmissionSet A} {X : EmissionSet B} {v} → Shows U → Few (Truncate U) v
          → (∀ {k e} → X k e → k ≺ v → ¬ ¬ Σ Pos λ z → Σ (Ev A) (U z) × Step k z) → Few X v
few-below {U = U} {X} {v} sh fv@(ks , h) st = v ∷ up v ∷ ks ++ L.map up ks , pick
  where
    pick : ∀ {k e} → X k e → k ≺ v → k ∈ v ∷ up v ∷ ks ++ L.map up ks
    pick {k} x kv = ∈-stable λ ¬i → st x kv λ { (z , (_ , u) , s) → few-lift sh fv u (step-≼ s kv) λ t → ¬i (place s (≼-split {z} {v} (step-≼ s kv)) t) }
      where
        place : ∀ {z e′} → Step k z → z ≺ v ⊎ z ≡ v → Truncate U z e′ → k ∈ v ∷ up v ∷ ks ++ L.map up ks
        place (inj₁ refl) (inj₁ lt) t = there (there (∈-++⁺ˡ (h t lt)))
        place (inj₂ refl) (inj₁ lt) t = there (there (∈-++⁺ʳ ks (subst (_∈ L.map up ks) (up-⊕ k (ix 0)) (∈-map⁺ up (h t lt)))))
        place (inj₁ refl) (inj₂ eq) _ = here eq
        place (inj₂ refl) (inj₂ eq) _ = there (here (trans (sym (up-⊕ k (ix 0))) (cong up eq)))
