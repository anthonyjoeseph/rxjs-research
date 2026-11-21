{-# OPTIONS --guardedness #-}

-- A WORLD ROW UNDER A HOT ROW lies under one of that hot row's `sub`s,
-- naming a position at or past the world's subscription: a world reaches
-- inside a hot row only by joining it, or by joining a hot row already
-- under it so.
module denotation.Laws.HotBelow where

open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import denotation.Position using (Pos; Path; sub; _⊕_; _∙_; fired; _▸_)
open import denotation.EmissionSet using (_≼_)
open import denotation.Laws.Worlds using (W; W⁼; here; inW; step; timer; join; Real; _⊑_; ⊑-snoc; ⊕-assoc; real-init; real-last; world-after⁼)
open import denotation.Laws.Modulus using (≼-trans)

-- What leads a minted position is it.
lead-mint : ∀ {y t e l} → y ⊑ (fired t e ▸ l) → y ≡ fired t e ▸ l
lead-mint {_ ∙ []}      ([] , refl) = refl
lead-mint {_ ∙ []}      (_ ∷ _ , ())
lead-mint {_ ∙ (_ ∷ _)} (_ , ())

module _ {H : Pos → Set} {s q y : Pos} (qs : q ≼ s)
         (hy : ∀ {h} → H h → y ⊑ h → h ≡ y ⊎ Σ Pos λ e → Σ Path λ zs → h ≡ y ⊕ (sub e ∷ zs) × q ≼ e)
         (dj : ∀ {w} → W H s w → w ≡ y → ⊥) (sy : y ⊑ s → ⊥) where

  -- Under one of `y`'s `sub`s, naming a position at or past `q`.
  Under : Pos → Set
  Under z = Σ Pos λ e → Σ Path λ zs → z ≡ y ⊕ (sub e ∷ zs) × q ≼ e

  private
    snoc : ∀ {x} l → Under x → Under (x ⊕ [ l ])
    snoc l (e , zs , refl , qe) = e , zs ++ [ l ] , ⊕-assoc y (sub e ∷ zs) [ l ] , qe

  under-hot : ∀ {z} → W H s z → Real z → y ⊑ z → Under z
  under-hot (step {x} {l} w pl) r yz with ⊑-snoc x yz
  ... | inj₂ eq = ⊥-elim (dj (step w pl) (sym eq))
  under-hot (step here pl)          r yz | inj₁ yx = ⊥-elim (sy yx)
  under-hot (step {x} {l} (inW w) pl) r yz | inj₁ yx = snoc l (under-hot w (real-init x [ l ] r) yx)
  under-hot (timer t w lt pl) r yz = ⊥-elim (dj (timer t w lt pl) (sym (lead-mint yz)))
  under-hot (join {h} {e} hw w eh) r yz with ⊑-snoc h yz
  ... | inj₂ eq = ⊥-elim (dj (join hw w eh) (sym eq))
  under-hot (join {h} {e} (inj₂ wh) w eh) r yz | inj₁ yh = snoc (sub e) (under-hot wh (real-init h [ sub e ] r) yh)
  under-hot (join {h} {e} (inj₁ hh) w eh) r yz | inj₁ yh with hy hh yh
  ... | inj₂ u    = snoc (sub e) u
  ... | inj₁ refl = e , [] , refl , ≼-trans {q} {s} {e} qs (world-after⁼ w (real-last h r))
