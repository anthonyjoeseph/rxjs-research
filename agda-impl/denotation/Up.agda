-- ONE LABEL UP: a position with its last label dropped, so a row shown
-- one label down is found again.
module denotation.Up where

open import Data.List using (List; []; _∷_; [_]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import denotation.Position using (Pos; Label; _∙_; _⊕_)

private
  dropLast : List Label → List Label
  dropLast []           = []
  dropLast (_ ∷ [])     = []
  dropLast (y ∷ z ∷ zs) = y ∷ dropLast (z ∷ zs)

  dropLast-++ : ∀ ys l → dropLast (ys ++ [ l ]) ≡ ys
  dropLast-++ []           l = refl
  dropLast-++ (y ∷ [])     l = refl
  dropLast-++ (y ∷ z ∷ zs) l = cong (y ∷_) (dropLast-++ (z ∷ zs) l)

up : Pos → Pos
up (i ∙ ys) = i ∙ dropLast ys

up-⊕ : ∀ q l → up (q ⊕ [ l ]) ≡ q
up-⊕ (i ∙ ys) l = cong (i ∙_) (dropLast-++ ys l)
