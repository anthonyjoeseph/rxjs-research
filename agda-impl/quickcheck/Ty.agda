{-# OPTIONS --guardedness #-}

-- THE TYPES A GENERATED PROGRAM MAY USE.  First-order and finite, so every
-- value can be compared and printed — what testing needs, and what an
-- arbitrary Agda `Set` does not give.  Nothing below `quickcheck/` sees
-- this: the tree takes any `Set`.
module quickcheck.Ty where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_; intersperse)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; _≟ᵖ_)

infixr 5 _×ᵗ_ _+ᵗ_

data Ty : Set where
  unitᵗ boolᵗ natᵗ : Ty
  _×ᵗ_ _+ᵗ_        : Ty → Ty → Ty
  listᵗ            : Ty → Ty
  -- a `fresh` name: compared, carried, never computed with
  nameᵗ            : Ty

⟦_⟧ᵀ : Ty → Set
⟦ unitᵗ ⟧ᵀ   = ⊤
⟦ boolᵗ ⟧ᵀ   = Bool
⟦ natᵗ ⟧ᵀ    = ℕ
⟦ s ×ᵗ t ⟧ᵀ  = ⟦ s ⟧ᵀ × ⟦ t ⟧ᵀ
⟦ s +ᵗ t ⟧ᵀ  = ⟦ s ⟧ᵀ ⊎ ⟦ t ⟧ᵀ
⟦ listᵗ t ⟧ᵀ = List ⟦ t ⟧ᵀ
⟦ nameᵗ ⟧ᵀ    = Pos

eqᵀ : ∀ t → ⟦ t ⟧ᵀ → ⟦ t ⟧ᵀ → Bool
eqᵀ unitᵗ     _        _        = true
eqᵀ boolᵗ     true     true     = true
eqᵀ boolᵗ     false    false    = true
eqᵀ boolᵗ     _        _        = false
eqᵀ natᵗ      m        n        = m ≡ᵇ n
eqᵀ (s ×ᵗ t)  (a , b)  (c , d)  = eqᵀ s a c ∧ eqᵀ t b d
eqᵀ (s +ᵗ t)  (inj₁ a) (inj₁ c) = eqᵀ s a c
eqᵀ (s +ᵗ t)  (inj₂ b) (inj₂ d) = eqᵀ t b d
eqᵀ (s +ᵗ t)  _        _        = false
eqᵀ (listᵗ t) []       []       = true
eqᵀ (listᵗ t) (a ∷ as) (b ∷ bs) = eqᵀ t a b ∧ eqᵀ (listᵗ t) as bs
eqᵀ (listᵗ t) _        _        = false
eqᵀ nameᵗ     p        q        = does (p ≟ᵖ q)

-- JSON, the oracle's wire format.
showᵀ : ∀ t → ⟦ t ⟧ᵀ → String
showᵀ unitᵗ     _        = "null"
showᵀ boolᵗ     true     = "true"
showᵀ boolᵗ     false    = "false"
showᵀ natᵗ      n        = showℕ n
showᵀ (s ×ᵗ t)  (a , b)  = "[" ++ showᵀ s a ++ "," ++ showᵀ t b ++ "]"
showᵀ (s +ᵗ t)  (inj₁ a) = "{\"l\":" ++ showᵀ s a ++ "}"
showᵀ (s +ᵗ t)  (inj₂ b) = "{\"r\":" ++ showᵀ t b ++ "}"
showᵀ (listᵗ t) xs       = "[" ++ intersperse "," (go xs) ++ "]"
  where
    go : List ⟦ t ⟧ᵀ → List String
    go []       = []
    go (x ∷ xs) = showᵀ t x ∷ go xs
showᵀ nameᵗ     p        = "{\"name\":\"" ++ showPos p ++ "\"}"
  where
    -- no digit follows a separator, so the oracle's number-quoting never
    -- reaches inside a name
    mutual
      showPos : Pos → String
      showPos []       = ""
      showPos (l ∷ ls) = showLabel l ++ "." ++ showPos ls

      showLabel : Label → String
      showLabel (ix n)  = "i" ++ showℕ n
      showLabel (sub q) = "s(" ++ showPos q ++ ")"
      showLabel last    = "L"
