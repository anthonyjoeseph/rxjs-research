-- WHEN A PENDING CONTINUATION RUNS: at the position of the event it
-- makes, or, for one that makes none, `after` a position — later than
-- everything under it, earlier than whatever follows it.  Keys compare as
-- positions do, a key `after p` reading as `p` with a label past every
-- other appended.
module operation.Key where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; [_])
open import Relation.Nullary using (does)

open import denotation.MonotonicList.Events using (Pos; Label; _<ᵖ_; _≟ˡ_)

data Key : Set where
  at    : Pos → Key
  after : Pos → Key

private
  data XL : Set where
    lab : Label → XL
    top : XL

  -- A label strictly before another.
  _≺_ : XL → XL → Bool
  lab a ≺ lab b = [ a ] <ᵖ [ b ]
  lab _ ≺ top   = true
  top   ≺ _     = false

  _≐_ : XL → XL → Bool
  lab a ≐ lab b = does (a ≟ˡ b)
  top   ≐ top   = true
  _     ≐ _     = false

  lex : List XL → List XL → Bool
  lex []      []      = false
  lex []      (_ ∷ _) = true
  lex (_ ∷ _) []      = false
  lex (a ∷ p) (b ∷ q) = (a ≺ b) ∨ ((a ≐ b) ∧ lex p q)

  labs : Pos → List XL
  labs []      = []
  labs (a ∷ p) = lab a ∷ labs p

  ext : Key → List XL
  ext (at p)    = labs p
  ext (after p) = labs p Data.List.++ [ top ]

-- Strictly earlier.
_<ᴷ_ : Key → Key → Bool
k <ᴷ k′ = lex (ext k) (ext k′)
