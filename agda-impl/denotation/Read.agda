{-# OPTIONS --guardedness #-}

-- READING AN EMISSION SET: what a subscriber meets, one row at a time.  It is
-- told only values and the end; the next is the least of those past the last
-- one met, and it is met only once it is reached (`Seen`).  Skips and pins
-- are never met: they only decide which rows are reached.
module denotation.Read where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; _≺_; _≼_; Seen; Silent; hush; held)

-- Past a cursor; with none, anywhere.
After : Maybe Pos → Pos → Set
After nothing  q = ⊤
After (just c) q = c ≺ q

-- A row a subscriber is told of: a value or the end.
Visible : ∀ {A} → Ev A → Set
Visible (out _) = ⊤
Visible skip    = ⊥
Visible (pin _) = ⊥
Visible end     = ⊤

-- A row told of is not silent.
loud : ∀ {A} {e : Ev A} → Visible e → Silent e → ⊥
loud () hush
loud () held

-- Where a reader at `c` stands once it has met `rs`.
cursor : ∀ {A} → Maybe Pos → List (Pos × Ev A) → Maybe Pos
cursor c []             = c
cursor c ((q , _) ∷ rs) = cursor (just q) rs

module _ {A : Set} (t : EmissionSet A) where

  -- `q` is the first visible row past `c`.
  Least : Maybe Pos → Pos → Set
  Least c q = After c q × (∀ {k e} → t k e → Visible e → After c k → q ≼ k)

  -- The rows a reader at `c` meets, in order.
  data Run : Maybe Pos → List (Pos × Ev A) → Set where
    []  : ∀ {c} → Run c []
    _∷_ : ∀ {c q e rs} → Seen t q e × Visible e × Least c q → Run (just q) rs → Run c ((q , e) ∷ rs)

-- What a subscriber at the root is shown first.
Meets : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Set
Meets t vs = Run t nothing vs
