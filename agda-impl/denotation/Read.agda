{-# OPTIONS --guardedness #-}

-- READING AN EMISSION SET: what a subscriber meets, one row at a time.  The next
-- row is the least past the last one met, and it is met only once it is
-- reached (`Seen`).
module denotation.Read where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; _≺_; _≼_; Seen)

-- Past a cursor; with none, anywhere.
After : Maybe Pos → Pos → Set
After nothing  q = ⊤
After (just c) q = c ≺ q

-- What a subscriber is shown of the rows met: values and the end.
shown : ∀ {A} → List (Pos × Ev A) → List (Pos × Ev A)
shown []                 = []
shown ((q , out a) ∷ rs) = (q , out a) ∷ shown rs
shown ((q , skip)  ∷ rs) = shown rs
shown ((q , pin _) ∷ rs) = shown rs
shown ((q , end)   ∷ rs) = (q , end) ∷ shown rs

-- Where a reader at `c` stands once it has met `rs`.
cursor : ∀ {A} → Maybe Pos → List (Pos × Ev A) → Maybe Pos
cursor c []             = c
cursor c ((q , _) ∷ rs) = cursor (just q) rs

module _ {A : Set} (t : EmissionSet A) where

  -- `q` is the first row past `c`.
  Least : Maybe Pos → Pos → Set
  Least c q = After c q × (∀ {k e} → t k e → After c k → q ≼ k)

  -- The rows a reader at `c` meets, in order.
  data Run : Maybe Pos → List (Pos × Ev A) → Set where
    []  : ∀ {c} → Run c []
    _∷_ : ∀ {c q e rs} → Seen t q e × Least c q → Run (just q) rs → Run c ((q , e) ∷ rs)

-- What a subscriber at the root is shown first: the shown rows of some
-- reader's run.
Meets : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Set
Meets t vs = Σ _ λ rs → Run t nothing rs × shown rs ≡ vs
