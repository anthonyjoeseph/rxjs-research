{-# OPTIONS --guardedness #-}

-- READING A TABLE: what a subscriber meets, one row at a time.  The next
-- row is the least past the last one met, and it is met only once it is
-- reached (`Seen`).  A skip is met but tells nothing; a reader who meets
-- no row past the last is told the run has gone silent.
module denotation.Table.Read where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; tick)
open import denotation.Order using (Item; val; fin; silent)
open import denotation.Table using (Ev; out; skip; end; Table; Work; _≺_; _≼_; Seen)

-- Past a cursor; with none, anywhere.
After : Maybe Pos → Pos → Set
After nothing  q = ⊤
After (just c) q = c ≺ q

-- Where a reader at `c` stands once it has met `rs`.
cursor : ∀ {A} → Maybe Pos → List (Pos × Ev A) → Maybe Pos
cursor c []             = c
cursor c ((q , _) ∷ rs) = cursor (just q) rs

-- What meeting `rs` tells a reader: its values, each at its tick, and
-- the completion.
items : ∀ {A} → List (Pos × Ev A) → List (Item A)
items []                 = []
items ((q , out a) ∷ rs) = val (tick q) a ∷ items rs
items ((q , skip) ∷ rs)  = items rs
items ((q , end) ∷ rs)   = fin ∷ []

module _ {A : Set} (t : Table A) where

  -- `q` is the first row past `c`.
  Least : Maybe Pos → Pos → Set
  Least c q = After c q × (∀ {k e} → t k e → After c k → q ≼ k)

  -- No row past `c`.
  Hush : Maybe Pos → Set
  Hush c = ∀ {k e} → t k e → ¬ After c k

  -- The rows a reader at `c` meets, in order.
  data Run : Maybe Pos → List (Pos × Ev A) → Set where
    []  : ∀ {c} → Run c []
    _∷_ : ∀ {c q e rs} → Seen t q e × Least c q → Run (just q) rs → Run c ((q , e) ∷ rs)

  -- A reader of the table is told `is`: what the rows it has met tell
  -- it, and silence once none follows an unended run.
  data Reads : List (Item A) → Set where
    met    : ∀ {rs} → Run nothing rs → Reads (items rs)
    hushed : ∀ {rs} → Run nothing rs → All (λ r → Work (proj₂ r)) rs → Hush (cursor nothing rs)
           → Reads (items rs ++ silent ∷ [])
