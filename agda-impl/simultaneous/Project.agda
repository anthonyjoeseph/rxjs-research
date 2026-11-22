{-# OPTIONS --guardedness #-}

-- WHAT A READER MEETS FIRST, IT MET: a run's prefix is a run.
module simultaneous.Project where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_)

open import denotation.Position using (Pos)
open import denotation.EmissionSet using (Ev)
open import denotation.Read using (Run; []; _∷_)

-- What a reader meets first, it met.
run-prefix : ∀ {A t c} (xs : List (Pos × Ev A)) {ys} → Run t c (xs ++ ys) → Run t c xs
run-prefix []       _        = []
run-prefix (_ ∷ xs) (r ∷ rn) = r ∷ run-prefix xs rn
