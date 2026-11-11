{-# OPTIONS --guardedness #-}

-- A RUN, SPLIT BY BRANCH.  A reading that merges branches, each read
-- through a join (`denotation.EmissionSet.Rejoin`), shows each branch row
-- one `sub` label below where the branch shows it.  `Proj` relates a run
-- of the reading to the rows of it one branch sent, where the branch shows
-- them: what a counter over that branch's rows is read against.
module simultaneous.Project where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos; sub; _⊕_)
open import denotation.EmissionSet using (Ev; out; end)
open import denotation.Read using (Run; []; _∷_)

-- The rows a run's branch sent: each row the tag reads as the branch's,
-- where the branch shows it; every other row dropped.
data Proj {X Y : Set} (tag : Ev X → Maybe (Ev Y)) : List (Pos × Ev X) → List (Pos × Ev Y) → Set where
  []   : Proj tag [] []
  keep : ∀ {q e y e′ w rx rs} → tag e ≡ just e′ → q ≡ y ⊕ [ sub w ] → Proj tag rx rs
       → Proj tag ((q , e) ∷ rx) ((y , e′) ∷ rs)
  drop : ∀ {q e rx rs} → tag e ≡ nothing → Proj tag rx rs → Proj tag ((q , e) ∷ rx) rs

-- A tag that reads only values never hands its branch an end.
proj-outs : ∀ {X Y} {tag : Ev X → Maybe (Ev Y)} → (∀ {e e′} → tag e ≡ just e′ → Σ Y λ x → e′ ≡ out x)
          → ∀ {rx rs} → Proj tag rx rs → ∀ {c} → (c , end) ∈ rs → ⊥
proj-outs vo (keep t _ _) (here refl) with vo t
... | _ , ()
proj-outs vo (keep _ _ pr) (there i) = proj-outs vo pr i
proj-outs vo (drop _ pr) i = proj-outs vo pr i

-- What a reader meets first, it met.
run-prefix : ∀ {A t c} (xs : List (Pos × Ev A)) {ys} → Run t c (xs ++ ys) → Run t c xs
run-prefix []       _        = []
run-prefix (_ ∷ xs) (r ∷ rn) = r ∷ run-prefix xs rn
