-- The denotational model: an observable is a time-ordered list of
-- emissions. merge is a stable sort-merge (on equal Times the left
-- argument wins — the model counterpart of rxjs subscription order).
-- batchSpec is the SPECIFICATION of batchSimultaneous: group consecutive
-- equal Times.
module TimedObs where

open import Prelude
open import Time

TimedObs : Set → Set
TimedObs A = List (Time × A)

mergeT : {A : Set} → TimedObs A → TimedObs A → TimedObs A
mergeT []       ys       = ys
mergeT (x ∷ xs) []       = x ∷ xs
mergeT (x ∷ xs) (y ∷ ys) =
  if timeLeq (fst x) (fst y)
  then (x ∷ mergeT xs (y ∷ ys))
  else (y ∷ mergeT (x ∷ xs) ys)

mapT : {A B : Set} → (A → B) → TimedObs A → TimedObs B
mapT f []             = []
mapT f ((t , v) ∷ xs) = (t , f v) ∷ mapT f xs

takeT : {A : Set} → ℕ → TimedObs A → TimedObs A
takeT zero    _        = []
takeT (suc n) []       = []
takeT (suc n) (x ∷ xs) = x ∷ takeT n xs

-- group consecutive equal Times (they are adjacent in a merged list);
-- written as a right fold so induction steps are structural
insertBatch : {A : Set} → Time → A → TimedObs (List A) → TimedObs (List A)
insertBatch t v [] = (t , v ∷ []) ∷ []
insertBatch t v ((t′ , vs) ∷ rest) =
  if timeEq t t′
  then ((t , v ∷ vs) ∷ rest)
  else ((t , v ∷ []) ∷ (t′ , vs) ∷ rest)

batchSpec : {A : Set} → TimedObs A → TimedObs (List A)
batchSpec []             = []
batchSpec ((t , v) ∷ xs) = insertBatch t v (batchSpec xs)

-- emissions of the second observable that happen strictly after a boundary
-- (concat subscribes its second argument only once the first has closed, so
-- for hot sources everything at or before that close is missed)
filterAfter : {A : Set} → Time → TimedObs A → TimedObs A
filterAfter c []             = []
filterAfter c ((t , v) ∷ xs) =
  if timeLt c t
  then ((t , v) ∷ filterAfter c xs)
  else filterAfter c xs

-- the close of take n: the time of the nth emission if it exists, the
-- source's own close if the source has fewer, and the beginning of time for
-- take 0 (which completes at subscription)
takeClose : {A : Set} → ℕ → TimedObs A → Time → Time
takeClose zero          _              _ = timeMin
takeClose (suc n)       []             c = c
takeClose (suc zero)    ((t , _) ∷ _)  _ = t
takeClose (suc (suc n)) (_ ∷ xs)       c = takeClose (suc n) xs c

-- non-decreasing times, tracked from a lower bound: the well-formedness of
-- every observable's emission list
data SortedFrom {A : Set} : Time → TimedObs A → Set where
  sf[] : {b : Time} → SortedFrom b []
  sf∷  : {b t : Time} {v : A} {xs : TimedObs A}
       → timeLeq b t ≡ true
       → SortedFrom t xs
       → SortedFrom b ((t , v) ∷ xs)

Sorted : {A : Set} → TimedObs A → Set
Sorted xs = SortedFrom timeMin xs

-- every emission happens at or before a boundary (an observable's close)
data BoundedBy {A : Set} (c : Time) : TimedObs A → Set where
  bb[] : BoundedBy c []
  bb∷  : {t : Time} {v : A} {xs : TimedObs A}
       → timeLeq t c ≡ true
       → BoundedBy c xs
       → BoundedBy c ((t , v) ∷ xs)

-- strictly increasing times: the shape of a root source's denotation
-- (one emission per instant)
data StrictMono {A : Set} : TimedObs A → Set where
  mono-[]  : StrictMono []
  mono-one : {x : Time × A} → StrictMono (x ∷ [])
  mono-∷   : {x y : Time × A} {xs : TimedObs A}
           → timeLt (fst x) (fst y) ≡ true
           → StrictMono (y ∷ xs)
           → StrictMono (x ∷ y ∷ xs)

mono-tail : {A : Set} {x : Time × A} {xs : TimedObs A}
          → StrictMono (x ∷ xs) → StrictMono xs
mono-tail mono-one     = mono-[]
mono-tail (mono-∷ _ m) = m
