-- The anchor law:
--
--   batchSimultaneous (merge a a) ≡ map (λ x → [ x , x ]) a
--
-- proved against the specification batchSpec, for any observable whose
-- denotation is strictly monotone (one emission per instant — the shape of
-- every root source).
module Diamond where

open import Prelude
open import Time
open import TimedObs

dbl : {A : Set} → A → List A
dbl v = v ∷ v ∷ []

-- does x's time precede everything in xs? (trivially so for [])
headLtB : {A : Set} → Time × A → TimedObs A → Bool
headLtB _ []             = true
headLtB x ((t′ , _) ∷ _) = timeLt (fst x) t′

-- merging a stream with its own tail-cons duplicates the head:
-- mergeT xs (x ∷ xs) ≡ x ∷ mergeT xs xs, when x precedes all of xs
merge-dup-tail : {A : Set} (x : Time × A) (xs : TimedObs A)
               → headLtB x xs ≡ true
               → mergeT xs (x ∷ xs) ≡ x ∷ mergeT xs xs
merge-dup-tail x [] _ = refl
merge-dup-tail (t , v) ((t′ , v′) ∷ ys) hl
  rewrite timeLt⇒timeLeq-flip-false t t′ hl = refl

-- the self-merge of a stream duplicates its head twice over
merge-dup : {A : Set} (x : Time × A) (xs : TimedObs A)
          → headLtB x xs ≡ true
          → mergeT (x ∷ xs) (x ∷ xs) ≡ x ∷ x ∷ mergeT xs xs
merge-dup (t , v) xs hl
  rewrite timeLeq-refl t = cong (_∷_ (t , v)) (merge-dup-tail (t , v) xs hl)

-- THE DIAMOND: batching the self-merge of a strictly monotone stream
-- pairs every value with itself
diamond : {A : Set} (xs : TimedObs A) → StrictMono xs
        → batchSpec (mergeT xs xs) ≡ mapT dbl xs
diamond [] mono-[] = refl
diamond ((t , v) ∷ []) mono-one
  rewrite timeLeq-refl t | timeEq-refl t = refl
diamond ((t , v) ∷ (t′ , v′) ∷ xs) (mono-∷ lt m)
  rewrite merge-dup (t , v) ((t′ , v′) ∷ xs) lt
        | diamond ((t′ , v′) ∷ xs) m
        | timeLt⇒timeEq-false t t′ lt
        | timeEq-refl t
  = refl
