-- The anchor laws: batching a self-merge groups simultaneous copies.
--
--   batchSpec (mergeT (mapT f xs) (mapT g xs)) ≡ mapT (λ v → f v ∷ g v ∷ []) xs
--   batchSpec (nMerge (suc n) xs)              ≡ mapT (replicate (suc n)) xs
--
-- both for any strictly monotone xs (one emission per instant — the shape
-- of every root source). The classic diamond (merge a a batches to pairs)
-- is the binary law at f = g = id.
module Diamond where

open import Prelude
open import Time
open import TimedObs

-- merging with [] on the right is the identity
mergeT-nil : {A : Set} (xs : TimedObs A) → mergeT xs [] ≡ xs
mergeT-nil []       = refl
mergeT-nil (x ∷ xs) = refl

mapT-id : {A : Set} (xs : TimedObs A) → mapT (λ v → v) xs ≡ xs
mapT-id []             = refl
mapT-id ((t , v) ∷ xs) = cong (_∷_ (t , v)) (mapT-id xs)

-- does x's time precede everything in xs? (trivially so for [])
headLtB : {A : Set} → Time × A → TimedObs A → Bool
headLtB _ []             = true
headLtB x ((t′ , _) ∷ _) = timeLt (fst x) t′

-- does t precede-or-equal the head of ys? (trivially so for [])
headLeqB : {A : Set} → Time → TimedObs A → Bool
headLeqB _ []             = true
headLeqB t ((t′ , _) ∷ _) = timeLeq t t′

-- an element strictly ahead of the left list surfaces from the right
merge-consR : {A : Set} (t : Time) (w : A) (xs ys : TimedObs A)
  → headLtB (t , w) xs ≡ true
  → mergeT xs ((t , w) ∷ ys) ≡ (t , w) ∷ mergeT xs ys
merge-consR t w []              ys _  = refl
merge-consR t w ((t′ , v) ∷ xs) ys hl
  rewrite timeLt⇒timeLeq-flip-false t t′ hl = refl

-- an element at-or-before the right list surfaces from the left
merge-consL : {A : Set} (t : Time) (w : A) (xs ys : TimedObs A)
  → headLeqB t ys ≡ true
  → mergeT ((t , w) ∷ xs) ys ≡ (t , w) ∷ mergeT xs ys
merge-consL t w xs []              _  = cong (_∷_ (t , w)) (sym (mergeT-nil xs))
merge-consL t w xs ((t′ , v) ∷ ys) hl rewrite hl = refl

-- a run of simultaneous elements passes through a merge as a block
merge-rep : {A : Set} (n : ℕ) (x : Time × A) (xs ys : TimedObs A)
  → headLtB x xs ≡ true
  → mergeT xs (replicate n x ++ ys) ≡ replicate n x ++ mergeT xs ys
merge-rep zero    x        xs ys _  = refl
merge-rep (suc n) (t , w) xs ys hl =
  trans (merge-consR t w xs (replicate n (t , w) ++ ys) hl)
        (cong (_∷_ (t , w)) (merge-rep n (t , w) xs ys hl))

merge-repL : {A : Set} (n : ℕ) (t : Time) (w : A) (rest ys : TimedObs A)
  → headLeqB t ys ≡ true
  → mergeT (replicate n (t , w) ++ rest) ys
    ≡ replicate n (t , w) ++ mergeT rest ys
merge-repL zero    t w rest ys _  = refl
merge-repL (suc n) t w rest ys hl =
  trans (merge-consL t w (replicate n (t , w) ++ rest) ys hl)
        (cong (_∷_ (t , w)) (merge-repL n t w rest ys hl))

-- one more simultaneous copy joins a run of n
merge-rep-self : {A : Set} (n : ℕ) (t : Time) (w : A)
  → mergeT (replicate n (t , w)) ((t , w) ∷ []) ≡ replicate (suc n) (t , w)
merge-rep-self zero    t w = refl
merge-rep-self (suc n) t w
  rewrite timeLeq-refl t = cong (_∷_ (t , w)) (merge-rep-self n t w)

-- n-fold self-merge (n live subscriptions of one hot stream)
nMerge : {A : Set} → ℕ → TimedObs A → TimedObs A
nMerge zero    xs = []
nMerge (suc n) xs = mergeT xs (nMerge n xs)

nMerge-nil : {A : Set} (n : ℕ) → nMerge {A} n [] ≡ []
nMerge-nil zero    = refl
nMerge-nil (suc n) = nMerge-nil n

headLeqB-rep : {A : Set} (n : ℕ) (t : Time) (w : A) (xs : TimedObs A)
  → headLeqB t (replicate n (t , w) ++ nMerge n xs) ≡ true
headLeqB-rep zero    t w xs = refl
headLeqB-rep (suc n) t w xs = timeLeq-refl t

-- the head of a self-merge duplicates n-fold up front
nMerge-cons : {A : Set} (n : ℕ) (x : Time × A) (xs : TimedObs A)
  → headLtB x xs ≡ true
  → nMerge n (x ∷ xs) ≡ replicate n x ++ nMerge n xs
nMerge-cons zero    x        xs _  = refl
nMerge-cons (suc n) (t , w) xs hl =
  trans (cong (mergeT ((t , w) ∷ xs)) (nMerge-cons n (t , w) xs hl))
  (trans (merge-consL t w xs (replicate n (t , w) ++ nMerge n xs)
           (headLeqB-rep n t w xs))
         (cong (_∷_ (t , w)) (merge-rep n (t , w) xs (nMerge n xs) hl)))

-- head-time disequality: the batch boundary
data HeadNe {A : Set} (t : Time) : TimedObs A → Set where
  hn[] : HeadNe t []
  hn∷  : {t′ : Time} {v : A} {xs : TimedObs A}
       → timeEq t t′ ≡ false → HeadNe t ((t′ , v) ∷ xs)

merge-headNe : {A : Set} (t : Time) (xs ys : TimedObs A)
  → HeadNe t xs → HeadNe t ys → HeadNe t (mergeT xs ys)
merge-headNe t []              ys              hn[]     hy       = hy
merge-headNe t (x ∷ xs)        []              hx       hn[]     = hx
merge-headNe t ((t₁ , v) ∷ xs) ((t₂ , w) ∷ ys) (hn∷ n₁) (hn∷ n₂)
  with timeLeq t₁ t₂
... | true  = hn∷ n₁
... | false = hn∷ n₂

nMerge-headNe : {A : Set} (n : ℕ) (t : Time) (xs : TimedObs A)
  → HeadNe t xs → HeadNe t (nMerge n xs)
nMerge-headNe zero    t xs hx = hn[]
nMerge-headNe (suc n) t xs hx =
  merge-headNe t xs (nMerge n xs) hx (nMerge-headNe n t xs hx)

insertBatch-headNe : {A : Set} (t t′ : Time) (w : A) (bs : TimedObs (List A))
  → timeEq t t′ ≡ false → HeadNe t (insertBatch t′ w bs)
insertBatch-headNe t t′ w []              ne = hn∷ ne
insertBatch-headNe t t′ w ((t″ , vs) ∷ bs) ne with timeEq t′ t″
... | true  = hn∷ ne
... | false = hn∷ ne

batchSpec-headNe : {A : Set} (t : Time) (xs : TimedObs A)
  → HeadNe t xs → HeadNe t (batchSpec xs)
batchSpec-headNe t []              hn[]     = hn[]
batchSpec-headNe t ((t′ , v) ∷ xs) (hn∷ ne) =
  insertBatch-headNe t t′ v (batchSpec xs) ne

-- inserting at a fresh time starts a fresh batch
insert-ne : {A : Set} (t : Time) (v : A) (bs : TimedObs (List A))
  → HeadNe t bs → insertBatch t v bs ≡ (t , v ∷ []) ∷ bs
insert-ne t v []              hn[]     = refl
insert-ne t v ((t′ , vs) ∷ bs) (hn∷ ne) rewrite ne = refl

-- a simultaneous run batches as ONE group in front of the rest
rep-batch : {A : Set} (n : ℕ) (t : Time) (v : A) (rest : TimedObs A)
  → HeadNe t rest
  → batchSpec (replicate (suc n) (t , v) ++ rest)
    ≡ (t , replicate (suc n) v) ∷ batchSpec rest
rep-batch zero    t v rest ne =
  insert-ne t v (batchSpec rest) (batchSpec-headNe t rest ne)
rep-batch (suc n) t v rest ne
  rewrite rep-batch n t v rest ne | timeEq-refl t = refl

-- strictly monotone streams batch to singletons
mono-batch : {A : Set} (xs : TimedObs A) → StrictMono xs
  → batchSpec xs ≡ mapT (λ v → v ∷ []) xs
mono-batch []                        mono-[]      = refl
mono-batch ((t , v) ∷ [])            mono-one     = refl
mono-batch ((t , v) ∷ (t′ , w) ∷ xs) (mono-∷ lt m)
  rewrite mono-batch ((t′ , w) ∷ xs) m | timeLt⇒timeEq-false t t′ lt = refl

mono-headLt : {A : Set} {x : Time × A} {xs : TimedObs A}
  → StrictMono (x ∷ xs) → headLtB x xs ≡ true
mono-headLt                            mono-one      = refl
mono-headLt {xs = (t′ , w) ∷ xs}       (mono-∷ lt _) = lt

mono-headNe : {A : Set} {t : Time} {v : A} {xs : TimedObs A}
  → StrictMono ((t , v) ∷ xs) → HeadNe t xs
mono-headNe                        mono-one      = hn[]
mono-headNe {t = t} {xs = (t′ , w) ∷ xs} (mono-∷ lt _) =
  hn∷ (timeLt⇒timeEq-false t t′ lt)

-- THE N-ARY DIAMOND: n live subscriptions of a strictly monotone stream
-- batch every value with multiplicity n
diamondN : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → batchSpec (nMerge (suc n) xs) ≡ mapT (λ v → replicate (suc n) v) xs
diamondN {A} n [] mono-[] rewrite nMerge-nil {A} n = refl
diamondN n ((t , v) ∷ xs) m =
  trans (cong batchSpec (nMerge-cons (suc n) (t , v) xs (mono-headLt m)))
  (trans (rep-batch n t v (nMerge (suc n) xs)
           (nMerge-headNe (suc n) t xs (mono-headNe m)))
         (cong (_∷_ (t , replicate (suc n) v)) (diamondN n xs (mono-tail m))))

-- THE BINARY DIAMOND, with distinct arms: batching the merge of two maps
-- of one strictly monotone stream pairs every value's two images
diamond2 : {A B : Set} (f g : A → B) (xs : TimedObs A) → StrictMono xs
  → batchSpec (mergeT (mapT f xs) (mapT g xs))
    ≡ mapT (λ v → f v ∷ g v ∷ []) xs
diamond2 f g [] mono-[] = refl
diamond2 f g ((t , v) ∷ []) mono-one
  rewrite timeLeq-refl t | timeEq-refl t = refl
diamond2 f g ((t , v) ∷ (t′ , v′) ∷ xs) (mono-∷ lt m)
  rewrite timeLeq-refl t
        | merge-consR t (g v) (mapT f ((t′ , v′) ∷ xs)) (mapT g ((t′ , v′) ∷ xs)) lt
        | diamond2 f g ((t′ , v′) ∷ xs) m
        | timeLt⇒timeEq-false t t′ lt
        | timeEq-refl t
  = refl

dbl : {A : Set} → A → List A
dbl v = v ∷ v ∷ []

-- THE DIAMOND: batching the self-merge of a strictly monotone stream
-- pairs every value with itself
diamond : {A : Set} (xs : TimedObs A) → StrictMono xs
        → batchSpec (mergeT xs xs) ≡ mapT dbl xs
diamond xs m =
  trans (cong (λ l → batchSpec (mergeT l l)) (sym (mapT-id xs)))
        (diamond2 (λ v → v) (λ v → v) xs m)
