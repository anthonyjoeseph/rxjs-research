-- Monotonicity preservation: every combinator preserves sortedness and
-- boundedness. "These are really just various approaches to preserving
-- monotonicity" — this module is that sentence, machine-checked.
module Sorting where

open import Prelude
open import Time
open import TimedObs

sortedFrom-weaken : {A : Set} {b b′ : Time} {xs : TimedObs A}
  → timeLeq b′ b ≡ true → SortedFrom b xs → SortedFrom b′ xs
sortedFrom-weaken le sf[] = sf[]
sortedFrom-weaken {A} {b} {b′} le (sf∷ {t = t} le′ s) =
  sf∷ (timeLeq-trans b′ b t le le′) s

boundedBy-weaken : {A : Set} {c c′ : Time} {xs : TimedObs A}
  → timeLeq c c′ ≡ true → BoundedBy c xs → BoundedBy c′ xs
boundedBy-weaken le bb[] = bb[]
boundedBy-weaken {A} {c} {c′} le (bb∷ {t = t} le′ b) =
  bb∷ (timeLeq-trans t c c′ le′ le) (boundedBy-weaken le b)

-- merge ----------------------------------------------------------------------

merge-sortedFrom : {A : Set} {b : Time} (xs ys : TimedObs A)
  → SortedFrom b xs → SortedFrom b ys → SortedFrom b (mergeT xs ys)
merge-sortedFrom []       ys sf[] sy   = sy
merge-sortedFrom (x ∷ xs) [] sx   sf[] = sx
merge-sortedFrom {A} {b} xss@((t₁ , v₁) ∷ xs) yss@((t₂ , v₂) ∷ ys)
                 (sf∷ b₁ s₁) (sf∷ b₂ s₂) =
  if-elim (timeLeq t₁ t₂)
    (λ w → SortedFrom b
             (if w then ((t₁ , v₁) ∷ mergeT xs yss)
                   else ((t₂ , v₂) ∷ mergeT xss ys)))
    (λ cmp → sf∷ b₁ (merge-sortedFrom xs yss s₁ (sf∷ cmp s₂)))
    (λ cmp → sf∷ b₂ (merge-sortedFrom xss ys
                       (sf∷ (timeLeq-total t₁ t₂ cmp) s₁) s₂))

merge-bounded : {A : Set} {c : Time} (xs ys : TimedObs A)
  → BoundedBy c xs → BoundedBy c ys → BoundedBy c (mergeT xs ys)
merge-bounded []       ys bb[] by   = by
merge-bounded (x ∷ xs) [] bx   bb[] = bx
merge-bounded {A} {c} xss@((t₁ , v₁) ∷ xs) yss@((t₂ , v₂) ∷ ys)
              (bb∷ l₁ b₁) (bb∷ l₂ b₂) =
  if-elim (timeLeq t₁ t₂)
    (λ w → BoundedBy c
             (if w then ((t₁ , v₁) ∷ mergeT xs yss)
                   else ((t₂ , v₂) ∷ mergeT xss ys)))
    (λ _ → bb∷ l₁ (merge-bounded xs yss b₁ (bb∷ l₂ b₂)))
    (λ _ → bb∷ l₂ (merge-bounded xss ys (bb∷ l₁ b₁) b₂))

-- map ------------------------------------------------------------------------

mapT-sortedFrom : {A B : Set} {b : Time} (f : A → B) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (mapT f xs)
mapT-sortedFrom f []             sf[]       = sf[]
mapT-sortedFrom f ((t , v) ∷ xs) (sf∷ le s) = sf∷ le (mapT-sortedFrom f xs s)

mapT-bounded : {A B : Set} {c : Time} (f : A → B) (xs : TimedObs A)
  → BoundedBy c xs → BoundedBy c (mapT f xs)
mapT-bounded f []             bb[]       = bb[]
mapT-bounded f ((t , v) ∷ xs) (bb∷ le b) = bb∷ le (mapT-bounded f xs b)

-- take -----------------------------------------------------------------------

take-sortedFrom : {A : Set} {b : Time} (n : ℕ) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (takeT n xs)
take-sortedFrom zero    xs             _          = sf[]
take-sortedFrom (suc n) []             sf[]       = sf[]
take-sortedFrom (suc n) ((t , v) ∷ xs) (sf∷ le s) =
  sf∷ le (take-sortedFrom n xs s)

head-leq-takeClose : {A : Set} (n : ℕ) (xs : TimedObs A) (c t : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeClose (suc n) xs c) ≡ true
head-leq-takeClose n       []              c t _          _           tc = tc
head-leq-takeClose zero    ((t′ , v) ∷ xs) c t (sf∷ le _) _           _  = le
head-leq-takeClose (suc n) ((t′ , v) ∷ xs) c t (sf∷ le s) (bb∷ lc bx) _  =
  timeLeq-trans t t′ _ le (head-leq-takeClose n xs c t′ s bx lc)

take-bounded : {A : Set} {b : Time} (n : ℕ) (xs : TimedObs A) (c : Time)
  → SortedFrom b xs → BoundedBy c xs
  → BoundedBy (takeClose n xs c) (takeT n xs)
take-bounded zero          xs             c _          _           = bb[]
take-bounded (suc n)       []             c _          _           = bb[]
take-bounded (suc zero)    ((t , v) ∷ xs) c _          _           =
  bb∷ (timeLeq-refl t) bb[]
take-bounded (suc (suc n)) ((t , v) ∷ xs) c (sf∷ le s) (bb∷ tc bx) =
  bb∷ (head-leq-takeClose n xs c t s bx tc) (take-bounded (suc n) xs c s bx)

-- filterAfter (the concat machinery) ------------------------------------------

filterAfter-keep : {A : Set} {b : Time} (c : Time) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (filterAfter c xs)
filterAfter-keep c []             sf[]       = sf[]
filterAfter-keep c ((t , v) ∷ xs) (sf∷ le s) with timeLt c t
... | true  = sf∷ le (filterAfter-keep c xs s)
... | false = filterAfter-keep c xs (sortedFrom-weaken le s)

filterAfter-from : {A : Set} {b : Time} (c : Time) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom c (filterAfter c xs)
filterAfter-from c []             _          = sf[]
filterAfter-from c ((t , v) ∷ xs) (sf∷ le s) with timeLt c t in k
... | true  = sf∷ (timeLt⇒timeLeq c t k) (filterAfter-keep c xs s)
... | false = filterAfter-from c xs s

filterAfter-bounded : {A : Set} {c : Time} (c′ : Time) (xs : TimedObs A)
  → BoundedBy c xs → BoundedBy c (filterAfter c′ xs)
filterAfter-bounded c′ []             bb[]       = bb[]
filterAfter-bounded c′ ((t , v) ∷ xs) (bb∷ le b) with timeLt c′ t
... | true  = bb∷ le (filterAfter-bounded c′ xs b)
... | false = filterAfter-bounded c′ xs b

-- a later filter absorbs an earlier one (a ref's own suffix of an
-- already-suffixed hot history is just the ref's suffix — connection time
-- is invariant for hot bindings)
filterAfter-absorb : {A : Set} (tc u : Time) (xs : TimedObs A)
  → timeLeq tc u ≡ true
  → filterAfter u (filterAfter tc xs) ≡ filterAfter u xs
filterAfter-absorb tc u [] le = refl
filterAfter-absorb tc u ((x , v) ∷ xs) le with timeLt tc x in k₁
filterAfter-absorb tc u ((x , v) ∷ xs) le | true with timeLt u x
... | true  = cong (_∷_ (x , v)) (filterAfter-absorb tc u xs le)
... | false = filterAfter-absorb tc u xs le
filterAfter-absorb tc u ((x , v) ∷ xs) le | false with timeLt u x in k₂
... | false = filterAfter-absorb tc u xs le
... | true  = true≢false
    (trans (sym (timeLeq-trans x tc u (timeLt-false⇒timeLeq-flip tc x k₁) le))
           (timeLt⇒timeLeq-flip-false u x k₂))

-- filtering strictly below a sorted list's lower bound keeps everything
filterAfter-none : {A : Set} (c b : Time) (xs : TimedObs A)
  → SortedFrom b xs → timeLt c b ≡ true → filterAfter c xs ≡ xs
filterAfter-none c b []             sf[]       cb = refl
filterAfter-none c b ((t , v) ∷ xs) (sf∷ le s) cb
  rewrite timeLt-leq-trans c b t cb le
  = cong (_∷_ (t , v)) (filterAfter-none c t xs s (timeLt-leq-trans c b t cb le))

mono⇒sortedFrom : {A : Set} (t : Time) (v : A) (xs : TimedObs A)
  → StrictMono ((t , v) ∷ xs) → SortedFrom t xs
mono⇒sortedFrom t v []              mono-one      = sf[]
mono⇒sortedFrom t v ((t′ , w) ∷ xs) (mono-∷ lt m) =
  sf∷ (timeLt⇒timeLeq t t′ lt) (mono⇒sortedFrom t′ w xs m)

-- the suffix of one-event-per-instant is one-event-per-instant
filterAfter-mono : {A : Set} (c : Time) (xs : TimedObs A)
  → StrictMono xs → StrictMono (filterAfter c xs)
filterAfter-mono c [] mono-[] = mono-[]
filterAfter-mono c ((t , v) ∷ []) mono-one with timeLt c t
... | true  = mono-one
... | false = mono-[]
filterAfter-mono c ((t , v) ∷ (t′ , v′) ∷ xs) (mono-∷ lt m) with timeLt c t in k
... | false = filterAfter-mono c ((t′ , v′) ∷ xs) m
... | true rewrite filterAfter-none c t′ ((t′ , v′) ∷ xs)
                     (sf∷ (timeLeq-refl t′) (mono⇒sortedFrom t′ v′ xs m))
                     (timeLt-trans c t t′ k lt)
           = mono-∷ lt m

-- append (concat = append past a pivot) ---------------------------------------

append-sortedFrom : {A : Set} {b p : Time} (xs ys : TimedObs A)
  → SortedFrom b xs → BoundedBy p xs → SortedFrom p ys
  → timeLeq b p ≡ true
  → SortedFrom b (xs ++ ys)
append-sortedFrom []             ys sf[]       bb[]        sy bp =
  sortedFrom-weaken bp sy
append-sortedFrom ((t , v) ∷ xs) ys (sf∷ le s) (bb∷ tp bx) sy bp =
  sf∷ le (append-sortedFrom xs ys s bx sy tp)

append-bounded : {A : Set} {c : Time} (xs ys : TimedObs A)
  → BoundedBy c xs → BoundedBy c ys → BoundedBy c (xs ++ ys)
append-bounded []             ys bb[]       by = by
append-bounded ((t , v) ∷ xs) ys (bb∷ le b) by = bb∷ le (append-bounded xs ys b by)

-- constant-time lists (the shape of `of`) -------------------------------------

const-sortedFrom : {A : Set} (t : Time) (vs : List A)
  → SortedFrom t (map (λ v → (t , v)) vs)
const-sortedFrom t []       = sf[]
const-sortedFrom t (v ∷ vs) = sf∷ (timeLeq-refl t) (const-sortedFrom t vs)

const-bounded : {A : Set} (t : Time) (vs : List A)
  → BoundedBy t (map (λ v → (t , v)) vs)
const-bounded t []       = bb[]
const-bounded t (v ∷ vs) = bb∷ (timeLeq-refl t) (const-bounded t vs)
