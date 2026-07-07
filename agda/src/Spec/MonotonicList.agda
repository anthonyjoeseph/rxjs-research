-- Time, timed lists, and observables whose sortedness is BY CONSTRUCTION.
--
-- The spec's whole authority comes from timestamps, so a "timed
-- observable" whose sortedness is a separate theorem is a weaker
-- statement than one whose type guarantees it. TObsOf bundles a timed
-- emission list with its complete well-formedness evidence, RELATIVE to
-- the subscription time it was born at: emissions start no earlier than
-- the subscription, the close is no earlier than the subscription, and
-- every emission happens by the close. The close is load-bearing, not
-- decoration: the serial joins subscribe their next inner at the
-- previous one's close, and take manufactures a close.
--
-- Below the record: the raw timed-list operators (merge, map, take,
-- scan, filterAfter) and the lemma toolkit proving each preserves
-- sortedness and boundedness — the machinery every spec combinator's
-- evidence fields are assembled from.
module Spec.MonotonicList where

open import Prelude

------------------------------------------------------------------------
-- Time = (tick, origin), lexicographic. Tick 0 is the subscription
-- frame; tick k+1 is the k-th async emission. The origin coordinate
-- orders feedback: a reentrant .next() lands strictly after the batch
-- that caused it.

Time : Set
Time = ℕ × ℕ

t₀ : Time
t₀ = (zero , zero)

timeEq : Time → Time → Bool
timeEq (a , b) (c , d) = eqℕ a c ∧ eqℕ b d

timeLt : Time → Time → Bool
timeLt (a , b) (c , d) = ltℕ a c ∨ (eqℕ a c ∧ ltℕ b d)

timeLeq : Time → Time → Bool
timeLeq (a , b) (c , d) = ltℕ a c ∨ (eqℕ a c ∧ leqℕ b d)

timeMax : Time → Time → Time
timeMax x y = if timeLeq x y then y else x

------------------------------------------------------------------------
-- the order lemmas (transcribed from the proven v1 tower)

timeEq-refl : (t : Time) → timeEq t t ≡ true
timeEq-refl (a , b) rewrite eqℕ-refl a | eqℕ-refl b = refl

timeLeq-refl : (t : Time) → timeLeq t t ≡ true
timeLeq-refl (a , b) rewrite ltℕ-irrefl a | eqℕ-refl a | leqℕ-refl b = refl

timeLt-irrefl : (t : Time) → timeLt t t ≡ false
timeLt-irrefl (a , b) rewrite ltℕ-irrefl a | eqℕ-refl a | ltℕ-irrefl b = refl

t₀-least : (t : Time) → timeLeq t₀ t ≡ true
t₀-least (zero  , b) = refl
t₀-least (suc a , b) = refl

timeEq-sound : (x y : Time) → timeEq x y ≡ true → x ≡ y
timeEq-sound (a , b) (c , d) p
  with eqℕ-sound a c (∧-split-left (eqℕ a c) (eqℕ b d) p)
     | eqℕ-sound b d (∧-split-right (eqℕ a c) (eqℕ b d) p)
... | refl | refl = refl

-- helpers that make a timeLeq/timeLt goal compute after rewriting
lt-head-leq : (a c b d : ℕ) → ltℕ a c ≡ true → timeLeq (a , b) (c , d) ≡ true
lt-head-leq a c b d p rewrite p = refl

eq-head-leq : (a b d : ℕ) → leqℕ b d ≡ true → timeLeq (a , b) (a , d) ≡ true
eq-head-leq a b d p rewrite ltℕ-irrefl a | eqℕ-refl a | p = refl

lt-head-lt : (a c b d : ℕ) → ltℕ a c ≡ true → timeLt (a , b) (c , d) ≡ true
lt-head-lt a c b d p rewrite p = refl

eq-head-lt : (a b d : ℕ) → ltℕ b d ≡ true → timeLt (a , b) (a , d) ≡ true
eq-head-lt a b d p rewrite ltℕ-irrefl a | eqℕ-refl a | p = refl

-- ticks at origin 0 order exactly as their ℕ ticks
tick-leq : (a c : ℕ) → leqℕ a c ≡ true → timeLeq (a , 0) (c , 0) ≡ true
tick-leq zero    zero    _ = refl
tick-leq zero    (suc c) _ = refl
tick-leq (suc a) zero    ()
tick-leq (suc a) (suc c) p = tick-leq a c p

timeLt⇒timeLeq : (x y : Time) → timeLt x y ≡ true → timeLeq x y ≡ true
timeLt⇒timeLeq (a , b) (c , d) p with ∨-split (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p
... | left ac = lt-head-leq a c b d ac
... | right r =
  subst (λ z → timeLeq (a , b) (z , d) ≡ true)
        (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r))
        (eq-head-leq a b d (ltℕ⇒leqℕ b d (∧-split-right (eqℕ a c) (ltℕ b d) r)))

timeLeq-total : (x y : Time) → timeLeq x y ≡ false → timeLeq y x ≡ true
timeLeq-total (a , b) (c , d) h
  with ltℕ-false-split a c (∨-false-left (ltℕ a c) (eqℕ a c ∧ leqℕ b d) h)
... | left ca = lt-head-leq c a d b ca
... | right aeqc =
  subst (λ z → timeLeq (c , d) (z , b) ≡ true) (sym aeqc)
        (eq-head-leq c d b
          (leqℕ-false⇒flip b d
            (∧-true-false (eqℕ a c) (leqℕ b d)
              (eqℕ-complete a c aeqc)
              (∨-false-right (ltℕ a c) (eqℕ a c ∧ leqℕ b d) h))))

timeLeq-trans : (x y z : Time)
  → timeLeq x y ≡ true → timeLeq y z ≡ true → timeLeq x z ≡ true
timeLeq-trans (a , b) (c , d) (e , f) p q
  with ∨-split (ltℕ a c) (eqℕ a c ∧ leqℕ b d) p
     | ∨-split (ltℕ c e) (eqℕ c e ∧ leqℕ d f) q
... | left ac  | left ce  = lt-head-leq a e b f (ltℕ-trans a c e ac ce)
... | left ac  | right r  =
  lt-head-leq a e b f
    (subst (λ z′ → ltℕ a z′ ≡ true)
           (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r)) ac)
... | right r  | left ce  =
  lt-head-leq a e b f
    (subst (λ z′ → ltℕ z′ e ≡ true)
           (sym (eqℕ-sound a c (∧-split-left (eqℕ a c) (leqℕ b d) r))) ce)
... | right r₁ | right r₂ =
  subst (λ z′ → timeLeq (a , b) (z′ , f) ≡ true)
        (trans (eqℕ-sound a c (∧-split-left (eqℕ a c) (leqℕ b d) r₁))
               (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r₂)))
        (eq-head-leq a b f
          (leqℕ-trans b d f
            (∧-split-right (eqℕ a c) (leqℕ b d) r₁)
            (∧-split-right (eqℕ c e) (leqℕ d f) r₂)))

timeLt-leq-trans : (x y z : Time)
  → timeLt x y ≡ true → timeLeq y z ≡ true → timeLt x z ≡ true
timeLt-leq-trans (a , b) (c , d) (e , f) p q
  with ∨-split (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p
     | ∨-split (ltℕ c e) (eqℕ c e ∧ leqℕ d f) q
... | left ac  | left ce  = lt-head-lt a e b f (ltℕ-trans a c e ac ce)
... | left ac  | right r  =
  lt-head-lt a e b f
    (subst (λ z′ → ltℕ a z′ ≡ true)
           (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r)) ac)
... | right r  | left ce  =
  lt-head-lt a e b f
    (subst (λ z′ → ltℕ z′ e ≡ true)
           (sym (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r))) ce)
... | right r₁ | right r₂ =
  subst (λ z′ → timeLt (a , b) (z′ , f) ≡ true)
        (trans (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r₁))
               (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r₂)))
        (eq-head-lt a b f
          (ltℕ-leqℕ-trans b d f
            (∧-split-right (eqℕ a c) (ltℕ b d) r₁)
            (∧-split-right (eqℕ c e) (leqℕ d f) r₂)))

timeLt-false⇒timeLeq-flip : (x y : Time)
  → timeLt x y ≡ false → timeLeq y x ≡ true
timeLt-false⇒timeLeq-flip (a , b) (c , d) p
  with ltℕ-false-split a c (∨-false-left (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p)
... | left q     = lt-head-leq c a d b q
... | right refl = eq-head-leq a d b
    (ltℕ-false⇒leqℕ-flip b d
      (∧-true-false (eqℕ a a) (ltℕ b d) (eqℕ-refl a)
        (∨-false-right (ltℕ a a) (eqℕ a a ∧ ltℕ b d) p)))

timeMax-left : (x y : Time) → timeLeq x (timeMax x y) ≡ true
timeMax-left x y with timeLeq x y in e
... | true  = e
... | false = timeLeq-refl x

timeMax-right : (x y : Time) → timeLeq y (timeMax x y) ≡ true
timeMax-right x y with timeLeq x y in e
... | true  = timeLeq-refl y
... | false = timeLeq-total x y e

------------------------------------------------------------------------
-- timed lists and the raw operators over them

TimedObs : Set → Set
TimedObs A = List (Time × A)

-- stable sort-merge: on equal Times the left argument wins (the model
-- counterpart of rxjs subscription order)
mergeL : {A : Set} → TimedObs A → TimedObs A → TimedObs A
mergeL []       ys       = ys
mergeL (x ∷ xs) []       = x ∷ xs
mergeL (x ∷ xs) (y ∷ ys) =
  if timeLeq (fst x) (fst y)
  then (x ∷ mergeL xs (y ∷ ys))
  else (y ∷ mergeL (x ∷ xs) ys)

mapL : {A B : Set} → (A → B) → TimedObs A → TimedObs B
mapL f []             = []
mapL f ((t , v) ∷ xs) = (t , f v) ∷ mapL f xs

takeL : {A : Set} → ℕ → TimedObs A → TimedObs A
takeL zero    _        = []
takeL (suc n) []       = []
takeL (suc n) (x ∷ xs) = x ∷ takeL n xs

scanL : {A B : Set} → (B → A → B) → B → TimedObs A → TimedObs B
scanL f z []             = []
scanL f z ((u , v) ∷ xs) = (u , f z v) ∷ scanL f (f z v) xs

-- emissions strictly after a boundary (hot semantics: a subject does
-- not replay; concat subscribes leg 2 only once leg 1 has closed)
filterAfterL : {A : Set} → Time → TimedObs A → TimedObs A
filterAfterL c []             = []
filterAfterL c ((t , v) ∷ xs) =
  if timeLt c t
  then ((t , v) ∷ filterAfterL c xs)
  else filterAfterL c xs

-- the close of `take n` when the subscription happened at t: the time
-- of the nth emission if it exists, the source's close if it has fewer,
-- and the subscription instant itself for take 0
takeCloseL : {A : Set} → Time → ℕ → TimedObs A → Time → Time
takeCloseL t zero          _               _ = t
takeCloseL t (suc n)       []              c = c
takeCloseL t (suc zero)    ((t′ , _) ∷ _)  _ = t′
takeCloseL t (suc (suc n)) (_ ∷ xs)        c = takeCloseL t (suc n) xs c

------------------------------------------------------------------------
-- sortedness and boundedness, tracked from a bound

data SortedFrom {A : Set} : Time → TimedObs A → Set where
  sf[] : {b : Time} → SortedFrom b []
  sf∷  : {b t : Time} {v : A} {xs : TimedObs A}
       → timeLeq b t ≡ true
       → SortedFrom t xs
       → SortedFrom b ((t , v) ∷ xs)

data BoundedBy {A : Set} (c : Time) : TimedObs A → Set where
  bb[] : BoundedBy c []
  bb∷  : {t : Time} {v : A} {xs : TimedObs A}
       → timeLeq t c ≡ true
       → BoundedBy c xs
       → BoundedBy c ((t , v) ∷ xs)

------------------------------------------------------------------------
-- THE verified-by-construction observable: emissions + close + the
-- complete well-formedness evidence relative to its subscription time

record TObsOf (A : Set) (t : Time) : Set where
  constructor tobs
  field
    emits   : TimedObs A
    close   : Time
    sorted  : SortedFrom t emits
    closeAt : timeLeq t close ≡ true
    bounded : BoundedBy close emits
open TObsOf public

emptyT : {A : Set} (t : Time) → TObsOf A t
emptyT t = tobs [] t sf[] (timeLeq-refl t) bb[]

------------------------------------------------------------------------
-- the preservation toolkit: every operator preserves sortedness and
-- boundedness (transcribed from the proven v1 Sorting module)

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

-- merge

merge-sortedFrom : {A : Set} {b : Time} (xs ys : TimedObs A)
  → SortedFrom b xs → SortedFrom b ys → SortedFrom b (mergeL xs ys)
merge-sortedFrom []       ys sf[] sy   = sy
merge-sortedFrom (x ∷ xs) [] sx   sf[] = sx
merge-sortedFrom {A} {b} xss@((t₁ , v₁) ∷ xs) yss@((t₂ , v₂) ∷ ys)
                 (sf∷ b₁ s₁) (sf∷ b₂ s₂) =
  if-elim (timeLeq t₁ t₂)
    (λ w → SortedFrom b
             (if w then ((t₁ , v₁) ∷ mergeL xs yss)
                   else ((t₂ , v₂) ∷ mergeL xss ys)))
    (λ cmp → sf∷ b₁ (merge-sortedFrom xs yss s₁ (sf∷ cmp s₂)))
    (λ cmp → sf∷ b₂ (merge-sortedFrom xss ys
                       (sf∷ (timeLeq-total t₁ t₂ cmp) s₁) s₂))

merge-bounded : {A : Set} {c : Time} (xs ys : TimedObs A)
  → BoundedBy c xs → BoundedBy c ys → BoundedBy c (mergeL xs ys)
merge-bounded []       ys bb[] by   = by
merge-bounded (x ∷ xs) [] bx   bb[] = bx
merge-bounded {A} {c} xss@((t₁ , v₁) ∷ xs) yss@((t₂ , v₂) ∷ ys)
              (bb∷ l₁ b₁) (bb∷ l₂ b₂) =
  if-elim (timeLeq t₁ t₂)
    (λ w → BoundedBy c
             (if w then ((t₁ , v₁) ∷ mergeL xs yss)
                   else ((t₂ , v₂) ∷ mergeL xss ys)))
    (λ _ → bb∷ l₁ (merge-bounded xs yss b₁ (bb∷ l₂ b₂)))
    (λ _ → bb∷ l₂ (merge-bounded xss ys (bb∷ l₁ b₁) b₂))

-- map

mapL-sortedFrom : {A B : Set} {b : Time} (f : A → B) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (mapL f xs)
mapL-sortedFrom f []             sf[]       = sf[]
mapL-sortedFrom f ((t , v) ∷ xs) (sf∷ le s) = sf∷ le (mapL-sortedFrom f xs s)

mapL-bounded : {A B : Set} {c : Time} (f : A → B) (xs : TimedObs A)
  → BoundedBy c xs → BoundedBy c (mapL f xs)
mapL-bounded f []             bb[]       = bb[]
mapL-bounded f ((t , v) ∷ xs) (bb∷ le b) = bb∷ le (mapL-bounded f xs b)

-- scan

scanL-sortedFrom : {A B : Set} {b : Time} (f : B → A → B) (z : B)
  (xs : TimedObs A) → SortedFrom b xs → SortedFrom b (scanL f z xs)
scanL-sortedFrom f z []             sf[]       = sf[]
scanL-sortedFrom f z ((u , v) ∷ xs) (sf∷ le s) =
  sf∷ le (scanL-sortedFrom f (f z v) xs s)

scanL-bounded : {A B : Set} {c : Time} (f : B → A → B) (z : B)
  (xs : TimedObs A) → BoundedBy c xs → BoundedBy c (scanL f z xs)
scanL-bounded f z []             bb[]       = bb[]
scanL-bounded f z ((u , v) ∷ xs) (bb∷ le b) =
  bb∷ le (scanL-bounded f (f z v) xs b)

-- take

take-sortedFrom : {A : Set} {b : Time} (n : ℕ) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (takeL n xs)
take-sortedFrom zero    xs             _          = sf[]
take-sortedFrom (suc n) []             sf[]       = sf[]
take-sortedFrom (suc n) ((t , v) ∷ xs) (sf∷ le s) =
  sf∷ le (take-sortedFrom n xs s)

head-leq-takeClose : {A : Set} (t₀′ : Time) (n : ℕ) (xs : TimedObs A)
  (c t : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeCloseL t₀′ (suc n) xs c) ≡ true
head-leq-takeClose t₀′ n       []              c t _          _           tc = tc
head-leq-takeClose t₀′ zero    ((t′ , v) ∷ xs) c t (sf∷ le _) _           _  = le
head-leq-takeClose t₀′ (suc n) ((t′ , v) ∷ xs) c t (sf∷ le s) (bb∷ lc bx) _  =
  timeLeq-trans t t′ _ le (head-leq-takeClose t₀′ n xs c t′ s bx lc)

take-closeAt : {A : Set} (t : Time) (n : ℕ) (xs : TimedObs A) (c : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeCloseL t n xs c) ≡ true
take-closeAt t zero    xs c _ _ _  = timeLeq-refl t
take-closeAt t (suc n) xs c s b tc = head-leq-takeClose t n xs c t s b tc

take-bounded : {A : Set} (t₀′ : Time) {b : Time} (n : ℕ) (xs : TimedObs A)
  (c : Time)
  → SortedFrom b xs → BoundedBy c xs
  → BoundedBy (takeCloseL t₀′ n xs c) (takeL n xs)
take-bounded t₀′ zero          xs             c _          _           = bb[]
take-bounded t₀′ (suc n)       []             c _          _           = bb[]
take-bounded t₀′ (suc zero)    ((t , v) ∷ xs) c _          _           =
  bb∷ (timeLeq-refl t) bb[]
take-bounded t₀′ (suc (suc n)) ((t , v) ∷ xs) c (sf∷ le s) (bb∷ tc bx) =
  bb∷ (head-leq-takeClose t₀′ n xs c t s bx tc)
      (take-bounded t₀′ (suc n) xs c s bx)

-- filterAfter

filterAfter-keep : {A : Set} {b : Time} (c : Time) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (filterAfterL c xs)
filterAfter-keep c []             sf[]       = sf[]
filterAfter-keep c ((t , v) ∷ xs) (sf∷ le s) with timeLt c t
... | true  = sf∷ le (filterAfter-keep c xs s)
... | false = filterAfter-keep c xs (sortedFrom-weaken le s)

filterAfter-from : {A : Set} {b : Time} (c : Time) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom c (filterAfterL c xs)
filterAfter-from c []             _          = sf[]
filterAfter-from c ((t , v) ∷ xs) (sf∷ le s) with timeLt c t in k
... | true  = sf∷ (timeLt⇒timeLeq c t k) (filterAfter-keep c xs s)
... | false = filterAfter-from c xs s

filterAfter-bounded : {A : Set} {c : Time} (c′ : Time) (xs : TimedObs A)
  → BoundedBy c xs → BoundedBy c (filterAfterL c′ xs)
filterAfter-bounded c′ []             bb[]       = bb[]
filterAfter-bounded c′ ((t , v) ∷ xs) (bb∷ le b) with timeLt c′ t
... | true  = bb∷ le (filterAfter-bounded c′ xs b)
... | false = filterAfter-bounded c′ xs b

-- append (concat = append past a pivot)

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
append-bounded ((t , v) ∷ xs) ys (bb∷ le b) by =
  bb∷ le (append-bounded xs ys b by)

-- constant-time lists (the shape of `of`)

const-sortedFrom : {A : Set} (t : Time) (vs : List A)
  → SortedFrom t (map (λ v → (t , v)) vs)
const-sortedFrom t []       = sf[]
const-sortedFrom t (v ∷ vs) = sf∷ (timeLeq-refl t) (const-sortedFrom t vs)

const-bounded : {A : Set} (t : Time) (vs : List A)
  → BoundedBy t (map (λ v → (t , v)) vs)
const-bounded t []       = bb[]
const-bounded t (v ∷ vs) = bb∷ (timeLeq-refl t) (const-bounded t vs)
