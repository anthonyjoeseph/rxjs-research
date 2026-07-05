-- THE COUNTING MECHANISM.
--
-- batchImpl (BatchImpl.agda) flushes when the next emission's TIME differs —
-- a comparison the TypeScript implementation cannot make, because at runtime
-- there are no timestamps. The real mechanism counts: the provenance memory
-- records how many deliveries each instant owes (totalNum, learned from
-- registration inits), ticks a countdown per arrival (awaitingValueCount),
-- and flushes when the countdown runs out.
--
-- batchCount is that mechanism: `mult` is totalNum, the countdown argument
-- is awaitingValueCount, the accumulator is the memory's batch field.
-- The flush decision makes NO time comparison whatsoever.
--
-- The simulation theorem batchCount-impl says: whenever the recorded
-- multiplicities are truthful — `mult t` = the number of emissions instant t
-- actually delivers, the invariant "totalNum = live subscriptions" —
-- counting computes exactly the same flushes as time-comparison:
--
--   batchCount mult xs ≡ batchImpl xs      (≡ batchSpec xs, by BatchImpl)
--
-- The `Instants` predicate is that truthfulness invariant. For the
-- arbitrary-depth diamond fragment, expand-instants DISCHARGES it: a merge
-- tree with k leaves delivers every source instant exactly k times, so
-- `mult = λ _ → k` is truthful — closing the tower for count-deep-diamond:
--
--   counting mechanism ≡ flush behavior ≡ specification ≡ one batch/instant
--
-- (Modeling notes, honestly stated: the memory here holds one open instant,
-- not a map keyed by provenance — justified because on a sorted stream an
-- instant's deliveries are adjacent, so at most one window is ever open.
-- And `mult` is static, matching the fragment where no branch closes early;
-- take-induced mid-stream totalNum changes are future work.)
module BatchCount where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Obs
open import Exp
open import Deep

-- the mechanism ---------------------------------------------------------------

mutual
  batchCount : {A : Set} (mult : Time → ℕ) → TimedObs A → TimedObs (List A)
  batchCount mult []             = []
  batchCount mult ((t , v) ∷ xs) = window mult t (mult t) v xs

  -- an instant opens: n is the multiplicity the memory recorded for it
  window : {A : Set} (mult : Time → ℕ) (t : Time) (n : ℕ) (v : A)
         → TimedObs A → TimedObs (List A)
  window mult t zero          v xs = (t , v ∷ []) ∷ batchCount mult xs
  window mult t (suc zero)    v xs = (t , v ∷ []) ∷ batchCount mult xs
  window mult t (suc (suc n)) v xs = countdown mult t n (v ∷ []) xs

  -- suc r more deliveries owed to the open instant; note: the incoming
  -- emission's time is never inspected — the flush is decided by the count
  countdown : {A : Set} (mult : Time → ℕ) (t : Time) (r : ℕ) (acc : List A)
            → TimedObs A → TimedObs (List A)
  countdown mult t r       acc []              = (t , acc) ∷ []
  countdown mult t zero    acc ((t′ , v) ∷ xs) =
    (t , acc ++ (v ∷ [])) ∷ batchCount mult xs
  countdown mult t (suc r) acc ((t′ , v) ∷ xs) =
    countdown mult t r (acc ++ (v ∷ [])) xs

-- the truthfulness invariant ---------------------------------------------------

-- length of the leading block of emissions at time t
runLength : {A : Set} → Time → TimedObs A → ℕ
runLength t []             = 0
runLength t ((t′ , _) ∷ xs) = if timeEq t t′ then suc (runLength t xs) else 0

-- the stream after that leading block
dropRun : {A : Set} → Time → TimedObs A → TimedObs A
dropRun t []              = []
dropRun t ((t′ , v) ∷ xs) =
  if timeEq t t′ then dropRun t xs else ((t′ , v) ∷ xs)

-- "totalNum is truthful": at the start of every instant of the stream, the
-- recorded multiplicity equals the number of deliveries that follow
data Instants {A : Set} (mult : Time → ℕ) : TimedObs A → Set where
  ins[] : Instants mult []
  ins∷  : {t : Time} {v : A} {xs : TimedObs A}
        → mult t ≡ suc (runLength t xs)
        → Instants mult (dropRun t xs)
        → Instants mult ((t , v) ∷ xs)

dropRun-none : {A : Set} (t : Time) (xs : TimedObs A)
  → runLength t xs ≡ 0 → dropRun t xs ≡ xs
dropRun-none t []              _  = refl
dropRun-none t ((t′ , v) ∷ xs) rl with timeEq t t′
... | true  = suc≢zero rl
... | false = refl

-- the simulation proof ---------------------------------------------------------

-- the instant is over (no more emissions at t): both sides flush the buffer
-- and continue on the rest of the stream. The continuation equality is
-- passed in (the caller's induction hypothesis), keeping this helper out of
-- the recursive cycle.
flush-lemma : {A : Set} (mult : Time → ℕ) (t : Time) (acc : List A)
              (xs : TimedObs A)
  → runLength t xs ≡ 0
  → batchCount mult xs ≡ batchImpl xs
  → (t , acc) ∷ batchCount mult xs ≡ batchAcc t acc xs
flush-lemma mult t acc [] _ _ = refl
flush-lemma mult t acc ((t″ , u) ∷ xs″) rl eq with timeEq t t″
... | true  = suc≢zero rl
... | false = cong (_∷_ (t , acc)) eq

mutual
  -- THE SIMULATION THEOREM: truthful counting = time-comparison flushing
  batchCount-impl : {A : Set} (mult : Time → ℕ) (xs : TimedObs A)
    → Instants mult xs
    → batchCount mult xs ≡ batchImpl xs
  batchCount-impl mult [] ins[] = refl
  batchCount-impl mult ((t , v) ∷ xs) (ins∷ meq H) rewrite meq
    with runLength t xs in rl
  ... | zero  =
    flush-lemma mult t (v ∷ []) xs rl
      (batchCount-impl mult xs
        (subst (Instants mult) (dropRun-none t xs rl) H))
  ... | suc n = countdown-acc mult t n (v ∷ []) xs rl H

  -- an open window with a truthful countdown tracks batchAcc exactly:
  -- suc r more deliveries owed ⟺ suc r more emissions at this time ahead
  countdown-acc : {A : Set} (mult : Time → ℕ) (t : Time) (r : ℕ)
                  (acc : List A) (xs : TimedObs A)
    → runLength t xs ≡ suc r
    → Instants mult (dropRun t xs)
    → countdown mult t r acc xs ≡ batchAcc t acc xs
  countdown-acc mult t r acc [] rl H = zero≢suc rl
  countdown-acc mult t zero acc ((t′ , w) ∷ xs′) rl H
    with timeEq t t′
  ... | false = zero≢suc rl
  ... | true  =
    flush-lemma mult t (acc ++ (w ∷ [])) xs′ (suc-inj rl)
      (batchCount-impl mult xs′
        (subst (Instants mult) (dropRun-none t xs′ (suc-inj rl)) H))
  countdown-acc mult t (suc r) acc ((t′ , w) ∷ xs′) rl H
    with timeEq t t′
  ... | false = zero≢suc rl
  ... | true  = countdown-acc mult t r (acc ++ (w ∷ [])) xs′ (suc-inj rl) H

-- discharging the invariant for arbitrary-depth diamonds ------------------------

-- a block of k emissions at time t, followed by emissions at other times,
-- has run length k …
runLength-block : {A B : Set} (t : Time) (v : A) (fs : List (A → B))
                  (rest : TimedObs B)
  → runLength t rest ≡ 0
  → runLength t (map (λ f → (t , f v)) fs ++ rest) ≡ length fs
runLength-block t v []       rest r0 = r0
runLength-block t v (f ∷ fs) rest r0 rewrite timeEq-refl t =
  cong suc (runLength-block t v fs rest r0)

-- … and dropping it lands exactly on the rest
dropRun-block : {A B : Set} (t : Time) (v : A) (fs : List (A → B))
                (rest : TimedObs B)
  → runLength t rest ≡ 0
  → dropRun t (map (λ f → (t , f v)) fs ++ rest) ≡ rest
dropRun-block t v []       rest r0 = dropRun-none t rest r0
dropRun-block t v (f ∷ fs) rest r0 rewrite timeEq-refl t =
  dropRun-block t v fs rest r0

expand-run0 : {A B : Set} (f : A → B) (fs : List (A → B))
              (t : Time) (v : A) (xs : TimedObs A)
  → StrictMono ((t , v) ∷ xs)
  → runLength t (expand (f ∷ fs) xs) ≡ 0
expand-run0 f fs t v []              _             = refl
expand-run0 f fs t v ((t₁ , w) ∷ xs) (mono-∷ lt _)
  rewrite timeLt⇒timeEq-false t t₁ lt = refl

-- THE INVARIANT HOLDS: a diamond with k leaves delivers every source
-- instant exactly k times, so "totalNum = number of merged branches" is
-- truthful on the expanded stream
expand-instants : {A B : Set} (f : A → B) (fs : List (A → B))
                  (xs : TimedObs A)
  → StrictMono xs
  → Instants (λ _ → suc (length fs)) (expand (f ∷ fs) xs)
expand-instants f fs [] _ = ins[]
expand-instants f fs ((t , v) ∷ xs) m =
  ins∷ (cong suc (sym (runLength-block t v fs (expand (f ∷ fs) xs)
                        (expand-run0 f fs t v xs m))))
       (subst (Instants (λ _ → suc (length fs)))
              (sym (dropRun-block t v fs (expand (f ∷ fs) xs)
                     (expand-run0 f fs t v xs m)))
              (expand-instants f fs xs (mono-tail m)))

expand-instants′ : {A B : Set} (fs : List (A → B)) (xs : TimedObs A)
  → NonEmptyL fs → StrictMono xs
  → Instants (λ _ → length fs) (expand fs xs)
expand-instants′ (f ∷ fs) xs neL m = expand-instants f fs xs m

-- the closed tower ---------------------------------------------------------------

-- the anchor law, computed by the counting mechanism with totalNum = 2
merge-self-expand : {A : Set} (xs : TimedObs A) → StrictMono xs
  → mergeT xs xs ≡ expand ((λ v → v) ∷ (λ v → v) ∷ []) xs
merge-self-expand xs m =
  trans (cong₂ mergeT (sym (expand-id xs)) (sym (expand-id xs)))
        (expand-merge (λ v → v) [] (λ v → v) [] xs m)

count-diamond : {A : Set} (xs : TimedObs A) → StrictMono xs
  → batchCount (λ _ → 2) (mergeT xs xs) ≡ mapT dbl xs
count-diamond xs m =
  trans (cong (batchCount (λ _ → 2)) (merge-self-expand xs m))
 (trans (batchCount-impl (λ _ → 2) (expand ((λ v → v) ∷ (λ v → v) ∷ []) xs)
          (expand-instants (λ v → v) ((λ v → v) ∷ []) xs m))
 (trans (batchImpl-spec (expand ((λ v → v) ∷ (λ v → v) ∷ []) xs))
        (batch-expand (λ v → v) ((λ v → v) ∷ []) xs m)))

-- THE CLOSED TOWER: for ANY merge/map tree over one source at ANY depth,
-- the counting mechanism — run with totalNum = the tree's leaf count —
-- produces exactly one batch per source instant
count-deep-diamond : (i : ℕ) (e : Exp) (env : Env)
  → DiamondOver i e
  → StrictMono (emits (env i))
  → batchCount (λ _ → length (funs e)) (emits (⟦ e ⟧ env))
  ≡ mapT (applyAll (funs e)) (emits (env i))
count-deep-diamond i e env d m =
  trans (cong (batchCount (λ _ → length (funs e))) (expand-denote i e env d m))
 (trans (batchCount-impl (λ _ → length (funs e))
          (expand (funs e) (emits (env i)))
          (expand-instants′ (funs e) (emits (env i)) (funs-ne d) m))
 (trans (batchImpl-spec (expand (funs e) (emits (env i))))
        (batch-expand′ (funs e) (emits (env i)) (funs-ne d) m)))
