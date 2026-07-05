-- A LATE SUBSCRIBER TO A SHARED STREAM: the time-reversed dual of take.
--
-- share preserves the upstream provenance across subscribers — which is
-- what justifies the model's habit of reusing one timed list on both sides
-- of a merge (every diamond theorem is implicitly a share theorem). The
-- genuinely new law is the LATE subscriber: it missed the first n instants
-- (registration-only replay, hot semantics), so
--
--   batchSpec (mergeT xs (dropT n xs)) ≡ lateDiamondSpec n xs
--
-- — single batches before the subscriber joins, doubled after. Where take
-- cuts a branch's future ([[1,1],[2]]), a late subscription cuts a
-- branch's past ([[1],[2,2]]). And the counting mechanism realizes it with
-- a dynamic multiplicity rising 1 → 2 as the subscriber joins (lateMult),
-- mirroring takeMult's 2 → 1.
module Share where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import BatchCount
open import Deep
open import TakeDiamond
open import TakeDeep

-- the missed past: drop the first n emissions
dropT : {A : Set} → ℕ → TimedObs A → TimedObs A
dropT zero    xs       = xs
dropT (suc n) []       = []
dropT (suc n) (x ∷ xs) = dropT n xs

-- expected batches: single before the join, doubled after
lateDiamondSpec : {A : Set} → ℕ → TimedObs A → TimedObs (List A)
lateDiamondSpec zero    xs             = mapT dbl xs
lateDiamondSpec (suc n) []             = []
lateDiamondSpec (suc n) ((t , v) ∷ xs) =
  (t , v ∷ []) ∷ lateDiamondSpec n xs

-- small facts -------------------------------------------------------------------

dropT-allAfter : {A : Set} {t₀ : Time} (n : ℕ) (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (dropT n xs)
dropT-allAfter zero    xs       a          = a
dropT-allAfter (suc n) []       aa[]       = aa[]
dropT-allAfter (suc n) (x ∷ xs) (aa∷ _ a) = dropT-allAfter n xs a

mapT-allAfter : {A B : Set} {t₀ : Time} (f : A → B) (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (mapT f xs)
mapT-allAfter f []             aa[]        = aa[]
mapT-allAfter f ((t , v) ∷ xs) (aa∷ lt a) = aa∷ lt (mapT-allAfter f xs a)

lateDiamondSpec-allAfter : {A : Set} {t₀ : Time} (n : ℕ) (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (lateDiamondSpec n xs)
lateDiamondSpec-allAfter zero    xs             a           = mapT-allAfter dbl xs a
lateDiamondSpec-allAfter (suc n) []             aa[]        = aa[]
lateDiamondSpec-allAfter (suc n) ((t , v) ∷ xs) (aa∷ lt a) =
  aa∷ lt (lateDiamondSpec-allAfter n xs a)

-- a leading left emission before everything on the right is emitted first
merge-pull-left-one : {A : Set} (t : Time) (v : A) (M R : TimedObs A)
  → HeadLeqB t R ≡ true
  → mergeT ((t , v) ∷ M) R ≡ (t , v) ∷ mergeT M R
merge-pull-left-one t v M [] _ rewrite mergeT-idr M = refl
merge-pull-left-one t v M ((tr , u) ∷ rs) hl rewrite hl = refl

insert-far : {A : Set} (t : Time) (v : A) {S : TimedObs (List A)}
  → AllAfter t S → insertBatch t v S ≡ (t , v ∷ []) ∷ S
insert-far t v aa[] = refl
insert-far t v (aa∷ {t = t₁} lt _)
  rewrite timeLt⇒timeEq-false t t₁ lt = refl

-- THE LATE DIAMOND: a subscriber that joined at instant n batches alone
-- before it existed and together with the source afterwards
late-diamond : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → batchSpec (mergeT xs (dropT n xs)) ≡ lateDiamondSpec n xs
late-diamond zero    xs m = diamond xs m
late-diamond (suc n) [] _ = refl
late-diamond (suc n) ((t , v) ∷ xs) m
  rewrite merge-pull-left-one t v xs (dropT n xs)
            (allAfter-headLeq (dropT-allAfter n xs (strictMono-allAfter m)))
  = trans (cong (insertBatch t v) (late-diamond n xs (mono-tail m)))
          (insert-far t v
            (lateDiamondSpec-allAfter n xs (strictMono-allAfter m)))

-- the counting version: totalNum RISES 1 → 2 when the subscriber joins ----------

lateMult : {A : Set} → ℕ → TimedObs A → Time → ℕ
lateMult n xs t = suc (countOf t (dropT n xs))

mono-headLtB : {A : Set} {t : Time} {v : A} {xs : TimedObs A}
  → StrictMono ((t , v) ∷ xs) → headLtB (t , v) xs ≡ true
mono-headLtB mono-one                     = refl
mono-headLtB (mono-∷ {y = (t₁ , w)} lt _) = lt

-- the fully-joined phase: every instant delivers two, counted from countOf
dbl-instants : {A : Set} (xs : TimedObs A) → StrictMono xs
  → Instants (λ t → suc (countOf t xs)) (mergeT xs xs)
dbl-instants [] _ = ins[]
dbl-instants ((t , v) ∷ xs) m
  rewrite merge-dup (t , v) xs (mono-headLtB m)
  = ins∷ meq
      (subst (Instants (λ t′ → suc (countOf t′ ((t , v) ∷ xs))))
             (sym (trans (dropRun-head-eq t v M) (dropRun-none t M rl0)))
             instantsM)
  where
  M : TimedObs _
  M = mergeT xs xs

  aaM : AllAfter t M
  aaM = merge-allAfter xs xs (strictMono-allAfter m) (strictMono-allAfter m)

  rl0 : runLength t M ≡ 0
  rl0 = runLength-allAfter0 M aaM

  meq : suc (countOf t ((t , v) ∷ xs)) ≡ suc (runLength t ((t , v) ∷ M))
  meq = cong suc
    (trans (countOf-head-eq t v xs)
    (trans (cong suc (countOf-allAfter0 xs (strictMono-allAfter m)))
           (sym (trans (runLength-head-eq t v M) (cong suc rl0)))))

  instantsM : Instants (λ t′ → suc (countOf t′ ((t , v) ∷ xs))) M
  instantsM = instants-ext-gt
    {m₁ = λ t′ → suc (countOf t′ xs)}
    {m₂ = λ t′ → suc (countOf t′ ((t , v) ∷ xs))} t M
    (λ t′ lt → cong suc
      (sym (countOf-skip {t = t} {t′ = t′} {v = v} xs
             (timeLt⇒timeEq-false-flip t t′ lt))))
    aaM
    (dbl-instants xs (mono-tail m))

late-instants : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → Instants (lateMult n xs) (mergeT xs (dropT n xs))
late-instants zero    xs m = dbl-instants xs m
late-instants (suc n) [] _ = ins[]
late-instants (suc n) ((t , v) ∷ xs) m
  rewrite merge-pull-left-one t v xs (dropT n xs)
            (allAfter-headLeq (dropT-allAfter n xs (strictMono-allAfter m)))
  = ins∷ meq
      (subst (Instants (lateMult (suc n) ((t , v) ∷ xs)))
             (sym (dropRun-none t M rl0))
             (late-instants n xs (mono-tail m)))
  where
  M : TimedObs _
  M = mergeT xs (dropT n xs)

  aaM : AllAfter t M
  aaM = merge-allAfter xs (dropT n xs) (strictMono-allAfter m)
          (dropT-allAfter n xs (strictMono-allAfter m))

  rl0 : runLength t M ≡ 0
  rl0 = runLength-allAfter0 M aaM

  meq : lateMult (suc n) ((t , v) ∷ xs) t ≡ suc (runLength t M)
  meq = cong suc
    (trans (countOf-allAfter0 (dropT n xs)
             (dropT-allAfter n xs (strictMono-allAfter m)))
           (sym rl0))

-- the closed tower for the late subscriber
count-late-diamond : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → batchCount (lateMult n xs) (mergeT xs (dropT n xs))
  ≡ lateDiamondSpec n xs
count-late-diamond n xs m =
  trans (batchCount-impl (lateMult n xs) (mergeT xs (dropT n xs))
          (late-instants n xs m))
 (trans (batchImpl-spec (mergeT xs (dropT n xs)))
        (late-diamond n xs m))
