-- A BRANCH THAT CLOSES EARLY, AND DYNAMIC MULTIPLICITIES.
--
-- merge(a, take n a): a diamond whose second branch closes after n values.
-- The law (the TS test "a taken branch of a diamond leaves the rest of the
-- diamond intact", [[1,1],[2]]):
--
--   batchSpec (mergeT xs (takeT n xs)) ≡ takeDiamondSpec n xs
--
-- — the first n instants batch doubled, every later instant batches alone.
--
-- The counting version closes roadmap item "dynamic multiplicities": the
-- memory's totalNum is 2 while both branches live and 1 after the take
-- closes. Because instants are distinct Times, a per-Time multiplicity
-- suffices: takeMult n xs t = 2 on taken instants, 1 afterwards — computed
-- from the stream, and proved truthful (take-instants), so the counting
-- mechanism satisfies the law end to end (count-take-diamond).
module TakeDiamond where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import BatchCount
open import Deep

-- the expected output: doubled for the first n instants, single after
takeDiamondSpec : {A : Set} → ℕ → TimedObs A → TimedObs (List A)
takeDiamondSpec zero    xs             = mapT (λ v → v ∷ []) xs
takeDiamondSpec (suc n) []             = []
takeDiamondSpec (suc n) ((t , v) ∷ xs) = (t , v ∷ v ∷ []) ∷ takeDiamondSpec n xs

-- small head-level facts -------------------------------------------------------

mono-headGt : {A : Set} {t : Time} {v : A} {xs : TimedObs A}
  → StrictMono ((t , v) ∷ xs) → HeadGtB t xs ≡ true
mono-headGt mono-one                        = refl
mono-headGt (mono-∷ {y = (t₁ , w)} lt _) = lt

mono-run0 : {A : Set} {t : Time} {v : A} {xs : TimedObs A}
  → StrictMono ((t , v) ∷ xs) → runLength t xs ≡ 0
mono-run0 mono-one = refl
mono-run0 {t = t} (mono-∷ {y = (t₁ , w)} lt _)
  rewrite timeLt⇒timeEq-false t t₁ lt = refl

-- a later-starting left argument lets a single right emission through
merge-pull-one : {A : Set} (t : Time) (v : A) (M R : TimedObs A)
  → HeadGtB t M ≡ true
  → mergeT M ((t , v) ∷ R) ≡ (t , v) ∷ mergeT M R
merge-pull-one t v []              R _  = refl
merge-pull-one t v ((t₁ , w) ∷ M′) R hg
  rewrite timeLt⇒timeLeq-flip-false t t₁ hg = refl

-- inserting the same value twice ahead of later batches makes a pair
insert-insert-far : {A : Set} (t : Time) (v : A) (S : TimedObs (List A))
  → HeadGtB t S ≡ true
  → insertBatch t v (insertBatch t v S) ≡ (t , v ∷ v ∷ []) ∷ S
insert-insert-far t v [] _ rewrite timeEq-refl t = refl
insert-insert-far t v ((s , g) ∷ rest) hg
  rewrite timeLt⇒timeEq-false t s hg | timeEq-refl t = refl

-- a strictly monotone stream batches into singletons
batchSpec-mono : {A : Set} (xs : TimedObs A) → StrictMono xs
  → batchSpec xs ≡ mapT (λ v → v ∷ []) xs
batchSpec-mono []                          _             = refl
batchSpec-mono ((t , v) ∷ [])              mono-one      = refl
batchSpec-mono ((t , v) ∷ (t₁ , w) ∷ xs) (mono-∷ lt m)
  rewrite batchSpec-mono ((t₁ , w) ∷ xs) m
        | timeLt⇒timeEq-false t t₁ lt
  = refl

headGt-takeDiamondSpec : {A : Set} (n : ℕ) {t : Time} {v : A}
  (xs : TimedObs A)
  → StrictMono ((t , v) ∷ xs)
  → HeadGtB t (takeDiamondSpec n xs) ≡ true
headGt-takeDiamondSpec zero    []             _             = refl
headGt-takeDiamondSpec (suc n) []             _             = refl
headGt-takeDiamondSpec zero    ((t₁ , w) ∷ _) (mono-∷ lt _) = lt
headGt-takeDiamondSpec (suc n) ((t₁ , w) ∷ _) (mono-∷ lt _) = lt

-- THE LAW: merge with a taken branch — doubled for n instants, single after
take-diamond : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → batchSpec (mergeT xs (takeT n xs)) ≡ takeDiamondSpec n xs
take-diamond zero xs m rewrite mergeT-idr xs = batchSpec-mono xs m
take-diamond (suc n) [] _ = refl
take-diamond (suc n) ((t , v) ∷ xs) m
  rewrite timeLeq-refl t
        | merge-pull-one t v xs (takeT n xs) (mono-headGt m)
        | take-diamond n xs (mono-tail m)
  = insert-insert-far t v (takeDiamondSpec n xs)
      (headGt-takeDiamondSpec n xs m)

-- the dynamic multiplicity ------------------------------------------------------

countOf : {A : Set} → Time → TimedObs A → ℕ
countOf t []              = 0
countOf t ((t′ , _) ∷ xs) =
  if timeEq t t′ then suc (countOf t xs) else countOf t xs

-- totalNum as a function of the instant: 2 while the taken branch lives
-- (its instants appear once in takeT n xs), 1 afterwards
takeMult : {A : Set} → ℕ → TimedObs A → Time → ℕ
takeMult n xs t = suc (countOf t (takeT n xs))

-- every emission strictly after a boundary ---------------------------------------

data AllAfter {A : Set} (t₀ : Time) : TimedObs A → Set where
  aa[] : AllAfter t₀ []
  aa∷  : {t : Time} {v : A} {xs : TimedObs A}
       → timeLt t₀ t ≡ true
       → AllAfter t₀ xs
       → AllAfter t₀ ((t , v) ∷ xs)

allAfter-weaken : {A : Set} {t₀ t₁ : Time} {xs : TimedObs A}
  → timeLt t₀ t₁ ≡ true → AllAfter t₁ xs → AllAfter t₀ xs
allAfter-weaken lt aa[] = aa[]
allAfter-weaken {t₀ = t₀} {t₁ = t₁} lt (aa∷ {t = t} lt′ a) =
  aa∷ (timeLt-trans t₀ t₁ t lt lt′) (allAfter-weaken lt a)

strictMono-allAfter : {A : Set} {t : Time} {v : A} {xs : TimedObs A}
  → StrictMono ((t , v) ∷ xs) → AllAfter t xs
strictMono-allAfter mono-one = aa[]
strictMono-allAfter (mono-∷ {y = (t₁ , w)} lt m) =
  aa∷ lt (allAfter-weaken lt (strictMono-allAfter m))

take-allAfter : {A : Set} {t₀ : Time} (n : ℕ) (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (takeT n xs)
take-allAfter zero    xs       _          = aa[]
take-allAfter (suc n) []       aa[]       = aa[]
take-allAfter (suc n) (x ∷ xs) (aa∷ lt a) = aa∷ lt (take-allAfter n xs a)

merge-allAfter : {A : Set} {t₀ : Time} (xs ys : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ ys → AllAfter t₀ (mergeT xs ys)
merge-allAfter []       ys aa[] ay   = ay
merge-allAfter (x ∷ xs) [] ax   aa[] = ax
merge-allAfter {A} {t₀} xss@((t₁ , v₁) ∷ xs) yss@((t₂ , v₂) ∷ ys)
               (aa∷ l₁ a₁) (aa∷ l₂ a₂) =
  if-elim (timeLeq t₁ t₂)
    (λ w → AllAfter t₀
             (if w then ((t₁ , v₁) ∷ mergeT xs yss)
                   else ((t₂ , v₂) ∷ mergeT xss ys)))
    (λ _ → aa∷ l₁ (merge-allAfter xs yss a₁ (aa∷ l₂ a₂)))
    (λ _ → aa∷ l₂ (merge-allAfter xss ys (aa∷ l₁ a₁) a₂))

countOf-allAfter0 : {A : Set} {t : Time} (xs : TimedObs A)
  → AllAfter t xs → countOf t xs ≡ 0
countOf-allAfter0 []                      aa[]       = refl
countOf-allAfter0 {t = t} ((t′ , v) ∷ xs) (aa∷ lt a)
  rewrite timeLt⇒timeEq-false t t′ lt = countOf-allAfter0 xs a

runLength-allAfter0 : {A : Set} {t : Time} (xs : TimedObs A)
  → AllAfter t xs → runLength t xs ≡ 0
runLength-allAfter0 []                      aa[]       = refl
runLength-allAfter0 {t = t} ((t′ , v) ∷ xs) (aa∷ lt _)
  rewrite timeLt⇒timeEq-false t t′ lt = refl

-- Instants only reads mult at the stream's times: multiplicities may be
-- swapped wherever they agree beyond a bound below the whole stream
instants-ext-gt : {A : Set} {m₁ m₂ : Time → ℕ} (t₀ : Time) (zs : TimedObs A)
  → ((t : Time) → timeLt t₀ t ≡ true → m₁ t ≡ m₂ t)
  → AllAfter t₀ zs
  → Instants m₁ zs → Instants m₂ zs
instants-ext-gt t₀ [] agree aa[] ins[] = ins[]
instants-ext-gt t₀ ((t , v) ∷ xs) agree (aa∷ lt a) (ins∷ meq H) =
  ins∷ (trans (sym (agree t lt)) meq)
       (instants-ext-gt t₀ (dropRun t xs) agree (allAfter-dropRun t xs a) H)
  where
  allAfter-dropRun : {A : Set} {t₀ : Time} (t : Time) (xs : TimedObs A)
    → AllAfter t₀ xs → AllAfter t₀ (dropRun t xs)
  allAfter-dropRun t []              aa[]        = aa[]
  allAfter-dropRun t ((t′ , w) ∷ xs) (aa∷ lt′ a′) with timeEq t t′
  ... | true  = allAfter-dropRun t xs a′
  ... | false = aa∷ lt′ a′

-- helper equalities ------------------------------------------------------------

countOf-head-eq : {A : Set} (t : Time) (v : A) (xs : TimedObs A)
  → countOf t ((t , v) ∷ xs) ≡ suc (countOf t xs)
countOf-head-eq t v xs rewrite timeEq-refl t = refl

countOf-skip : {A : Set} {t t′ : Time} {v : A} (xs : TimedObs A)
  → timeEq t′ t ≡ false → countOf t′ ((t , v) ∷ xs) ≡ countOf t′ xs
countOf-skip xs ne rewrite ne = refl

runLength-head-eq : {A : Set} (t : Time) (v : A) (xs : TimedObs A)
  → runLength t ((t , v) ∷ xs) ≡ suc (runLength t xs)
runLength-head-eq t v xs rewrite timeEq-refl t = refl

dropRun-head-eq : {A : Set} (t : Time) (v : A) (xs : TimedObs A)
  → dropRun t ((t , v) ∷ xs) ≡ dropRun t xs
dropRun-head-eq t v xs rewrite timeEq-refl t = refl

-- THE INVARIANT IS TRUTHFUL: takeMult reports every instant's real delivery
-- count on the merged stream — 2 while the take lives, 1 after
take-instants : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → Instants (takeMult n xs) (mergeT xs (takeT n xs))
take-instants zero xs m rewrite mergeT-idr xs = mono-instants xs m
  where
  mono-instants : {A : Set} (xs : TimedObs A) → StrictMono xs
    → Instants (λ _ → 1) xs
  mono-instants []             _ = ins[]
  mono-instants ((t , v) ∷ xs) m =
    ins∷ (cong suc (sym (mono-run0 m)))
         (subst (Instants (λ _ → 1))
                (sym (dropRun-none t xs (mono-run0 m)))
                (mono-instants xs (mono-tail m)))
take-instants (suc n) [] _ = ins[]
take-instants {A} (suc n) ((t , v) ∷ xs) m
  rewrite timeLeq-refl t
        | merge-pull-one t v xs (takeT n xs) (mono-headGt m)
  = ins∷ meq
      (subst (Instants (takeMult (suc n) ((t , v) ∷ xs)))
             (sym (trans (dropRun-head-eq t v M) (dropRun-none t M rl0)))
             instantsM)
  where
  M : TimedObs A
  M = mergeT xs (takeT n xs)

  aaM : AllAfter t M
  aaM = merge-allAfter xs (takeT n xs) (strictMono-allAfter m)
          (take-allAfter n xs (strictMono-allAfter m))

  rl0 : runLength t M ≡ 0
  rl0 = runLength-allAfter0 M aaM

  meq : takeMult (suc n) ((t , v) ∷ xs) t ≡ suc (runLength t ((t , v) ∷ M))
  meq = cong suc
    (trans (countOf-head-eq t v (takeT n xs))
    (trans (cong suc (countOf-allAfter0 (takeT n xs)
             (take-allAfter n xs (strictMono-allAfter m))))
           (sym (trans (runLength-head-eq t v M) (cong suc rl0)))))

  instantsM : Instants (takeMult (suc n) ((t , v) ∷ xs)) M
  instantsM = instants-ext-gt
    {m₁ = takeMult n xs} {m₂ = takeMult (suc n) ((t , v) ∷ xs)} t M
    (λ t′ lt → cong suc
      (sym (countOf-skip {t = t} {t′ = t′} {v = v} (takeT n xs)
             (timeLt⇒timeEq-false-flip t t′ lt))))
    aaM
    (take-instants n xs (mono-tail m))

-- THE CLOSED LAW WITH DYNAMIC MULTIPLICITIES: the counting mechanism, with
-- totalNum = 2 on taken instants and 1 afterwards, computes the take-diamond
count-take-diamond : {A : Set} (n : ℕ) (xs : TimedObs A) → StrictMono xs
  → batchCount (takeMult n xs) (mergeT xs (takeT n xs))
  ≡ takeDiamondSpec n xs
count-take-diamond n xs m =
  trans (batchCount-impl (takeMult n xs) (mergeT xs (takeT n xs))
          (take-instants n xs m))
 (trans (batchImpl-spec (mergeT xs (takeT n xs)))
        (take-diamond n xs m))
