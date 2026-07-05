-- INDEPENDENT DIAMONDS DON'T INTERFERE.
--
-- The origin discipline earns its keep: streams whose origins differ can
-- never share an instant, so batching distributes over their merge —
--
--   batchSpec (mergeT xs ys) ≡ mergeT (batchSpec xs) (batchSpec ys)
--
-- and therefore a merge of two arbitrary-depth diamonds over DIFFERENT
-- sources batches each diamond independently (indep-diamonds): the
-- machine-checked generalization of the TS test "keeps two independent
-- sources in separate batches".
module Indep where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Obs
open import Exp
open import Deep

-- every emission of the stream carries this origin
data OriginIs {A : Set} (i : ℕ) : TimedObs A → Set where
  oi[] : OriginIs i []
  oi∷  : {k : ℕ} {v : A} {xs : TimedObs A}
       → OriginIs i xs
       → OriginIs i (((k , i) , v) ∷ xs)

-- the head of an insertBatch is always the inserted time
headGt-insert : {A : Set} (t′ t : Time) (v : A) (S : TimedObs (List A))
  → HeadGtB t′ (insertBatch t v S) ≡ timeLt t′ t
headGt-insert t′ t v [] = refl
headGt-insert t′ t v ((s , g) ∷ rest) with timeEq t s
... | true  = refl
... | false = refl

-- inserting at a time strictly before everything in S₂ commutes with the
-- merge, landing in the left argument (head-level fact, no recursion)
insert-merge-left : {A : Set} (t₁ : Time) (v₁ : A)
                    (S₁ S₂ : TimedObs (List A))
  → HeadGtB t₁ S₂ ≡ true
  → insertBatch t₁ v₁ (mergeT S₁ S₂)
  ≡ mergeT (insertBatch t₁ v₁ S₁) S₂
insert-merge-left t₁ v₁ [] [] _ = refl
insert-merge-left t₁ v₁ [] ((s₂ , h) ∷ S₂′) hg
  rewrite timeLt⇒timeEq-false t₁ s₂ hg | timeLt⇒timeLeq t₁ s₂ hg = refl
insert-merge-left t₁ v₁ ((s , g) ∷ S₁′) [] _
  rewrite mergeT-idr (insertBatch t₁ v₁ ((s , g) ∷ S₁′)) = refl
insert-merge-left t₁ v₁ ((s , g) ∷ S₁′) ((s₂ , h) ∷ S₂′) hg
  with timeEq t₁ s in e
... | true
  rewrite subst (λ z → timeLeq z s₂ ≡ true) (timeEq-sound t₁ s e)
            (timeLt⇒timeLeq t₁ s₂ hg)
        | e
        | timeLt⇒timeLeq t₁ s₂ hg
  = refl
... | false with timeLeq s s₂ in e2
...   | true  rewrite e | timeLt⇒timeLeq t₁ s₂ hg | e2 = refl
...   | false
  rewrite timeLt⇒timeEq-false t₁ s₂ hg
        | timeLt⇒timeLeq t₁ s₂ hg
        | e2
  = refl

-- inserting at a time strictly before everything in S₁ commutes with the
-- merge, landing in the right argument
insert-merge-right : {A : Set} (t₂ : Time) (v₂ : A)
                     (S₁ S₂ : TimedObs (List A))
  → HeadGtB t₂ S₁ ≡ true
  → insertBatch t₂ v₂ (mergeT S₁ S₂)
  ≡ mergeT S₁ (insertBatch t₂ v₂ S₂)
insert-merge-right t₂ v₂ [] S₂ _ = refl
insert-merge-right t₂ v₂ ((s₁ , g) ∷ S₁′) [] hg
  rewrite timeLt⇒timeEq-false t₂ s₁ hg
        | timeLt⇒timeLeq-flip-false t₂ s₁ hg
  = refl
insert-merge-right t₂ v₂ ((s₁ , g) ∷ S₁′) ((s₂ , h) ∷ S₂′) hg
  with timeLeq s₁ s₂ in e2
... | true
  rewrite timeLt⇒timeEq-false t₂ s₁ hg
        | timeLt⇒timeEq-false t₂ s₂ (timeLt-leq-trans t₂ s₁ s₂ hg e2)
        | timeLt⇒timeLeq-flip-false t₂ s₁ hg
        | e2
  = refl
... | false with timeEq t₂ s₂
...   | true  rewrite timeLt⇒timeLeq-flip-false t₂ s₁ hg = refl
...   | false rewrite timeLt⇒timeLeq-flip-false t₂ s₁ hg | e2 = refl

-- THE DISTRIBUTION THEOREM: batching commutes with merging streams of
-- distinct origins — independent sources batch independently
batch-merge-indep : {A : Set} (i j : ℕ) (xs ys : TimedObs A)
  → eqℕ i j ≡ false
  → OriginIs i xs → OriginIs j ys
  → batchSpec (mergeT xs ys) ≡ mergeT (batchSpec xs) (batchSpec ys)
batch-merge-indep i j [] ys ne oi[] oy = refl
batch-merge-indep i j (x ∷ xs) [] ne ox oi[] =
  sym (mergeT-idr (batchSpec (x ∷ xs)))
batch-merge-indep i j (((k₁ , .i) , v₁) ∷ xs) (((k₂ , .j) , v₂) ∷ ys)
                  ne (oi∷ ox) (oi∷ oy) =
  if-elim (timeLeq (k₁ , i) (k₂ , j))
    (λ w → batchSpec
             (if w then (((k₁ , i) , v₁) ∷ mergeT xs (((k₂ , j) , v₂) ∷ ys))
                   else (((k₂ , j) , v₂) ∷ mergeT (((k₁ , i) , v₁) ∷ xs) ys))
         ≡ mergeT (batchSpec (((k₁ , i) , v₁) ∷ xs))
                  (batchSpec (((k₂ , j) , v₂) ∷ ys)))
    (λ cmp →
      trans (cong (insertBatch (k₁ , i) v₁)
              (batch-merge-indep i j xs (((k₂ , j) , v₂) ∷ ys) ne ox (oi∷ oy)))
            (insert-merge-left (k₁ , i) v₁ (batchSpec xs)
              (batchSpec (((k₂ , j) , v₂) ∷ ys))
              (trans (headGt-insert (k₁ , i) (k₂ , j) v₂ (batchSpec ys))
                     (timeLeq-neq⇒timeLt (k₁ , i) (k₂ , j) cmp
                       (neq-origins k₁ k₂ i j ne)))))
    (λ cmp →
      trans (cong (insertBatch (k₂ , j) v₂)
              (batch-merge-indep i j (((k₁ , i) , v₁) ∷ xs) ys ne (oi∷ ox) oy))
            (insert-merge-right (k₂ , j) v₂
              (batchSpec (((k₁ , i) , v₁) ∷ xs)) (batchSpec ys)
              (trans (headGt-insert (k₂ , j) (k₁ , i) v₁ (batchSpec xs))
                     (timeLeq-false⇒timeLt-flip (k₁ , i) (k₂ , j) cmp))))

-- expansion preserves origins -------------------------------------------------

++-origins : {A : Set} {i : ℕ} {xs ys : TimedObs A}
  → OriginIs i xs → OriginIs i ys → OriginIs i (xs ++ ys)
++-origins oi[]     oy = oy
++-origins (oi∷ ox) oy = oi∷ (++-origins ox oy)

block-origins : {A B : Set} {i : ℕ} (k : ℕ) (v : A) (fs : List (A → B))
  → OriginIs i (map (λ f → ((k , i) , f v)) fs)
block-origins k v []       = oi[]
block-origins k v (f ∷ fs) = oi∷ (block-origins k v fs)

expand-origins : {A B : Set} {i : ℕ} (fs : List (A → B)) (xs : TimedObs A)
  → OriginIs i xs → OriginIs i (expand fs xs)
expand-origins fs []                      oi[]     = oi[]
expand-origins fs (((k , i) , v) ∷ xs) (oi∷ ox) =
  ++-origins (block-origins k v fs) (expand-origins fs xs ox)

-- THE THEOREM: a merge of two arbitrary-depth diamonds over different
-- sources batches each diamond independently — no cross-talk, ever
indep-diamonds : (i j : ℕ) (a b : Exp) (env : Env)
  → eqℕ i j ≡ false
  → DiamondOver i a → DiamondOver j b
  → OriginIs i (emits (env i)) → OriginIs j (emits (env j))
  → StrictMono (emits (env i)) → StrictMono (emits (env j))
  → batchSpec (emits (⟦ mergeE a b ⟧ env))
  ≡ mergeT (mapT (applyAll (funs a)) (emits (env i)))
           (mapT (applyAll (funs b)) (emits (env j)))
indep-diamonds i j a b env ne da db oxi oxj mi mj =
  trans (cong batchSpec
          (cong₂ mergeT (expand-denote i a env da mi)
                        (expand-denote j b env db mj)))
 (trans (batch-merge-indep i j
          (expand (funs a) (emits (env i)))
          (expand (funs b) (emits (env j)))
          ne
          (expand-origins (funs a) (emits (env i)) oxi)
          (expand-origins (funs b) (emits (env j)) oxj))
        (cong₂ mergeT
          (batch-expand′ (funs a) (emits (env i)) (funs-ne da) mi)
          (batch-expand′ (funs b) (emits (env j)) (funs-ne db) mj)))
