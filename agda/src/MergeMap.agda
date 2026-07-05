-- THE ASYNC HALF OF THE BLESSED CAUSAL-BATCHING SEMANTICS (option 1).
--
-- An inner spawned by an async trigger inherits the trigger's instant: its
-- values are simultaneous with the event that caused them. Denotationally,
-- mergeMap over an async source is a time-preserving bind — each source
-- emission (t , v) becomes the block [(t , w) | w ∈ inner(v)] — and the
-- mergeMap-diamond law follows:
--
--   batchSpec (mergeT xs (bindT g gs xs)) ≡ mapT (λ v → v ∷ g v ∷ gs v) xs
--
-- merge(a, a.mergeMap(v → of(g v , …gs v))) yields ONE batch per source
-- instant: the trigger's value followed by all the inner's values (the TS
-- test [5, 50, 500], as a law). The inner is split as head g v + tail gs v
-- so per-instant non-emptiness is structural.
--
-- (The sync half needs no new theorem: a sync-burst-triggered inner is a
-- fresh root cause — semantically just another `of` — governed by the
-- existing origin-discipline results (of-batch, batch-merge-indep).)
module MergeMap where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Deep
open import TakeDiamond

-- the time-preserving bind: option 1's async inheritance
bindT : {A B : Set} → (A → B) → (A → List B) → TimedObs A → TimedObs B
bindT g gs [] = []
bindT g gs ((t , v) ∷ xs) =
  (t , g v) ∷ (map (λ w → (t , w)) (gs v) ++ bindT g gs xs)

-- block pulling for plain value blocks
pull-right-vals : {A : Set} (t : Time) (ws : List A) (M R : TimedObs A)
  → HeadGtB t M ≡ true
  → mergeT M (map (λ w → (t , w)) ws ++ R)
  ≡ map (λ w → (t , w)) ws ++ mergeT M R
pull-right-vals t []       M               R _  = refl
pull-right-vals t (w ∷ ws) []              R _  = refl
pull-right-vals t (w ∷ ws) ((tm , u) ∷ ms) R hg
  rewrite timeLt⇒timeLeq-flip-false t tm hg =
  cong (_∷_ (t , w)) (pull-right-vals t ws ((tm , u) ∷ ms) R hg)

-- fusing a source with its own bound inners: per instant, the trigger's
-- value followed by the inner's values (stability: source branch is left)
merge-bind : {A : Set} (g : A → A) (gs : A → List A) (xs : TimedObs A)
  → StrictMono xs
  → mergeT xs (bindT g gs xs) ≡ bindT (λ v → v) (λ v → g v ∷ gs v) xs
merge-bind g gs [] _ = refl
merge-bind g gs ((t , v) ∷ xs) m
  rewrite timeLeq-refl t
        | merge-pull-one t (g v) xs
            (map (λ w → (t , w)) (gs v) ++ bindT g gs xs) (mono-headGt m)
        | pull-right-vals t (gs v) xs (bindT g gs xs) (mono-headGt m)
        | merge-bind g gs xs (mono-tail m)
  = refl

-- batching one instant's block joins all its values into one group
batch-cons-block : {A : Set} (t : Time) (x : A) (ws : List A)
                   (rest : TimedObs A)
  → batchSpec ((t , x) ∷ (map (λ w → (t , w)) ws ++ rest))
  ≡ joinHead t (x ∷ ws) (batchSpec rest)
batch-cons-block t x []       rest = insert-join t x (batchSpec rest)
batch-cons-block t x (w ∷ ws) rest =
  trans (cong (insertBatch t x) (batch-cons-block t w ws rest))
        (insert-into-join t x (w ∷ ws) (batchSpec rest))

-- batching a bound stream: exactly one batch per source instant
batch-bind : {A B : Set} (g : A → B) (gs : A → List B) (xs : TimedObs A)
  → StrictMono xs
  → batchSpec (bindT g gs xs) ≡ mapT (λ v → g v ∷ gs v) xs
batch-bind g gs []             _        = refl
batch-bind g gs ((t , v) ∷ []) mono-one = batch-cons-block t (g v) (gs v) []
batch-bind g gs ((t , v) ∷ (t₁ , w) ∷ xs) (mono-∷ lt m) =
  trans (batch-cons-block t (g v) (gs v) (bindT g gs ((t₁ , w) ∷ xs)))
 (trans (cong (joinHead t (g v ∷ gs v))
          (batch-bind g gs ((t₁ , w) ∷ xs) m))
        (join-far t t₁ (g v ∷ gs v) (g w ∷ gs w)
          (mapT (λ u → g u ∷ gs u) xs) (timeLt⇒timeEq-false t t₁ lt)))

-- THE MERGEMAP-DIAMOND: an async-triggered inner is simultaneous with its
-- trigger — merge(a, mergeMap(inner)(a)) batches [v , inner v …] per instant
mergeMap-diamond : {A : Set} (g : A → A) (gs : A → List A) (xs : TimedObs A)
  → StrictMono xs
  → batchSpec (mergeT xs (bindT g gs xs)) ≡ mapT (λ v → v ∷ g v ∷ gs v) xs
mergeMap-diamond g gs xs m =
  trans (cong batchSpec (merge-bind g gs xs m))
        (batch-bind (λ v → v) (λ v → g v ∷ gs v) xs m)

-- and the implementation port satisfies it
impl-mergeMap-diamond : {A : Set} (g : A → A) (gs : A → List A)
                        (xs : TimedObs A)
  → StrictMono xs
  → batchImpl (mergeT xs (bindT g gs xs)) ≡ mapT (λ v → v ∷ g v ∷ gs v) xs
impl-mergeMap-diamond g gs xs m =
  trans (batchImpl-spec (mergeT xs (bindT g gs xs)))
        (mergeMap-diamond g gs xs m)
