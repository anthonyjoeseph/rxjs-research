-- DYNAMIC INNER ARRIVAL: subscribers that join over time.
--
-- The time-reversed dual of TakeDeep: there, leaves carried HORIZONS and
-- died as takes expired; here, leaves carry DELAYS and are born as
-- subscribers join (a hot stream subscribed by each trigger of a join —
-- mergeAll(map(v => x))). The normal form expandD emits, per instant, the
-- values of the already-born leaves, and the theorem
--
--   grow-diamond : batchSpec (mergeList (xs ∷ map (λ n → dropT n xs) ns))
--                ≡ specD ((id , 0) ∷ map (λ n → (id , n)) ns) xs
--
-- says a stream merged with ANY family of late subscriptions batches one
-- batch per instant whose multiplicity GROWS as subscribers arrive. The
-- single-subscriber instance recovers Share's late-diamond spec.
module Grow where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Deep
open import MergeMap
open import TakeDiamond
open import TakeDeep
open import Share
open import Derived

-- delays: a leaf is born when its delay reaches zero
activeD : ℕ → Bool
activeD zero    = true
activeD (suc _) = false

tickD : ℕ → ℕ
tickD zero    = zero
tickD (suc n) = n

DFn : Set → Set → Set
DFn A B = (A → B) × ℕ

applyD : {A B : Set} → List (DFn A B) → A → List B
applyD []             v = []
applyD ((f , d) ∷ fs) v =
  if activeD d then (f v ∷ applyD fs v) else applyD fs v

tickAllD : {A B : Set} → List (DFn A B) → List (DFn A B)
tickAllD = map (λ fd → (fst fd , tickD (snd fd)))

expandD : {A B : Set} → List (DFn A B) → TimedObs A → TimedObs B
expandD fs []             = []
expandD fs ((t , v) ∷ xs) =
  map (λ w → (t , w)) (applyD fs v) ++ expandD (tickAllD fs) xs

specD : {A B : Set} → List (DFn A B) → TimedObs A → TimedObs (List B)
specD fs []             = []
specD fs ((t , v) ∷ xs) =
  prependBatch t (applyD fs v) (specD (tickAllD fs) xs)

-- normal forms ------------------------------------------------------------------

expandD-nil : {A B : Set} (xs : TimedObs A)
  → expandD {A} {B} [] xs ≡ []
expandD-nil []             = refl
expandD-nil ((t , v) ∷ xs) = expandD-nil xs

expandD-id : {A : Set} (xs : TimedObs A)
  → expandD (((λ v → v) , 0) ∷ []) xs ≡ xs
expandD-id []             = refl
expandD-id ((t , v) ∷ xs) = cong (_∷_ (t , v)) (expandD-id xs)

drop-expandD : {A : Set} (n : ℕ) (xs : TimedObs A)
  → dropT n xs ≡ expandD (((λ v → v) , n) ∷ []) xs
drop-expandD zero    xs             = sym (expandD-id xs)
drop-expandD (suc n) []             = refl
drop-expandD (suc n) ((t , v) ∷ xs) = drop-expandD n xs

-- merging expansions fuses the leaf lists (mirror of TakeDeep) ------------------

applyD-++ : {A B : Set} (fs ks : List (DFn A B)) (v : A)
  → applyD (fs ++ ks) v ≡ applyD fs v ++ applyD ks v
applyD-++ []             ks v = refl
applyD-++ ((f , d) ∷ fs) ks v with activeD d
... | true  = cong (_∷_ (f v)) (applyD-++ fs ks v)
... | false = applyD-++ fs ks v

tickAllD-++ : {A B : Set} (fs ks : List (DFn A B))
  → tickAllD (fs ++ ks) ≡ tickAllD fs ++ tickAllD ks
tickAllD-++ = map-++ (λ fd → (fst fd , tickD (snd fd)))

expandD-allAfter : {A B : Set} {t₀ : Time} (fs : List (DFn A B))
  (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (expandD fs xs)
expandD-allAfter fs []             aa[]       = aa[]
expandD-allAfter fs ((t , v) ∷ xs) (aa∷ lt a) =
  allAfter-++ (allAfter-vals-block lt (applyD fs v))
              (expandD-allAfter (tickAllD fs) xs a)

expandD-split : {A B : Set} (fs ks : List (DFn A B)) (t : Time) (v : A)
  (xs : TimedObs A)
  → expandD (fs ++ ks) ((t , v) ∷ xs)
  ≡ map (λ w → (t , w)) (applyD fs v)
    ++ (map (λ w → (t , w)) (applyD ks v)
        ++ expandD (tickAllD fs ++ tickAllD ks) xs)
expandD-split fs ks t v xs =
  trans (cong₂ (λ a b → map (λ w → (t , w)) a ++ expandD b xs)
          (applyD-++ fs ks v) (tickAllD-++ fs ks))
 (trans (cong (_++ expandD (tickAllD fs ++ tickAllD ks) xs)
          (map-++ (λ w → (t , w)) (applyD fs v) (applyD ks v)))
        (++-assoc (map (λ w → (t , w)) (applyD fs v))
                  (map (λ w → (t , w)) (applyD ks v))
                  (expandD (tickAllD fs ++ tickAllD ks) xs)))

merge-expandD : {A B : Set} (fs ks : List (DFn A B)) (xs : TimedObs A)
  → StrictMono xs
  → mergeT (expandD fs xs) (expandD ks xs) ≡ expandD (fs ++ ks) xs
merge-expandD fs ks [] _ = refl
merge-expandD fs ks ((t , v) ∷ xs) m =
  trans (pull-left-vals t (applyD fs v) (expandD (tickAllD fs) xs)
          (expandD ks ((t , v) ∷ xs))
          (headLeq-vals-++ t (applyD ks v) (expandD (tickAllD ks) xs)
            (expandD-allAfter (tickAllD ks) xs (strictMono-allAfter m))))
 (trans (cong (_++_ (map (λ w → (t , w)) (applyD fs v)))
          (pull-right-vals t (applyD ks v) (expandD (tickAllD fs) xs)
            (expandD (tickAllD ks) xs)
            (allAfter-headGt (expandD-allAfter (tickAllD fs) xs
              (strictMono-allAfter m)))))
 (trans (cong (λ z → map (λ w → (t , w)) (applyD fs v)
                     ++ (map (λ w → (t , w)) (applyD ks v) ++ z))
          (merge-expandD (tickAllD fs) (tickAllD ks) xs (mono-tail m)))
        (sym (expandD-split fs ks t v xs))))

-- batching an expansion: one batch per instant with born leaves ------------------

specD-allAfter : {A B : Set} {t₀ : Time} (fs : List (DFn A B))
  (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (specD fs xs)
specD-allAfter fs []             aa[]       = aa[]
specD-allAfter fs ((t , v) ∷ xs) (aa∷ lt a) with applyD fs v
... | []       = specD-allAfter (tickAllD fs) xs a
... | (w ∷ ws) = aa∷ lt (specD-allAfter (tickAllD fs) xs a)

batch-expandD : {A B : Set} (fs : List (DFn A B)) (xs : TimedObs A)
  → StrictMono xs
  → batchSpec (expandD fs xs) ≡ specD fs xs
batch-expandD fs [] _ = refl
batch-expandD fs ((t , v) ∷ xs) m with applyD fs v
... | []       = batch-expandD (tickAllD fs) xs (mono-tail m)
... | (w ∷ ws) =
  trans (batch-cons-block t w ws (expandD (tickAllD fs) xs))
 (trans (cong (joinHead t (w ∷ ws))
          (batch-expandD (tickAllD fs) xs (mono-tail m)))
        (join-far-allAfter t (w ∷ ws)
          (specD-allAfter (tickAllD fs) xs (strictMono-allAfter m))))

-- THE GROW DIAMOND ---------------------------------------------------------------

mergeList-expandD : {A : Set} (dss : List (List (DFn A A))) (xs : TimedObs A)
  → StrictMono xs
  → mergeList (map (λ ds → expandD ds xs) dss)
  ≡ expandD (concatMap (λ z → z) dss) xs
mergeList-expandD []         xs m = sym (expandD-nil xs)
mergeList-expandD (ds ∷ dss) xs m =
  trans (cong (mergeT (expandD ds xs)) (mergeList-expandD dss xs m))
        (merge-expandD ds (concatMap (λ z → z) dss) xs m)

concat-singles : {X : Set} (mk : ℕ → X) (ns : List ℕ)
  → concatMap (λ z → z) (map (λ n → mk n ∷ []) ns) ≡ map mk ns
concat-singles mk []       = refl
concat-singles mk (n ∷ ns) = cong (_∷_ (mk n)) (concat-singles mk ns)

-- a stream merged with any family of late subscriptions (join points ns)
-- batches per instant with multiplicity growing as subscribers arrive
grow-diamond : {A : Set} (ns : List ℕ) (xs : TimedObs A)
  → StrictMono xs
  → batchSpec (mergeList (xs ∷ map (λ n → dropT n xs) ns))
  ≡ specD (((λ v → v) , 0) ∷ map (λ n → ((λ v → v) , n)) ns) xs
grow-diamond ns xs m =
  trans (cong batchSpec
          (trans (cong mergeList
            (cong₂ _∷_ (sym (expandD-id xs))
              (trans (map-ext (λ n → drop-expandD n xs) ns)
                     (sym (map-map (λ ds → expandD ds xs)
                            (λ n → ((λ v → v) , n) ∷ []) ns)))))
          (mergeList-expandD
            ((((λ v → v) , 0) ∷ []) ∷ map (λ n → ((λ v → v) , n) ∷ []) ns)
            xs m)))
 (trans (cong (λ z → batchSpec (expandD (((λ v → v) , 0) ∷ z) xs))
          (concat-singles (λ n → ((λ v → v) , n)) ns))
        (batch-expandD (((λ v → v) , 0) ∷ map (λ n → ((λ v → v) , n)) ns)
          xs m))

-- the single-subscriber instance recovers Share's late diamond
specD-late : {A : Set} (n : ℕ) (xs : TimedObs A)
  → specD (((λ v → v) , 0) ∷ ((λ v → v) , n) ∷ []) xs
  ≡ lateDiamondSpec n xs
specD-late zero    []             = refl
specD-late (suc n) []             = refl
specD-late zero    ((t , v) ∷ xs) =
  cong (_∷_ (t , v ∷ v ∷ [])) (specD-late zero xs)
specD-late (suc n) ((t , v) ∷ xs) =
  cong (_∷_ (t , v ∷ [])) (specD-late n xs)
