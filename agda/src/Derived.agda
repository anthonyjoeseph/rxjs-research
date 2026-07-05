-- THE JOIN AS THE PRIMITIVE, THE COMBINATORS AS THEOREMS.
--
-- The canonical primitive set makes mergeAll primitive and merge/mergeMap
-- derived: merge(a,b) = mergeAll(of(a,b)), mergeMap(f) = mergeAll ∘ map(f).
-- Here the second sort (stream-of-streams expressions) gets a denotation of
-- its own, and the derivations become machine-checked theorems:
--
--   merge-derived    : ⟦ mergeAll (ofS [a, b]) ⟧ ≡ mergeT ⟦a⟧ ⟦b⟧
--   mergeMap-derived : ⟦ mergeAll (mapS g gs e) ⟧ ≡ bindT g gs ⟦e⟧
--
-- (the latter on async-only triggers — a sync-burst trigger's inner is a
-- fresh root cause, handled by the origin-supply in bindTSplit, exactly the
-- oracle's rule). Every batch-shape theorem then transfers to the primitive
-- forms by composition.
module Derived where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Obs
open import Exp
open import Deep
open import MergeMap

-- the second sort: stream-of-streams expressions
data ExpS : Set where
  ofS  : List Exp → ExpS                              -- a sync burst of inners
  mapS : (Val → Val) → (Val → List Val) → Exp → ExpS  -- inners from triggers

-- merging a subscription burst of inners, in subscription order
mergeList : {A : Set} → List (TimedObs A) → TimedObs A
mergeList []         = []
mergeList (xs ∷ xss) = mergeT xs (mergeList xss)

-- the blessed rule with its origin supply: an async trigger's inner
-- inherits the trigger's instant; a sync-burst trigger's inner is a fresh
-- root cause at tick 0
bindTSplit : (Val → Val) → (Val → List Val) → ℕ → TimedObs Val → TimedObs Val
bindTSplit g gs o [] = []
bindTSplit g gs o (((zero , o′) , v) ∷ xs) =
  map (λ w → ((0 , o) , w)) (g v ∷ gs v) ++ bindTSplit g gs (suc o) xs
bindTSplit g gs o (((suc k , o′) , v) ∷ xs) =
  ((suc k , o′) , g v)
    ∷ (map (λ w → ((suc k , o′) , w)) (gs v) ++ bindTSplit g gs o xs)

-- the join's denotation
mergeAllD : ExpS → Env → TimedObs Val
mergeAllD (ofS es)       env = mergeList (map (λ e → emits (⟦ e ⟧ env)) es)
mergeAllD (mapS g gs e)  env = bindTSplit g gs 0 (emits (⟦ e ⟧ env))

-- THEOREM: binary merge is the two-element burst
merge-derived : (a b : Exp) (env : Env)
  → mergeAllD (ofS (a ∷ b ∷ [])) env
  ≡ mergeT (emits (⟦ a ⟧ env)) (emits (⟦ b ⟧ env))
merge-derived a b env =
  cong (mergeT (emits (⟦ a ⟧ env))) (mergeT-idr (emits (⟦ b ⟧ env)))

-- every emission is an async instant (tick ≥ 1): the shape of every
-- source-derived stream, where no origin supply is ever consumed
data AsyncOnly {A : Set} : TimedObs A → Set where
  ao[] : AsyncOnly []
  ao∷  : {k o : ℕ} {v : A} {xs : TimedObs A}
       → AsyncOnly xs
       → AsyncOnly (((suc k , o) , v) ∷ xs)

-- THEOREM: on async triggers, the join over mapped inners is exactly the
-- time-preserving bind — mergeMap = mergeAll ∘ map
bindTSplit-async : (g : Val → Val) (gs : Val → List Val) (o : ℕ)
  (xs : TimedObs Val)
  → AsyncOnly xs
  → bindTSplit g gs o xs ≡ bindT g gs xs
bindTSplit-async g gs o [] ao[] = refl
bindTSplit-async g gs o (((suc k , o′) , v) ∷ xs) (ao∷ a) =
  cong
    (λ z →
      ((suc k , o′) , g v)
        ∷ (map (λ w → ((suc k , o′) , w)) (gs v) ++ z))
    (bindTSplit-async g gs o xs a)

mergeMap-derived : (g : Val → Val) (gs : Val → List Val) (e : Exp) (env : Env)
  → AsyncOnly (emits (⟦ e ⟧ env))
  → mergeAllD (mapS g gs e) env ≡ bindT g gs (emits (⟦ e ⟧ env))
mergeMap-derived g gs e env ao =
  bindTSplit-async g gs 0 (emits (⟦ e ⟧ env)) ao

-- the batch-shape theorems transfer to the primitive forms ----------------------

-- the diamond, stated on the join primitive: mergeAll(of(e, e))
mergeAll-of-diamond : (e : Exp) (env : Env)
  → StrictMono (emits (⟦ e ⟧ env))
  → batchSpec (mergeAllD (ofS (e ∷ e ∷ [])) env)
  ≡ mapT dbl (emits (⟦ e ⟧ env))
mergeAll-of-diamond e env m =
  trans (cong batchSpec (merge-derived e e env))
        (diamond (emits (⟦ e ⟧ env)) m)

-- the mergeMap-diamond, stated on the join primitive: the inner of every
-- async trigger batches with it
mergeAll-map-diamond : (g : Val → Val) (gs : Val → List Val)
  (e : Exp) (env : Env)
  → AsyncOnly (emits (⟦ e ⟧ env))
  → StrictMono (emits (⟦ e ⟧ env))
  → batchSpec (mergeT (emits (⟦ e ⟧ env)) (mergeAllD (mapS g gs e) env))
  ≡ mapT (λ v → v ∷ g v ∷ gs v) (emits (⟦ e ⟧ env))
mergeAll-map-diamond g gs e env ao m =
  trans (cong (λ z → batchSpec (mergeT (emits (⟦ e ⟧ env)) z))
          (mergeMap-derived g gs e env ao))
        (mergeMap-diamond g gs (emits (⟦ e ⟧ env)) m)
