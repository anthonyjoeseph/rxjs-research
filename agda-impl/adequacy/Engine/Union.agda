{-# OPTIONS --guardedness #-}

-- TAILS JOINED: a merge's pool joins the tails its parts leave in the
-- order they ended, the engine's in the order its lanes sit.  Joined
-- tails regroup freely (`∪-assocᵀ`); two tails each in position order
-- join the same either way round (`∪-commᵀ`).  Out of order they need
-- not: a tie takes the right-hand tail's step first, so `2 2` joined
-- with `2 1` is not `2 1` joined with `2 2`.
module adequacy.Engine.Union where

open import Data.Nat using (zero; suc)

open import denotation.MonotonicList.Events using (Tail; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (Agreeᵀ; stopᵀ; pin⁼; idle⁼)
open import adequacy.Placed.Trail using (SortedT)
open Tail∞

-- A tail joined to none.
∪-idleᵀ : ∀ n (t : Tail) → Agreeᵀ n (t ∪ idle) t
∪-idleᵀ zero    t         = stopᵀ
∪-idleᵀ (suc n) idle      = idle⁼
∪-idleᵀ (suc n) (pin k r) = pin⁼ (∪-idleᵀ n (later r))

postulate
  -- Joined tails regroup.
  ∪-assocᵀ : ∀ n t u v → Agreeᵀ n ((t ∪ u) ∪ v) (t ∪ (u ∪ v))

  -- Two tails in position order join the same either way round.
  ∪-commᵀ : ∀ n t u → SortedT t → SortedT u → Agreeᵀ n (t ∪ u) (u ∪ t)
