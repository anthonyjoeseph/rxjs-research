{-# OPTIONS --guardedness #-}

-- PROGRESS: whatever item the meaning's events reach, finitely many steps
-- of the machine, read to as many ticks, reach.  The upper half of the
-- link (`port.adequacy.Adequacy`).
module port.adequacy.Progress where

open import Data.List using ([]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ)

open import denotation.MonotonicList.Events using (root)
open import denotation.MonotonicList using (observe)
open import denotation.Denote using (⟦_⟧)
open import adequacy.Record using (Ahead; items)
open import port.operation.PureObservable using (PureObs; module Driver; module Machine)

module Progressing (R : Set) where
  open Driver R using (reading; Read)
  open Machine using (load)

  postulate
    -- LIVENESS: whatever item the meaning's events reach, some prefix of
    -- the launch's run reads, as many steps as ticks.
    --
    -- OLD BODY: 85c14392490061b71342d104b2d16a16cb4ec724 agda-impl/adequacy/Progress.agda
    reached : (o : PureObs [] R) → ∀ {k} → Ahead (observe (⟦ o ⟧ []) root) k
            → Σ ℕ λ n → k ≤ length (items (Read.log (reading n n 0 (load o))) (Read.endedAs (reading n n 0 (load o))))
