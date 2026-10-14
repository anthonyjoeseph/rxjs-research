{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- pure run's approximants is the meaning, observed at the root, with
-- positions forgotten down to ticks.
--
-- Both halves compare the run against the meaning itself, over one
-- configuration of the whole running program (`Config`, `Bound`).
-- BELOW: every approximant of the run is below the meaning.  Its record,
-- ghost positions and all, is placed against the events the root is
-- shown (`operation.Placed`), so it shows nothing they do not.
-- ABOVE: whatever the meaning shows, some approximant of the run shows.
module Adequacy where

open import Data.List using ([]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_,_; Σ; proj₁; proj₂)

open import operation.Placed using (Up; Ahead; ahead; module Ran)
open import Bound using (module Places)
open import operation.Budget using (module Approx)
open import operation.PureObservable using (PureObs; module Pure; toArray)
open import denotation.MonotonicList using (ML; observe; root; ticks)
open import denotation.Order using (_⊑_; _≃_; Shows; limit; Chain; limit-ub; limit-least; shows-≼; shows-cmp; cmp-long)
open import denotation.Unfold using (⟦_⟧)

-- The pure run: the limit of its approximants.
run : ∀ {A} → PureObs [] A → ML A
run o = limit λ n → toArray n o

-- The meaning, as the run reports one.
meaning : ∀ {A} → PureObs [] A → ML A
meaning o = ticks (observe (⟦ o ⟧ []) root)

module Link (R : Set) where
  open Pure R using (compileᴺ)
  open Approx R using (runPure-mono)
  open Ran R using (ran; recorded-⊑; itemsOf; observed; recorded-shows)
  open Places R using (places)

  postulate
    -- The meaning's ticks never fall.
    ticks-up : (o : PureObs [] R) → Up 0 (observe (⟦ o ⟧ []) root)

    -- THE RUN GETS AS FAR: wherever the meaning's events reach, some
    -- approximant of the run records as many items — finitely many events
    -- need only finite budget.  Which items is the bound half's business
    -- (`reaches`).
    --
    -- False wherever a `connect` source the body outlives stands between
    -- the root and an event the meaning shows.  The meaning steps a
    -- source only as its joiners copy it, so a body that never joins
    -- shows past it; the engine runs the source inline, and a source
    -- that spins stops the whole run there — as rxjs does, by
    -- overflowing — while one that runs forever keeps the engine firing
    -- its timers, so the silence the meaning shows after the body is
    -- never reported.  The meaning keeping such a source's events, or
    -- `adequacy` assuming none, is Anthony's call.
    -- DEAD ROUTE: a logical relation per operator, by induction over
    --   the tree's approximants, each kernel against its own timeline.  A
    --   connect's subject is state its siblings share, which no relation
    --   on one kernel at a time can carry.
    enough : (o : PureObs [] R) → ∀ {k} → Ahead (observe (⟦ o ⟧ []) root) k → Σ ℕ λ n → k ≤ length (itemsOf (ran n (compileᴺ n o [])))

  -- Whatever the meaning shows, some approximant of the run shows as many
  -- items.
  progress : (o : PureObs [] R) → ∀ {is} → Shows (meaning o) is → Σ ℕ λ n → length is ≤ length (itemsOf (ran n (compileᴺ n o [])))
  progress o s = enough o (ahead s)

  -- The run's approximants are a chain.
  toArray-chain : (o : PureObs [] R) → Chain (λ n → toArray n o)
  toArray-chain o n = runPure-mono o (n≤1+n n) (n≤1+n n)

  -- THE UPPER HALF: whatever the meaning shows, some approximant of the
  -- run shows.  It shows as many items, and they are the meaning's.
  reaches : (o : PureObs [] R) → ∀ {is} → Shows (meaning o) is → Σ ℕ λ n → Shows (toArray n o) is
  reaches o s with progress o s
  ... | n , long = n , shows-≼ (cmp-long (shows-cmp s (recorded-shows (ran n (compileᴺ n o [])) (ticks-up o) (places n o n))) long)
                                (observed (ran n (compileᴺ n o [])))

  -- Each approximant of the run is below the meaning.
  complete : (o : PureObs [] R) (n : ℕ) → toArray n o ⊑ meaning o
  complete o n = recorded-⊑ (ran n (compileᴺ n o [])) (ticks-up o) (places n o n)

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy {A} o = limit-least (toArray-chain o) (complete o)
               , λ s → limit-ub (toArray-chain o) (proj₁ (reaches o s)) (proj₂ (reaches o s))
  where open Link A
