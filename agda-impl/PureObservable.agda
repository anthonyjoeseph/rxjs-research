{-# OPTIONS --guardedness #-}

-- THE PURE OPERATIONAL SEMANTICS.  The same `subscribe`, interpreted over
-- a heap and a virtual clock.  A cold leaf is a timeline relative to its
-- subscribe time, so the program itself says when everything happens:
-- there is no separate schedule, and quantifying over programs covers
-- every ordering.
module PureObservable where

open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)

open import AbstractObservable
open import MonotonicList using (Time; ML; Timeline)

Addr : Set
Addr = ℕ

-- No native effects: a pure observer can only write to refs.  Refs,
-- sinks and handles are all heap addresses; a started cold's cell records
-- which of its queued frames are still live.
Pureᴾ : Prims
Pureᴾ = record { Ref = λ _ → Addr ; Cold = Timeline ; Handle = Addr ; Sink = λ _ → Addr ; Eff = λ _ → ⊥ }

open Run Pureᴾ

PureObs : List Set → Set → Set₁
PureObs = Obs Timeline

-- The top-level observer writes into a sink: `just a` per value,
-- `nothing` for completion.  The loop reads the sink after each cascade.
sinkObserver : ∀ {A} → Addr → Observer A
sinkObserver {A} sink = record
  { next     = λ a → readRef {A = List (Maybe A)} sink λ xs → writeRef sink (just a ∷ xs) (done tt)
  ; complete = readRef {A = List (Maybe A)} sink λ xs → writeRef sink (nothing ∷ xs) (done tt)
  }

postulate
  -- THE PURE EVENT LOOP.  Allocates the sink, runs the subscription
  -- cascade at time 0 as frame 0, then repeatedly pops the earliest
  -- queued frame, runs its cascade, and drains the sink into the next
  -- frame of the result.  `startCold` delivers frame 0 of a timeline
  -- inline and queues each later frame at now + offset; frames due at the
  -- same time run in the order they were queued, as two `setTimeout`s
  -- with one delay do.  Each `child` is unfolded by calling `subscribe`
  -- and emits one `Burst` `stall`, so a synchronous loop yields a burst
  -- that never closes instead of a hang: productive because the loop's
  -- OWN output guards the unfolding, which no operator can strip.
  loop : ∀ {A} → (Addr → Act ⊤) → ML A

runPure : ∀ {A} → PureObs [] A → ML A
runPure o = loop λ sink → subscribe o [] (sinkObserver sink) λ _ → done tt
