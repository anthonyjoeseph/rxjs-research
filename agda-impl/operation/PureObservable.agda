{-# OPTIONS --guardedness #-}

-- THE PURE RUNTIME.  The shared engine, run in a state monad over a heap
-- and a virtual clock.  A cold leaf is a timeline relative to its
-- subscribe time, so the program itself says when everything happens:
-- there is no separate schedule, and quantifying over programs covers
-- every ordering.
--
-- Recursion is closed by unfolding: approximant n compiles n nested
-- `defer`s, runs callbacks n deep and takes n turns of the loop, and past
-- that shows nothing.  Every approximant is a finite run; the program's
-- meaning is their limit, as `Denote`'s is.
module operation.PureObservable where

open import Data.Empty using (⊥)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)

open import Tree using (Obs; Later)
open import operation.AbstractObservable using (Prims; module Run)
open import denotation.MonotonicList using (ML; Timeline)

Addr : Set
Addr = ℕ

-- No native effects: a pure observer can only write to refs.  Refs,
-- sinks and handles are all heap addresses.
Pureᴾ : Prims
Pureᴾ = record { Ref = λ _ → Addr ; Cold = Timeline ; Handle = Addr ; Sink = λ _ → Addr ; Eff = λ _ → ⊥ }

open Run Pureᴾ

PureObs : List Set → Set → Set₁
PureObs = Obs Timeline

postulate
  -- THE PURE MONAD at budget n.  A heap of refs and registered sinks, a
  -- virtual clock, and a queue of pending frames, each a sink and the
  -- rest of a timeline.  `startColdᴿ` delivers frame 0 inline and queues
  -- each later frame at now + offset; `nextᴿ` pops the earliest.  A
  -- burst is walked at most n elements before it reads as `diverge`.
  Pureᴿ : ℕ → Runtime

  -- Runs `go` with a top-level observer recording each value into the
  -- frame the clock is on, and reads the frames off as a timeline: done
  -- if the root completed, quiet if the queue ran dry, a burst that
  -- stalls forever where the budget ran out.
  observing : ∀ n {A} → (Observer A → Runtime.M (Pureᴿ n) ⊤) → ML A

-- Approximant n of the compiler: a `defer` nested more than n deep shows
-- nothing.  Lines up clause for clause with `denotation.Denote.approx`.
deferredᴺ : ℕ → Deferred
deferredᴺ zero    l ρ = ⊥ᴷ
deferredᴺ (suc n) l ρ = compileWith (deferredᴺ n) (Later.force l) ρ

compileᴺ : ℕ → ∀ {Γ A} → PureObs Γ A → Env Γ → Subscribe A
compileᴺ n = compileWith (deferredᴺ n)

-- Runs a subscription on approximant n of the engine.
runPure : ℕ → ∀ {A} → Subscribe A → ML A
runPure n s = observing n (drive (runᴺ n) (loopᴺ n) s)
  where
    open Engine (Pureᴿ n)

    runᴺ : ℕ → RunAct
    runᴺ zero    = λ _ → Runtime.divergeᴿ (Pureᴿ n)
    runᴺ (suc m) = interpret (runᴺ m)

    loopᴺ : ℕ → Runtime.M (Pureᴿ n) ⊤
    loopᴺ zero    = Runtime.divergeᴿ (Pureᴿ n)
    loopᴺ (suc m) = loopStep (runᴺ (suc m)) (loopᴺ m)

-- Approximant n of a program's run.
toArray : ℕ → ∀ {A} → PureObs [] A → ML A
toArray n o = runPure n (compileᴺ n o [])
