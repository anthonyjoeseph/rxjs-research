{-# OPTIONS --guardedness #-}

-- ONE DRIVER: the engine as a pure transition function, `state → input →
-- state × outputs`, and one generic driver feeding it inputs.  The pure
-- runtime feeds it the clock; the IO runtime feeds it whatever the world
-- does next.  Everything the two share is the transition; only the input
-- source differs, so every fact proven of the transition holds of both.
--
-- Today the IO runtime interprets `operation.AbstractObservable`'s `Act`
-- in `IO` directly and only the pure side is a machine
-- (`operation.Machine`); this module states the shape both are to be.
module operation.Driver where

open import Data.List using (List; []; _∷_; _++_; zipWith)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.MonotonicList using (Pos; Time)
open import operation.Machine using (module Machine)
open import operation.PureObservable using (PureObs)

-- A pure transition function.
record Driver (S : Set₁) (I O : Set) : Set₁ where
  field transition : S → I → S × List O

-- The generic driver: feed it inputs, collect its outputs.
drive : ∀ {S I O} → Driver S I O → S → List I → S × List O
drive d s []       = s , []
drive d s (i ∷ is) with Driver.transition d s i
... | s′ , os with drive d s′ is
...   | s″ , os′ = s″ , os ++ os′

module Driven (R : Set) where
  open Machine R using (Mach; begin; reading; trace; Read)
  open Read

  -- The positions and values of a read, as the engine's outputs.
  records : Read → List (Pos × Time × R)
  records r = zipWith (λ p x → p , x) (marks r) (log r)

  postulate
    -- THE ENGINE: one transition, the input a clock reading, the outputs
    -- the root's deliveries at their positions.
    engine : Driver Mach Time (Pos × Time × R)

    -- The pure runtime is the engine driven by the clock: every prefix's
    -- record is the outputs of some clock the engine was fed from the
    -- program's start.
    driven : ∀ (o : PureObs [] R) n → Σ (List Time) λ ts →
             Σ Mach λ m → drive engine (begin o) ts ≡ (m , records (reading n 0 (trace (begin o))))
