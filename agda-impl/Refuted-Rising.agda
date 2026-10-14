{-# OPTIONS --guardedness #-}

-- A cold whose ticks fall refutes `rising`: its second frame, "at tick 2",
-- comes after a frame at tick 3.
module Refuted-Rising where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; s≤s)
open import Data.Product using (_,_)
open import Level using (lift)

open import Tree using (cold)
open import denotation.MonotonicList using (ML; Burst∞; ML∞; at; emit; close; done)
open import operation.PureObservable using (PureObs)
open import Adequacy using (module Link; Rises)

open Burst∞
open ML∞
open Rises

A : ML ℕ
A = at 3 (emit 1 λ where .force → close λ where .force → at 2 (emit 2 λ where .force → close λ where .force → done))

o : PureObs [] ℕ
o = cold (lift A)

refuted : ⊥
refuted with rises (Link.rising ℕ 0 o)
... | _ , r with rises (rises (rises r))
... | s≤s (s≤s ()) , _
