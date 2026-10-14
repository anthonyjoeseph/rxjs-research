{-# OPTIONS --guardedness #-}

-- A cold whose ticks go backwards refutes `complete`, and so `adequacy`:
-- the denotation places the later frame at its own tick, before the other
-- cold's frame at the tick already reached; the engine sets its timer for
-- now, behind the timers already due.  Denotation `1 2 9`, engine `1 9 2`.
module Refuted-Backwards where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Level using (lift)

open import Tree using (Obs; merge; cold)
open import denotation.MonotonicList using (ML; Timeline; Burst∞; ML∞; at; emit; close; done)
open import denotation.Order using (Shows; ShowsIn; at⁺; emit⁺; stall⁺; close⁺; nil)
open import operation.PureObservable using (PureObs; toArray)
open import Adequacy using (module Link; approxAt)

open Burst∞
open ML∞

-- 1 at tick 3, then a frame "at tick 2"; and 9 at tick 3.
A B : ML ℕ
A = at 3 (emit 1 λ where .force → close λ where .force → at 2 (emit 2 λ where .force → close λ where .force → done))
B = at 3 (emit 9 λ where .force → close λ where .force → done)

o : PureObs [] ℕ
o = merge (cold (lift A)) (cold (lift B))

-- The engine shows 1 then 9 at tick 3; the denotation shows 2 after 1.
refuted : ⊥
refuted with Link.complete ℕ o 30 (at⁺ (emit⁺ (emit⁺ nil)))
... | at⁺ (stall⁺ (stall⁺ (stall⁺ (close⁺ (at⁺ (emit⁺ (stall⁺ ())))))))
