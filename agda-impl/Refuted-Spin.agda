{-# OPTIONS --guardedness #-}

-- A `connect` whose source spins synchronously refutes `run-rel`: the
-- body ignores the subject, so `connectᴰ` shows the body's 7 at tick 3,
-- the source's spin dropped with the rest of its events; the engine
-- subscribes the source after the body and aborts the whole run there,
-- on every budget.
module Refuted-Spin where

open import Data.Empty using (⊥)
import Data.List
open Data.List using (_∷_)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (n≤1+n; ≤-refl)
open import Level using (lift)

open import Tree using (Later; cold; connect; defer)
open import denotation.MonotonicList using (ML; Burst∞; ML∞; at; emit; close; done; stall)
open import denotation.Order using (_⊑_; ShowsIn; at⁺; emit⁺; stall⁺; nil; limit-least)
open import operation.PureObservable using (PureObs; module Pure)
open import operation.Budget using (module Approx)
open import Adequacy using (module Link)

open Burst∞
open ML∞

loop : ∀ {Γ} → PureObs Γ ℕ
loop = defer λ where .Later.force → loop

X : ML ℕ
X = at 3 (emit 7 λ where .force → close λ where .force → done)

o : PureObs Data.List.[] ℕ
o = connect loop (cold (lift X))

open Pure ℕ using (runPure; compileᴺ; stalls)
open Approx ℕ using (runPure-mono)

cutAt0 : ML ℕ
cutAt0 = at 0 (stall stalls)

-- On every budget the run is cut at tick 0, having recorded nothing.
bound : ∀ m → runPure m (compileᴺ 5 o All.[]) ⊑ cutAt0
bound zero    s = s
bound (suc m) s = s

-- A cut shows nothing, however far it is read.
blank : ∀ {i is} → ShowsIn {ℕ} 0 (stall stalls) (i ∷ is) → ⊥
blank (stall⁺ p) = blank p

refuted : ⊥
refuted with limit-least (λ m → runPure-mono {n = 5} o (n≤1+n m) ≤-refl) bound
               (Link.run-rel ℕ (Link.fundamental ℕ 5 o Link.[]) (at⁺ (emit⁺ nil)))
... | at⁺ p = blank p
