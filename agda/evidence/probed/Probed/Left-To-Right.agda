-- THE BATCHER'S SANDWICH AT THREE FIRST-ORDER PROGRAMS AND AT THE ONE
-- ITS ONE-PAST FORM WAS REFUTED AT, BOTH PREFIXES DECIDED.  Every row is
-- LOAD-BEARING for the values: each run emits, so a batcher that lost or
-- invented a value makes one of the two decisions `no` and the `tt`
-- unfillable.  The first three take the batcher's witness at the run's
-- own fuel and are DEGENERATE for the slack: every run completes inside
-- its fuel.  The fourth is LOAD-BEARING for it: its open instant holds
-- two values at fuel one, the second arrival is silent, and the witness
-- one -- the run's own fuel -- fails the second prefix; two, the fuel
-- just before the closing arrival, holds both.
-- TARGET: batched-sandwich @5c50c9
module Probed.Left-To-Right where

open import Data.Unit using (tt)
open import Data.Nat using (_≟_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties using (prefix?)
open import Relation.Nullary.Decidable using (toWitness)

open import Left-To-Right.Statement using (batched-sandwich)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)
open import Refuted.Batched-Sandwich using (prog; script; ins)
open import CLI.Unit-Test.Prelude using (κOf)

_ : Confirms (batched-sandwich tt (κᵖ take-one) 30 (Point.prog take-one) (insᵖ take-one))
_ = 30 , ≤-refl , toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt

_ : Confirms (batched-sandwich tt (κᵖ two-arrivals) 30 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = 30 , ≤-refl , toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt

_ : Confirms (batched-sandwich tt (κᵖ of-two) 30 (Point.prog of-two) (insᵖ of-two))
_ = 30 , ≤-refl , toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt

_ : Confirms (batched-sandwich tt (κOf script) 1 prog ins)
_ = 2 , s≤s z≤n , toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt
