-- LEFT-TO-RIGHT AT THREE FIRST-ORDER PROGRAMS, BOTH PREFIXES DECIDED.
-- Every row is LOAD-BEARING: each run emits, so an impl that lost or
-- invented a value makes one of the two decisions `no` and the `tt`
-- unfillable.  The one-past slack is DEGENERATE here: every run completes
-- inside its fuel.
-- TARGET: left-to-right @9d7058
module Probed.Left-To-Right where

open import Data.Unit using (tt)
open import Data.Nat using (_≟_)
open import Data.Product using (_,_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties using (prefix?)
open import Relation.Nullary.Decidable using (toWitness)

open import Left-To-Right.Statement using (left-to-right)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)

_ : Confirms (left-to-right tt (κᵖ take-one) 30 (Point.prog take-one) (insᵖ take-one))
_ = toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt

_ : Confirms (left-to-right tt (κᵖ two-arrivals) 30 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt

_ : Confirms (left-to-right tt (κᵖ of-two) 30 (Point.prog of-two) (insᵖ of-two))
_ = toWitness {a? = prefix? _≟_ _ _} tt , toWitness {a? = prefix? _≟_ _ _} tt
