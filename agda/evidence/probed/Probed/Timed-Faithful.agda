-- TIMED-FAITHFUL AT THREE FIRST-ORDER PROGRAMS, BY RUNNING BOTH SIDES.
-- Every row is LOAD-BEARING: both sides are non-empty value lists, so a
-- translation that dropped, duplicated or reordered a value fails `refl`.
-- TARGET: timed-faithful @22bfa9
module Probed.Timed-Faithful where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Timed.Faithful using (timed-faithful)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)

_ : Confirms (timed-faithful tt (κᵖ take-one) 30 (Point.prog take-one) (insᵖ take-one))
_ = refl

_ : Confirms (timed-faithful tt (κᵖ two-arrivals) 30 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = refl

_ : Confirms (timed-faithful tt (κᵖ of-two) 30 (Point.prog of-two) (insᵖ of-two))
_ = refl
