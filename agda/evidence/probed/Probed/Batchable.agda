-- BATCHABLE AT THREE FIRST-ORDER PROGRAMS, BY RUNNING BOTH SIDES.
-- Every row is LOAD-BEARING: each emits, `two-arrivals` puts two values in
-- two instants and `of-two` puts two in ONE, so a grouping that split the
-- one or merged the two fails `refl`.
-- TARGET: batchable @591818
module Probed.Batchable where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Batchable.Statement using (batchable)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)

_ : Confirms (batchable tt (κᵖ take-one) 30 (Point.prog take-one) (insᵖ take-one))
_ = refl

_ : Confirms (batchable tt (κᵖ two-arrivals) 30 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = refl

_ : Confirms (batchable tt (κᵖ of-two) 30 (Point.prog of-two) (insᵖ of-two))
_ = refl
