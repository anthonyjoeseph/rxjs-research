-- E1's counterexample: a src-side file reaching INTO the evidence tree.
-- This is the pet peeve the boundary exists for -- proof code coming to
-- depend on a `refl` at three concrete inputs.
module Bad where

open import Probed.Demand using (someReceipt)
open import Refuted.Thru-Loop using (thru-absurd)
