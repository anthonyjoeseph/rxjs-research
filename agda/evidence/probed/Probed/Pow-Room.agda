-- THE ROOM THE NESTING CEILING'S STEP IS PAID OUT OF, at numerals.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: pow-room-ℕ @3d6291
--
-- WHAT IS BEING TESTED.  The caps face has discharged everything
-- cap-shaped out of the ceiling's step, and what is left is three
-- numbers: the size at an instant, the size it steps to, and an
-- exponent the delivery side contributes.  Every hypothesis is a
-- numeral comparison, so unlike the statement it replaced this one is
-- instantiable at all -- the caps recurrence does not appear on either
-- side, and neither does anything sealed.
--
-- WHICH AXIS CAN REFUTE.  The exponent moves only the LEFT, so it is
-- the measure-side axis and a row at its cap is the honest test.  The
-- step size moves BOTH sides and moves the right one faster, so
-- enlarging it can only weaken the claim; it is swept once anyway,
-- because the cap on the exponent is stated in the OTHER size and a
-- reader has no way to see from the type that the two do not race.
--
-- ROWS A, C, D are LOAD-BEARING at the tightest corner the hypotheses
-- allow: the step size at its floor, the exponent at its ceiling.  Row
-- B is DEGENERATE on the exponent -- it is here to show the additive
-- terms alone are not what is tight, and it could not have failed.
-- Row E moves the step size off its floor at fixed exponent.
--
-- ROWS F AND G ARE THE NON-VACUITY WITNESSES, and they FAIL: the same
-- arithmetic with the exponent past its cap does not fit, pinned as
-- `false`.  Without them every row above is consistent with the
-- inequality being unfalsifiable at these shapes.
--
-- WHAT IS NOT COVERED.  Sizes above ten, and the whole region where
-- the step size is far above its floor -- one row reaches four times
-- it and no row reaches the doubly exponential sizes the recurrence
-- actually produces.  Both directions make the claim EASIER, which is
-- why the sweep is where it is.
module Probed.Pow-Room where

open import Data.Nat using (ℕ; suc; _+_; _^_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

room : ℕ → ℕ → ℕ → Bool
room S S′ K = (S′ + 3 + (2 ^ S + suc S′ ^ K) + suc S′ ^ K) ≤ᵇ 2 ^ S′

-- ROW A: the floor of the step size at the ceiling of the exponent,
-- eight against two-to-the-eight-times-eight and six sizes and nine.
rowA : room 8 2048 57 ≡ true
rowA = refl

-- ROW B: the exponent at zero -- DEGENERATE, the additive terms alone.
rowB : room 8 2048 0 ≡ true
rowB = refl

-- ROW C, ROW D: one and two sizes up, each again at both extremes.
rowC : room 9 4608 63 ≡ true
rowC = refl

rowD : room 10 10240 69 ≡ true
rowD = refl

-- ROW E: the step size four times its floor, exponent unchanged.
rowE : room 8 8192 57 ≡ true
rowE = refl

-- ROW F, ROW G: the exponent past its cap, and the room is gone.
rowF : room 8 2048 200 ≡ false
rowF = refl

rowG : room 9 4608 400 ≡ false
rowG = refl
