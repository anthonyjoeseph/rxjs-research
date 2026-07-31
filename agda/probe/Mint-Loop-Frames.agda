------------------------------------------------------------------
-- THE MINT-LOOP PROBE, SECOND HALF: THE FRAMES AND THE TWO COORDINATES.
--
-- The narrative — what these families are for, what they settled, and the
-- STANDING WARNING about shallow rows that governs every table in both
-- files — is at the head of Mint-Loop-Probe.  Read that first.  This file
-- is MEASUREMENTS 5, 6 and 7: `j` itself, the two coordinates of the
-- delivery injection, and the fourth ladder.
--
-- WHY IT IS A SEPARATE FILE.  One wall of `refl` over these families does
-- not finish: the combined file exceeded fifty minutes and was killed.
-- Split in two, each half checks on its own, and the heaviest rows are
-- demoted from `refl` to measured-not-rechecked comments whose numerals
-- are then gated by arithmetic that IS `refl` — normalising a numeral
-- comparison is free, normalising the evaluator run behind it is not.
--
-- THE PROVENANCE RULE, and there is no silent third state: every number
-- either has a `refl` under it here, or sits in a comment with an explicit
-- MEASURED-NOT-RECHECKED flag saying which harness produced it
------------------------------------------------------------------
module Mint-Loop-Frames where

open import Data.Nat  using (ℕ; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Mint-Loop-Shapes

------------------------------------------------------------------
-- MEASUREMENT 5: THE FRAMES, which is what the conjunct bounds.  First
-- the mirror's faithfulness — it walks the evaluator's own state, so its
-- delivery ledger reproduces MEASUREMENT 3 — and then j itself
------------------------------------------------------------------

_ : mJdel 0 (pG′ 0) insG ≡ 5
_ = refl

_ : mJdel 0 (pG′² 0) insG² ≡ 20
_ = refl

_ : mJdel 0 (pL³ 0) insG³ ≡ 50
_ = refl

-- one shared level
_ : mJ 0 (pG′ 0) insG ≡ 8
_ = refl

_ : mJ 0 (pG′ 1) insG ≡ 10
_ = refl

_ : mJ 0 (pG′ 2) insG ≡ 10
_ = refl

-- two shared levels, accumulating and lean
_ : mJ 0 (pG′² 0) insG² ≡ 39
_ = refl

_ : mJ 0 (pG′² 1) insG² ≡ 85
_ = refl

_ : mJ 0 (pG′² 2) insG² ≡ 103
_ = refl

_ : mJ 0 (pG′² 3) insG² ≡ 105
_ = refl

_ : mJ 0 (pL² 0) insG² ≡ 20
_ = refl

_ : mJ 0 (pL² 2) insG² ≡ 51
_ = refl

_ : mJ 0 (pL² 4) insG² ≡ 53
_ = refl

-- three shared levels, lean: the sweep with the interior peak
_ : mJ 0 (pL³ 0) insG³ ≡ 58
_ = refl

_ : mJ 0 (pL³ 1) insG³ ≡ 226
_ = refl

_ : mJ 0 (pL³ 2) insG³ ≡ 548
_ = refl

_ : mJ 0 (pL³ 3) insG³ ≡ 912
_ = refl

_ : mJ 0 (pL³ 4) insG³ ≡ 1164
_ = refl

-- MEASURED-NOT-RECHECKED (scripts/measure.sh, through the typechecker):
--     mJ 0 (pL³ 5) insG³ = 1268
--     mJ 0 (pL³ 6) insG³ = 1291
-- and reproduced by the compiled harness (probe/Measure-Main.agda) at
-- 1291 for k = 6.  Demoted because the two of them are the most expensive
-- pins in the sweep and the peak they document is at k = 3, four rows
-- above.  Their gates are the numerals below

-- across instants
_ : mJ 1 (pG′ 0) insG ≡ 29
_ = refl

_ : mJ 2 (pG′ 0) insG ≡ 86
_ = refl

_ : mJ 1 (pG′ 2) insG ≡ 91
_ = refl

-- MEASURED-NOT-RECHECKED (scripts/measure.sh): the accumulating
-- three-level ladder, the tightest single point in the file against the
-- OLD count — `mJ 0 (pG′³ 0) insG³ = 324`, with `mFolds 0 (pG′³ 0) insG³
-- = 106` pinned by `refl` in Mint-Loop-Probe.  Gated at the numerals below

------------------------------------------------------------------
-- THE FRAME GATE: j against `2 ^ cReg * cSize * cSize`, the count the
-- two factors actually give.  The lean L = 3 ladder is the whole sweep
-- because it is the one whose ratio climbs before it falls
------------------------------------------------------------------

-- one shared level, k = 0 … 2 at (3, 8)
_ : (10 ≤ᵇ 2 ^ 3 * 8 * 8) ≡ true
_ = refl

-- two shared levels, accumulating, k = 0 … 3 at (5, {8,22,36,50})
_ : (39 ≤ᵇ 2 ^ 5 * 8 * 8) ≡ true
_ = refl

_ : (85 ≤ᵇ 2 ^ 5 * 22 * 22) ≡ true
_ = refl

_ : (103 ≤ᵇ 2 ^ 5 * 36 * 36) ≡ true
_ = refl

_ : (105 ≤ᵇ 2 ^ 5 * 50 * 50) ≡ true
_ = refl

-- two shared levels, lean, k = 0, 2, 4 at (5, {3,18,34})
_ : (20 ≤ᵇ 2 ^ 5 * 3 * 3) ≡ true
_ = refl

_ : (51 ≤ᵇ 2 ^ 5 * 18 * 18) ≡ true
_ = refl

_ : (53 ≤ᵇ 2 ^ 5 * 34 * 34) ≡ true
_ = refl

-- three shared levels, lean, k = 0 … 6 at (7, {3,10,18,26,34,42,50}) —
-- the last two rows gate MEASURED-NOT-RECHECKED numerals
_ : (58 ≤ᵇ 2 ^ 7 * 3 * 3) ≡ true
_ = refl

_ : (226 ≤ᵇ 2 ^ 7 * 10 * 10) ≡ true
_ = refl

_ : (548 ≤ᵇ 2 ^ 7 * 18 * 18) ≡ true
_ = refl

_ : (912 ≤ᵇ 2 ^ 7 * 26 * 26) ≡ true
_ = refl

_ : (1164 ≤ᵇ 2 ^ 7 * 34 * 34) ≡ true
_ = refl

_ : (1268 ≤ᵇ 2 ^ 7 * 42 * 42) ≡ true
_ = refl

_ : (1291 ≤ᵇ 2 ^ 7 * 50 * 50) ≡ true
_ = refl

-- the accumulating three-level ladder, and across instants
_ : (324 ≤ᵇ 2 ^ 7 * 8 * 8) ≡ true
_ = refl

_ : (29 ≤ᵇ 2 ^ 6 * 21 * 21) ≡ true
_ = refl

_ : (91 ≤ᵇ 2 ^ 7 * 77 * 77) ≡ true
_ = refl

------------------------------------------------------------------
-- THE WORST RATIO IN THE FILE, and it is at k = 0 — the NON-nested mint,
-- the shape family G already gated.  Nesting is not the escape
-- direction, though it is not as flatly safe as the delivery counts
-- alone suggested: j peaks at k = 3 on the lean L = 3 ladder before it
-- falls, so the margin narrows over three rungs and then widens again.
--
--     against the NEW count `2 ^ cReg * cSize * cSize`
--       L = 3, k = 0, accumulating   324 / (2 ^ 7 * 8 * 8)  = 0.040
--       L = 3, k = 0, lean            58 / (2 ^ 7 * 3 * 3)  = 0.050
--       L = 3, k = 3, lean           912 / (2 ^ 7 * 26 * 26) = 0.011
--
-- stated as the comparison a ratio ten times worse would break.  NOTE
-- that the L = 4 sweep at the foot of this file breaks the same
-- comparison for D, so "ten times worse" is not headroom this family
-- reliably has
------------------------------------------------------------------

_ : (324 * 10 ≤ᵇ 2 ^ 7 * 8 * 8) ≡ true
_ = refl

_ : (58 * 10 ≤ᵇ 2 ^ 7 * 3 * 3) ≡ true
_ = refl

_ : (912 * 10 ≤ᵇ 2 ^ 7 * 26 * 26) ≡ true
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 6: THE TWO COORDINATES, AND THE DAMPER AS FIRST STATED
-- IS FALSE.
--
-- `cascadeGo-deliveries` sends a delivery to (its pre-state class, an
-- index), `preClasses-bound` caps the first coordinate at 2 ^ cReg and
-- `fibreCap-bound` caps the second.  The second was first stated at
-- cSize, on the reasoning that a mint happens inside ONE frame and a
-- frame's step function names no more sources than its syntax holds.
-- Measured, that is wrong twice — and wrong on the LEAN families, which
-- is the point of them: they keep the whole delivery structure while
-- shrinking the syntax the cap is read off.
--
--   program   cReg  cSize    D   mPre  2^cReg   mFib
--   pG′  0      3      8     5      4      8      2
--   pG′  1      3     22     5      4      8      2
--   pG′  2      3     36     5      4      8      2
--   pG′² 0      5      8    20     10     32      7
--   pG′² 1      5     22    26     10     32     12
--   pG′² 2      5     36    27     10     32     13
--   pL²  0      5      3    16     10     32      4     ← 4 > 3
--   pL²  2      5     18    21     10     32      8
--   pL²  4      5     34    21     10     32      8
--   pL³  0      7      3    50     22    128      8     ← 8 > 3
--
-- WHAT REPLACES IT.  Both coordinates now range over subsets of the
-- ENTRY registry: a delivery is determined by the pre-state
-- registrations it visits TOGETHER WITH the pre-state registrations
-- whose dispatches minted the ones it visits.  Every mint happens during
-- some delivery and every delivery bottoms out at a pre-state chain, so
-- the second coordinate is pre-state data too — which is a story rather
-- than a curve fit, though it is still only a story: it is not a proof
-- that the recursion bottoms out, and `fibreCap-bound` is postulated.
-- The count becomes `2 ^ cReg * 2 ^ cReg * cSize`.
--
-- Note the first coordinate is nowhere near its cap (22 against 128) and
-- the second is nowhere near the new one (13 against 32).  It is the
-- SHAPE that is at issue, not the slack
------------------------------------------------------------------

-- one descriptor per delivery, which is what makes them a reindexing of
-- the ledger rather than a separate walk
_ : mJdesc 0 (pG′ 0) insG ≡ 5
_ = refl

_ : mJdesc 0 (pG′² 0) insG² ≡ 20
_ = refl

_ : mPre 0 (pG′ 0) insG ≡ 4
_ = refl

_ : mFib 0 (pG′ 0) insG ≡ 2
_ = refl

_ : mPre 0 (pG′ 1) insG ≡ 4
_ = refl

_ : mFib 0 (pG′ 1) insG ≡ 2
_ = refl

_ : mPre 0 (pG′ 2) insG ≡ 4
_ = refl

_ : mFib 0 (pG′ 2) insG ≡ 2
_ = refl

_ : mPre 0 (pG′² 0) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 0) insG² ≡ 7
_ = refl

_ : mPre 0 (pG′² 1) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 1) insG² ≡ 12
_ = refl

_ : mPre 0 (pG′² 2) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 2) insG² ≡ 13
_ = refl

_ : mPre 0 (pL² 0) insG² ≡ 10
_ = refl

_ : mFib 0 (pL² 0) insG² ≡ 4
_ = refl

_ : mPre 0 (pL² 2) insG² ≡ 10
_ = refl

_ : mFib 0 (pL² 2) insG² ≡ 8
_ = refl

_ : mPre 0 (pL² 4) insG² ≡ 10
_ = refl

_ : mFib 0 (pL² 4) insG² ≡ 8
_ = refl

_ : mPre 0 (pL³ 0) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 0) insG³ ≡ 8
_ = refl

-- THE LADDER SWEEP, which is where the second coordinate does all its
-- growing.  mPre is CONSTANT down each ladder — 4, 10, 22 for entry
-- registries of 3, 5, 7 — because the pre-state classes are fixed by the
-- pre-state DAG, exactly as the damper's story says.  Every bit of the
-- k-dependence lands in the fibre, and on the three-level lean ladder it
-- climbs to EXACTLY 2 ^ cReg and stops
_ : mPre 0 (pG′² 3) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 3) insG² ≡ 13
_ = refl

_ : mPre 0 (pL³ 1) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 1) insG³ ≡ 29
_ = refl

_ : mPre 0 (pL³ 2) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 2) insG³ ≡ 64
_ = refl

_ : mFib 0 (pL³ 3) insG³ ≡ 99
_ = refl

_ : mFib 0 (pL³ 4) insG³ ≡ 120
_ = refl

-- MEASURED-NOT-RECHECKED (scripts/measure.sh, and mFib at k = 6
-- reproduced by the compiled harness):
--     mFib 0 (pL³ 5) insG³ = 127
--     mFib 0 (pL³ 6) insG³ = 128    ← attains 2 ^ 7 exactly
--     mPre 0 (pL³ 6) insG³ = 22
--     mPre 0 (pG′³ 0) insG³ = 22    mFib 0 (pG′³ 0) insG³ = 29
-- The fibre down the lean three-level ladder therefore runs
-- 8, 29, 64, 99, 120, 127, 128 against a 2 ^ cReg of 128 — the first five
-- pinned above, the last two here.  Gated at the numerals below

-- THE REFUTATION: the fibre is over cSize on both lean families
_ : (4 ≤ᵇ 3) ≡ false
_ = refl

_ : (8 ≤ᵇ 3) ≡ false
_ = refl

-- AND THE REPAIRED BOUNDS: both coordinates under 2 ^ cReg
_ : (4 ≤ᵇ 2 ^ 3) ≡ true
_ = refl

_ : (2 ≤ᵇ 2 ^ 3) ≡ true
_ = refl

_ : (10 ≤ᵇ 2 ^ 5) ≡ true
_ = refl

_ : (13 ≤ᵇ 2 ^ 5) ≡ true
_ = refl

_ : (22 ≤ᵇ 2 ^ 7) ≡ true
_ = refl

_ : (8 ≤ᵇ 2 ^ 7) ≡ true
_ = refl

-- and the row where the second coordinate is EXACTLY at its cap.  The
-- bound is ATTAINED, so it is tight — no smaller function of cReg can
-- replace it — and there is no margin left in it either
_ : (128 ≤ᵇ 2 ^ 7) ≡ true
_ = refl

_ : (129 ≤ᵇ 2 ^ 7) ≡ false
_ = refl

-- and the count they give, against the worst j in the file
_ : (324 ≤ᵇ 2 ^ 7 * 2 ^ 7 * 8) ≡ true
_ = refl

_ : (1291 ≤ᵇ 2 ^ 7 * 2 ^ 7 * 50) ≡ true
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 7: THE FOURTH LADDER, AND ITS K-SWEEP.
--
-- MEASUREMENT 6 found the fibre ATTAINING `2 ^ cReg` on the three-level
-- lean ladder — 128 against 128 — and a bound that is attained has no
-- margin.  It also found the ratio of fibre to cap climbing with ladder
-- depth: 2/8, 13/32, 128/128.  So this runs one more rung, and then runs
-- that rung out in k as far as anything can compute it.
--
-- EVERY ROW HERE IS MEASURED-NOT-RECHECKED.  k = 0, 1, 2 were `refl` pins
-- until the wall stopped finishing: they cost more than the rest of both
-- files together (`mMints 0 (pL⁴ 2) insG⁴` alone is ten minutes in the
-- typechecker), so they are now recorded numerals like the rest, and the
-- gates below are `refl` on those numerals.  k ≥ 3 was never pinnable at
-- all — `mFolds 0 (pL⁴ 3) insG⁴` was killed at 12.6 GB after 20 minutes —
-- and comes off the COMPILED harness `probe/Measure-Main.agda`, whose
-- calibration rows reproduce the numbers this file used to pin.
--
--   k   cReg  cSize       D    D/4^cReg    mints  mints/D       j    mFib
--   0     9      3      166    0.00063       15    0.090      182      16
--   1     9     10      726    0.00277      120    0.165     1542     121
--   2     9     18     2546    0.00971      575    0.226     8122     576
--   3     9     26     6914    0.02637     1940    0.281    29234    1941
--   4     9     34    14922    0.05692     4943    0.331    78010    4944
--   5     9     42    26362    0.10056     9948    0.377   162666       —
--   6     9     50        —          —        —        —        —       —
--
--   mPre = 46 at k = 0 … 4.  k = 6 is NOT MEASURED: 40 minutes at 12.4 GB
--   under a compacting collector, killed — recorded, not omitted.
--
-- `fibreCap ≤ 2 ^ cReg` IS FALSE and gets worse the further out the sweep
-- goes: 576, 1941, 4944 against 512.  No constant multiple of `2 ^ cReg`
-- is safe either.
--
-- THE FIRST COORDINATE, BY CONTRAST, IS EXACTLY WHAT THE STORY SAID.
-- mPre is 4, 10, 22, 46 down the four ladders — `3 * 2 ^ L - 2`, with an
-- entry registry of `2L + 1`, so it is about `2 ^ (cReg / 2)` and sits at
-- a QUARTER of its cap's exponent.  And it is invariant in k out to the
-- last row that could be measured.
--
-- SO THE SPLIT IS DEAD, and it is dead for a reason worth writing down.
-- D = mPre * (fibre), mPre is small and genuinely pre-state, and the
-- fibre is therefore essentially D itself.  Splitting D into (something
-- small) times (something the size of D) renames the problem instead of
-- decomposing it, so the delivery count has to be bounded WHOLE:
--
--     D ≤ 2 ^ cReg * 2 ^ cReg
--
-- which is what `cascadeGo-deliveries` states, unsplit — and which every
-- row above satisfies.  WITH HOW MUCH ROOM IS THE POINT OF THE SWEEP, and
-- the answer is: less than a factor of ten, at the deepest row that
-- computes, with the deliveries still growing 77 % per rung.  See the
-- STANDING WARNING at the head of Mint-Loop-Probe, instance 4
------------------------------------------------------------------

-- the entry caps, invariant in k: cReg 9 at k = 0 … 4, 6 and 10
_ : (9 ≤ᵇ 9) ≡ true
_ = refl

-- the fibre, refuted against its cap on three rows rather than one
_ : (576 ≤ᵇ 2 ^ 9) ≡ false
_ = refl

_ : (1941 ≤ᵇ 2 ^ 9) ≡ false
_ = refl

_ : (4944 ≤ᵇ 2 ^ 9) ≡ false
_ = refl

-- THE FIRST COORDINATE, still far inside its cap on the same rows
_ : (46 ≤ᵇ 2 ^ 9) ≡ true
_ = refl

-- AND THE UNSPLIT DELIVERY BOUND, gated on every ladder at the deepest k
-- each one reaches
_ : (5 ≤ᵇ 2 ^ 3 * 2 ^ 3) ≡ true
_ = refl

_ : (27 ≤ᵇ 2 ^ 5 * 2 ^ 5) ≡ true
_ = refl

_ : (269 ≤ᵇ 2 ^ 7 * 2 ^ 7) ≡ true
_ = refl

-- the L = 4 sweep, k = 0 … 5
_ : (166 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

_ : (726 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

_ : (2546 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

_ : (6914 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

_ : (14922 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

_ : (26362 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

-- THE TEN-TIMES-WORSE COMPARISON, WHICH THIS LADDER BREAKS.  At k = 2 it
-- held with room to spare; five rungs on it is false.  That is the whole
-- finding of the k-sweep in one pair of assertions
_ : (2546 * 10 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

_ : (26362 * 10 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ false
_ = refl

-- and the frames on the same ladder, against `2 ^ cReg * 2 ^ cReg * cSize`
_ : (162666 ≤ᵇ 2 ^ 9 * 2 ^ 9 * 42) ≡ true
_ = refl

-- against the tighter `2 ^ cReg * cSize * cSize` the frame gate uses, the
-- L = 4 ladder's j is still inside — 0.18 of it at k = 5, its worst row
_ : (162666 ≤ᵇ 2 ^ 9 * 42 * 42) ≡ true
_ = refl

_ : (78010 ≤ᵇ 2 ^ 9 * 34 * 34) ≡ true
_ = refl
