------------------------------------------------------------------
-- STANDING WARNING — DO NOT EXTRAPOLATE FROM SHALLOW ROWS.
--
-- It is at the top because the next reader of any measurement table in
-- this family will reach for the trend before the last row, and this
-- family has punished exactly that FOUR times now.  Every one of them
-- looked like a settled trend at the depth then affordable:
--
--   1. THE CROSSOVER INVISIBLE BELOW k = 7.  Fold-Count-Probe's ladder
--      folds `2 ^ k` times against a budget of `12k + 6`.  Every depth
--      that probe can NORMALISE has the budget winning — 8 ≤ 42 at k = 3,
--      64 ≤ 78 at k = 6 — and the crossover is at k = 7, 128 against 90,
--      reachable only as arithmetic.  A "safe on every row we can check"
--      would have been false.
--
--   2. THE RATIO THAT FELL MONOTONICALLY UNTIL IT PEAKED AT k = 3.  This
--      file's own D-only reading said j falls in k.  Measured directly,
--      j / (2 ^ cReg * cSize) on the lean L = 3 ladder runs .15 .18 .24
--      .27 .27 .24 .20: the peak is INTERIOR.  Three rows of "monotone
--      fall" were three rows of a climb not yet turned over.
--
--   3. THE L = 4 FIBRE PROFILE THAT MATCHED L = 3 AT k = 1 AND BREACHED
--      TWO RUNGS LATER.  `fibreCap ≤ 2 ^ cReg` was ATTAINED at 128/128 on
--      L = 3 and looked fine on L = 4 at k = 1 (121 against 512).  At
--      k = 2 it is 576 — over the cap — and by k = 4 it is 4944, nearly
--      ten times it.
--
--   4. THE DELIVERY MARGIN THAT "GREW WITH LADDER DEPTH".  Finding (6)
--      below recorded the ratio `D / (2 ^ cReg * 2 ^ cReg)` falling
--      0.078, 0.026, 0.016, 0.0097 across the four ladders and read that
--      as margin to spare.  But those four numbers are taken at the
--      deepest k each ladder had then been swept to — and L = 4 had only
--      been swept to k = 2.  Swept to k = 5, L = 4 gives 0.10056: the
--      WORST ratio in the file, worse than the one-level ladder's 0.078,
--      and `D * 10 ≤ 2 ^ cReg * 2 ^ cReg` is now FALSE there.  The
--      "growing margin" was a comparison of a deep ladder's late rows
--      with a deeper ladder's early ones.
--
-- The pattern in all four: the k-direction turns over LATE, and a ladder
-- one level deeper turns over later still.  So a row is evidence about
-- that row.  Where a trend is claimed, the claim must name the last k
-- actually measured — and where the last two rows are still moving, say
-- so.  (On the current numbers: L = 3 flattens by k = 5, changing under
-- 1 % per rung; L = 4 at its last measurable row is still growing 77 %
-- per rung.  Saturation at L = 4 is NOT OBSERVED.)
--
-- WHAT DOES SURVIVE, AND WHAT MAKES IT DIFFERENT.  Exactly one claim
-- about this family has been tested OUT OF SAMPLE: the delivery closed
-- form of Mint-Loop-Shapes' MEASUREMENT 8(d) was written down, with five
-- exact L = 5 rows, and COMMITTED (probe/Delivery-Law-Prediction.md,
-- 9deeb29) before the L = 5 shapes existed.  Every rung this container
-- can reach — k = 0, 1, 2 — matched it exactly.  That is not a
-- counterexample to the four instances above; it is the procedure that
-- makes the difference.  A trend read off measured rows and extended is
-- what got punished four times.  A form sealed before the rows exist is
-- what did not.  The warning is against the first, not the second
------------------------------------------------------------------
-- THE MINT-LOOP PROBE: does the minting feedback loop CLOSE?
--
-- Fold-Count-Probe derived `j ≤ 2 ^ cReg * cSize` and gated it over four
-- share shapes.  One spot in that derivation is crude, and it is flagged
-- at the `frameBlowup` site: `shareAdmit` reads the registry AS OF THE
-- DISPATCH, not a snapshot taken at cascade entry, so a fold that MINTS a
-- registration on a shared slot widens the branching for every later
-- dispatch of that slot.  The honest recursion is
--
--     deliveries d ≤ 2 ^ R_end       R_end ≤ R₀ + d * (mints per delivery)
--
-- which has no closed bound on its face — substitute the second into the
-- first and the right side outruns the left forever.  Fold-Count-Probe's
-- family G sampled ONE rung of that loop (mint once, deliver to the
-- minted) and found four orders of magnitude of slack.  deepScan is the
-- standing lesson about what one rung of a tower is worth: it always
-- looks absorbable.
--
-- SO THIS PROBE CLOSES THE LOOP.  `mintG′ (suc k)` re-subscribes the
-- shared slot THROUGH A SCAN whose own step mints at level k, so a minted
-- chain can itself mint and branching feeds branching inside one cascade.
-- Nothing exotic: it is a scan under a share whose step function's
-- emitted observable subscribes that share, nested k deep.
--
-- TWO NUMBERS, AND THEY ARE NOT THE SAME NUMBER.  `D`, the DELIVERIES,
-- is one per registration the cascade folds into.  `j`, the conjunct's
-- own index, is one per FRAME STEPPED — what `foldPath-caps` accumulates
-- at its `↠` clause, and a delivery whose path is `root` or `share-sink`
-- costs none.  This file measured only D when it was written and read the
-- result as a statement about j.  MEASUREMENT 5 now counts j directly and
-- the two answers differ in kind, not just in scale, so both are kept and
-- each is used for what it settles.
--
-- THE FINDING: THE LOOP DOES NOT TOWER ON THE LADDERS THAT SATURATE —
-- but the ROUTE to the count is dead, the count itself had to change, and
-- the deepest ladder does not saturate within reach.  In detail:
--
--   (1) DELIVERIES SATURATE IN THE NESTING DEPTH, ON THREE LADDERS OF
--       FOUR.  k = 0 …:
--
--         L = 1    5   5   5
--         L = 2   20  26  27  27
--         L = 3   50 106 176 232 260 268 269        (lean variant)
--         L = 4  166 726 2546 6914 14922 26362      (lean; k = 6 unreachable)
--
--       Nesting buys deliveries and then stops buying them — on L = 1, 2
--       and 3.  The reason is structural: a rung only widens branching by
--       MINTING, a minted registration is only reachable by dispatches
--       that come AFTER it, and the number of dispatches still to come is
--       fixed by the PRE-STATE DAG.  Once the nesting is deeper than the
--       pre-state's remaining dispatch rounds, the extra levels are never
--       reached.
--
--       L = 4 IS NOT ONE OF THE THREE.  Its growth per rung is 4.37,
--       3.51, 2.72, 2.16, 1.77 — decelerating, but the last rung
--       measurable still buys 77 %, and the next one cannot be computed
--       (40 minutes at 12.4 GB, killed).  The mechanism above predicts it
--       will flatten; nothing measured says it has.
--
--   (2) THE ENTRY REGISTRY DOES NOT MOVE WITH k — 3, 5, 7, 9 for the four
--       ladders, every k (9 checked out to k = 10).  The nested scans are
--       subscribed mid-cascade and never at the root subscribe, which is
--       exactly why they looked dangerous: they are free at the pre-state
--       the budget is read off.
--
--   (3) BUT THE ENTRY cSize DOES, LINEARLY: each nesting level adds a
--       constant to the step function's syntax, so cSize climbs 3, 10,
--       18, 26, 34, 42, 50 — `8k + 2` for k ≥ 1, on both deep ladders.
--
--   (4) `D ≤ 2 ^ cReg` IS FALSE, and that is the derivation's own
--       intermediate step.  L = 3 lean, k = 2: 176 deliveries against an
--       entry registry of 7, and 2 ^ 7 = 128.  The DAG-path count is over
--       R_end, and the mint puts R_end above cReg — which is exactly what
--       the crude spot said and what this probe was run to price.  It is
--       priced, and the price is not zero: the intermediate claim is
--       refuted, so `D * cSize ≤ 2 ^ cReg * cSize` is unavailable, and
--       with it the whole "paths × frames-per-path" route.
--
--       What survives is the same injection with a SECOND COORDINATE:
--       deliveries into (subset of the pre-state registry) × (an index)
--       rather than into subsets alone.
--
--   (5) AND THE SPLIT INTO TWO COORDINATES IS DEAD, both ways it was
--       tried.  MEASUREMENT 6 gives the coordinates definitions and
--       measures them: the fibre of a pre-state class is 4 against a
--       cSize of 3 on the lean two-level ladder, so `≤ cSize` is out; it
--       then ATTAINS `2 ^ cReg` exactly (128 against 128) on the
--       three-level one, and MEASUREMENT 7 runs a fourth ladder where it
--       reaches 576 against a cap of 512 — and 4944 against it two rungs
--       further on.  So `≤ 2 ^ cReg` is out too, and no constant multiple
--       of it is safe.
--
--       The FIRST coordinate is exactly what the story said — mPre is
--       4, 10, 22, 46 for entry registries of 3, 5, 7, 9, about
--       `2 ^ (cReg / 2)`, and invariant in k because the pre-state
--       classes are fixed by the pre-state DAG.  Which is precisely why
--       the split does not decompose anything: D is (something small)
--       times (something the size of D).
--
--   (6) SO THE DELIVERY BOUND IS STATED WHOLE: `D ≤ 2 ^ cReg * 2 ^ cReg`,
--       gated on every row in both files.  The count is
--       `2 ^ cReg * 2 ^ cReg * cSize`.
--
--       ITS MARGIN DOES NOT GROW WITH LADDER DEPTH — that reading came
--       from comparing L = 3 at k = 6 with L = 4 at k = 2, and it is
--       STANDING WARNING instance 4.  At the deepest k each ladder
--       reaches, `D / (2 ^ cReg * 2 ^ cReg)` is 0.078, 0.026, 0.016 and
--       0.10056: the fourth ladder is the worst row in the file, and
--       `D * 10 ≤ 2 ^ cReg * 2 ^ cReg` is false there.  The bound HOLDS
--       everywhere measured.  It holds by a factor under ten.
--
--   (7) j DOES NOT FALL MONOTONICALLY IN k, which the D-only reading of
--       this file claimed.  L = 3 lean, j against the intermediate
--       `2 ^ cReg * cSize`:
--
--         k        0     1     2     3     4     5     6
--         j       58   226   548   912  1164  1268  1291
--         ratio  .15   .18   .24   .27   .27   .24   .20
--
--       It PEAKS at k = 3 and only then falls — j keeps climbing after D
--       has flattened, because the nesting lengthens the chains even once
--       it stops widening them.  The peak is interior, so "deeper is
--       safer" was the wrong lesson; the right one is that both j and D
--       saturate while cSize does not — ON THE LADDERS THAT SATURATE.
--       This is STANDING WARNING instance 2.
--
-- THE FEEDBACK IS REAL rxjs, not an evaluator artefact, and that had to
-- be checked because it is what decides whether the loop exists at all.
-- In rxjs 7.8:
--
--     const src = new Subject();
--     const s = merge(src, src).pipe(share());   // one arrival, two emissions
--     let armed = true;
--     s.subscribe(v => { log('A' + v);
--       if (armed) { armed = false; s.subscribe(w => log('B' + w)); } });
--     src.next(1);                               // ⇒  A1 A1 B1
--
-- A subscriber added mid-cascade misses the IN-FLIGHT emission and
-- receives the cascade's LATER ones — which is precisely the evaluator's
-- behaviour, and precisely what makes a mid-cascade mint able to widen
-- the same cascade.
--
-- WHAT IS MEASURED HOW, AND HOW IT IS RECORDED.  The pre-state caps
-- (`mReg`, `mS` at fuel 0) are cheap on the shallow ladders: they need
-- only the root subscribe.  The fold counts never are — every one re-runs
-- the evaluator through a real cascade — so they are pinned by `refl` and
-- the gate is then arithmetic over the pinned numbers, the same economy
-- Fold-Count-Probe's crossover uses.  Past a depth they cannot be pinned
-- at all, and a number is then in exactly one of two other states, both
-- explicit:
--
--   · MEASURED-NOT-RECHECKED (typechecker): read off a normal form by
--     `scripts/measure.sh`, too expensive to leave in a wall that has to
--     finish.  Its numerals are gated by `refl` arithmetic.
--   · MEASURED-NOT-RECHECKED (compiled): read off `probe/Measure-Main.agda`
--     through the GHC backend, for rows the typechecker cannot normalise
--     at all — `mFolds 0 (pL⁴ 3) insG⁴` was killed at 12.6 GB after 20
--     minutes; compiled it answers in seconds.  Believed only because the
--     harness's calibration rows reproduce the pinned ones exactly.
--
-- There is no silent third state, and a row that could not be measured is
-- recorded as not measured rather than dropped.
--
-- TWO RUNGS ARE MISSING AND THEY ARE NAMED.  The ACCUMULATING three-level
-- ladder at k = 1 (`mFolds 0 (pG′³ 1) insG³`) does not normalise — 46
-- minutes and 7.2 GB without an answer.  Its k-sweep is carried by the
-- LEAN variant, which drops the `accV` occurrence from the step so the
-- accumulator stays a fixed term while every registration, dispatch and
-- delivery is unchanged.  The lean and accumulating families are not the
-- same program (the lean one delivers less: 16 vs 20 at L = 2, k = 0), so
-- the lean sweep is evidence about the SHAPE of the k-dependence, and the
-- accumulating family is gated wherever it does normalise.  And the LEAN
-- FOUR-level ladder at k = 6 is not measured by either harness: 40
-- minutes at 12.4 GB under a compacting collector, killed.
------------------------------------------------------------------
-- The families and the measures are in Mint-Loop-Shapes, so that
-- measuring one number does not pay for this file's pins.  MEASUREMENTS
-- 5, 6 and 7 — the frames, the two coordinates, and the fourth ladder —
-- are in Mint-Loop-Frames, because ONE wall over these families does not
-- finish: combined it ran past fifty minutes and was killed.  Everything
-- below is MEASUREMENTS 1 to 4 and the delivery gate.
------------------------------------------------------------------
module Mint-Loop-Probe where

open import Data.Nat  using (ℕ; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Mint-Loop-Shapes

------------------------------------------------------------------
-- MEASUREMENT 1: THE ENTRY REGISTRY IS INVARIANT IN THE NESTING DEPTH.
--
-- This is the fact that makes the family adversarial at all.  The nested
-- scans live inside a step function, so they are subscribed mid-cascade
-- and never at the root subscribe: they are FREE at the pre-state the
-- budget is read off.  If deliveries towered in k, the budget's
-- exponential would be reading a number that does not move
------------------------------------------------------------------

_ : mReg 0 (pG′ 0) insG ≡ 3
_ = refl

_ : mReg 0 (pG′ 2) insG ≡ 3
_ = refl

_ : mReg 0 (pG′² 0) insG² ≡ 5
_ = refl

_ : mReg 0 (pG′² 3) insG² ≡ 5
_ = refl

_ : mReg 0 (pL³ 0) insG³ ≡ 7
_ = refl

_ : mReg 0 (pL³ 6) insG³ ≡ 7
_ = refl

_ : mReg 0 (pG′³ 0) insG³ ≡ 7
_ = refl

-- MEASURED-NOT-RECHECKED, the fourth ladder's entry registry.  These are
-- minutes each in the typechecker because the TERM is large even where
-- the run is not — `mReg 0 (pL⁴ 3) insG⁴` alone is 159 s — so they are
-- recorded rather than pinned:
--     mReg 0 (pL⁴ k) insG⁴ = 9   for k = 0, 1, 2  (typechecker)
--                                    k = 3, 4     (typechecker)
--                                    k = 6, 10    (compiled harness)

------------------------------------------------------------------
-- MEASUREMENT 2: BUT THE ENTRY cSize IS LINEAR IN IT.
--
-- Each nesting level adds a constant to the step function's syntax, and
-- the step function is a `scan-f` frame on a registered chain, so
-- `pathSize` reads it.  cSize climbs by 8 (lean) or 14 (accumulating)
-- per level and never stops.  This is the budget's answer to the nesting:
-- `2 ^ cReg * cSize` grows in k even though `cReg` does not
------------------------------------------------------------------

_ : mS 0 (pL³ 0) insG³ ≡ 3
_ = refl

_ : mS 0 (pL³ 1) insG³ ≡ 10
_ = refl

_ : mS 0 (pL³ 2) insG³ ≡ 18
_ = refl

_ : mS 0 (pL³ 3) insG³ ≡ 26
_ = refl

_ : mS 0 (pL³ 4) insG³ ≡ 34
_ = refl

_ : mS 0 (pL³ 5) insG³ ≡ 42
_ = refl

_ : mS 0 (pL³ 6) insG³ ≡ 50
_ = refl

_ : mS 0 (pG′² 0) insG² ≡ 8
_ = refl

_ : mS 0 (pG′² 1) insG² ≡ 22
_ = refl

_ : mS 0 (pG′² 2) insG² ≡ 36
_ = refl

_ : mS 0 (pG′² 3) insG² ≡ 50
_ = refl

_ : mS 0 (pG′ 2) insG ≡ 36
_ = refl

_ : mS 0 (pG′³ 0) insG³ ≡ 8
_ = refl

-- MEASURED-NOT-RECHECKED, the same law one ladder deeper — the L = 4
-- cSize is the L = 3 cSize, rung for rung, which is what says the extra
-- shared level costs the SYNTAX nothing:
--     mS 0 (pL⁴ k) insG⁴ = 3, 10, 18  for k = 0, 1, 2  (typechecker)
--                        = 26, 34     for k = 3, 4     (typechecker, ~11 min each)
--                        = 42, 50     for k = 5, 6     (compiled harness)
--                        = 98         for k = 12       (compiled harness)
-- so `8k + 2` for k ≥ 1 on both deep ladders.  The k = 3 row was measured
-- BOTH ways and both say 26, which is one of the harness's calibrations

------------------------------------------------------------------
-- MEASUREMENT 3: THE DELIVERIES SATURATE — ON THREE LADDERS OF FOUR.
--
-- The question, in four rows.  Deeper nesting buys deliveries and then
-- stops buying them — 5 flat at one level, 27 at two, 269 at three.  A
-- rung can only widen branching by MINTING; a minted registration is
-- reachable only by dispatches that come AFTER it; and how many
-- dispatches are still to come is fixed by the PRE-STATE DAG.  Past that
-- depth the extra levels are never reached at all.
--
-- The FOURTH ladder's row is in Mint-Loop-Frames and it does NOT flatten
-- within reach: 166, 726, 2546, 6914, 14922, 26362, with k = 6
-- uncomputable.  Do not read the three flat ladders as covering it
------------------------------------------------------------------

-- one shared level: flat from the start
_ : mFolds 0 (pG′ 0) insG ≡ 5
_ = refl

_ : mFolds 0 (pG′ 1) insG ≡ 5
_ = refl

_ : mFolds 0 (pG′ 2) insG ≡ 5
_ = refl

-- two shared levels: rises, then stops
_ : mFolds 0 (pG′² 0) insG² ≡ 20
_ = refl

_ : mFolds 0 (pG′² 1) insG² ≡ 26
_ = refl

_ : mFolds 0 (pG′² 2) insG² ≡ 27
_ = refl

_ : mFolds 0 (pG′² 3) insG² ≡ 27
_ = refl

-- two shared levels, lean: the same shape at smaller numbers
_ : mFolds 0 (pL² 0) insG² ≡ 16
_ = refl

_ : mFolds 0 (pL² 2) insG² ≡ 21
_ = refl

_ : mFolds 0 (pL² 4) insG² ≡ 21
_ = refl

-- three shared levels: the longest climb, and it still flattens
_ : mFolds 0 (pL³ 0) insG³ ≡ 50
_ = refl

_ : mFolds 0 (pL³ 1) insG³ ≡ 106
_ = refl

_ : mFolds 0 (pL³ 2) insG³ ≡ 176
_ = refl

_ : mFolds 0 (pL³ 3) insG³ ≡ 232
_ = refl

_ : mFolds 0 (pL³ 4) insG³ ≡ 260
_ = refl

-- MEASURED-NOT-RECHECKED (typechecker; k = 6 also reproduced by the
-- compiled harness), the two rows where the climb flattens:
--     mFolds 0 (pL³ 5) insG³ = 268
--     mFolds 0 (pL³ 6) insG³ = 269
-- 268 → 269 is 0.4 % per rung, which is what "flattens" means here and
-- what the fourth ladder conspicuously does not do.  Gated below

-- and the accumulating three-level ladder at the one rung it reaches,
-- which is the tightest single point in the file: 106 deliveries against
-- a pre-state registry of 7
_ : mFolds 0 (pG′³ 0) insG³ ≡ 106
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 4: ACROSS INSTANTS, where the mints of one cascade are the
-- registry of the next.  This is the direction the recursion actually
-- runs, and it is self-limiting for the same reason: every extra
-- delivery costs a REGISTRATION, and a registration doubles the budget.
-- Deliveries grow additively in what minting adds; the budget grows
-- multiplicatively in it
--
--     k  instant   folds   cReg   cSize
--     0     0        5       3      8
--     0     1       13       6     21
--     0     2       29      13     39
--     2     0        5       3     36
--     2     1       20       7     77
--     2     2      114      35    151
--
-- The last row is MEASURED-NOT-RECHECKED (typechecker) rather than
-- pinned: it is a 114-delivery cascade over a 35-registration registry
-- and costs more than the other thirty assertions together.  Nothing
-- rests on it — it is the row that shows the trend continuing, and the
-- trend is already `refl`-checked twice above it
------------------------------------------------------------------

_ : mFolds 1 (pG′ 0) insG ≡ 13
_ = refl

_ : mReg 1 (pG′ 0) insG ≡ 6
_ = refl

_ : mS 1 (pG′ 0) insG ≡ 21
_ = refl

_ : mFolds 2 (pG′ 0) insG ≡ 29
_ = refl

_ : mReg 2 (pG′ 0) insG ≡ 13
_ = refl

_ : mFolds 1 (pG′ 2) insG ≡ 20
_ = refl

_ : mReg 1 (pG′ 2) insG ≡ 7
_ = refl

_ : mS 1 (pG′ 2) insG ≡ 77
_ = refl

------------------------------------------------------------------
-- THE DELIVERY GATE: every row above against `2 ^ cReg * cSize` at the
-- tightest caps the pre-state admits.  This is NOT the conjunct — the
-- conjunct bounds j, and Mint-Loop-Frames gates that — it is the FIRST of
-- the two factors: the claim that deliveries inject into (subsets of the
-- pre-state registry) × (an index below cSize).  Arithmetic over the
-- pinned numbers rather than a re-run of the evaluator per assertion.
--
-- The row that matters is `176 ≤ 2 ^ 7 * 18`, because the SAME row has
-- `176 > 2 ^ 7`: the second coordinate is doing real work, and without
-- it the bound is false rather than loose
------------------------------------------------------------------

-- one shared level, k = 0, 1, 2:  5 against 2 ^ 3 * 8
_ : (5 ≤ᵇ 2 ^ 3 * 8) ≡ true
_ = refl

-- two shared levels, k = 0 … 3:  20, 26, 27, 27 against 2 ^ 5 * {8,22,36,50}
_ : (20 ≤ᵇ 2 ^ 5 * 8) ≡ true
_ = refl

_ : (26 ≤ᵇ 2 ^ 5 * 22) ≡ true
_ = refl

_ : (27 ≤ᵇ 2 ^ 5 * 36) ≡ true
_ = refl

_ : (27 ≤ᵇ 2 ^ 5 * 50) ≡ true
_ = refl

-- three shared levels, lean, k = 0 … 6 against 2 ^ 7 * {3,10,18,26,34,42,50};
-- the last two gate MEASURED-NOT-RECHECKED numerals
_ : (50 ≤ᵇ 2 ^ 7 * 3) ≡ true
_ = refl

_ : (106 ≤ᵇ 2 ^ 7 * 10) ≡ true
_ = refl

_ : (176 ≤ᵇ 2 ^ 7 * 18) ≡ true
_ = refl

_ : (232 ≤ᵇ 2 ^ 7 * 26) ≡ true
_ = refl

_ : (260 ≤ᵇ 2 ^ 7 * 34) ≡ true
_ = refl

_ : (268 ≤ᵇ 2 ^ 7 * 42) ≡ true
_ = refl

_ : (269 ≤ᵇ 2 ^ 7 * 50) ≡ true
_ = refl

-- the accumulating three-level ladder, the tightest point measured
_ : (106 ≤ᵇ 2 ^ 7 * 8) ≡ true
_ = refl

-- and across instants: 13 at (6, 21), 20 at (7, 77), 114 at (35, 151)
_ : (13 ≤ᵇ 2 ^ 6 * 21) ≡ true
_ = refl

_ : (20 ≤ᵇ 2 ^ 7 * 77) ≡ true
_ = refl

_ : (114 ≤ᵇ 2 ^ 35 * 151) ≡ true
_ = refl

------------------------------------------------------------------
-- THE ROUTE IS DEAD, and this is where it dies.  The derivation at the
-- `frameBlowup` site reads
--
--     deliveries ≤ 2 ^ cReg        frames per delivery ≤ cSize
--
-- and the LEFT one is false on a program a few assertions above: L = 3
-- lean at k = 2 delivers 176 times out of an entry registry of 7.  The
-- DAG-path count is `2 ^ R_end`, the mint lifts R_end above cReg, and the
-- excess MATERIALISES rather than being damped away.  So the product
-- route does not merely lose slack, it loses the inequality: the
-- intermediate quantity `D * cSize` is itself over the old budget.
--
-- The fourth ladder makes the same point without needing the nesting to
-- be deep: 166 deliveries at k = 0 against a `2 ^ cReg` of 512 is fine,
-- 2546 at k = 2 is five times it, and 26362 at k = 5 is fifty
------------------------------------------------------------------

_ : (176 ≤ᵇ 2 ^ 7) ≡ false
_ = refl

_ : (176 * 18 ≤ᵇ 2 ^ 7 * 18) ≡ false
_ = refl

_ : (2546 ≤ᵇ 2 ^ 9) ≡ false
_ = refl

_ : (26362 ≤ᵇ 2 ^ 9) ≡ false
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 8: THE BRANCHING PROFILES — AND NOT ONE ROW OF IT IS
-- PINNED HERE, which is a fact about the MEASURES and not about the
-- numbers.  `mFolds` normalises cheaply because it forces
-- `EvalSt.delivered`, a list of RegIds.  `mFires` and `mDelivs` read
-- the cascade's EMIT STREAM, so the typechecker has to build every
-- emitted value to get at the event constructors, and that is the
-- expensive half of the evaluator.  Pinning even the share-DAG control
-- with no scan under it — `mFires 0 pS³ insG³`, a thirty-delivery
-- cascade — ran past ten minutes; with the ladders in, this file ran
-- past forty-five and was killed twice.
--
-- So MEASUREMENT 8 is MEASURED-NOT-RECHECKED (compiled) IN FULL, and
-- its tables are in Mint-Loop-Shapes.  What stands in for the `refl`
-- state is three calibrations the tables carry, each against a number
-- this wall or the mints table already holds:
--
--   · every delivery row SUMS to the pinned `mFolds` — 50, 106, 176,
--     232, 260 above, and 269 and the whole four-level row next door;
--   · every generation row SUMS to the recorded `mMints` — 92 at
--     pL³ 2, 254 at pL³ 6, 575 at pL⁴ 2;
--   · and the mirror's own fire count (`mFiresM`, off the walk that
--     produces `j`) equals the evaluator's handoff count on pL² 2,
--     pL³ 2 and pL⁴ 2, so the two harnesses are counting one event.
--
-- A row that could not be measured is still recorded as not measured:
-- `mGens 0 (pL⁴ 5) insG⁴` and `mGenMax 0 (pL⁴ 5) insG⁴` were killed and
-- are absent from the tables rather than guessed at
------------------------------------------------------------------
