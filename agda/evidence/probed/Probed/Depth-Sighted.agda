-- THE SIGHTED DESCENT CEILING, INSTANTIATED AT THE FAMILY THAT KILLED
-- THE BARE SUM.  Both leaves of the depth split say a sweep descends no
-- further than a function of what it can SEE, and every summand is
-- computed rather than bounded, so the rows below read the two sides at
-- states the evaluator actually reaches and compare them directly.
--
-- LOAD-BEARING ON THE CEILING'S SHAPE, WHICH IS WHAT THEY SETTLED.  A
-- row fails exactly when the descent passes the ceiling, and two
-- cheaper shapes were failed here rather than argued away: a bare
-- multiple of the three nesting summands, and that sum with the
-- program's size added rather than multiplied.  The rows are read along
-- BOTH axes the corpus varies -- the fold depth, which every summand
-- sees, and the delivered count, which none of them does -- because a
-- ceiling calibrated on one axis is a fitted constant until a second
-- axis agrees.
--
-- THE PARTS ROW IS THE FINDING AND NOT A DIAGNOSTIC.  It reads nine
-- quantities at two programs that differ only in the delivered count,
-- and every sighted one of them is identical while the descent moves by
-- a third; the program's size is the sole separator.  That is what
-- rules out repairing the ceiling by enlarging a summand, and it is not
-- visible from either side's pass/fail alone.
--
-- THE PREMISES ARE NOT DISCHARGED AND CANNOT BE.  `capsOK?` computes
-- nowhere -- `capsAt` sits on the caps recurrence and does not
-- terminate even natively -- so these are conclusion-side rows, which
-- is the coverage this can have rather than a gap in the sweeping.
-- TARGET: sight-all @8d81ef
-- TARGET: sight-scan @d7eb02
-- TARGET: cascade-depth-sighted @ebd9e3
module Probed.Depth-Sighted where

open import Data.Nat using (ℕ; suc; _+_; _*_; _^_)
open import Data.List using (length; map)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; obs; sizeᵛ; sizeᵉ; syncSizeᵉ;
  ofᵉ; scanᵉ; mergeAllᵉ; input; varᵗ; inlᵗ; caseᵗ; fstᵗ; strmᵗ; nat̂; emptyᵉ; Tm)
open import Data.Maybe using (nothing)
open import Data.List using ([]; _∷_) renaming (map to mapL)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Fin using (zero)
open import Rx.Prim using (gasPad; g0)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainsOf; arrTy; arrVal; budgetAt; LiveSource)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)

open import Refuted.Demand-Programs
  using (Γ₂; progU; progF; insT; insF; sucGU; sucGF)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthCascade)
open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; nestUnit; sightCeil)

-- ── the subscribe side, at the root ────────────────────────────────

slotsT : Slots Γ₂
slotsT = insT 1 2 0

descRoot : ℕ → ℕ
descRoot k =
  depthE (budgetAt (progU k 2) slotsT 0) (progU k 2) root 0 0
         (sched-init (progU k 2) slotsT) (st-init (progU k 2))

sightRoot : ℕ → ℕ
sightRoot k =
  sightCeil (sizeᵉ (progU k 2)) (2 ^ syncSizeᵉ (progU k 2) * nestDᵉ (progU k 2))
            (storeNestMax (sched-init (progU k 2) slotsT) (st-init (progU k 2)))
            (nestUnit (progU k 2) slotsT)

-- packed base-10^41 so one build returns every figure: Agda aborts a
-- module at its first mismatch, so a tuple of pins leaks one number per
-- build and a sum leaks all of them at once
rootFigs : ℕ
rootFigs = descRoot 2 + 100000000000000000000000000000000000000000 * (sightRoot 2
         + 100000000000000000000000000000000000000000 * (descRoot 20 + 100000000000000000000000000000000000000000 * sightRoot 20))

rootFigs≡ : rootFigs ≡ 2816719633707125730125674522348300000000000000000000000000000000000000000810000000000000000000000000000003113851318600000000000000000000000000000000000000009

-- ── the delivery side, at the second cascade ───────────────────────

slotsF : Slots Γ₂
slotsF = insF 1 2 2

-- ONE FAMILY'S SECOND CASCADE, WHERE THE DRAIN HAS SOMETHING PARKED.
-- Written over the program rather than over a fold depth, so the same
-- three lines read every axis the corpus varies.
sub : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → Sched Γ₂ × EvalSt p
sub p sl g = let r = subscribeE (gasPad g g0) p root 0 0
                                (sched-init p sl) (st-init p)
             in proj₁ (proj₂ r) , proj₂ (proj₂ r)

after1 : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → Sched Γ₂ × EvalSt p
after1 p sl g with sched-next (proj₁ (sub p sl g))
... | inj₁ _        = sub p sl g
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ (sub p sl g))
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

delivRow : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → ℕ × ℕ
delivRow p sl g with sched-next (proj₁ (after1 p sl g))
... | inj₁ _        = 0 , 0
... | inj₂ (a , sd) =
  let st = proj₂ (after1 p sl g)
  in depthCascade a 2 (chainsOf a st) sd (cascadeLatch a st)
   , sightCeil (sizeᵉ p) (nestDᵛ (arrTy a) (arrVal a))
               (storeNestMax sd st) (nestUnit p (Sched.slots sd))

uRow : ℕ → ℕ × ℕ
uRow d = delivRow (progU d 2) slotsF (sucGU 1 2 2 d 2)

delivFigs : ℕ
delivFigs = proj₁ (uRow 2) + 1000000 * proj₂ (uRow 2)
          + 1000000000000 * proj₁ (uRow 8)
          + 1000000000000000000 * proj₂ (uRow 8)

delivFigs≡ : delivFigs ≡ 1219000049000319000013

-- ── the count axis, which is where the two cheaper shapes died ──────

-- the delivered COUNT rather than the fold depth, and the WIDTH family,
-- whose mergeAll is unbounded and therefore drains nothing.
natsRow : ℕ × ℕ
natsRow = delivRow (progU 8 6) slotsF (sucGU 1 2 2 8 6)

widRow : ℕ × ℕ
widRow = delivRow (progF 3 2) slotsF (sucGF 1 2 2 3 2)

axisFigs : ℕ
axisFigs = proj₁ natsRow + 1000000 * proj₂ natsRow
         + 1000000000000 * proj₁ widRow
         + 1000000000000000000 * proj₂ widRow

axisFigs≡ : axisFigs ≡ 465000013001311000081

-- THE COUNT AXIS AT FOUR TIMES THE REACH, which is what separates a
-- size SUMMAND from a size FACTOR: size gains one per delivered value
-- and the descent gains eight, so the summand is outrun.
farRow : ℕ × ℕ
farRow = delivRow (progU 8 20) slotsF (sucGU 1 2 2 8 20)

farFigs : ℕ
farFigs = proj₁ farRow + 1000000 * proj₂ farRow
        + 1000000000000 * sizeᵉ (progU 8 20)

farFigs≡ : farFigs ≡ 70001633000193

-- ── THE THIRD INSTANT, WHICH NOTHING HAS EVER REACHED ──────────────

-- Every row above stops at the SECOND cascade, so the ceiling's
-- coverage ended exactly where the caps recurrence starts growing.
-- One more `cascade` is the whole apparatus needed to ask -- and the
-- scripted slot has to be handed a THIRD value, since it emits exactly
-- as many as it is given and every row above gives it two.  That is
-- the only reason the region read as unreachable.
--
-- LOAD-BEARING, and it fails if the descent passes the ceiling at the
-- third instant on either fold depth.  It does not: both sides grow,
-- and the ceiling grows faster.  A zero pair here would have been the
-- other finding -- the run stopping short, a corpus boundary rather
-- than a ceiling one.
after2 : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → Sched Γ₂ × EvalSt p
after2 p sl g with sched-next (proj₁ (after1 p sl g))
... | inj₁ _        = after1 p sl g
... | inj₂ (a , sd) =
  let r = cascade a 2 sd (proj₂ (after1 p sl g))
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

deliv3Row : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → ℕ × ℕ
deliv3Row p sl g with sched-next (proj₁ (after2 p sl g))
... | inj₁ _        = 0 , 0
... | inj₂ (a , sd) =
  let st = proj₂ (after2 p sl g)
  in depthCascade a 3 (chainsOf a st) sd (cascadeLatch a st)
   , sightCeil (sizeᵉ p) (nestDᵛ (arrTy a) (arrVal a))
               (storeNestMax sd st) (nestUnit p (Sched.slots sd))

-- three scheduled values rather than two, since the corpus's hot slot
-- emits exactly as many as it is given and every row above took two
slotsF3 : Slots Γ₂
slotsF3 = insF 1 2 3

u3Row : ℕ → ℕ × ℕ
u3Row d = deliv3Row (progU d 2) slotsF3 (sucGU 1 2 3 d 2)

thirdFigs : ℕ
thirdFigs = proj₁ (u3Row 2) + 1000000 * proj₂ (u3Row 2)
          + 1000000000000 * proj₁ (u3Row 8)
          + 1000000000000000000 * proj₂ (u3Row 8)

thirdFigs≡ : thirdFigs ≡ 1590000057000348000015

-- THE COUNT AXIS AT THE THIRD INSTANT, AND THE WIDTH FAMILY THERE.
-- The rows above reach the third cascade on one family at one delivered
-- count, so the two axes the second instant is read along both stop one
-- instant short.  These close that: the same fold depth at three times
-- the count, and the family whose mergeAll is unbounded and therefore
-- drains nothing, both read where the caps recurrence has already
-- stepped twice.
--
-- LOAD-BEARING, and each fails if its descent passes its ceiling.  A
-- zero pair is the other finding rather than a pass -- it says the run
-- stopped before the instant, which is a corpus boundary and not a
-- ceiling one.
u3cRow : ℕ × ℕ
u3cRow = deliv3Row (progU 8 6) slotsF3 (sucGU 1 2 3 8 6)

w3Row : ℕ × ℕ
w3Row = deliv3Row (progF 3 2) slotsF3 (sucGF 1 2 3 3 2)

third2Figs : ℕ
third2Figs = proj₁ u3cRow + 1000000 * proj₂ u3cRow
           + 1000000000000 * proj₁ w3Row
           + 1000000000000000000 * proj₂ w3Row

third2Figs≡ : third2Figs ≡ 589000017001710000089

-- THE CORNER WHERE BOTH EROSIONS COMPOUND, which is the one cell worth
-- reading once the other two axes are.  The count is what the ceiling
-- cannot see, so its margin is the one that narrows -- and the instant
-- is where the descent has had the most chances to accumulate.  Read
-- at the far end of the count axis at the third instant, so a shape
-- that only survives by being taken at small counts fails here.
u3fRow : ℕ × ℕ
u3fRow = deliv3Row (progU 8 20) slotsF3 (sucGU 1 2 3 8 20)

cornerFigs : ℕ
cornerFigs = proj₁ u3fRow + 1000000 * proj₂ u3fRow

cornerFigs≡ : cornerFigs ≡ 2130000201

-- THE ROOT SIDE OFF ITS ONE FAMILY AND ITS ONE SLOT VOCABULARY, which
-- is the whole of what that side's coverage was missing: every row
-- above reads the subscribe descent at `progU` under the late-connect
-- vocabulary alone.  The width family and the hot vocabulary are the
-- two nearest things it is not, and neither shares the fold depth the
-- calibration was taken at.
descRootF : ℕ → ℕ
descRootF w =
  depthE (budgetAt (progF w 2) slotsF 0) (progF w 2) root 0 0
         (sched-init (progF w 2) slotsF) (st-init (progF w 2))

sightRootF : ℕ → ℕ
sightRootF w =
  sightCeil (sizeᵉ (progF w 2)) (2 ^ syncSizeᵉ (progF w 2) * nestDᵉ (progF w 2))
            (storeNestMax (sched-init (progF w 2) slotsF) (st-init (progF w 2)))
            (nestUnit (progF w 2) slotsF)

descRootH : ℕ → ℕ
descRootH k =
  depthE (budgetAt (progU k 2) slotsF 0) (progU k 2) root 0 0
         (sched-init (progU k 2) slotsF) (st-init (progU k 2))

sightRootH : ℕ → ℕ
sightRootH k =
  sightCeil (sizeᵉ (progU k 2)) (2 ^ syncSizeᵉ (progU k 2) * nestDᵉ (progU k 2))
            (storeNestMax (sched-init (progU k 2) slotsF) (st-init (progU k 2)))
            (nestUnit (progU k 2) slotsF)

rootWideFigs : ℕ
rootWideFigs = descRootF 3 + 100000000000000000000000000000000000000000 * (sightRootF 3
             + 100000000000000000000000000000000000000000 * (descRootH 8 + 100000000000000000000000000000000000000000 * sightRootH 8))

rootWideFigs≡ : rootWideFigs ≡ 2386907802506363728000000000000000000000000000000000000000040000000000000000000000000000009985798991100000000000000000000000000000000000000005

-- ── which sighted quantity sees the count, and the answer is none ───

-- Nine readings per program, packed base-1000 in the order named, at
-- the two programs whose descents differ by a third.
pendCount : LiveSource Γ₂ → ℕ
pendCount ls = length (LiveSource.pending ls)

partsRow : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → ℕ
partsRow p sl g with sched-next (proj₁ (after1 p sl g))
... | inj₁ _        = 0
... | inj₂ (a , sd) =
  let st = proj₂ (after1 p sl g)
  in nestDᵛ (arrTy a) (arrVal a)
   + 1000 * storeNestMax sd st
   + 1000000 * nestUnit p (Sched.slots sd)
   + 1000000000 * length (chainsOf a st)
   + 1000000000000 * length (EvalSt.registry st)
   + 1000000000000000 * sizeᵛ (arrTy a) (arrVal a)
   + 1000000000000000000 * length (Sched.live sd)
   + 1000000000000000000000 * sum (map pendCount (Sched.live sd))
   + 1000000000000000000000000 * sizeᵉ p

partsFigs : ℕ
partsFigs = partsRow (progU 8 2) slotsF (sucGU 1 2 2 8 2)
          + 1000000000000000000000000000 * partsRow (progU 8 6) slotsF (sucGU 1 2 2 8 6)

partsFigs≡ : partsFigs ≡ 56000001001001001013009000052000001001001001013009000

-- the size axis on its own, so the slope claims above are readable
sizeFigs : ℕ
sizeFigs = sizeᵉ (progU 2 2) + 1000 * sizeᵉ (progU 8 2)
         + 1000000 * sizeᵉ (progU 20 2) + 1000000000 * sizeᵉ (progF 3 2)

sizeFigs≡ : sizeFigs ≡ 30100052028

rootFigs≡ = refl
delivFigs≡ = refl
axisFigs≡ = refl
farFigs≡ = refl
partsFigs≡ = refl
sizeFigs≡ = refl
thirdFigs≡ = refl
third2Figs≡ = refl
cornerFigs≡ = refl
rootWideFigs≡ = refl


-- ── THE SCAN'S OWN SEED, which is the one shape the corpus above has
-- no example of.  Every family there folds from a seed weighing
-- nothing, so the install a scan makes is free and the clause's
-- arithmetic never shows.  This one seeds from the term
-- `Refuted.Eval-Seed-Nest` is built around -- a `caseᵗ` whose branch
-- names its bound observable on both sides of a sum -- so the node the
-- scan installs is strictly deeper than the seed's own charge, which is
-- the state the clause cannot pay for.
--
-- LOAD-BEARING, and it is the clause's OWN statement that is read: the
-- program's head is the scan, so the root call is the leaf at the empty
-- path rather than an assembly that happens to contain one.  The row
-- fails exactly when the ceiling loses to the descent at the shape
-- whose local route is known dead, which is what decides whether the
-- statement needs restating or only a different decomposition.

-- the scrutinee, wrapped `d` deep, so the seed's own nesting is an AXIS
-- rather than a constant
deep : ℕ → Closed Γ₂ natᵗ
deep 0       = ofᵉ (nat̂ 0 ∷ [])
deep (suc d) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep d) ∷ []))

seedTm : ℕ → Tm Γ₂ [] [] [] (obs (obs natᵗ))
seedTm d =
  caseᵗ {s = obs natᵗ} {t = obs natᵗ}
    (inlᵗ (strmᵗ (deep d)))
    (strmᵗ (scanᵉ (fstᵗ (varᵗ (here refl)))
                  (varᵗ (here refl))
                  (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))))
    (strmᵗ emptyᵉ)

-- THE PROGRAM'S HEAD IS THE SCAN ITSELF, so the root call IS the
-- clause's statement at the empty path rather than a reading of the
-- assembly that happens to contain one
progSeed : ℕ → Closed Γ₂ (obs (obs natᵗ))
progSeed d = scanᵉ (fstᵗ (varᵗ (here refl))) (seedTm d) (input zero)

descSeed : ℕ → ℕ
descSeed d =
  depthE (budgetAt (progSeed d) slotsT 0) (progSeed d) root 0 0
         (sched-init (progSeed d) slotsT) (st-init (progSeed d))

sightSeed : ℕ → ℕ
sightSeed d =
  sightCeil (sizeᵉ (progSeed d)) (2 ^ syncSizeᵉ (progSeed d) * nestDᵉ (progSeed d))
            (storeNestMax (sched-init (progSeed d) slotsT) (st-init (progSeed d)))
            (nestUnit (progSeed d) slotsT)

-- the shallow seed and a seed four layers deep, packed together: two
-- ceilings and two descents, so one build says whether the margin
-- narrows as the seed's own nesting grows
seedFigs : ℕ
seedFigs = descSeed 1 + 100000000000000000000000000000000000000000 * (sightSeed 1
           + 100000000000000000000000000000000000000000 * (descSeed 4 + 100000000000000000000000000000000000000000 * sightSeed 4))

seedFigs≡ : seedFigs ≡ 26113401160098000000000000000000000000000000000000000030000000000000000000000000000000174483067200000000000000000000000000000000000000003
seedFigs≡ = refl
