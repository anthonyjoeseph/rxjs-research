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
--
-- THE SUBSCRIBE-SIDE ROWS READ THE `*All` HEAD WHOLE, which is the
-- join of a proven descent and the burst below it.  A green row is
-- therefore evidence about the WALK a fortiori -- the burst side is
-- under the join and the ceiling is the same one -- and it is NOT
-- evidence that the burst side alone has any particular margin, since
-- nothing here separates the two summands.  The burst's ENTRY FIT is
-- not covered at all: it is a hypothesis-side claim about the store
-- the payload subscribe hands back, and no row here computes it.  Nor
-- is the fit the walk leaf ASSUMES: its grant carries a slot summand
-- these rows never read, and a row that measures only a conclusion is
-- unmoved by a hypothesis widening -- which is exactly why re-running
-- them says nothing about the summand.
--
-- THE WIDTH IS READ AT NOUGHT, which is the smallest number the
-- ceiling admits and so the strongest reading: the grant is monotone
-- in it, so a row holding here holds at every legal `descW` bound.
-- TARGET: sight-all-walk @b9a208
-- TARGET: chain-depth-sighted @36ffe2
module Probed.Depth-Sighted where

open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤ᵇ_; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤m+n)
open import Data.List using (List; length; map)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; obs; sizeᵛ; sizeᵉ; ofᵉ; scanᵉ; mergeAllᵉ; input; varᵗ; inlᵗ; caseᵗ; fstᵗ;
  strmᵗ; nat̂; emptyᵉ; Tm; syncSizeᵉ; Fn; _×ᵗ_)
open import Data.Maybe using (nothing)
open import Data.List using ([]; _∷_) renaming (map to mapL)
open import Data.Bool using (Bool; true; false)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Rx.Prim using (gasPad; g0; cold; hot)
open import Rx.Slots using (Slots; Slot; scripted; shared)
open import Data.Nat.Properties using (≤-refl; ≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainsOf; arrTy; arrVal; budgetAt; LiveSource;
         Arrival; Path; thru-outer; mergeAllᵒ; installNode; mergeAll-st)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵉ)

open import Refuted.Demand-Programs
  using (Γ₂; progU; progF; insT; insF; sucGU; sucGF; asyncNats)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthCascade; depthChain; depthFrame)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps
  using (chain-depth-sighted)
open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; nestUnit; sightCeil; pathNestD; sightCeil-mono; fitB)
open import Verify-Budget-Sufficient.Nest-Cap using (nestB-base)
open import Verify-Budget-Sufficient.Depth-Sighted using (sight-all-walk)

open import Probed.Apparatus using (Confirms)


-- THE CEILING WRITTEN OUT, because the grant it reads sits inside the
-- sealed `nestB` and a sealed family does not reduce for a row.  What
-- follows is that grant's body at the root, at a width of NOUGHT --
-- the smallest number the ceiling admits and therefore the strongest
-- reading, since the grant is monotone in the width, so a row holding
-- here holds at every legal `descW` bound.  The slot sum is spelled at
-- the two slots this context has rather than folded, which is the same
-- number.
fac : ∀ {t} (p : Closed Γ₂ t) → ℕ → ℕ
fac p m = ((2 ^ sizeᵉ p) ^ suc 0) ^ m

wrap1 : ∀ {t j u} (p : Closed Γ₂ t) (sl : Slots Γ₂) → Slot Γ₂ j u → ℕ
wrap1 p sl (scripted _) = 0
wrap1 p sl (shared d)   =
  fac p (syncSizeᵉ d) * (nestDᵉ d + suc (syncSizeᵉ d) * nestUnit p sl)

fitOf : ∀ {t} (p : Closed Γ₂ t) (sl : Slots Γ₂) → ℕ
fitOf {t} p sl =
  fac p (syncSizeᵉ p)
    * ((pathNestD (root {Γ = Γ₂} {t = t}) + nestDᵉ p)
        + suc (syncSizeᵉ p) * nestUnit p sl)
  + 2 * (wrap1 p sl (sl zero) + wrap1 p sl (sl (fsuc zero)))

Sight : ∀ {t} (p : Closed Γ₂ t) (sl : Slots Γ₂) → ℕ
Sight p sl =
  sightCeil (sizeᵉ p) (fitOf p sl)
            (storeNestMax (sched-init p sl) (st-init p))
            (nestUnit p sl)

-- ── the subscribe side, at the root ────────────────────────────────

slotsT : Slots Γ₂
slotsT = insT 1 2 0

descRoot : ℕ → ℕ
descRoot k =
  depthE (budgetAt (progU k 2) slotsT 0) (progU k 2) root 0 0
         (sched-init (progU k 2) slotsT) (st-init (progU k 2))

sightRoot : ℕ → ℕ
sightRoot k =
  Sight (progU k 2) slotsT

-- THE CEILING IS NO LONGER A FIGURE TO PRINT, AND THAT IS THE READING.
-- Its grant is a tower whose exponent is the program's size times its
-- sync size, so a packed decimal of it would be thousands of digits
-- while the descent beside it is one.  So each section below reports
-- the two DESCENTS and the two EXPONENTS -- both small, both packed --
-- and states the comparison as its own row.  The margin is the gap
-- between a digit and a power of two in a two-figure exponent, which
-- is what the columns say and what a printed ceiling would not.
--
-- LOAD-BEARING: a row fails exactly when the descent passes the
-- ceiling.  Packed base-10^6, since Agda aborts a module at its first
-- mismatch and a sum leaks every field at once.  Base 10^9.
rootFigs : ℕ
rootFigs = descRoot 2 + 1000000000 * descRoot 20
         + 1000000000000000000 * (sizeᵉ (progU 2 2) * syncSizeᵉ (progU 2 2))
         + 1000000000000000000000000000 * (sizeᵉ (progU 20 2) * syncSizeᵉ (progU 20 2))

rootFigs≡ : rootFigs ≡ 10000000000784000000081000000009

rootRow : List Bool
rootRow = (descRoot 2 ≤ᵇ sightRoot 2) ∷ (descRoot 20 ≤ᵇ sightRoot 20) ∷ []

rootRow≡ : rootRow ≡ true ∷ true ∷ []

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
  Sight (progF w 2) slotsF

descRootH : ℕ → ℕ
descRootH k =
  depthE (budgetAt (progU k 2) slotsF 0) (progU k 2) root 0 0
         (sched-init (progU k 2) slotsF) (st-init (progU k 2))

sightRootH : ℕ → ℕ
sightRootH k =
  Sight (progU k 2) slotsF

rootWideFigs : ℕ
rootWideFigs = descRootF 3 + 1000000000 * descRootH 8
             + 1000000000000000000 * (sizeᵉ (progF 3 2) * syncSizeᵉ (progF 3 2))
             + 1000000000000000000000000000 * (sizeᵉ (progU 8 2) * syncSizeᵉ (progU 8 2))

rootWideFigs≡ : rootWideFigs ≡ 2704000000900000000004000000005

rootWideRow : List Bool
rootWideRow = (descRootF 3 ≤ᵇ sightRootF 3) ∷ (descRootH 8 ≤ᵇ sightRootH 8) ∷ []

rootWideRow≡ : rootWideRow ≡ true ∷ true ∷ []

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

-- ── the tie, at the chain leaf rather than the round ────────────────

-- Every reading above is taken at `depthCascade`, and the chain leaf
-- speaks about `depthChain`.  The round's descent is the JOIN over its
-- chains, so a green round is a green chain -- but that step is an
-- ARGUMENT, and the whole point of a tie is that no argument stands
-- between a row and the statement.  So the point below is the chain
-- itself: the second instant's arrival, the FIRST chain the registry
-- admits for it, and the state `depthCascade` hands that chain.
--
-- BOTH PREMISES ARE DISCHARGED, AT THE TIGHTEST VALUE EACH ADMITS.
-- The slots equation is reflexivity by taking `sl` to be the schedule's
-- own; the store bound is reflexivity by taking `S` to be the store's
-- own maximum.  Nothing is weakened by either -- the ceiling is
-- monotone in `S`, so the least admissible `S` is the strongest
-- reading, and a row here holds at every larger one a caller supplies.
--
-- NON-VACUITY IS PINNED AND NOT ASSERTED.  A point taken from an
-- exhausted schedule or an empty chain list falls to the default below,
-- whose descent is nought and whose row could not fail; the equation
-- pins the descent this point actually reaches, so the default is
-- visible as a number rather than hidden behind a green.
record Point (p : Closed Γ₂ natᵗ) : Set where
  constructor pt
  field
    arr : Arrival Γ₂
    pth : Path Γ₂ (arrTy arr) natᵗ
    sc  : Sched Γ₂
    stt : EvalSt p

noPoint : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) → Point p
noPoint p sl =
  pt (record { tick = 0 ; ordinal = 0 ; source = 0
             ; elemTy = natᵗ ; payload = 0 ; isLast = true })
     root (sched-init p sl) (st-init p)

point : (p : Closed Γ₂ natᵗ) (sl : Slots Γ₂) (g : ℕ) → Point p
point p sl g with sched-next (proj₁ (after1 p sl g))
... | inj₁ _        = noPoint p sl
... | inj₂ (a , sd) with chainsOf a (proj₂ (after1 p sl g))
...   | []            = noPoint p sl
...   | (rid , c) ∷ _ = pt a c sd (cascadeLatch a (proj₂ (after1 p sl g)))

uPt : Point (progU 8 2)
uPt = point (progU 8 2) slotsF (sucGU 1 2 2 8 2)

uArr : Arrival Γ₂
uArr = Point.arr uPt

uPth : Path Γ₂ (arrTy uArr) natᵗ
uPth = Point.pth uPt

uSc : Sched Γ₂
uSc = Point.sc uPt

uSt : EvalSt (progU 8 2)
uSt = Point.stt uPt

chainDesc : ℕ
chainDesc = depthChain 2 uArr uPth uSc uSt

chainDesc≡ : chainDesc ≡ 17

chainRow : Confirms
  (chain-depth-sighted (Sched.slots uSc) uArr 2 (storeNestMax uSc uSt)
     uPth uSc uSt refl ≤-refl)
chainRow = ≤ᵇ⇒≤ _ _ tt

-- AND THE SAME TIE AT THE FAR END OF THE COUNT AXIS -- WHERE THE
-- READING IS THAT THE CHAIN LEAF DOES NOT SEE THAT AXIS AT ALL, which
-- is a coverage boundary the round's rows cannot show and this row
-- reports as a number.  The round's descent moves with the delivered
-- count, forty-nine to one hundred and ninety-three, and it is that
-- movement the ceiling's shape was calibrated against.  The FIRST
-- chain's descent does not move: seventeen at both counts, pinned
-- either side.  So the growth lives wholly in the round's join over
-- LATER chains and the states they leave, which is `depthCascade`'s
-- territory and not this leaf's, and no row here -- at any count --
-- constrains the chain leaf along that axis.  What the second point
-- does reach is the ceiling and the store at the far count, both of
-- which move; what it does not reach is a descent that does.
fPt : Point (progU 8 20)
fPt = point (progU 8 20) slotsF (sucGU 1 2 2 8 20)

fArr : Arrival Γ₂
fArr = Point.arr fPt

fPth : Path Γ₂ (arrTy fArr) natᵗ
fPth = Point.pth fPt

fSc : Sched Γ₂
fSc = Point.sc fPt

fSt : EvalSt (progU 8 20)
fSt = Point.stt fPt

farDesc : ℕ
farDesc = depthChain 2 fArr fPth fSc fSt

farDesc≡ : farDesc ≡ 17

farChainRow : Confirms
  (chain-depth-sighted (Sched.slots fSc) fArr 2 (storeNestMax fSc fSt)
     fPth fSc fSt refl ≤-refl)
farChainRow = ≤ᵇ⇒≤ _ _ tt

rootFigs≡ = refl
rootRow≡ = refl
chainDesc≡ = refl
farDesc≡ = refl
rootWideRow≡ = refl
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
  Sight (progSeed d) slotsT

-- the shallow seed and a seed four layers deep, packed together: two
-- ceilings and two descents, so one build says whether the margin
-- narrows as the seed's own nesting grows
seedFigs : ℕ
seedFigs = descSeed 1 + 1000000000 * descSeed 4
         + 1000000000000000000 * (sizeᵉ (progSeed 1) * syncSizeᵉ (progSeed 1))
         + 1000000000000000000000000000 * (sizeᵉ (progSeed 4) * syncSizeᵉ (progSeed 4))

seedFigs≡ : seedFigs ≡ 1369000000625000000003000000003
seedFigs≡ = refl

seedRow : List Bool
seedRow = (descSeed 1 ≤ᵇ sightSeed 1) ∷ (descSeed 4 ≤ᵇ sightSeed 4) ∷ []

seedRow≡ : seedRow ≡ true ∷ true ∷ []
seedRow≡ = refl

-- ── THE DOUBLING FAMILY AT A CASCADE ───────────────────────────────

-- Every family above wraps its accumulator a FIXED number of layers
-- per value, so the delivered nesting is linear in the instant and a
-- ceiling reading the arrival cannot be outrun by it.  This step names
-- its accumulator in both additive slots an inner `scanᵉ` offers, so
-- one application DOUBLES what the subscription delivers -- the family
-- that kills the entry fold's width-free grant, run where the
-- cascade's ceiling is read.  Its script is HOT, so the applications
-- land at separate instants rather than inside one subscribe frame.
--
-- AND THE AXIS DOES NOT REACH THIS SIDE, WHICH IS THE FINDING.  The
-- descent reads TWO at the second instant, at the third, and at twice
-- the script length, while the ceiling moves eighty-four to ninety-
-- eight; doubling the script changes neither column by one.  What the
-- doubling grows is a SUM over an instant's emitted values, and a
-- descent is a JOIN over them -- so the quantity that crossed the
-- fold's grant is invisible here, and the ceiling is not exposed to
-- the family that took the fold apart.
--
-- LOAD-BEARING, and it fails if the descent passes the ceiling at
-- either instant.  A zero pair is the other finding rather than a
-- pass: it says the run stopped before the instant.
deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                  (fstᵗ (varᵗ (here refl)))
                  (input (fsuc zero))))

progX : Closed Γ₂ natᵗ
progX = mergeAllᵉ nothing (scanᵉ deepen (strmᵗ emptyᵉ) (input (fsuc zero)))

slX : ℕ → Slots Γ₂
slX j zero          = scripted (cold [] [])
slX j (fsuc zero)   = scripted (hot (asyncNats j))

xRow2 : ℕ × ℕ
xRow2 = delivRow progX (slX 4) 400

xRow3 : ℕ × ℕ
xRow3 = deliv3Row progX (slX 4) 400

xRow3L : ℕ × ℕ
xRow3L = deliv3Row progX (slX 8) 400

dblFigs : ℕ
dblFigs = proj₁ xRow2 + 1000000 * proj₂ xRow2
        + 1000000000000 * proj₁ xRow3
        + 1000000000000000000 * proj₂ xRow3

dblFigs≡ : dblFigs ≡ 98000002000084000002
dblFigs≡ = refl

dblLongFigs : ℕ
dblLongFigs = proj₁ xRow3L + 1000000 * proj₂ xRow3L

dblLongFigs≡ : dblLongFigs ≡ 98000002
dblLongFigs≡ = refl


-- ══════════════════════════════════════════════════════════════════
-- THE WALK LEAF ITSELF, rather than the parent that lands on it.
--
-- Every reading above is taken at `depthE` from the root, where this
-- leaf is one summand of a join; a green parent is a green leaf, but
-- that step is an ARGUMENT and a tie is what leaves no argument
-- standing between a row and the statement.  So the point below is the
-- frame: a `mergeAll` outer with one inner arriving, walked at the
-- empty path, with the entry pair and the current pair taken to be the
-- same.
--
-- THE TWO FREE NUMBERS ARE READ AT NOUGHT, which is the strongest
-- reading the statement admits: the grant is monotone in the width and
-- the slot count is multiplied by them, so a row holding here holds at
-- every larger pair a caller supplies.
--
-- AND THE CONCLUSION IS SEALED, so the row does not compare numerals.
-- `fitB` is `nestB` plus a slot term, and `nestB` does not reduce at
-- any point; `nestB-base` puts the grant's own depth argument under it
-- unconditionally, and that argument -- the path's nesting plus the
-- outer's, one `suc` up -- is computed off the term.  So the row reads
-- the descent against the ceiling taken at THAT floor, which is a
-- numeric comparison, and widens it into the sealed form by
-- monotonicity.  A weakening through a proven inequality is what
-- reaches a sealed statement at all.
--
-- LOAD-BEARING, and it fails exactly when the walk passes the ceiling
-- read at the floor -- which is a strictly harder row than the sealed
-- statement asks for, since the floor is below the grant.  The two
-- points are the shallow inner and one four layers deep, so a pass
-- that only survives at a flat arrival fails here.
-- ══════════════════════════════════════════════════════════════════

wSched : Sched Γ₂
wSched = sched-init (progU 8 2) slotsT

wSt : EvalSt (progU 8 2)
wSt = installNode 7 (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
                  (st-init (progU 8 2))

wB : ℕ → Closed Γ₂ (obs natᵗ)
wB d = ofᵉ (strmᵗ (deep d) ∷ [])

wDesc : ℕ → ℕ
wDesc d = depthFrame (gasPad 400 g0) 0 0 (thru-outer mergeAllᵒ 7)
                     (root {Γ = Γ₂} {t = natᵗ}) (deep d ∷ []) false wSched wSt

-- the ceiling at the FLOOR of the sealed grant, which is what the row
-- actually compares against
wFloor : ℕ → ℕ
wFloor d =
  sightCeil (sizeᵉ (progU 8 2))
            (pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB d)))
            (storeNestMax wSched wSt)
            (nestUnit (progU 8 2) slotsT)

walkFigs : ℕ
walkFigs = wDesc 1 + 1000 * wFloor 1 + 1000000 * wDesc 4 + 1000000000 * wFloor 4

walkFigs≡ : walkFigs ≡ 1113005954002
walkFigs≡ = refl

walkRow : List Bool
walkRow = (wDesc 1 ≤ᵇ wFloor 1) ∷ (wDesc 4 ≤ᵇ wFloor 4) ∷ []

walkRow≡ : walkRow ≡ true ∷ true ∷ []
walkRow≡ = refl

walkTie : ∀ (d : ℕ) →
  pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB d))
    ≤ fitB (progU 8 2) slotsT 0 0
        (pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB d)))
        (suc (syncSizeᵉ (wB d)))
walkTie d =
  ≤-trans (nestB-base (sizeᵉ (progU 8 2)) 0 (nestUnit (progU 8 2) slotsT)
             (pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB d)))
             (suc (syncSizeᵉ (wB d))))
          (m≤m+n _ _)

tieWalk1 : Confirms
  (sight-all-walk (gasPad 400 g0) 0 0 mergeAllᵒ 7 (wB 1)
     (root {Γ = Γ₂} {t = natᵗ}) 0 0 wSched wSt (deep 1 ∷ []) false wSched wSt)
tieWalk1 _ _ =
  ≤-trans (≤ᵇ⇒≤ (wDesc 1) (wFloor 1) tt)
          (sightCeil-mono (sizeᵉ (progU 8 2))
             {v = pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB 1))}
             {v′ = fitB (progU 8 2) slotsT 0 0
                     (pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB 1)))
                     (suc (syncSizeᵉ (wB 1)))}
             {s = storeNestMax wSched wSt} {s′ = storeNestMax wSched wSt}
             (nestUnit (progU 8 2) slotsT) (walkTie 1) ≤-refl)

tieWalk4 : Confirms
  (sight-all-walk (gasPad 400 g0) 0 0 mergeAllᵒ 7 (wB 4)
     (root {Γ = Γ₂} {t = natᵗ}) 0 0 wSched wSt (deep 4 ∷ []) false wSched wSt)
tieWalk4 _ _ =
  ≤-trans (≤ᵇ⇒≤ (wDesc 4) (wFloor 4) tt)
          (sightCeil-mono (sizeᵉ (progU 8 2))
             {v = pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB 4))}
             {v′ = fitB (progU 8 2) slotsT 0 0
                     (pathNestD (root {Γ = Γ₂} {t = natᵗ}) + suc (nestDᵉ (wB 4)))
                     (suc (syncSizeᵉ (wB 4)))}
             {s = storeNestMax wSched wSt} {s′ = storeNestMax wSched wSt}
             (nestUnit (progU 8 2) slotsT) (walkTie 4) ≤-refl)
