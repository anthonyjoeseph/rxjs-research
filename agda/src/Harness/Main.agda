-- THE MEASUREMENT HARNESS — a COMPILED calculator for the machine's own
-- arithmetic.  A MODULE_ROOT (`make harness-build` / `make harness`), so it
-- lives in `src` under the wiring law rather than in a staging directory
-- outside the claim graph.  `src/Main.agda` never reaches it, so `make agda`
-- does not pay for it.
--
-- WHY IT EXISTS.  Two of this machine's number families do not normalise in
-- the TYPECHECKER at all:
--
--   * the `fLvlD`/`sizeAt`/`widAt`/`regAt` family is `abstract`
--     `abstract` in `Rx.Evaluator`, as is `blowH`, both for a
--     measured performance reason — with the bodies visible, one whnf
--     unfolds the whole loop and the consuming module runs past an hour.
--     `poolCount` is NOT itself abstract, but it calls `fLvlD`, so
--     `poolCount 1 0` is STUCK at the smallest possible arguments;
--   * the deep rungs simply exceed the typechecker (one was killed at
--     12.6 GB after 20 minutes).
--
-- THE GHC BACKEND RUNS THE SAME DEFINITIONS AND IGNORES `abstract`, because
-- opacity is a TYPECHECKING contract and not a runtime one.  So a number
-- unreachable by `refl` is reachable here.
--
-- ⚠ ANYTHING READ OFF THIS BINARY IS `measured-not-rechecked` BY
-- CONSTRUCTION, and must be flagged as such wherever it is recorded.  A
-- compiled number is NOT a `refl` pin and must never be reported as one: no
-- proof may depend on it, and it cannot discharge a postulate.  Its use is
-- to AIM the grind and to REFUTE — a single compiled row that contradicts a
-- postulate is a finding worth chasing back to a type-level witness.
--
-- THE GUARD against a backend that has quietly diverged from the
-- typechecker is CALIBRATION.  Row 0 is a value this very module also pins
-- by `refl` (`calibration-pin` below), so the typechecker fixes the
-- expected number at compile time and the binary prints the computed one.
-- IF ROW 0 DOES NOT PRINT 65536, EVERY OTHER ROW IS VOID — stop and
-- diagnose the backend, do not read on.
--
-- ONE ROW PER PROCESS, deliberately: a single process that computes several
-- deep rungs retains all of them and dies of memory; a fresh process per row
-- does not.
--
--     make harness-build          compile it
--     make harness                every row, one process each
--     make harness ARGS='1'       just row 1
module Harness.Main where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; Unit)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Prim using (towerℕ; gasPad; g0)
open import Rx.Evaluator using (poolCount; blowH; capsHgo; lvls; iterL; capsBase; subscribeE; sched-init; st-init; root;
  Sched; EvalSt; sched-next; cascade; arrTy; arrVal)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵉ)
open import Rx.Evaluator using (budgetAt; chainsOf; cascadeLatch)
open import Verify-Budget-Sufficient.Caps-Depth using (depthCascade)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Demand-Programs
  using (runDry; progD; sucG; ins₀; runDryS; progS; sucGS; insS;
         progT; sucGT; insT; subjN; pathN)
open import Verify-Budget-Sufficient.Nest-Store
  using (nestSyn; nestCapAt; realWidAt; storeNestMax; slotsNestSum; nestOK?;
         pathNestD; chainsNestD)

------------------------------------------------------------------
-- THE CALIBRATION PIN.  `towerℕ` is the one member of this
-- neighbourhood that DOES normalise in the typechecker, which is what
-- makes it usable as a cross-check: the same expression is fixed here by
-- `refl` (so `make agda-dev` checks it) and printed by the compiled
-- binary as row 0.  Agreement is the evidence that the backend computes
-- what the typechecker computes; divergence voids every other row.
--
-- NB `towerℕ` is NOT the thing the harness exists to reach — it was
-- tested and found NOT to be the blocker for the anchor.  It is here
-- precisely BECAUSE it is computable on both sides.
------------------------------------------------------------------

calibration : ℕ
calibration = towerℕ 4

-- ANONYMOUS by the bug-cache idiom (`_ : lhs ≡ rhs`), not by accident: a
-- NAMED pin is a proven definition with no consumer, i.e. an orphan, and
-- `make wiring-gate` rightly fails it (observed while landing this file).
-- Anonymous, the typechecker still fixes the number at compile time and
-- there is no name to orphan.
_ : calibration ≡ 65536
_ = refl

-- THE FAMILY CALIBRATION, pinned.  `towerℕ` agreement says the backend
-- does arithmetic; it says nothing about whether it runs `subscribeE`.
-- These two pin the dry threshold of `progD 1 2` exactly, and rows 3-4
-- print the same two expressions from the compiled binary.  Cheap
-- because the PROGRAM is small (d·k(k+1)/2 = 3 subscription levels), not
-- because drying exits early — it does not.
_ : runDry 2 (progD 1 2) ≡ true
_ = refl
_ : runDry 3 (progD 1 2) ≡ false
_ = refl

------------------------------------------------------------------
-- THE ROWS.  Add rows freely; keep row 0 where it is.  State for each
-- what it would take to make the row INTERESTING — a row that could not
-- have surprised anyone is not a row (CLAUDE.md, de-risk mode).
------------------------------------------------------------------

-- ROWS 0–2 TERMINATE and are what `make harness` sweeps.
-- ROWS 10+ ARE THE QUARANTINE: measured non-terminating, kept because
-- they are the exact expressions someone will want to retry.  They are
-- NOT in the default sweep — running them is an explicit `ARGS=10`.

showB : Bool → String
showB true  = "true"
showB false = "false"

-- Indices 20+ cannot be literal PATTERNS (Agda expands a numeric
-- literal pattern to that many constructors), so Series N dispatches on
-- an offset instead.  Row 20+k is `nestRow k`.
-- SERIES N-SWEEP — how deep an instant ACTUALLY drives the store, against
-- what the currency allows it.  `progD d k` scans k values with a fold
-- wrapping its accumulator d mergeAll-levels deeper each time, so the
-- stored accumulator is the one object in reach whose nesting grows with
-- the run rather than with the syntax — which is exactly the growth the
-- increment has to cover.
--
-- WHAT IS MEASURED, precisely, because the coverage claim is the whole
-- value of a row: this is the ROOT SUBSCRIBE frame, not `cascade`.  So it
-- constrains the subscribe side of the currency and is INDICATIVE ONLY
-- for `store-growth`, whose own instant is a delivery.  The allowance
-- printed beside it is the increment at instant 0 with `realWidAt`
-- unfolded to its base — the recurrence is sealed, and its zero clause
-- IS `capsBase`.
--
-- A ROW FAILS INTERESTINGLY when `over` reads true: the store went
-- deeper in one instant than the instant was allowed to buy.  That is a
-- lead to chase to a type-level witness, never itself the finding.
storeAfterRoot : ℕ → ℕ → ℕ
storeAfterRoot d k =
  let p = progD d k
      r = subscribeE (gasPad (sucG p) g0) p root 0 0
                     (sched-init p ins₀) (st-init p)
  in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

allowance : ℕ → ℕ → ℕ
allowance d k = capsBase (progD d k) ins₀ * nestSyn (progD d k) ins₀

-- SERIES S — the same two numbers over the SHARED-SLOT family, whose
-- one slot holds a def of the family's own shape.  The row prints
-- `slotsNestSum` beside them because that is the arm Series Q cannot
-- enter: a zero there says the sweep measured the same thing again.
storeAfterRootS : ℕ → ℕ → ℕ → ℕ → ℕ
storeAfterRootS ds ks d k =
  let p = progS d k
      r = subscribeE (gasPad (sucGS ds ks d k) g0) p root 0 0
                     (sched-init p (insS ds ks)) (st-init p)
  in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

allowanceS : ℕ → ℕ → ℕ → ℕ → ℕ
allowanceS ds ks d k =
  capsBase (progS d k) (insS ds ks) * nestSyn (progS d k) (insS ds ks)

-- SERIES C — `store-growth`'s OWN conclusion, at states the evaluator
-- reaches by running.  The subscribe frame hands over a schedule and a
-- state; `sched-next` then yields the arrival the evaluator would take
-- next, and `cascade` is the statement's own instant.  Each step prints
-- the store before and after, the increment the currency allows, and a
-- verdict.
--
-- THE HYPOTHESIS SIDE IS HALF BLOCKED, and that is the coverage
-- boundary: `capsOK?` reads `capsAt`, which sits on the caps recurrence
-- and does not terminate even in native code, so no row can discharge
-- it.  The two that DO compute are checked and reported as `H`.  A row
-- reading `OVER H` is a refutation candidate modulo the caps premise;
-- a row reading `OVER h` is not a candidate at all.
walkC : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      → ℕ → ℕ → ℕ → Sched Γ → EvalSt e → String
walkC e sl 0       id nextId sched st = ""
walkC e sl (suc m) id nextId sched st with sched-next sched
... | inj₁ _          = " [done]"
... | inj₂ (a , sd) =
  let before = storeNestMax sd st
      r      = cascade a nextId sd st
      after  = storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      bound  = before + realWidAt e sl id * nestSyn e sl
  in " | id=" ++ show id ++ " " ++ show before ++ "→" ++ show after
     ++ "/cap" ++ show (nestCapAt e sl id)
     ++ (if after ≤ᵇ bound then " ok" else " OVER")
     ++ (if nestOK? e sl id sd st then " N" else " n")
     ++ (if nestDᵛ (arrTy a) (arrVal a) ≤ᵇ nestCapAt e sl id
         then " V" else " v")
     ++ walkC e sl m (suc id) (suc nextId)
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

cascadeRow : ℕ → ℕ → ℕ → String
cascadeRow steps d k =
  let p = progD d k
      r = subscribeE (gasPad (sucG p) g0) p root 0 0
                     (sched-init p ins₀) (st-init p)
  in "d=" ++ show d ++ " k=" ++ show k
     ++ walkC p ins₀ steps 1 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

cascadeRowS : ℕ → ℕ → ℕ → ℕ → ℕ → String
cascadeRowS steps ds ks d k =
  let sl = insS ds ks
      p  = progS d k
      r  = subscribeE (gasPad (sucGS ds ks d k) g0) p root 0 0
                      (sched-init p sl) (st-init p)
  in "ds=" ++ show ds ++ " ks=" ++ show ks
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ walkC p sl steps 1 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

cascadeRowT : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String
cascadeRowT steps ds ks j d k =
  let sl = insT ds ks j
      p  = progT d k
      r  = subscribeE (gasPad (sucGT ds ks j d k) g0) p root 0 0
                      (sched-init p sl) (st-init p)
  in "ds=" ++ show ds ++ " ks=" ++ show ks ++ " j=" ++ show j
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ walkC p sl steps 1 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- SERIES D — `depth-nest-compositional`'s conclusion at the ROOT call,
-- which is the instance `depthE≤capsH-root` spends and the one index
-- where the fresh term is `capsBase` rather than the wrap tower.  Both
-- sides compute; only the `capsOK?` premise does not, for the reason
-- Series C's block gives.  A row reading OVER is a refutation
-- candidate modulo that premise.
depthRow : ℕ → ℕ → String
depthRow d k =
  let p   = progD d k
      sd  = sched-init p ins₀
      st  = st-init p
      lhs = depthE (budgetAt p ins₀ 0) p root 0 0 sd st
      rhs = nestDᵉ p + storeNestMax sd st
            + realWidAt p ins₀ 0 * nestSyn p ins₀
  in "d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE = " ++ show lhs
     ++ "  bound = " ++ show rhs
     ++ (if lhs ≤ᵇ rhs then "  ok" else "  OVER")

-- SERIES E — the same conclusion at an INNER subject under a CLIMBED
-- path, which is the axis Series D fixes.  The state is the one the
-- root subscribe hands over, so it is reached by running; only the
-- subject and the path are chosen, and the statement quantifies over
-- both.  `thru-outer` peels one `obs`, so the two move together.
depthRowInner : ℕ → ℕ → ℕ → String
depthRowInner j d k =
  let p   = progD d k
      r   = subscribeE (gasPad (sucG p) g0) p root 0 0
                       (sched-init p ins₀) (st-init p)
      sd  = proj₁ (proj₂ r)
      st  = proj₂ (proj₂ r)
      b   = subjN j d k
      κ   = pathN j
      lhs = depthE (budgetAt p ins₀ 0) b κ 0 0 sd st
      rhs = nestDᵉ b + pathNestD κ + storeNestMax sd st
            + realWidAt p ins₀ 0 * nestSyn p ins₀
  in "j=" ++ show j ++ " d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE = " ++ show lhs
     ++ "  bound = " ++ show rhs
     ++ (if lhs ≤ᵇ rhs then "  ok" else "  OVER")

-- SERIES F — `cascade-nest-compositional`, the delivery half.  It probes
-- more cleanly than its subscribe sibling: its only uncomputable premise
-- is `capsOK?`, so at any index the row is a straight comparison with
-- nothing to satisfy first.  The arrival is the evaluator's own next one,
-- taken off the schedule the root subscribe hands over.
--
-- The index is printed because it decides whether the row means
-- anything.  At zero the fresh term is `capsBase` and a row can fail; at
-- one and above it is the wrap tower and the row cannot.  Zero is not an
-- index a run reaches, which is the same boundary `store-growth` carries.
cascNest : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
         → ℕ → Sched Γ → EvalSt e → String
cascNest e sl id sched st with sched-next sched
... | inj₁ _        = " [no arrival]"
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      lhs = depthCascade a 1 (chainsOf a st) sd stL
      rhs = nestDᵛ (arrTy a) (arrVal a) + chainsNestD (chainsOf a st)
            + storeNestMax sd stL + realWidAt e sl id * nestSyn e sl
  in " | id=" ++ show id ++ " depthCascade = " ++ show lhs
     ++ " bound = " ++ show rhs
     ++ (if lhs ≤ᵇ rhs then " ok" else " OVER")

cascRow : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String
cascRow id ds ks j d k =
  let sl = insT ds ks j
      p  = progT d k
      r  = subscribeE (gasPad (sucGT ds ks j d k) g0) p root 0 0
                      (sched-init p sl) (st-init p)
  in "ds=" ++ show ds ++ " ks=" ++ show ks ++ " j=" ++ show j
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ cascNest p sl id (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

nestRow : ℕ → String
nestRow 0 = "capsBase (progD 1 1) ins₀ = "      ++ show (capsBase (progD 1 1) ins₀)
nestRow 1 = "nestSyn (progD 1 1) ins₀ = "       ++ show (nestSyn (progD 1 1) ins₀)
nestRow 2 = "nestCapAt (progD 1 1) ins₀ 0 = "   ++ show (nestCapAt (progD 1 1) ins₀ 0)
nestRow 3 = "realWidAt (progD 1 1) ins₀ 0 = "   ++ show (realWidAt (progD 1 1) ins₀ 0)
nestRow 4 = "nestCapAt (progD 1 1) ins₀ 1 = "   ++ show (nestCapAt (progD 1 1) ins₀ 1)
nestRow 5 = "realWidAt (progD 1 1) ins₀ 1 = "   ++ show (realWidAt (progD 1 1) ins₀ 1)
nestRow 6 = "nestCapAt (progD 1 1) ins₀ 2 = "   ++ show (nestCapAt (progD 1 1) ins₀ 2)
nestRow _ = "(no such row)"

rowAt : ℕ → String
rowAt 0 = "CALIBRATION towerℕ 4 (refl-pinned 65536 in this module) = "
            ++ show calibration
-- towerℕ is the SCALE REFERENCE, not a target: it is the one member of
-- this neighbourhood the typechecker also evaluates, and it shows how
-- fast the caps arithmetic's inputs climb.  towerℕ 5 = 2^65536 is a
-- ~19730-digit number, hence printed as its digit count rather than in
-- full.
rowAt 1 = "towerℕ 3 = " ++ show (towerℕ 3)
rowAt 2 = "towerℕ 4 = " ++ show (towerℕ 4)

------------------------------------------------------------------
-- SERIES N, THE NESTING CURRENCY — rows 20-26.  The re-denominated cap
-- is the one quantity in this neighbourhood designed to stay OFF the
-- caps recurrence, so unlike the anchor it has no `blowH` in it and
-- there is a real question whether it computes.  These rows answer
-- that question and nothing else: they are a COMPUTABILITY BOUNDARY,
-- not evidence for any inequality, because the side these caps would
-- have to fit under is the anchor and the anchor does not compute.
--
-- WHAT WOULD MAKE A ROW INTERESTING.  Row 20 is load-bearing in the
-- weakest sense that matters here — `capsBase` reaches `entryCeil`,
-- and if THAT diverges then the whole nesting currency is
-- symbolic-only and the roadmap's instruction to probe it first is not
-- executable as written.  Rows 22-26 are load-bearing on the GROWTH
-- RATE: `realWidAt` squares its own width each instant, so the row
-- that fails to print is the instant at which no probe of this
-- currency can reach, and that index is the coverage boundary every
-- later receipt has to state.
------------------------------------------------------------------


------------------------------------------------------------------
-- SERIES Q, THE CROSSOVER — rows 3-8.  The one region this campaign
-- has named FALSITY and left unmeasured, and the reason it was left is
-- exactly the reason this harness exists: `runDry` short-circuits in
-- NEITHER direction (`hasDry` reads the stream `subscribeE` returns, so
-- the whole run normalises before the first dry event is visible), the
-- cost is d·k(k+1)/2 subscription levels, and at the cheapest crossing
-- point that is ~250 — where the typechecker burned 56 min CPU at (8,8)
-- without finishing.  The blowup here is NORMALISER OVERHEAD, not the
-- computational blowup that quarantined rows 10+: ~250 subscription
-- levels is nothing for native code.
--
-- WHAT A ROW MEANS.  `sucG p` is the gas the walk face's demand
-- hypothesis supplies at the adversarial instantiation (Ŝ = R̂ = F = 0,
-- no shares), where `hasAtLeast-pad` makes the gas hypothesis hold
-- EXACTLY.  Every other hypothesis of the face is satisfiable there.
-- So the face asserts `runDry (sucG p) p ≡ false`, and a TRUE row
-- REFUTES WalkStmt itself — not merely a leaf.
--
-- ROWS 3-4 ARE THE FAMILY CALIBRATION and they are load-bearing in both
-- directions: they pin the dry threshold of `progD 1 2` EXACTLY (true at
-- 2, false at 3), and both are ALSO `refl`-pinned in this module below.
-- Row 0 calibrates `towerℕ`, which says nothing about whether the
-- backend runs `subscribeE` the way the typechecker does; these do.
------------------------------------------------------------------

-- the sum side, so a crossover row is self-documenting
rowAt 3 = "CALIBRATION runDry 2 (progD 1 2) [refl-pinned true here] = "
            ++ showB (runDry 2 (progD 1 2))
rowAt 4 = "CALIBRATION runDry 3 (progD 1 2) [refl-pinned false here] = "
            ++ showB (runDry 3 (progD 1 2))
rowAt 5 = "sucG (progD 6 8) = " ++ show (sucG (progD 6 8))
            ++ "   sucG (progD 6 9) = " ++ show (sucG (progD 6 9))
            ++ "   sucG (progD 7 8) = " ++ show (sucG (progD 7 8))
-- (6,8): model says the LAST SAFE point — sucG 50 against demand 49.
-- INTERESTING either way: `true` refutes, `false` is the tight safe row.
rowAt 6 = "runDry (sucG (progD 6 8)) (progD 6 8)  [false = safe] = "
            ++ showB (runDry (sucG (progD 6 8)) (progD 6 8))
-- (6,9): model says the FIRST REFUTING point — sucG 51 against demand 55.
rowAt 7 = "runDry (sucG (progD 6 9)) (progD 6 9)  [TRUE = REFUTES] = "
            ++ showB (runDry (sucG (progD 6 9)) (progD 6 9))
-- (7,8): the second crossing, independent of (6,9) in both d and k.
rowAt 8 = "runDry (sucG (progD 7 8)) (progD 7 8)  [TRUE = REFUTES] = "
            ++ showB (runDry (sucG (progD 7 8)) (progD 7 8))

------------------------------------------------------------------
-- QUARANTINE.  The caps counting family is UNREACHABLE BY MEASUREMENT,
-- and compiling it does not change that.
--
-- WHAT WAS TRIED.  This harness was built partly on the hypothesis that
-- `poolCount`'s silence in the typechecker was OPACITY (`fLvlD` is
-- `abstract` at Rx.Evaluator, `blowH` at :899) and that the GHC backend,
-- which ignores `abstract`, would therefore compute it.
--
-- WHAT HAPPENED.  Native, -O, at the SMALLEST POSSIBLE ARGUMENTS:
-- `poolCount 1 0` and `blowH 0` each still running at 45 s, killed with
-- no value.  Row 0 calibrated at 65536 in the same binary, so this is
-- not a broken build — it is the arithmetic.
--
-- WHY IT IS STRUCTURAL, not a matter of waiting longer or of hardware:
-- `blowH m = 6 + m + 2 * poolCount (towerℕ m) m` feeds `poolCount` a
-- TOWER as its first argument, and `poolCount` pools that through
-- `lvls`/`dLvl`/`iterL`, where `dLvl S W d J = iterL S W d (suc (sizeAt S J)) J`
-- iterates a number that itself grows with the level.  The value is
-- astronomically large by construction; no backend prints it.
--
-- CONSEQUENCE — this CONFIRMS the ruling "THE ANCHOR CANNOT
-- BE PROBED" by an INDEPENDENT route (native code, no typechecker in the
-- loop), and confirms its stated reason: the blowup is COMPUTATIONAL,
-- not definitional.  Un-sealing the `abstract` blocks would not help,
-- and neither would a faster machine.  **Do not build a probe, a
-- harness row, or a `refl` pin against this family.  The anchor is
-- symbolic-or-nothing.**
------------------------------------------------------------------

rowAt 10 = "poolCount 1 0 = " ++ show (poolCount 1 0)   -- DIVERGENT (45s+, killed)
rowAt 11 = "poolCount 1 1 = " ++ show (poolCount 1 1)   -- DIVERGENT
rowAt 12 = "poolCount 2 0 = " ++ show (poolCount 2 0)   -- DIVERGENT
rowAt 13 = "blowH 0 = "       ++ show (blowH 0)         -- DIVERGENT (45s+, killed)
rowAt 14 = "blowH 1 = "       ++ show (blowH 1)         -- DIVERGENT
rowAt 15 = "capsHgo 0 0 = "   ++ show (capsHgo 0 0)     -- DIVERGENT
rowAt 16 = "lvls 1 1 0 0 1 = "  ++ show (lvls 1 1 0 0 1)
rowAt 17 = "iterL 1 1 0 1 0 = " ++ show (iterL 1 1 0 1 0)
-- THE SWEEPABLE ROW — `d*100 + k + 1000`, so 1608 is (6,8).  Rows 6-8
-- above are the three points the model singles out; this one exists
-- because the COST CURVE of the family had to be measured before any of
-- them could be trusted to terminate, and a rebuild per point is not a
-- measurement loop.  Prints the sum side and the verdict together, so a
-- row is readable without cross-referencing row 5.
rowAt n with 400000 ≤ᵇ n
... | true  = cascRow (m / 100000) ((m % 100000) / 10000)
                      ((m % 10000) / 1000) ((m % 1000) / 100)
                      ((m % 100) / 10) (m % 10)
  where m = n ∸ 400000
... | false with 300000 ≤ᵇ n
...   | true  = depthRowInner (m / 10000) ((m % 10000) / 100) (m % 100)
  where m = n ∸ 300000
...   | false with 200000 ≤ᵇ n
...     | true  = depthRow (m / 100) (m % 100)
  where m = n ∸ 200000
...     | false with 100000 ≤ᵇ n
...       | true  = cascadeRowT 8 (m / 10000) ((m % 10000) / 1000)
                             ((m % 1000) / 100) ((m % 100) / 10) (m % 10)
  where m = n ∸ 100000
...       | false with 20000 ≤ᵇ n
...         | true  = cascadeRowS 6 (m / 1000) ((m % 1000) / 100) ((m % 100) / 10) (m % 10)
  where m = n ∸ 20000
...         | false with 13000 ≤ᵇ n
...           | true  = cascadeRow 6 (m / 100) (m % 100)
  where m = n ∸ 13000
...           | false with 3000 ≤ᵇ n
...             | true  = sharedSweep (n ∸ 3000)
  where
  sharedSweep : ℕ → String
  sharedSweep m =
    let ds = m / 1000
        ks = (m % 1000) / 100
        d  = (m % 100) / 10
        k  = m % 10
        g  = storeAfterRootS ds ks d k
        A  = allowanceS ds ks d k
    in "ds=" ++ show ds ++ " ks=" ++ show ks
       ++ " d=" ++ show d ++ " k=" ++ show k
       ++ "  slotsNestSum = " ++ show (slotsNestSum (insS ds ks))
       ++ "  storeNestMax after root = " ++ show g
       ++ "  allowance = " ++ show A
       ++ "  over = " ++ showB (A ≤ᵇ g)
       ++ "  dry = " ++ showB (runDryS ds ks d k)
...             | false with 2000 ≤ᵇ n
...               | true  = nestSweep (n ∸ 2000)
  where
  nestSweep : ℕ → String
  nestSweep dk =
    let d = dk / 100
        k = dk % 100
        g = storeAfterRoot d k
        A = allowance d k
    in "d=" ++ show d ++ " k=" ++ show k
       ++ "  storeNestMax after root = " ++ show g
       ++ "  burst cap = " ++ show (nestCapAt (progD d k) ins₀ 1)
       ++ "  burst-over = " ++ showB (nestCapAt (progD d k) ins₀ 1 <ᵇ g)
       ++ "  allowance = " ++ show A
       ++ "  over = " ++ showB (A ≤ᵇ g)
       ++ "  dry = " ++ showB (runDry (sucG (progD d k)) (progD d k))
...               | false with 1000 ≤ᵇ n
...                 | false = if 20 ≤ᵇ n then nestRow (n ∸ 20) else "(no such row)"
...                 | true  =
  let dk = n ∸ 1000
      d  = dk / 100
      k  = dk % 100
      p  = progD d k
      G  = sucG p
  in "d=" ++ show d ++ " k=" ++ show k
     ++ "  sucG=" ++ show G
     ++ "  runDry G p = " ++ showB (runDry G p)
     ++ "   [true = REFUTES WalkStmt]"

------------------------------------------------------------------
-- stdin: a single row index.  Anything unparseable reads as 0, which is
-- the calibration row — the safe default, since a mis-typed index then
-- reports the one number whose expected value is written down.
------------------------------------------------------------------

private
  isDigit : ℕ → Bool
  isDigit c = if 48 ≤ᵇ c then c ≤ᵇ 57 else false

  digits : List ℕ → ℕ → ℕ
  digits []       acc = acc
  digits (c ∷ cs) acc =
    if isDigit c then digits cs (acc * 10 + (c ∸ 48)) else acc

  skipToDigit : List ℕ → List ℕ
  skipToDigit []       = []
  skipToDigit (c ∷ cs) = if isDigit c then (c ∷ cs) else skipToDigit cs

main : IO Unit
main = getContents >>= λ s →
  putStr (rowAt (digits (skipToDigit (map toℕ (toList s))) 0) ++ "\n")
