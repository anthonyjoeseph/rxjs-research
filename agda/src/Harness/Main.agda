-- THE MEASUREMENT HARNESS — a COMPILED calculator for the machine's own
-- arithmetic.  A MODULE_ROOT (`make harness-build` / `make harness`), so it
-- lives in `src` under the wiring law rather than in a staging directory
-- outside the claim graph.  `src/Main.agda` never reaches it, so `make gate-heavy`
-- does not pay for it.
--
-- WHY IT EXISTS.  Two of this machine's number families do not normalise in
-- the TYPECHECKER at all:
--
--   * `fLvlD` and `blowH` are `abstract` in `Rx.Evaluator`, and
--     `cDel`/`sizeCount` in `Verify-Budget-Sufficient.Caps`, all for a
--     measured performance reason — with the bodies visible, one whnf
--     unfolds the whole loop and the consuming module runs past an hour.
--     `sizeAt`/`widAt`/`regAt` and `poolCount` are NOT themselves
--     abstract, but they call the sealed ones, so `poolCount 1 0` is
--     STUCK at the smallest possible arguments — and so is the CAPS
--     RECURRENCE at its own entry, since `capsAt e sl 0` is
--     `frameBlowup` of `sizeCount`;
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

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; map; length; foldr)
  renaming (_++_ to _++ᴸ_)
open import Data.Maybe using (Maybe; nothing; just) renaming (maybe′ to maybeᴹ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc;
  toℕ to finℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _⊔_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_; toList)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; Unit)
open import Rx.Prim using (towerℕ; cold; hot; after_,_; gasPad; g0; Gas; Timed;
  InstEmit; Source)
open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_; scanᵉ;
  mergeAllᵉ; emptyᵉ; mapᵉ; ofᵉ; varᵗ; fstᵗ; strmᵗ; input; syncSizeᵉ; sizeᵉ)
open import Rx.Frame-Width using (outWⱽ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (poolCount; blowH; capsHgo; lvls; iterL;
  capsBase; subscribeE; sched-next; cascade; Sched; EvalSt; root; sched-init;
  st-init; drain; splitEvents; splitBurst; Stream; Path; share-sink; _↠_;
  shareAdmit; RegId; Chain)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit; slotWrapSum;
  nestCapAt)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestWalkAt;
  capΦAt; nestΦAt)

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

------------------------------------------------------------------
-- THE ROWS.  Add rows freely; keep row 0 where it is.  State for each
-- what it would take to make the row INTERESTING — a row that could not
-- have surprised anyone is not a row (CLAUDE.md, de-risk mode).
------------------------------------------------------------------

-- ROWS 0–2 TERMINATE and are what `make harness` sweeps.
-- ROWS 10+ ARE THE QUARANTINE: measured non-terminating, kept because
-- they are the exact expressions someone will want to retry.  They are
-- NOT in the default sweep — running them is an explicit `ARGS=10`.
-- Indices 20+ cannot be literal PATTERNS (Agda expands a numeric
-- literal pattern to that many constructors), so a series wanting them
-- dispatches on an offset from the catch-all clause instead.

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

------------------------------------------------------------------
-- SERIES — THE DEPTH CHARGE AT THE ENTRY INSTANT, PRICED.
--
-- TARGET: scanΦ-fit @ce80e6
--
-- WHY THIS CANNOT BE A PROBE.  The arm's residue is that no premise
-- names the node table, and the fact that would is ambient — so the
-- question is what the two sides actually MEASURE at a state a run
-- reached.  The store side computes in the typechecker; the charge
-- side does not, at any instant.  `nestΦAt` and its two summands are
-- sealed in `Caps-Face.Nest-Arith`, and the `-def` equations only hand
-- the body back in terms of `capsAt`, which is itself stuck at its own
-- ENTRY: `capsAt e sl 0` is `frameBlowup` of the sealed `sizeCount`,
-- so there is no instant at which a `refl` reaches these numbers.
--
-- AND THE CHARGE IS UNREACHABLE HERE TOO, WHICH IS WHAT THESE ROWS
-- REPORT.  Rows 3, 5, 6 and 18 terminate at once; rows 4, 7, 8 and 9
-- were each killed at 180 s with no value, native, at the smallest
-- program that reaches this arm.  They are kept for the reason the
-- quarantine's rows are kept — they are the expressions someone will
-- want to retry — and the cause is the same one, reached by a
-- different route: every one of them reads `Caps.cSize (capsAt e sl
-- 0)`, and the entry caps are `frameBlowup` of `sizeCount`, which
-- pools `cDel` through `lvls`.  `nestCapAt` is the one summand that
-- escapes, and only at the entry, where it IS `nestUnit`.
--
-- SO THE TWO SIDES CANNOT BE COMPARED BY INSTANTIATION AT ALL, and
-- that is a fact about the obligation rather than about this harness:
-- the store side computes in the typechecker and the charge side
-- computes nowhere.  A row above the walk would have been a FALSITY on
-- the charge, and no row can be taken.
--
-- WHAT THE STORE SIDE DOES SAY, and row 18 is where it says it.  The
-- table is read at the subscribe frame and after each arrival, and it
-- reads one less than two to the burst length, then DOUBLES on the
-- first later value and stands still after -- which is the doubling
-- step under the burst, in the table, at the arm's own shape.  The
-- side that can be measured therefore grows exponentially in a count
-- the arm's premises never bound, which is the same defect its header
-- records about `valsΦ?` arriving from the store rather than from the
-- charge.

Γᴴ : Ctx 2
Γᴴ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- THE ARM'S OWN SHAPE.  `scanΦ-fit` is the SCAN arm, and the step here
-- names its accumulator twice -- in the inner scan's seed and in its
-- step -- so one application doubles the stored nesting.  That is what
-- puts a positive `nodeNest` in the table at all; a `mapᵉ` program
-- leaves it flat at zero and its store row could not have failed.
deepenᴴ : Fn Γᴴ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepenᴴ = strmᵗ (mergeAllᵉ nothing
            (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                   (fstᵗ (varᵗ (here refl)))
                   (input (fsuc fzero))))

eᴴ : Closed Γᴴ (obs natᵗ)
eᴴ = scanᵉ deepenᴴ (strmᵗ emptyᵉ) (input (fsuc fzero))

slᴴ : Slots Γᴴ
slᴴ fzero        = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ []))
slᴴ (fsuc fzero) = scripted (cold (4 ∷ 3 ∷ 2 ∷ 1 ∷ []) ((after 9 , 0) ∷ []))

-- one arrival, state threaded; `drain` returns the stream alone, and
-- what this series needs is the store the run LEFT
stepH : Sched Γᴴ × EvalSt eᴴ → Sched Γᴴ × EvalSt eᴴ
stepH (sd , st) with sched-next sd
... | inj₁ _       = sd , st
... | inj₂ (a , s) = let r = cascade a 1 s st in proj₁ (proj₂ r) , proj₂ (proj₂ r)

driveH : ℕ → Sched Γᴴ × EvalSt eᴴ
driveH n = go n (let r = subscribeE
                           (gasPad (syncSizeᵉ eᴴ + hopDᵉ 0 (slotHop 0 slᴴ) eᴴ) g0)
                           eᴴ root 0 0 (sched-init eᴴ slᴴ) (st-init eᴴ)
                 in proj₁ (proj₂ r) , proj₂ (proj₂ r))
  where
  go : ℕ → Sched Γᴴ × EvalSt eᴴ → Sched Γᴴ × EvalSt eᴴ
  go 0       x = x
  go (suc k) x = go k (stepH x)


------------------------------------------------------------------
-- SERIES — THE DRIVEN REFOLD PAST THE LAYER THE PROBE TREE REACHES.
--
-- TARGET: scanΦ-fit @ce80e6
--
-- WHAT IS OWED.  `Probed.Fold-Width-Reach` decides the fork between
-- the two width READINGS and stops one layer in: its run crosses the
-- linear reading at the first hop, and two layers outran the evidence
-- loop outright.  What no row there reaches is whether a RUN keeps up
-- with the count the recurrence ADMITS, which grows by
-- `foldStep S w = S ^ suc w` and so towers in the level.  Compiled,
-- the same family runs further, and that is the only thing these rows
-- add.
--
-- AND THE DECISIVE AXIS IS THE BURST, NOT THE LAYER COUNT, which is
-- why the layer rows below stop where the probe's did.  `foldStep` is
-- exponential in the INCOMING width and only polynomial in the size,
-- and the width entering a refold is the synchronous burst its slot
-- script delivers -- a script parameter, carried by no part of the
-- program's size.  So the exponent is reachable at ONE layer if it is
-- reachable at all, and the burst rows sweep it there at a fixed
-- program while the later-arrival count is held still, so that the two
-- ways a script can widen an instant are not read as one.
--
-- WHAT WOULD MAKE THEM FAIL.  A widest instant growing about linearly
-- in the burst puts the admitted count out of reach of any run, and
-- the arm may then carry a premise bounding the count it is charged
-- for.  One growing like a power of the burst puts it IN reach, and
-- then the falsity is on the count axis and on the budget at this
-- recurrence rather than on this arm.
--
-- THE `outWⱽ` COLUMN IS THE PROVEN CEILING ON THE SUBSCRIBE BURST
-- ALONE (`burst-out`), and is printed because it is what seeds the
-- recurrence's own width -- not as a ceiling on the widest column,
-- which maxes over every later instant the drive reaches and is free
-- to exceed it.
--
-- ⚠ measured-not-rechecked, like every row in this file.  Layers 0 and
-- 1 are also pinned by `refl` in that probe, so their agreement
-- calibrates the backend ON THIS FAMILY rather than only on `towerℕ`.
------------------------------------------------------------------

gasᴴ : Gas
gasᴴ = gasPad 400 g0

-- k values delivered synchronously at subscribe, and k more arriving
-- one per later frame -- the second is what drives the refolds that
-- only re-enter after the flatten has subscribed them
syncᴴ : ℕ → List ℕ
syncᴴ zero    = []
syncᴴ (suc k) = k ∷ syncᴴ k

timedᴴ : ℕ → List (Timed ℕ)
timedᴴ zero    = []
timedᴴ (suc k) = (after 0 , k) ∷ timedᴴ k

-- THE LAYER SEEDS FROM A REAL SOURCE, not from `emptyᵉ`: an empty
-- observable emits nothing however long it is driven, which is what
-- held the undriven family to its entry burst
layerDᴴ : Closed Γᴴ natᵗ → Closed Γᴴ natᵗ
layerDᴴ e = mergeAllᵉ nothing (scanᵉ deepenᴴ (strmᵗ (input (fsuc fzero))) e)

towerDᴴ : ℕ → Closed Γᴴ natᵗ
towerDᴴ zero    = input fzero
towerDᴴ (suc k) = layerDᴴ (towerDᴴ k)

-- slot zero drives the base one value per frame; slot one carries both
-- the synchronous burst each refold reads at its own subscribe and the
-- later values the refolds re-enter on.  THE TWO ARE SEPARATE DIALS
-- here and were one in the probe: widening a burst and lengthening a
-- run are the two ways a script can grow an instant count, and a sweep
-- moving both at once cannot say which one the exponent reads.
slotsBᴴ : ℕ → ℕ → Slots Γᴴ
slotsBᴴ b l fzero        = scripted (cold [] (timedᴴ l))
slotsBᴴ b l (fsuc fzero) = scripted (cold (syncᴴ b) (timedᴴ l))

instWᴴ : ∀ {t} → Stream Γᴴ t → List ℕ
instWᴴ         []         = []
instWᴴ {t = t} (em ∷ ems) =
  length (proj₁ (splitEvents {A = Val Γᴴ t} (InstEmit.events em))) ∷ instWᴴ ems

-- the whole run: subscribe burst and every later frame `drain` reaches
runᴴ : ℕ → ℕ → ℕ → ℕ → Stream Γᴴ natᵗ
runᴴ b l fuel k =
  let r = subscribeE gasᴴ (towerDᴴ k) root 0 0
            (sched-init (towerDᴴ k) (slotsBᴴ b l)) (st-init (towerDᴴ k))
  in proj₁ r ++ᴸ drain fuel 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

wideᴴ : ℕ → ℕ → ℕ → ℕ → ℕ
wideᴴ b l fuel k = foldr _⊔_ 0 (instWᴴ (runᴴ b l fuel k))

countᴴ : ℕ → ℕ → ℕ → ℕ → ℕ
countᴴ b l fuel k = length (instWᴴ (runᴴ b l fuel k))

-- the SUBSCRIBE stream's total value count, which is the quantity
-- `burst-out` proves to be under `outWⱽ` -- kept apart from the widest
-- column so that a later frame outrunning that ceiling is not read as
-- the entry breaching it
entryTotᴴ : ℕ → ℕ → ℕ → ℕ
entryTotᴴ b l k = length (proj₁ (splitBurst {Γ = Γᴴ} {u = natᵗ}
                                            {A = Val Γᴴ natᵗ}
  (proj₁ (subscribeE gasᴴ (towerDᴴ k) root 0 0
    (sched-init (towerDᴴ k) (slotsBᴴ b l)) (st-init (towerDᴴ k))))))

-- the layer sweep, at the probe's own dials so its two `refl` rows
-- calibrate this binary: what the run DID, what the subscribe burst is
-- proven to be under, and what a per-hop-by-its-own-size reading allows
wideRow : ℕ → String
wideRow k = "driven layer " ++ show k
              ++ ": size = "     ++ show (sizeᵉ (towerDᴴ k))
              ++ "  widest = "   ++ show (wideᴴ 3 3 6 k)
              ++ "  instants = " ++ show (countᴴ 3 3 6 k)
              ++ "  outWⱽ = "    ++ show (outWⱽ 2 [] (slotsBᴴ 3 3) (towerDᴴ k))
              ++ "  fanout = "   ++ show (suc (k * sizeᵉ (towerDᴴ k)))

-- the burst sweep, which is what decides the binary: one layer, the
-- later-arrival count held at three, and only the synchronous burst
-- the refold reads at its own subscribe moving
burstRow : ℕ → String
burstRow b = "layer 1, burst " ++ show b
              ++ ": widest = "   ++ show (wideᴴ b 3 6 1)
              ++ "  entry = "    ++ show (entryTotᴴ b 3 1)
              ++ "  instants = " ++ show (countᴴ b 3 6 1)
              ++ "  outWⱽ = "    ++ show (outWⱽ 2 [] (slotsBᴴ b 3) (towerDᴴ 1))

-- the layer sweep again at the smallest dials the family admits, to
-- tell a run that is merely LARGE at two layers from one the evaluator
-- does not finish at all
smallRow : ℕ → String
smallRow k = "small layer " ++ show k
              ++ ": widest = "   ++ show (wideᴴ 1 1 2 k)
              ++ "  instants = " ++ show (countᴴ 1 1 2 k)

------------------------------------------------------------------
-- SERIES — WHERE A SINK HANDS ON TO, AND HOW FAR THAT CAN GO.
--
-- TARGET: sink-fan-sink @d156ce
--
-- WHAT IS OWED.  The arm's refutation and its header rest on one claim
-- about the MACHINE rather than about the arithmetic: that the hop
-- count is bounded by nothing but the dispatch gas, since `shareAdmit`
-- filters on the source and the element type and never on whether a
-- chain has already been delivered to.  If that is right, the leaf's
-- price has to dominate itself times a frame product an unbounded
-- number of times and no denomination survives.  What no row anywhere
-- reaches is whether a RUN can put a second hand-over under a sink at
-- all, and how deep hand-overs can nest, so the rows here read the
-- registry a real subscribe leaves and walk it.
--
-- AND THE DECIDING COMPARISON IS ACROSS THE FUEL, NOT INSIDE ONE RUN.
-- A hop walk needs a fuel to be total, so any single depth is
-- uninformative: a count bounded by the dispatch gas rises with
-- whatever fuel it is handed, and one bounded by the PROGRAM stands
-- still.  The rows therefore take the SAME registry at four fuels, the
-- last of them four times the slot count.
--
-- WHAT WOULD MAKE THEM FAIL.  A registry entry whose source is not
-- strictly below the slot its chain ends at -- the self-re-entry the
-- refutation's own witness uses, a chain from source zero terminating
-- at `share-sink` zero -- or a hop depth that grows when only the fuel
-- does.  Both are read off a run rather than constructed, and the
-- program is built to PRODUCE hand-overs: two shared slots, each
-- defined over the one below it, and a root that subscribes all three,
-- so a registry with no sink terminal at all would be the degenerate
-- reading and is visible in the census row.
--
-- ⚠ measured-not-rechecked, like every row in this module.
------------------------------------------------------------------

Γˢ : Ctx 3
Γˢ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

idˢ : Fn Γˢ [] [] [] natᵗ natᵗ
idˢ = varᵗ (here refl)

-- the telescope is STRATIFIED by construction -- slot k's def may name
-- only inputs below k -- and each `ok` field here is discharged by
-- unification, which is the whole of what a concrete program pays for
-- it.  Slot zero is `hot` rather than `cold`: a cold with an async tail
-- mints a fresh source per subscribe, and `shareAdmit` takes only slot
-- indices, so a cold source is admitted by no sink and the census would
-- read empty for a reason that has nothing to do with the question.
slˢ : Slots Γˢ
slˢ fzero               = scripted (hot ((after 0 , 1) ∷ (after 2 , 2) ∷ []))
slˢ (fsuc fzero)        = shared (mapᵉ idˢ (input fzero))
slˢ (fsuc (fsuc fzero)) = shared (mapᵉ idˢ (input (fsuc fzero)))

eˢ : Closed Γˢ natᵗ
eˢ = mergeAllᵉ nothing
       (ofᵉ (strmᵗ (input (fsuc (fsuc fzero)))
           ∷ strmᵗ (input (fsuc fzero))
           ∷ strmᵗ (input fzero) ∷ []))

regsˢ : List (RegId × Source × Chain Γˢ natᵗ)
regsˢ = EvalSt.registry (proj₂ (proj₂
          (subscribeE gasᴴ eˢ root 0 0 (sched-init eˢ slˢ) (st-init eˢ))))

-- a path holds exactly one leaf, and it is the leaf that says whether
-- the chain hands on
pathSinkˢ : ∀ {s} → Path Γˢ s natᵗ → Maybe (Fin 3)
pathSinkˢ root           = nothing
pathSinkˢ (share-sink i) = just i
pathSinkˢ (f ↠ p)        = pathSinkˢ p

termˢ : Maybe (Fin 3) → String
termˢ nothing  = "root"
termˢ (just i) = "sink " ++ show (finℕ i)

regRowˢ : RegId × Source × Chain Γˢ natᵗ → String
regRowˢ (_ , src , (_ , p)) =
  "  [src " ++ show src ++ " → " ++ termˢ (pathSinkˢ p) ++ "]"

-- the hop walk: from a sink, every chain the registry admits from it,
-- and from each chain that ends at another sink, the same again
hopGoˢ : ℕ → Fin 3 → ℕ
hopGoˢ zero    i = 0
hopGoˢ (suc f) i =
  foldr _⊔_ 0
    (map (λ rp → maybeᴹ (λ j → suc (hopGoˢ f j)) 0 (pathSinkˢ (proj₂ rp)))
         (shareAdmit i regsˢ))

regsRow : String
regsRow = "registry: " ++ show (length regsˢ) ++ " entries"
            ++ foldr _++_ "" (map regRowˢ regsˢ)

hopRow : ℕ → String
hopRow f = "hop depth at fuel " ++ show f
             ++ ": from sink 0 = " ++ show (hopGoˢ f fzero)
             ++ "  from sink 1 = " ++ show (hopGoˢ f (fsuc fzero))
             ++ "  from sink 2 = " ++ show (hopGoˢ f (fsuc (fsuc fzero)))

fuelAtˢ : ℕ → ℕ
fuelAtˢ 1 = 1
fuelAtˢ 2 = 3
fuelAtˢ 3 = 6
fuelAtˢ _ = 12

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

rowAt 3 = "capsBase = "   ++ show (capsBase eᴴ slᴴ)
rowAt 4 = "cSize@0 = "    ++ show (Caps.cSize (capsAt eᴴ slᴴ 0))   -- NO VALUE (180s)
rowAt 5 = "nestUnit = "   ++ show (nestUnit eᴴ slᴴ)
            ++ "  slotWrapSum = " ++ show (slotWrapSum slᴴ)
rowAt 6 = "nestCapAt@0 = " ++ show (nestCapAt eᴴ slᴴ 0)
rowAt 7 = "nestWalkAt@0 = " ++ show (nestWalkAt eᴴ slᴴ 0)  -- NO VALUE (180s)
rowAt 8 = "capΦAt@0 = "   ++ show (capΦAt eᴴ slᴴ 0)        -- NO VALUE (180s)
rowAt 9 = "nestΦAt@0 = "  ++ show (nestΦAt eᴴ slᴴ 0)       -- NO VALUE (180s)


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

-- the STORE side of the series above, kept out of the quarantine's
-- range: the node table a RUN reaches, driven past the subscribe frame
-- rather than read at `st-init`, whose `nodesMax` is zero by
-- construction and would make the row degenerate
rowAt 18 = "nodesMax@0..4 = " ++ show (nodesMax (proj₂ (driveH 0)))
             ++ " " ++ show (nodesMax (proj₂ (driveH 1)))
             ++ " " ++ show (nodesMax (proj₂ (driveH 2)))
             ++ " " ++ show (nodesMax (proj₂ (driveH 4)))
-- the driven refold's rows, one per process: 19 is layer zero and the
-- catch-all carries 20 to 22 as layers one to three, 23 to 29 as bursts
-- one to seven, 30 to 33 as the small-dial layers zero to three, 34 as
-- the sink census and 35 to 38 as the hop walk's four fuels --
-- dispatched by arithmetic because a numeric literal PATTERN at 20
-- expands to twenty constructors
rowAt 19 = wideRow 0
rowAt n = if n ≤ᵇ 22 then wideRow (n ∸ 19)
          else if n ≤ᵇ 29 then burstRow (n ∸ 22)
          else if n ≤ᵇ 33 then smallRow (n ∸ 30)
          else if n ≤ᵇ 34 then regsRow
          else if n ≤ᵇ 38 then hopRow (fuelAtˢ (n ∸ 34)) else "(no such row)"

main : IO Unit
main = getContents >>= λ s →
  putStr (rowAt (digits (skipToDigit (map toℕ (toList s))) 0) ++ "\n")

