------------------------------------------------------------------
-- THE MINT-LOOP SHAPES AND MEASURES.  Split out of Mint-Loop-Probe so
-- that measuring costs only the evaluator: every `refl` wall lives next
-- door, and `scripts/measure.sh` imports THIS module, so reading one
-- number off a normal form no longer pays for the whole file's pins.
--
-- The narrative — what these families are for and what they settled — is
-- at the head of Mint-Loop-Probe.  Nothing here is checked by anything
-- here; the assertions that give these definitions their meaning are in
-- that file and in Mint-Loop-Frames.
--
-- THIS FILE HOLDS THREE MEASUREMENT TABLES (the mints/R_end table, the
-- L = 4 k-sweep, and MEASUREMENT 8's branching profiles) AND NO
-- ASSERTIONS, so before reading a trend off any of them, read the
-- STANDING WARNING at the head of Mint-Loop-Probe.  Its four instances
-- are all cases where a trend read off this family's shallow rows was
-- false at the next rung, and two of the four are trends read off the
-- tables below.
------------------------------------------------------------------
module Mint-Loop-Shapes where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; sum; map; length; foldr; any)
open import Data.Vec  using (lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin; toℕ) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Tick; Gas; after_,_; hot; Source;
                           InstEmit; InstEvent; init; value; close;
                           handoff; complete; EmitKind; subscribe;
                           delivery; plumbing)
open import Rx.Exp  using (Ctx; Closed; Exp; Tm; Val; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂;
                           fstᵗ; varᵗ; sizeᵉ; sizeᵛ; sizeᵗ)
open import Rx.Evaluator using (Slots; scripted; shared; Sched; EvalSt;
                                LiveSource; NodeState; scan-st; take-st;
                                merge-st; concat-st; switch-st; exhaust-st;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; root; Path; Stream;
                                share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer;
                                RegId; Arrival; arrTy; arrVal; arrTick;
                                stepFrame; shareAdmit; shareLatch; shareFinish;
                                chainsOf; cascadeLatch)

------------------------------------------------------------------
-- THE HARNESS, Fold-Count-Probe's, kept to the parts this file reads
------------------------------------------------------------------

drainSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Fuel → Id → Sched Γ → EvalSt e → Id × Sched Γ × EvalSt e
drainSt zero    nextId sched st = nextId , sched , st
drainSt (suc k) nextId sched st with sched-next sched
... | inj₁ _            = nextId , sched , st
... | inj₂ (a , sched′) =
      let (_ , sched″ , st′) = cascade a nextId sched′ st
      in drainSt k (suc nextId) sched″ st′

runSt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
      → Id × Sched Γ × EvalSt e
runSt fuel e ins =
  let (_ , sched₀ , st₀) =
        subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
  in drainSt fuel 1 sched₀ st₀

stAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
     → Sched Γ × EvalSt e
stAt fuel e ins = proj₂ (runSt fuel e ins)

nodeSize : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeSize (scan-st {t} v)   = sizeᵛ t v
nodeSize (concat-st q _ _) = sum (map sizeᵉ q)
nodeSize (take-st _)       = 0
nodeSize (merge-st _ _)    = 0
nodeSize (switch-st _ _)   = 0
nodeSize (exhaust-st _ _)  = 0

liveSize : ∀ {n} {Γ : Ctx n} → LiveSource Γ → ℕ
liveSize l = foldr (λ tv m → sizeᵛ (LiveSource.elemTy l) (proj₂ tv) ⊔ m) 0
                   (LiveSource.pending l)

frameSize : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameSize (map-f fn)         = sizeᵗ fn
frameSize (scan-f fn _)      = sizeᵗ fn
frameSize (take-f _)         = 0
frameSize (from-inner _ _ _) = 0
frameSize (thru-outer _ _)   = 0

pathSize : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathSize root           = 0
pathSize (share-sink i) = 0
pathSize (f ↠ p)        = frameSize f ⊔ pathSize p

pathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathLen root           = 0
pathLen (share-sink i) = 0
pathLen (f ↠ p)        = suc (pathLen p)

mSize : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mSize fuel e ins =
  let (sched , st) = stAt fuel e ins
  in foldr (λ kv m → nodeSize (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveSize l ⊔ m) 0 (Sched.live sched)

mReg : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mReg fuel e ins = length (EvalSt.registry (proj₂ (stAt fuel e ins)))

mChain : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mChain fuel e ins =
  foldr (λ en m → pathSize (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (stAt fuel e ins)))

mLen : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mLen fuel e ins =
  foldr (λ en m → pathLen (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (stAt fuel e ins)))

-- the tightest cSize the state admits
mS : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mS fuel e ins = mSize fuel e ins ⊔ mChain fuel e ins ⊔ mLen fuel e ins

postAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → EvalSt e
postAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = st
...   | inj₂ (a , sched′) = proj₂ (proj₂ (cascade a nid sched′ st))

-- one cascade's deliveries, off the evaluator's own reset-per-arrival ledger
mFolds : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mFolds fuel e ins = length (EvalSt.delivered (postAt fuel e ins))

------------------------------------------------------------------
-- THE BRANCHING PROFILE, PER SLOT — off the REAL evaluator, not the
-- mirror.  A shared slot FIRES when a delivery's path bottoms out at
-- `share-sink i` and `foldPath` hands over to `dispatchShare`; that
-- clause, and only that clause, emits `handoff (toℕ i)`, so counting
-- handoffs of source `i` in the cascade's own emit stream counts
-- exactly the fan-outs of slot i.  (`dispatchShare` at gas 0 would emit
-- the handoff without fanning out; the evaluator's comment records that
-- branch as unreachable, and the mirror's own fire count next door
-- cross-checks the two agree.)
--
-- This is what the delivery recurrence needs and D does not give: D is
-- one number for the whole cascade, and a recurrence over the share DAG
-- has to know how the dispatches DISTRIBUTE over the levels of it
------------------------------------------------------------------

burstAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → Stream Γ t
burstAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = []
...   | inj₂ (a , sched′) = proj₁ (cascade a nid sched′ st)

handoffsOf : ∀ {A : Set} → Source → List (InstEvent A) → ℕ
handoffsOf s []              = 0
handoffsOf s (handoff r ∷ es) = (if r ≡ᵇ s then 1 else 0) + handoffsOf s es
handoffsOf s (init _   ∷ es) = handoffsOf s es
handoffsOf s (value _  ∷ es) = handoffsOf s es
handoffsOf s (close _ _ ∷ es) = handoffsOf s es
handoffsOf s (complete ∷ es) = handoffsOf s es

-- how many times each of the listed slots dispatches in cascade 0.  A
-- VECTOR rather than a scalar so that one profile costs one run of the
-- cascade instead of one per slot — the deep rungs are minutes each
mFires : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
       → List Source → List ℕ
mFires fuel e ins ss =
  let str = burstAt fuel e ins
  in map (λ s → sum (map (λ em → handoffsOf s (InstEmit.events em)) str)) ss

-- and the WIDTH each of those fan-outs reached.  `foldPath` opens every
-- delivery with exactly one emit of kind `delivery` stamped with the
-- DISPATCHING source, so the same stream splits D by who dispatched it.
-- Fires alone do not: a fire's cost is the registry as of that dispatch,
-- and the mint loop moves the registry between fires, so the profile the
-- recurrence needs is the PAIR
isDeliv : ∀ {A : Set} → Source → InstEmit A → ℕ
isDeliv s em with InstEmit.kind em
... | delivery  = if InstEmit.source em ≡ᵇ s then 1 else 0
... | subscribe = 0
... | plumbing  = 0

mDelivs : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
        → List Source → List ℕ
mDelivs fuel e ins ss =
  let str = burstAt fuel e ins
  in map (λ s → sum (map (isDeliv s) str)) ss

------------------------------------------------------------------
-- MEASUREMENT 8: THE BRANCHING PROFILES, L ≤ 4.
--
-- Everything above measures ONE number per cascade.  A recurrence
-- cannot be derived from one number, so this splits the cascade two
-- ways: how often each shared slot DISPATCHES, and how wide each of
-- those dispatches FANS OUT.  Slot numbering is the ladder's own —
-- slot 0 is the innermost share, slot L the scripted input, which
-- never fans out and so has no fire entry.
--
-- PROVENANCE, AND THERE IS NO `refl` STATE IN THIS TABLE AT ALL.
-- Every row is MEASURED-NOT-RECHECKED (compiled), read off
-- probe/Measure-Main through the GHC backend.  That is forced by the
-- MEASURES rather than by the numbers: `mFolds` forces
-- `EvalSt.delivered`, a list of RegIds, while `mFires` and `mDelivs`
-- force the cascade's EMIT STREAM, so the typechecker has to build
-- every emitted value to reach the event constructors.  Pinning even
-- the thirty-delivery share-DAG control ran past ten minutes; the wall
-- next door ran past forty-five with the ladders in and was killed
-- twice.  Mint-Loop-Probe's MEASUREMENT 8 records that and pins
-- nothing.
--
-- What stands in for the pins is that every row is CALIBRATED against
-- a number that is pinned or already recorded:
--
--   · every DELIVERY row sums to the `mFolds` the pins already hold —
--     50, 106, 176, 232, 260, 268, 269 on the three-level ladder and
--     166, 726, 2546, 6914, 14922, 26362 on the four-level one, every
--     row exact;
--   · every GENERATION row sums to the `mMints` the mints table
--     already holds — 92 at pL³ 2, 575 at pL⁴ 2, 254 at pL³ 6;
--   · and the mirror's own fire count (`mFiresM`, the walk that
--     produces `j`) reproduces the evaluator's handoff count exactly
--     on pL² 2, pL³ 2 and pL⁴ 2.
--
-- (a) THE FIRES DO NOT MOVE.  At all.
--
--   program                   slot0  slot1  slot2  slot3
--   pS¹                           2
--   pS²                           4      2
--   pS³                           8      4      2
--   pS⁴                          16      8      4      2
--   pL¹  k = 0 … 5                2
--   pL²  k = 0 … 5                4      2
--   pL³  k = 0 … 6                8      4      2
--   pL⁴  k = 0 … 5               16      8      4      2
--   pG′  k = 0, 2                 2
--   pG′² k = 0, 3                 4      2
--   pG′³ k = 0                    8      4      2
--
--   fires slot i = 2 ^ (L ∸ i), INVARIANT in k, invariant in the
--   lean/accumulating choice, and equal to the pure share-DAG
--   control's.  The mint loop buys DELIVERIES without buying
--   DISPATCHES, and the reason is structural: the minting happens in
--   the root program's scan, whose chain ends at `root`, so a minted
--   registration's path never ends at a `share-sink` and never adds a
--   fan-out.  Every registration it adds is a CONSUMER.
--
-- (b) SO THE WHOLE k-DEPENDENCE IS ONE NUMBER: the width of slot 0's
-- fan-outs.  Deliveries split by dispatching source (the row sums to D):
--
--   program        slot0  slot1  slot2  slot3  input      D
--   pS¹                4                          2       6
--   pS²                8      4                   2      14
--   pS³               16      8      4            2      30
--   pS⁴               32     16      8      4     2      62
--   pL¹  k = 0 … 5     3                          2       5
--   pL²  k = 0        10      4                   2      16
--        k = 1        14      4                   2      20
--        k = 2 … 5    15      4                   2      21
--   pL³  k = 0        36      8      4            2      50
--        k = 1        92      8      4            2     106
--        k = 2       162      8      4            2     176
--        k = 3       218      8      4            2     232
--        k = 4       246      8      4            2     260
--        k = 5       254      8      4            2     268
--        k = 6       255      8      4            2     269
--   pL⁴  k = 0       136     16      8      4     2     166
--        k = 1       696     16      8      4     2     726
--        k = 2      2516     16      8      4     2    2546
--        k = 3      6884     16      8      4     2    6914
--        k = 4     14892     16      8      4     2   14922
--        k = 5     26332     16      8      4     2   26362
--   pG′  k = 0, 2      3                          2       5
--   pG′² k = 0        14      4                   2      20
--        k = 3        21      4                   2      27
--   pG′³ k = 0        92      8      4            2     106
--
--   Off slot 0 the profile is rigid: deliveries slot i = 2 * fires
--   slot i for every i ≥ 1, and the scripted input dispatches the two
--   root chains, so the tail contributes 2 ^ (L + 1) ∸ 2 on every row.
--
-- (c) AND THE MINTS ARE A BINOMIAL FAN.  Registrations minted per
-- GENERATION — generation g meaning g mint-edges from the entry
-- registry, so a registration minted while delivering to a
-- generation-g one is generation g + 1:
--
--   program      g=1   g=2   g=3   g=4   g=5   total (= mMints)
--   pL¹ k = 0      2                                    2
--       k ≥ 1      2     1                              3
--   pL² k = 0      4                                    4
--       k = 1      4     6                             10
--       k = 2      4     6     4                       14
--       k ≥ 3      4     6     4     1                 15
--   pL³ k = 0      8                                    8
--       k = 1      8    28                             36
--       k = 2      8    28    56                       92
--       k = 3      8    28    56    70                162
--       k = 4      8    28    56    70    56          218
--       k = 5      8    28    56    70    56  (+28)   246
--   pL⁴ k = 0     15                                   15
--       k = 1     15   105                            120
--       k = 2     15   105   455                      575
--       k = 3     15   105   455  1365                1940
--       k = 4     15   105   455  1365  3003          4943
--       k = 5      —     —     —     —     —            —   (NOT MEASURED:
--                                                            killed at 20 min)
--   pS³, pS⁴       0     0     0     0     0            0
--
--   The deepest generation is k + 1 on every row (`mGenMax` reads 6 at
--   pL³ 5 and 5 at pL⁴ 4; `mGenMax 0 (pL⁴ 5) insG⁴` was killed and is
--   NOT MEASURED).
--
--   Generation g holds exactly `C(F , g)` registrations, where F is
--   slot 0`s fire count: 2, 4, 8 on pL¹ / pL² / pL³ — the fire count
--   itself — and 15 on pL⁴, which is 16 ∸ 1 because pL⁴ is the one
--   ladder whose scripted input holds a SINGLE emission, so cascade 0
--   is a COMPLETING cascade and the last fire`s mints are swept.  The
--   ceiling is the nesting depth: nothing above generation k + 1
--   exists, which is what the k-sweep is buying.  The share DAG with
--   no scan under it mints nothing at all.
--
-- (d) THE CLOSED FORM, AND IT REPRODUCES EVERY ROW ABOVE EXACTLY.
-- A minted registration is named by the SET of slot-0 fires it was
-- minted through — that is what makes the histogram binomial — and a
-- delivery goes to one registration, so
--
--     deliveries slot 0 (L , k) = Σ (g = 1 … k + 2) C (2 ^ L , g)
--     D (L , k)                 = that + 2 ^ (L + 1) ∸ 2
--
--   L = 1, C(2,·)  = 2 1                    :  3 flat
--   L = 2, C(4,·)  = 4 6 4 1                : 10 14 15 15 …
--   L = 3, C(8,·)  = 8 28 56 70 56 28 8 1   : 36 92 162 218 246 254 255
--   L = 4, C(16,·) = 16 120 560 1820 4368 8008 11440 …
--                                           : 136 696 2516 6884 14892 26332
--
--   Twenty-one measured rows, four ladders, no exceptions — including
--   every row of the four-level ladder, which is the one that has not
--   saturated.  It is a FIT, not a derivation: nothing here proves the
--   next row obeys it, and the standing warning at the head of
--   Mint-Loop-Probe is about exactly this family.  What is different
--   from the four instances that earned that warning is that this is
--   not a trend read off the shallow rows and extended — it is a
--   closed form that hits the DEEPEST affordable row of every ladder
--   on the nose.
--
-- (e) WHAT THE CLOSED FORM SAYS ABOUT THE BUDGET, AS ARITHMETIC AND
-- NOT AS MEASUREMENT.  Deliveries saturate at k ≥ 2 ^ L ∸ 2, where the
-- sum is the whole binomial expansion:
--
--     D_sat (L) = 2 ^ (2 ^ L) ∸ 1 + 2 ^ (L + 1) ∸ 2
--
--   and `cascadeGo-deliveries` allows `2 ^ cReg * 2 ^ cReg` with
--   cReg = 2L + 1, i.e. 2 ^ (4L + 2):
--
--     L    cReg   budget        D_sat          ratio    saturated by
--     1      3         64           5          0.078    k = 0
--     2      5       1024          21          0.0205   k = 2
--     3      7      16384         269          0.0164   k = 6
--     4      9     262144       65565          0.2501   k = 14  (NOT MEASURED —
--                                                        deepest measured is
--                                                        k = 5 at 26362, 0.1006)
--     5     11    4194304  4294967357       1024.0      k = 30  (NOT MEASURED —
--                                                        by standing ruling)
--
--   The mismatch is one of KIND, not of constant: D is DOUBLY
--   exponential in the ladder depth, `2 ^ (2 ^ L)`, and the budget is
--   only exponential, `2 ^ (4L + 2)`.  On the closed form the two
--   cross between L = 4 and L = 5 and never come back, so no constant
--   multiple of `2 ^ cReg * 2 ^ cReg` survives either.
--
--   L = 5 IS NOT MEASURED AND WAS NOT ATTEMPTED, by standing ruling:
--   the design session derives the recurrence from the evaluator`s
--   structure and predicts those rows before anyone runs them, so
--   running them first would spend the only out-of-sample test the
--   derivation has.  The row above is the closed form`s own arithmetic
--   and is labelled as such
------------------------------------------------------------------

------------------------------------------------------------------
-- `j` ITSELF, which is NOT the delivery count.  Everything above this
-- line measures DELIVERIES, and the conjunct bounds FRAMES: `j` is what
-- `foldPath-caps` accumulates, one summand per `↠` clause, and a
-- delivery whose path is `root` or `share-sink` costs zero of them.
-- The two were conflated when this file was written, and the difference
-- decides the derivation (see THE ROUTE IS DEAD, below), so the frames
-- get counted directly.
--
-- The mirror is `foldPath` / `dispatchShare` / `shareGo` / `cascadeGo`
-- clause for clause with the emit stream deleted and a ℕ threaded in its
-- place; it calls the REAL `stepFrame`, `shareAdmit`, `shareLatch` and
-- `shareFinish`, so the state it walks is the state the evaluator walks.
-- `mJ-faithful` checks that by comparing its final delivery ledger with
-- `mFolds`, which comes off the evaluator proper.
--
-- IT IS A LOWER BOUND on the conjunct's `j`, not the value: this counts
-- ONE per frame, and `stepFrame-caps` may report more than one when a
-- frame re-enters `subscribeE` (from-inner / thru-outer).  So a row that
-- BREAKS the budget here breaks it for real; a row that fits is evidence
-- and not a proof
------------------------------------------------------------------

-- a DELIVERY DESCRIPTOR: the registrations on the path from the root
-- chain down to this delivery, deepest first.  This is the object the
-- injection at `cascadeGo-deliveries` sends somewhere, made concrete, so
-- that `preClasses` and `fibreCap` stop being opaque and start being
-- measurable
Desc : Set
Desc = List RegId

-- WHAT ELSE THE WALK IS WORTH RECORDING WHILE IT IS RUNNING.  Both of
-- these are branching-profile data the delivery count collapses:
--
--   · `fires`, one entry per `dispatchShare` fan-out, holding the slot
--     that fired.  It is the mirror's own copy of what `mFire` reads off
--     the evaluator's handoffs, and the two are cross-checked next door.
--   · `gens`, one entry per registration MINTED during the cascade,
--     holding its GENERATION: how many mint-edges separate it from the
--     entry registry.  A registration minted while delivering to a
--     generation-g registration is generation g + 1, and everything in
--     the entry registry is generation 0.  The window is read off
--     `nextReg` around each delivery, which is exact because
--     registrations mint ids in order and nothing else moves the
--     counter
countEq : ℕ → List ℕ → ℕ
countEq x []       = 0
countEq x (y ∷ ys) = (if x ≡ᵇ y then 1 else 0) + countEq x ys

record Tally : Set where
  constructor tally
  field fires : List Source     -- one per fan-out: which slot fired
        gens  : List (RegId × ℕ)

emptyTally : Tally
emptyTally = tally [] []

genOf : RegId → List (RegId × ℕ) → ℕ
genOf r []             = 0
genOf r ((s , g) ∷ gl) = if r ≡ᵇ s then g else genOf r gl

-- stamp the `cnt` ids from `lo` upward at generation `g`, skipping any
-- the inner walk has already claimed at a deeper one
stampFrom : ℕ → RegId → ℕ → List (RegId × ℕ) → List (RegId × ℕ)
stampFrom zero      lo g gl = gl
stampFrom (suc cnt) lo g gl =
  stampFrom cnt (suc lo) g
    (if any (λ p → lo ≡ᵇ proj₁ p) gl then gl else (lo , g) ∷ gl)

fpFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
        → Gas → ℕ → Id → Tick → Desc → Tally
        → Path Γ u t → List (Val Γ u) → Bool
        → Sched Γ → EvalSt e → ℕ × List Desc × Tally × Sched Γ × EvalSt e

dsFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Gas → ℕ → Id → Tick → Desc → Tally → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → Sched Γ → EvalSt e → ℕ × List Desc × Tally × Sched Γ × EvalSt e

sgFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Gas → ℕ → Id → Tick → Desc → Tally → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → List (RegId × Path Γ (lookup Γ i) t)
        → Sched Γ → EvalSt e → ℕ × List Desc × Tally × Sched Γ × EvalSt e

fpFolds sf gas id now acc ta root vals fin sched st = 0 , [] , ta , sched , st
fpFolds sf gas id now acc ta (share-sink i) vals fin sched st =
  dsFolds sf gas id now acc ta i vals fin sched st
fpFolds sf gas id now acc ta (f ↠ p) vals fin sched st =
  let (vals′ , _ , fin′ , sched₁ , st₁) = stepFrame sf id now f p vals fin sched st
      (m , ds , ta₁ , sched₂ , st₂) = fpFolds sf gas id now acc ta p vals′ fin′ sched₁ st₁
  in suc m , ds , ta₁ , sched₂ , st₂

dsFolds sf zero id now acc ta i vals fin sched st = 0 , [] , ta , sched , st
dsFolds sf (suc gas) id now acc ta i vals fin sched st =
  let (m , ds , ta₁ , sched₁ , st₁) =
        sgFolds sf gas id now acc
          (record ta { fires = toℕ i ∷ Tally.fires ta }) i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)
      (_ , sched₂ , st₂) = shareFinish i fin ([] , sched₁ , st₁)
  in m , ds , ta₁ , sched₂ , st₂

sgFolds sf gas id now acc ta i vals fin []               sched st = 0 , [] , ta , sched , st
sgFolds sf gas id now acc ta i vals fin ((rid , p) ∷ ps) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = sgFolds sf gas id now acc ta i vals fin ps sched st
... | false =
  let d  = rid ∷ acc
      r₀ = EvalSt.nextReg st
      (m₁ , ds₁ , ta₁ , sched₁ , st₁) =
        fpFolds sf gas id now d ta p vals fin sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      ta′ = record ta₁
              { gens = stampFrom (EvalSt.nextReg st₁ ∸ r₀) r₀
                         (suc (genOf rid (Tally.gens ta))) (Tally.gens ta₁) }
      (m₂ , ds₂ , ta₂ , sched₂ , st₂) =
        sgFolds sf gas id now acc ta′ i vals fin ps sched₁ st₁
  in m₁ + m₂ , d ∷ (ds₁ ++ ds₂) , ta₂ , sched₂ , st₂

csFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → (a : Arrival Γ) → Id → Tally → List (RegId × Path Γ (arrTy a) t)
        → Sched Γ → EvalSt e → ℕ × List Desc × Tally × Sched Γ × EvalSt e
csFolds a id ta []                   sched st = 0 , [] , ta , sched , st
csFolds {n = n} {e = e} a id ta ((rid , c) ∷ chains) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = csFolds a id ta chains sched st
... | false =
  let d  = rid ∷ []
      r₀ = EvalSt.nextReg st
      (m₁ , ds₁ , ta₁ , sched₁ , st₁) =
        fpFolds (budgetAt e (Sched.slots sched) id) n id (arrTick a) d ta c
                (arrVal a ∷ []) (Arrival.isLast a) sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      ta′ = record ta₁
              { gens = stampFrom (EvalSt.nextReg st₁ ∸ r₀) r₀
                         (suc (genOf rid (Tally.gens ta))) (Tally.gens ta₁) }
      (m₂ , ds₂ , ta₂ , sched₂ , st₂) = csFolds a id ta′ chains sched₁ st₁
  in m₁ + m₂ , d ∷ (ds₁ ++ ds₂) , ta₂ , sched₂ , st₂

-- the run: the frames, the descriptors, the tally, the post-state, and
-- the RegIds the ENTRY registry held — the pre-state the first
-- coordinate reads
jAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
    → ℕ × List Desc × Tally × EvalSt e × List RegId
jAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = 0 , [] , emptyTally , st , []
...   | inj₂ (a , sched′) =
        let (m , ds , ta , _ , st′) =
              csFolds a nid emptyTally (chainsOf a st) sched′ (cascadeLatch a st)
        in m , ds , ta , st′ , map proj₁ (EvalSt.registry st)

------------------------------------------------------------------
-- R_end, AND IT DECIDES WHICH PROOF TECHNOLOGY THE DELIVERY BOUND GETS.
--
-- `cascadeGo-deliveries` says `D ≤ 2 ^ cReg * 2 ^ cReg` and has margin
-- without a route.  The DAG a delivery path runs through is the registry
-- AS OF THE DISPATCH, not at entry, so the inverted-pair argument — the
-- one leg that has never failed — proves `D ≤ 2 ^ R_end`, and whether
-- that is usable turns entirely on what R_end is:
--
--   · if the mints are bounded by entry data, `2 ^ R_end ≤ 4 ^ cReg`
--     lands the bound nearly verbatim and the grind starts on the
--     inverted pair;
--   · if the mints track the DELIVERIES, every subset-injection route is
--     dead for this bound whether or not it is true, and the proof has to
--     be what the damper natively is — an ORDERING fact, a
--     schedule-indexed induction on a decreasing remaining-dispatch
--     potential, not a statement about sets.
--
-- Registrations mint ids in order, so the mint count is just the
-- watermark's travel: `nextReg` after the cascade less `nextReg` before.
-- No threading, and it rides the `postAt` this file already computes.
--
-- THE READING, and it is the second outcome, unambiguously:
--
--   program   cReg      D   mints   mints/D
--   pG′  0      3      5       3      0.60
--   pG′  2      3      5       4      0.80
--   pG′² 0      5     20      10      0.50
--   pG′² 3      5     27      33      1.22
--   pL²  0      5     16       4      0.25
--   pL²  4      5     21      15      0.71
--   pL³  0      7     50       8      0.16
--   pL³  2      7    176      92      0.52
--   pL³  6      7    269     254      0.94
--   pL⁴  0      9    166      15      0.090   ‡
--   pL⁴  1      9    726     120      0.165   ‡
--   pL⁴  2      9   2546     575      0.226   ‡
--   pL⁴  3      9   6914    1940      0.281   †
--   pL⁴  4      9  14922    4943      0.331   †
--   pL⁴  5      9  26362    9948      0.377   †
--
--   ‡ mints measured through the typechecker (scripts/measure.sh), the D
--     column `refl`-pinned next door;  † measured through the compiled
--     harness (probe/Measure-Main.agda), measured-not-rechecked — see THE
--     L = 4 K-SWEEP below for the provenance rule
--
-- The L = 4 ladder does NOT contradict the reading; it sharpens it.  At a
-- FIXED k the ratio falls with ladder depth (k = 0: 0.60, 0.50, 0.16,
-- 0.090) and in k it climbs monotonically on every ladder, so "mints track
-- deliveries" is a statement about DEPTH IN k, and L = 4 is simply four
-- rungs short of where L = 3 ends up.  It climbs steadily — 0.090, 0.165,
-- 0.226, 0.281, 0.331, 0.377, still rising at the last row measured.
--
-- MINTS TRACK DELIVERIES.  At the deepest rung measured nearly every
-- delivery mints, and the registry the cascade LEAVES is 261 against an
-- entry cReg of 7 — thirty-seven times the entry registry, and it climbs
-- with the ladder.  R_end is not entry-computable by any margin.
--
-- SO EVERY SUBSET-INJECTION ROUTE IS DEAD FOR THE DELIVERY BOUND,
-- whether or not the bound is true.  The inverted-pair argument still
-- proves `D ≤ 2 ^ R_end` — it is the one leg that has never failed — but
-- at R_end = 261 that is 2 ^ 261 against a budget of 2 ^ 18, so it
-- proves nothing usable.  It also explains the fibre refutation
-- structurally rather than numerically: the minted registrations are
-- D-many, so the "second coordinate" was ranging over a set of size
-- 2 ^ D and never had a chance of sitting under 2 ^ cReg.
--
-- WHAT IS LEFT IS WHAT THE DAMPER NATIVELY IS: an ordering fact, not a
-- statement about sets.  A minted registration is reachable only by
-- dispatches that come AFTER it, so the proof wants a schedule-indexed
-- induction on a decreasing potential — the remaining-dispatch count,
-- fixed at each point by the DAG-so-far — rather than an injection into
-- anything.  That is different machinery from every route tried so far,
-- and this measurement is what says so before the grind rather than
-- after it
------------------------------------------------------------------

-- registrations MINTED during the one cascade
mMints : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mMints fuel e ins =
  EvalSt.nextReg (postAt fuel e ins) ∸ EvalSt.nextReg (proj₂ (stAt fuel e ins))

-- and the registry the cascade leaves behind (after cascadeFinish's
-- drop-and-sweep, so it is a floor on the DAG, not the peak)
mRegEnd : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mRegEnd fuel e ins = length (EvalSt.registry (postAt fuel e ins))

-- the frames one cascade steps
mJ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mJ fuel e ins = proj₁ (jAt fuel e ins)

-- the same walk's delivery ledger, for the faithfulness check
mJdel : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mJdel fuel e ins =
  length (EvalSt.delivered (proj₁ (proj₂ (proj₂ (proj₂ (jAt fuel e ins))))))

-- the mirror's own fire vector, for the cross-check against mFires
mFiresM : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
        → List Source → List ℕ
mFiresM fuel e ins ss =
  let fs = Tally.fires (proj₁ (proj₂ (proj₂ (jAt fuel e ins))))
  in map (λ s → countEq s fs) ss

-- how many registrations the cascade mints at each listed generation
-- (generation 0 is the entry registry, which the cascade does not mint,
-- so it is always 0 here)
mGens : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
      → List ℕ → List ℕ
mGens fuel e ins gs =
  let gl = map proj₂ (Tally.gens (proj₁ (proj₂ (proj₂ (jAt fuel e ins)))))
  in map (λ g → countEq g gl) gs

-- the deepest generation the mint loop reaches
mGenMax : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mGenMax fuel e ins =
  foldr (λ p m → proj₂ p ⊔ m) 0 (Tally.gens (proj₁ (proj₂ (proj₂ (jAt fuel e ins)))))

-- and the ledger's own size, which must agree with mMints
mGenTot : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mGenTot fuel e ins = length (Tally.gens (proj₁ (proj₂ (proj₂ (jAt fuel e ins)))))

-- and the descriptor count, which must agree with it: one descriptor per
-- delivery is the whole point
mJdesc : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mJdesc fuel e ins = length (proj₁ (proj₂ (jAt fuel e ins)))

------------------------------------------------------------------
-- THE TWO COORDINATES, DEFINED.  `cascadeGo-deliveries` postulates the
-- injection `delivery ↦ (pre-state class, index)` and bounds the two
-- coordinates separately at `preClasses-bound` and `fibreCap-bound`.
-- Both coordinates are opaque FUNCTIONS in the assembly, which means the
-- split locates work without proving anything — so here they are given
-- definitions and measured, which is the cheapest way to find out
-- whether `fibreCap ≤ cSize` is even true before anyone proves it.
--
-- The class of a delivery is the sub-list of its descriptor lying in the
-- ENTRY registry; the fibre of a class is how many deliveries share it
------------------------------------------------------------------

memN : ℕ → List ℕ → Bool
memN x xs = any (_≡ᵇ x) xs

bfilter : (ℕ → Bool) → List ℕ → List ℕ
bfilter p []       = []
bfilter p (x ∷ xs) = if p x then x ∷ bfilter p xs else bfilter p xs

eqNL : List ℕ → List ℕ → Bool
eqNL []       []       = true
eqNL []       (_ ∷ _)  = false
eqNL (_ ∷ _)  []       = false
eqNL (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqNL xs ys

memNL : List ℕ → List (List ℕ) → Bool
memNL x []       = false
memNL x (y ∷ ys) = eqNL x y ∨ memNL x ys

nubGo : List (List ℕ) → List (List ℕ) → List (List ℕ)
nubGo seen []       = seen
nubGo seen (x ∷ xs) = nubGo (if memNL x seen then seen else x ∷ seen) xs

countNL : List ℕ → List (List ℕ) → ℕ
countNL x []       = 0
countNL x (y ∷ ys) = (if eqNL x y then 1 else 0) + countNL x ys

maxFib : List (List ℕ) → List (List ℕ) → ℕ
maxFib []       all = 0
maxFib (c ∷ cs) all = countNL c all ⊔ maxFib cs all

classesOf : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → List Desc
classesOf fuel e ins with jAt fuel e ins
... | _ , ds , _ , _ , pre = map (bfilter (λ r → memN r pre)) ds

-- the first coordinate's range: how many distinct pre-state classes the
-- cascade's deliveries actually occupy.  `preClasses-bound` claims this
-- is at most 2 ^ cReg
mPre : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mPre fuel e ins = length (nubGo [] (classesOf fuel e ins))

-- the second coordinate's range: the largest fibre.  `fibreCap-bound`
-- claims this is at most cSize, and that claim is the DAMPER
mFib : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mFib fuel e ins =
  let cls = classesOf fuel e ins in maxFib (nubGo [] cls) cls

------------------------------------------------------------------
-- THE SHAPES
------------------------------------------------------------------

accV : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seedO : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

dup : ∀ {n} {Γ : Ctx n} {Θ} → Exp Γ [] [] Θ natᵗ → Exp Γ [] [] Θ natᵗ
dup e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ strmᵗ e ∷ []))

------------------------------------------------------------------
-- ONE SHARED LEVEL.  Five scripted emissions rather than two, because a
-- mid-emission subscriber misses the in-flight emission: the feedback is
-- one instant behind, so it can only be watched over several instants
------------------------------------------------------------------

Γˢ¹ : Ctx 2
Γˢ¹ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG : Slots Γˢ¹
insG fz        = shared (dup (input (fsuc fz)))
insG (fsuc fz) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3)
                                 ∷ (after 0 , 4) ∷ (after 0 , 5) ∷ []))

mintG′ : ∀ {Θ} → ℕ → Tm Γˢ¹ [] [] Θ (obs natᵗ)
mintG′ zero    = strmᵗ (input fz)
mintG′ (suc k) =
  strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′ k ∷ []))))
                          seedO (input fz)))

pG′ : ℕ → Closed Γˢ¹ natᵗ
pG′ k = mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′ k ∷ []))))
                         seedO (input fz))

-- the LEAN one-level ladder, so the lean family runs L = 1 … 4 rather
-- than starting at two.  Same drop as pL² / pL³ / pL⁴: no `accV` in the
-- step, so the accumulator is a fixed term and every registration,
-- dispatch and delivery keeps its shape
mintOnly¹ : ∀ {Θ} → ℕ → Tm Γˢ¹ [] [] Θ (obs natᵗ)
mintOnly¹ zero    = strmᵗ (input fz)
mintOnly¹ (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly¹ k) seedO (input fz)))

pL¹ : ℕ → Closed Γˢ¹ natᵗ
pL¹ k = mergeAllᵉ (scanᵉ (mintOnly¹ k) seedO (input fz))

------------------------------------------------------------------
-- TWO SHARED LEVELS, so share-DAG branching and self-similar minting
-- compound
------------------------------------------------------------------

Γˢ² : Ctx 3
Γˢ² = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG² : Slots Γˢ²
insG² fz               = shared (dup (input (fsuc fz)))
insG² (fsuc fz)        = shared (dup (input (fsuc (fsuc fz))))
insG² (fsuc (fsuc fz)) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3)
                                         ∷ (after 0 , 4) ∷ (after 0 , 5) ∷ []))

mintG′² : ∀ {Θ} → ℕ → Tm Γˢ² [] [] Θ (obs natᵗ)
mintG′² zero    = strmᵗ (input fz)
mintG′² (suc k) =
  strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′² k ∷ []))))
                          seedO (input fz)))

pG′² : ℕ → Closed Γˢ² natᵗ
pG′² k = mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′² k ∷ []))))
                          seedO (input fz))

------------------------------------------------------------------
-- THREE SHARED LEVELS.  The escape risk that is left after the nesting
-- direction saturates is the LADDER direction, so the tower is run over
-- the deepest ladder this normalises on
------------------------------------------------------------------

Γˢ³ : Ctx 4
Γˢ³ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG³ : Slots Γˢ³
insG³ fz                      = shared (dup (input (fsuc fz)))
insG³ (fsuc fz)               = shared (dup (input (fsuc (fsuc fz))))
insG³ (fsuc (fsuc fz))        = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insG³ (fsuc (fsuc (fsuc fz))) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

mintG′³ : ∀ {Θ} → ℕ → Tm Γˢ³ [] [] Θ (obs natᵗ)
mintG′³ zero    = strmᵗ (input fz)
mintG′³ (suc k) =
  strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′³ k ∷ []))))
                          seedO (input fz)))

pG′³ : ℕ → Closed Γˢ³ natᵗ
pG′³ k = mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′³ k ∷ []))))
                          seedO (input fz))

-- THE LEAN VARIANT, which carries the k-sweep the accumulating one
-- cannot reach.  Dropping `accV` from the step leaves the accumulator a
-- fixed term while every registration, dispatch and delivery keeps its
-- shape — less delivery, same k-dependence
mintOnly² : ∀ {Θ} → ℕ → Tm Γˢ² [] [] Θ (obs natᵗ)
mintOnly² zero    = strmᵗ (input fz)
mintOnly² (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly² k) seedO (input fz)))

pL² : ℕ → Closed Γˢ² natᵗ
pL² k = mergeAllᵉ (scanᵉ (mintOnly² k) seedO (input fz))

mintOnly³ : ∀ {Θ} → ℕ → Tm Γˢ³ [] [] Θ (obs natᵗ)
mintOnly³ zero    = strmᵗ (input fz)
mintOnly³ (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly³ k) seedO (input fz)))

pL³ : ℕ → Closed Γˢ³ natᵗ
pL³ k = mergeAllᵉ (scanᵉ (mintOnly³ k) seedO (input fz))

------------------------------------------------------------------
-- FOUR SHARED LEVELS, and this ladder exists for ONE question.  The
-- fibre of a pre-state class is capped at `2 ^ cReg` by `fibreCap-bound`
-- and MEASUREMENT 6 finds it ATTAINING that cap on the three-level lean
-- ladder — 128 against a 2 ^ cReg of 128, with the approach 8, 29, 64,
-- 99, 120, 127, 128.  A bound that is attained has no margin, and the
-- ratio of fibre to cap CLIMBS with ladder depth: 2/8, 13/32, 128/128 —
-- 0.25, 0.41, 1.00 at entry registries of 3, 5, 7.  Extrapolated, the
-- next rung breaks it.
--
-- So: same shape, one more shared level, entry registry 9, cap 512.  The
-- lean variant only — the accumulating one does not normalise past its
-- base rung two levels down, let alone here
------------------------------------------------------------------
-- THE L = 4 K-SWEEP, and it is the ladder's own answer to the question
-- MEASUREMENT 7 opened at k = 2 and stopped.  `D ≤ 2 ^ cReg * 2 ^ cReg` is
-- 4 ^ 9 = 262144 here.
--
--   k   cReg  cSize       D    D/262144    mints  mints/D       j    mFib
--   0     9      3      166    0.00063       15    0.090      182      16
--   1     9     10      726    0.00277      120    0.165     1542     121
--   2     9     18     2546    0.00971      575    0.226     8122     576
--   3     9     26     6914    0.02637     1940    0.281    29234    1941
--   4     9     34    14922    0.05692     4943    0.331    78010    4944
--   5     9     42    26362    0.10056     9948    0.377   162666       —
--   6     9     50        —          —        —        —        —       —
--
--   mPre is 46 at every k measured (k = 0 … 4); cReg is 9 at k = 0 … 4, 6
--   and 10; cSize is 8k + 2 for k ≥ 1 (98 at k = 12), 3 at k = 0.
--
-- PROVENANCE, and there is no silent third state.  k = 0, 1, 2 are the
-- `refl` pins next door, except the mints column, which is
-- measure.sh-through-the-typechecker.  Everything at k ≥ 3 comes off the
-- COMPILED harness (`probe/Measure-Main.agda`), so it is
-- measured-not-rechecked; the typechecker cannot reach it — `mFolds 0
-- (pL⁴ 3) insG⁴` was killed at 12.6 GB after 20 minutes, and the compiled
-- run answers it in seconds.  The harness's index 0 and 1 reproduce the
-- pinned 2546 and 576 exactly, and its `mS 0 (pL⁴ 3)` and `mMints 0
-- (pL⁴ 2)` agree with the typechecker's own 26 and 575, which is the only
-- reason any of the rest is believed.
--
-- k = 6 IS NOT MEASURED.  40 minutes at 12.4 GB under a compacting
-- collector with no answer, killed.  Recorded as measured-not-normalised,
-- not as absent.
--
-- WHAT THE SWEEP SAYS.  The bound HOLDS on every row — the largest D
-- measured anywhere in this file is 26362 against 262144.  But:
--
--   · D HAS NOT SATURATED.  Growth per rung is 4.37, 3.51, 2.72, 2.16,
--     1.77 — the last two rungs still buy 116 % and 77 %.  L = 3 flattened
--     by k = 5 (268 → 269, under 1 %); L = 4 at k = 5 is still nearly
--     doubling.  Nothing here observes saturation and nothing here should
--     be read as observing it.
--
--   · THE MARGIN SHRINKS IN k BY TWO ORDERS OF MAGNITUDE — 0.00063 at
--     k = 0 to 0.10056 at k = 5.  So the "margin GROWS as the ladder
--     deepens (0.078, 0.026, 0.016, 0.0097)" that Mint-Loop-Probe's
--     finding (6) records is a SHALLOW-k artefact: it compares L = 3 at
--     k = 6 with L = 4 at k = 2.  Compared at the deepest k each ladder
--     reaches, L = 4's 0.10056 is the WORST ratio in the file, worse than
--     the one-level ladder's 0.078.
--
--   · SO THE TEN-TIMES-WORSE GATE IS GONE at L = 4: 26362 * 10 = 263620,
--     which is over 262144.  The bound has under a factor of ten of head
--     room at the deepest row measured, and the row above it cannot be
--     measured in this container
--
-- ONE THING THE COLUMNS DO THAT NOBODY ASKED FOR: on this ladder the
-- largest fibre is the mint count PLUS ONE, on all five rows that have
-- both (16/15, 121/120, 576/575, 1941/1940, 4944/4943).  It is not a law —
-- L = 3 at k = 2 has 92 mints and a fibre of 64 — but on the ladder where
-- the fibre bound died it says exactly what killed it: the worst class's
-- fibre IS the cascade's minting, so capping it by anything entry-computable
-- is capping the mints by entry data, which the R_end reading above already
-- refuted.  Recorded as an observation, not explained
------------------------------------------------------------------

Γˢ⁴ : Ctx 5
Γˢ⁴ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG⁴ : Slots Γˢ⁴
insG⁴ fz                             = shared (dup (input (fsuc fz)))
insG⁴ (fsuc fz)                      = shared (dup (input (fsuc (fsuc fz))))
insG⁴ (fsuc (fsuc fz))               = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insG⁴ (fsuc (fsuc (fsuc fz)))        =
  shared (dup (input (fsuc (fsuc (fsuc (fsuc fz))))))
insG⁴ (fsuc (fsuc (fsuc (fsuc fz)))) = scripted (hot ((after 0 , 1) ∷ []))

mintOnly⁴ : ∀ {Θ} → ℕ → Tm Γˢ⁴ [] [] Θ (obs natᵗ)
mintOnly⁴ zero    = strmᵗ (input fz)
mintOnly⁴ (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly⁴ k) seedO (input fz)))

pL⁴ : ℕ → Closed Γˢ⁴ natᵗ
pL⁴ k = mergeAllᵉ (scanᵉ (mintOnly⁴ k) seedO (input fz))


------------------------------------------------------------------
-- THE NON-NESTED CONTROL: THE SHARE DAG WITH NOTHING UNDER IT.  No
-- scan, no minting, no k — just `merge(s, s)` through a ladder of
-- shares, so every dispatch is pre-state and the branching profile is
-- the DAG's own.  This is the row a delivery recurrence has to get
-- right before any mint-loop row is worth predicting.
--
-- These are Fold-Count-Probe's family C shapes at this file's SLOT
-- SCRIPTS, which are not the same programs: Fold-Count-Probe scripts
-- two emissions on every ladder, this file scripts five (L = 1, 2), two
-- (L = 3) and one (L = 4).  `Arrival.isLast` on the FIRST arrival
-- therefore differs, and every number below is measured on cascade 0,
-- so the two files' counts for "pS3" are not interchangeable.  The
-- accumulating control (family C's `pC`) is not repeated at all: the
-- k = 0 column of pL¹ … pL⁴ already is a non-nested scan over the same
-- ladder
pS¹ : Closed Γˢ¹ natᵗ
pS¹ = dup (input fz)

pS² : Closed Γˢ² natᵗ
pS² = dup (input fz)

pS³ : Closed Γˢ³ natᵗ
pS³ = dup (input fz)

pS⁴ : Closed Γˢ⁴ natᵗ
pS⁴ = dup (input fz)
