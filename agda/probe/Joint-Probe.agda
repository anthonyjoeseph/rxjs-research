------------------------------------------------------------------
-- THE JOINT-BOUND PROBE: is subscribeE-caps's hypothesis even TRUE?
--
-- `subscribeE-caps` (Verify-Budget-Sufficient/Caps-Face.agda) hypothesises
--
--     pathLen κ + sizeᵉ b ≤ Caps.cSize c
--
-- at every subscribe.  The DELIVERY side of the caps tree carries
-- `pathLen ≤ cSize` and `size ≤ cSize` SEPARATELY, and separate bounds do
-- not add: at a chain of length cSize ∸ 1 under a payload of size
-- cSize ∸ 1 the sum is twice the cap.  That is the single blocker on
-- thruWalk-caps, concatDrain-caps and innerFinish-caps, and the repair —
-- threading round 3's ℓ ledger through the delivery clique — is a change
-- to the hypothesis telescope of four ground clauses plus a state
-- predicate.  Expensive to make and worthless if the joint bound is false
-- on real runs, so it is MEASURED FIRST.
--
-- HOW.  scripts/joint-probe.sh copies agda/src to a scratch project and
-- scripts/joint-probe-instrument.py wraps `subscribeE` there with a
-- write-only log of `(pathLen κ , sizeᵉ b)` — the hypothesis's two
-- summands, at the exact argument positions the hypothesis names.  Every
-- recursive call inside the evaluator is indented, so the wrapper catches
-- ALL of them: root subscribe, structural descent, subscribeInner (the
-- *All edge, whose κ is `from-inner … ↠ κ`), subscribeAll's outer, the
-- shared-slot connect, deferᵉ and μᵉ.  This module therefore does NOT
-- typecheck against agda/src — like probe/Burst-Probe.agda, it only
-- builds inside the instrumented scratch project.
--
-- WHAT IS COMPARED AGAINST.  Not `capsAt`, which is a tower and would
-- pass vacuously.  The comparison is against the TIGHT ADMISSIBLE cSize:
-- the largest of the three quantities capsOK? forces cSize to dominate on
-- the state actually reached (max stored node size, max chain frame size,
-- max chain length).  If the joint sum sits under THAT, the joint form
-- demands nothing the separate bounds did not already demand, and the
-- ledger can be threaded.  If it sits over, the joint form is a strictly
-- new demand and the design session changes what subscribeE-caps asks
-- for instead.
--
-- The second reading is the WATERMARK the absorption argument needs: max
-- pathLen over the live registry against HALF the admissible cSize.  A
-- registry whose chains all sit under cSize / 2 is what would make a
-- joint ledger self-sustaining across ticks, because then a payload
-- bounded by cSize / 2 still fits alongside the chain.
--
------------------------------------------------------------------
-- THE READING, AND IT IS THE NEGATIVE ONE.
--
-- `joint ≤ adm` FAILS ON EVERY FAMILY MEASURED — seventeen programs,
-- three cascades each, no exceptions.  Worst joint / adm per family,
-- over fuel = 0, 1, 2 (rows below; all measured-not-rechecked, compiled):
--
--   family        worst joint   adm there   ratio
--   pR                    15         12     1.25
--   pRs                   31         30     1.03
--   pR2                   17         14     1.21
--   pM 1                  22         15     1.47
--   pM 2                  52         51     1.020
--   pM 3                 160        159     1.006
--   pM 4                 484        483     1.002
--   pD (deepScan)         27         24     1.13
--   pC0                   13         10     1.30
--   pC1                   18         17     1.06
--   pC2                   32         31     1.03
--   pC3                   60         59     1.02
--   pS1 / pS2 / pS3        7          0     — (adm is 0 from fuel 1 on)
--   pL¹ k = 0              9          2     4.5
--   pL¹ k = 1 … 3      17/25/33   10/18/26  1.70 / 1.39 / 1.27
--   pL² k = 0 … 3      as pL¹     as pL¹    as pL¹
--   pL³ k = 0              9          1     9.0
--   pL³ k = 1 … 3      17/25/33    9/17/25  1.89 / 1.47 / 1.32
--
-- TWO SHAPES OF FAILURE, and they are different failures.
--
--   (a) THE NARROW ONE, on every family carrying a scan: joint is
--       adm + 1 EXACTLY at the deep rungs — 22/21, 31/30, 26/25, 52/51,
--       160/159, 484/483, 18/17, 32/31, 60/59, 116/115.  The payload
--       being subscribed IS the stored accumulator, so its size alone
--       already attains the tight cap, and any chain at all on top
--       overshoots by that chain's length.  This is the memo's diagnosis
--       measured: the two separate bounds are each TIGHT, so their sum
--       cannot be under the same cap.
--
--   (b) THE WIDE ONE, on the families that store nothing: pS1 … pS3 and
--       every ladder's k = 0 rung.  There adm collapses to 0 or 1 or 2
--       while the joint is 7 or 9, so the ratio is not near 1 at all —
--       it is 4.5, 9, or undefined.  Nothing is stored, so there is no
--       size for the chain to hide under.
--
-- AGAINST THE CAPS TREE'S OWN PRE-BLOWUP BASE, `2 + sizeᵉ e +
-- slotsSize sl`, the picture is better but still not clean: the joint
-- fits on pS1 … pS3, on every mint ladder rung, on pM 1, and exactly on
-- pC0 (18 = 18) — and BREAKS on pR (22 > 20), pRs (31 > 24), pR2
-- (26 > 25), pM 2 … 4 (52 > 35, 160 > 43, 484 > 51), pD (47 > 32) and
-- pC1 … pC3 (32 > 25, 60 > 32, 116 > 39).  Worst there is pM 4 at 9.5x.
--
-- AGAINST THE cSize capsAt ACTUALLY SUPPLIES the joint holds with room
-- to burn, and that is not evidence of anything: capsAt 0 is
-- `frameBlowup` of the base, i.e. `iterSize base J base` with J =
-- `2 ^ cReg * 2 ^ cReg * base`, which on pM 4 alone is iterating
-- `s ↦ 51 * (1 + 2s)` some 10 ^ 31 times.  A bound that large is
-- satisfied by anything, which is exactly why the comparison that
-- decides the repair is against the TIGHT value and not against it.
--
-- THE WATERMARK, second reading: `2 * regLen ≤ adm` HOLDS on every
-- family that stores something — pR 4 ≤ 12, pRs 8 ≤ 30, pR2 4 ≤ 14,
-- pM 1…4 8/10/12/14 ≤ 15/51/159/483, pD 4 ≤ 24, pC0…pC3 4 ≤ 10/17/31/59,
-- and the mint ladders at k ≥ 1 (6 ≤ 10, 8 ≤ 18, 10 ≤ 26) — and FAILS on
-- exactly the same families as (b): pS1 … pS3 (2 > 1) and every ladder's
-- k = 0 rung (4 > 2).  It fails there for a STRUCTURAL reason, not a
-- numerical one: adm is itself a max that includes regLen, so
-- `2 * regLen ≤ adm` demands the SIZE side dominate the length side by a
-- factor of two, and a program that stores nothing has no size side.
--
-- SO THE HALF-CAP WATERMARK CANNOT BE STRENGTHENED INTO regsSz? AS IT
-- STANDS.  It is true wherever there is state to absorb it and false
-- wherever there is not, and the cases where it is false are the
-- simplest programs in the corpus, not the pathological ones
------------------------------------------------------------------
module Joint-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.String using (String; _++_; lines)
open import Data.List using (List; []; _∷_; map; foldr; length)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import CLI.IO

open import Rx.Prim using (Fuel; after_,_; hot)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Fn; natᵗ; obs; _×ᵗ_; input;
                          ofᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂;
                          fstᵗ; sndᵗ; varᵗ; sizeᵉ)
open import Rx.Evaluator using (Slots; scripted; shared; Sched; EvalSt;
                                sched-next; cascade; slotsSize)

open import Mint-Loop-Shapes
  using (runSt; nodeSize; liveSize; pathSize; pathLen; dup; accV; seedO;
         mFolds; mReg;
         Γˢ¹; Γˢ²; Γˢ³; insG; insG²; insG³; pL¹; pL²; pL³)

------------------------------------------------------------------
-- THE MEASURES, all read off the state AFTER cascade `fuel` — so
-- `fuel = 2` is "cascades 0, 1 and 2 have run", which is the window the
-- design session asked for
------------------------------------------------------------------

postBoth : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
         → Sched Γ × EvalSt e
postBoth fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = sched , st
...   | inj₂ (a , sched′) =
        let (_ , sched″ , st′) = cascade a nid sched′ st in sched″ , st′

-- capsOK?'s three cSize demands, at their tightest on the state reached
qSize : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qSize fuel e ins with postBoth fuel e ins
... | sched , st =
      foldr (λ kv m → nodeSize (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
      ⊔ foldr (λ l m → liveSize l ⊔ m) 0 (Sched.live sched)

qChain : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qChain fuel e ins =
  foldr (λ en m → pathSize (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (postBoth fuel e ins)))

-- THE WATERMARK: max chain length over the live registry
qLen : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qLen fuel e ins =
  foldr (λ en m → pathLen (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (postBoth fuel e ins)))

-- the tight admissible cSize
qAdm : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qAdm fuel e ins = qSize fuel e ins ⊔ qChain fuel e ins ⊔ qLen fuel e ins

------------------------------------------------------------------
-- and the log itself: one entry per subscribeE the run performed
------------------------------------------------------------------

jointsOf : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
         → List (ℕ × ℕ)
jointsOf fuel e ins = EvalSt.jointLog (proj₂ (postBoth fuel e ins))

-- the quantity subscribeE-caps hypothesises a bound on
qJoint : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qJoint fuel e ins =
  foldr (λ p m → (proj₁ p + proj₂ p) ⊔ m) 0 (jointsOf fuel e ins)

-- and its two summands separately, so a breach can be attributed
qJLen : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qJLen fuel e ins = foldr (λ p m → proj₁ p ⊔ m) 0 (jointsOf fuel e ins)

qJSz : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qJSz fuel e ins = foldr (λ p m → proj₂ p ⊔ m) 0 (jointsOf fuel e ins)

qJN : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qJN fuel e ins = length (jointsOf fuel e ins)

-- THE ONE THAT MATTERS.  The root subscribe and every sharedConnect have
-- pathLen 0 — `root` and `share-sink i` — so their joint sum degenerates
-- to the size bound, which is exactly why sharedConnect-caps composes and
-- the *All edge does not.  This is the max restricted to entries whose
-- chain is NON-EMPTY: the subscribeInner and subscribeAll edges, where
-- the hypothesis is genuinely joint
qJointI : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
qJointI fuel e ins =
  foldr (λ p m → (if 1 ≤ᵇ proj₁ p then proj₁ p + proj₂ p else 0) ⊔ m) 0
        (jointsOf fuel e ins)

-- the cSize the caps tree actually starts from, BEFORE capsAt's own
-- frameBlowup: the syntactic base `2 + sizeᵉ e + slotsSize sl`
qBase : ∀ {n} {Γ : Ctx n} {t} → (e : Closed Γ t) → Slots Γ → ℕ
qBase e ins = 2 + sizeᵉ e + slotsSize ins

------------------------------------------------------------------
-- THE SHAPES.  The mint ladders come from Mint-Loop-Shapes; the rest are
-- Fold-Count-Probe's families A, B, C and D at its own slot scripts,
-- repeated here because those modules carry `refl` walls that this
-- scratch build would have to recheck against an instrumented evaluator
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

ins1 : Slots Γ₁
ins1 fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

ins2 : Slots Γ₂
ins2 fz        = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))
ins2 (fsuc fz) = scripted (hot ((after 0 , 4) ∷ (after 0 , 5) ∷ []))

v0 : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ∷ Θ) (obs natᵗ)
v0 = varᵗ (here refl)

dup3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ) (obs natᵗ)
dup3 = strmᵗ (mergeAllᵉ (ofᵉ (v0 ∷ v0 ∷ v0 ∷ [])))

liftN : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] natᵗ (obs natᵗ)
liftN = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

keep : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ obs natᵗ) (obs natᵗ)
keep = sndᵗ (varᵗ (here refl))

-- FAMILY A: J-Budget-Probe's chain-length ladder
mapChain : ℕ → Closed Γ₁ (obs natᵗ)
mapChain zero    = mapᵉ liftN (input fz)
mapChain (suc k) = mapᵉ dup3 (mapChain k)

pM : ℕ → Closed Γ₁ natᵗ
pM k = mergeAllᵉ (scanᵉ keep seedO (mapChain k))

-- FAMILY B: the State-Blowup registry families and deepScan
wrap2ᵍ : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ Θ) (obs natᵗ)
wrap2ᵍ = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

deepScan : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepScan = strmᵗ (mergeAllᵉ (scanᵉ wrap2ᵍ seedO (mergeAllᵉ (ofᵉ (accV ∷ [])))))

pD : Closed Γ₁ natᵗ
pD = mergeAllᵉ (scanᵉ deepScan seedO (input fz))

wrapIn : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapIn = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ strmᵗ (input fz) ∷ [])))

pR : Closed Γ₁ natᵗ
pR = mergeAllᵉ (scanᵉ wrapIn seedO (input fz))

src3 : ∀ {n} {Γ : Ctx n} → Closed Γ natᵗ
src3 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

pRs : Closed Γ₁ natᵗ
pRs = mergeAllᵉ (scanᵉ wrapIn seedO src3)

wrapIn2 : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapIn2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ strmᵗ (input fz)
                                     ∷ strmᵗ (input (fsuc fz)) ∷ [])))

pR2 : Closed Γ₂ natᵗ
pR2 = mergeAllᵉ (scanᵉ wrapIn2 seedO (input fz))

-- FAMILIES C and D: the share ladders, at Fold-Count-Probe's two-emission
-- scripts (which are NOT Mint-Loop-Shapes' scripts, so these slot
-- telescopes are defined here rather than imported)
insᶜ¹ : Slots Γˢ¹
insᶜ¹ fz        = shared (dup (input (fsuc fz)))
insᶜ¹ (fsuc fz) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

insᶜ² : Slots Γˢ²
insᶜ² fz               = shared (dup (input (fsuc fz)))
insᶜ² (fsuc fz)        = shared (dup (input (fsuc (fsuc fz))))
insᶜ² (fsuc (fsuc fz)) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

insᶜ³ : Slots Γˢ³
insᶜ³ fz                      = shared (dup (input (fsuc fz)))
insᶜ³ (fsuc fz)               = shared (dup (input (fsuc (fsuc fz))))
insᶜ³ (fsuc (fsuc fz))        = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insᶜ³ (fsuc (fsuc (fsuc fz))) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

pS1 : Closed Γˢ¹ natᵗ
pS1 = dup (input fz)

pS2 : Closed Γˢ² natᵗ
pS2 = dup (input fz)

pS3 : Closed Γˢ³ natᵗ
pS3 = dup (input fz)

wrap1 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap1 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ [])))

pC0 : Closed Γ₁ natᵗ
pC0 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pC1 : Closed Γˢ¹ natᵗ
pC1 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pC2 : Closed Γˢ² natᵗ
pC2 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pC3 : Closed Γˢ³ natᵗ
pC3 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

------------------------------------------------------------------
-- THE ROWS.  One row per (program, fuel): the joint maximum, its two
-- summands, the tight admissible cSize, the registry chain watermark,
-- and how many subscribes the run performed
------------------------------------------------------------------

row : ∀ {n} {Γ : Ctx n} {t} → String → Fuel → (e : Closed Γ t) → Slots Γ
    → String
row nm fuel e ins =
  nm ++ " fuel=" ++ show fuel
     ++ "  joint=" ++ show (qJoint fuel e ins)
     ++ "  jLen="  ++ show (qJLen fuel e ins)
     ++ "  jSz="   ++ show (qJSz fuel e ins)
     ++ "  jointI=" ++ show (qJointI fuel e ins)
     ++ "  base="  ++ show (qBase e ins)
     ++ "  adm="   ++ show (qAdm fuel e ins)
     ++ "  regLen=" ++ show (qLen fuel e ins)
     ++ "  n="     ++ show (qJN fuel e ins)
     ++ "\n"

rows : List String
rows =
  -- 0 … 8: the State-Blowup families
    row "pR"   0 pR  ins1 ∷ row "pR"   1 pR  ins1 ∷ row "pR"   2 pR  ins1
  ∷ row "pRs"  0 pRs ins1 ∷ row "pRs"  1 pRs ins1 ∷ row "pRs"  2 pRs ins1
  ∷ row "pR2"  0 pR2 ins2 ∷ row "pR2"  1 pR2 ins2 ∷ row "pR2"  2 pR2 ins2
  -- 9 … 20: the J-Budget chain-length family
  ∷ row "pM1"  0 (pM 1) ins1 ∷ row "pM1"  1 (pM 1) ins1 ∷ row "pM1"  2 (pM 1) ins1
  ∷ row "pM2"  0 (pM 2) ins1 ∷ row "pM2"  1 (pM 2) ins1 ∷ row "pM2"  2 (pM 2) ins1
  ∷ row "pM3"  0 (pM 3) ins1 ∷ row "pM3"  1 (pM 3) ins1 ∷ row "pM3"  2 (pM 3) ins1
  ∷ row "pM4"  0 (pM 4) ins1 ∷ row "pM4"  1 (pM 4) ins1 ∷ row "pM4"  2 (pM 4) ins1
  -- 21 … 23: deepScan
  ∷ row "pD"   0 pD  ins1 ∷ row "pD"   1 pD  ins1 ∷ row "pD"   2 pD  ins1
  -- 24 … 35: the Fold-Count ladders, L ≤ 3
  ∷ row "pC0"  0 pC0 ins1 ∷ row "pC0"  1 pC0 ins1 ∷ row "pC0"  2 pC0 ins1
  ∷ row "pC1"  0 pC1 insᶜ¹ ∷ row "pC1"  1 pC1 insᶜ¹ ∷ row "pC1"  2 pC1 insᶜ¹
  ∷ row "pC2"  0 pC2 insᶜ² ∷ row "pC2"  1 pC2 insᶜ² ∷ row "pC2"  2 pC2 insᶜ²
  ∷ row "pC3"  0 pC3 insᶜ³ ∷ row "pC3"  1 pC3 insᶜ³ ∷ row "pC3"  2 pC3 insᶜ³
  -- 36 … 44: the pure share DAGs
  ∷ row "pS1"  0 pS1 insᶜ¹ ∷ row "pS1"  1 pS1 insᶜ¹ ∷ row "pS1"  2 pS1 insᶜ¹
  ∷ row "pS2"  0 pS2 insᶜ² ∷ row "pS2"  1 pS2 insᶜ² ∷ row "pS2"  2 pS2 insᶜ²
  ∷ row "pS3"  0 pS3 insᶜ³ ∷ row "pS3"  1 pS3 insᶜ³ ∷ row "pS3"  2 pS3 insᶜ³
  -- 45 … 80: the mint ladders, L ≤ 3, k ≤ 3
  ∷ row "pL1k0" 0 (pL¹ 0) insG ∷ row "pL1k0" 1 (pL¹ 0) insG ∷ row "pL1k0" 2 (pL¹ 0) insG
  ∷ row "pL1k1" 0 (pL¹ 1) insG ∷ row "pL1k1" 1 (pL¹ 1) insG ∷ row "pL1k1" 2 (pL¹ 1) insG
  ∷ row "pL1k2" 0 (pL¹ 2) insG ∷ row "pL1k2" 1 (pL¹ 2) insG ∷ row "pL1k2" 2 (pL¹ 2) insG
  ∷ row "pL1k3" 0 (pL¹ 3) insG ∷ row "pL1k3" 1 (pL¹ 3) insG ∷ row "pL1k3" 2 (pL¹ 3) insG
  ∷ row "pL2k0" 0 (pL² 0) insG² ∷ row "pL2k0" 1 (pL² 0) insG² ∷ row "pL2k0" 2 (pL² 0) insG²
  ∷ row "pL2k1" 0 (pL² 1) insG² ∷ row "pL2k1" 1 (pL² 1) insG² ∷ row "pL2k1" 2 (pL² 1) insG²
  ∷ row "pL2k2" 0 (pL² 2) insG² ∷ row "pL2k2" 1 (pL² 2) insG² ∷ row "pL2k2" 2 (pL² 2) insG²
  ∷ row "pL2k3" 0 (pL² 3) insG² ∷ row "pL2k3" 1 (pL² 3) insG² ∷ row "pL2k3" 2 (pL² 3) insG²
  ∷ row "pL3k0" 0 (pL³ 0) insG³ ∷ row "pL3k0" 1 (pL³ 0) insG³ ∷ row "pL3k0" 2 (pL³ 0) insG³
  ∷ row "pL3k1" 0 (pL³ 1) insG³ ∷ row "pL3k1" 1 (pL³ 1) insG³ ∷ row "pL3k1" 2 (pL³ 1) insG³
  ∷ row "pL3k2" 0 (pL³ 2) insG³ ∷ row "pL3k2" 1 (pL³ 2) insG³ ∷ row "pL3k2" 2 (pL³ 2) insG³
  ∷ row "pL3k3" 0 (pL³ 3) insG³ ∷ row "pL3k3" 1 (pL³ 3) insG³ ∷ row "pL3k3" 2 (pL³ 3) insG³
  -- 81, 82: CALIBRATION.  The instrumentation is only believable if the
  -- instrumented evaluator still computes what the uninstrumented one
  -- does, and the log being write-only is a syntactic check, not a
  -- behavioural one.  These two are `refl`-pinned next door in
  -- Mint-Loop-Probe at 176 and 7
  ∷ ("CAL mFolds 0 (pL3 2) insG3 [176] = " ++ show (mFolds 0 (pL³ 2) insG³) ++ "\n")
  ∷ ("CAL mReg   0 (pL3 2) insG3 [7]   = " ++ show (mReg 0 (pL³ 2) insG³) ++ "\n")
  ∷ []

idx : ℕ → List String → String
idx _       []       = "OUT-OF-RANGE\n"
idx zero    (x ∷ _)  = x
idx (suc n) (_ ∷ xs) = idx n xs

firstLine : String → String
firstLine s with lines s
... | []      = ""
... | (l ∷ _) = l

main : IO Unit
main =
  getContents >>= λ inp →
  putStr (maybe′ (λ n → idx n rows) "BAD-INDEX\n" (readMaybe 10 (firstLine inp)))
