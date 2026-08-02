------------------------------------------------------------------
-- THE NEST-COUNT PROBE: is the WIDTH COUNT a SYNTACTIC CONSTANT?
--
-- THE RULING UNDER TEST (2026-08-02, the split-count recurrence).  The
-- two frameStep axes get two different counts:
--
--   · the SIZE axis keeps a count that may read cWid, because
--     `iterSize` only MULTIPLIES per fold and stays a single
--     exponential in the count;
--   · the WIDTH axis, whose `iterFold` EXPONENTIATES per fold and so
--     buys a whole tower story per pass, gets a count that is a
--     SYNTACTIC CONSTANT — the maximal scan-NESTING depth reachable in
--     one instant:
--
--         widthCount e sl = suc (nestᵉ e + slotsNest sl)
--
-- The ruling rests on Mult-Width-Probe §7, which prices ONE `applyFn`:
-- a step function with TWO nested `scanᵉ` nodes over the plug is DOUBLY
-- exponential in the plug's width, and under `foldStep S w = S ^ suc w`
-- two nested nodes cost exactly TWO passes.  The claim generalises that
-- to a whole instant: per-instant width stories ≤ syntactic nesting,
-- cross-delivery compounding ≤ 1.
--
-- THE HALF THAT HOLDS AND THE HALF THAT DOES NOT.  Both are measured
-- below, on the family built to break the claim.
--
--   PER APPLICATION — HOLDS, exactly.  `pμD2M` drives ONE `applyFn` of
--   an fn2-shaped step per instant off the μ ticker, and the stored
--   accumulator's tower height climbs 2 → 4 → 6 → 8 → 10: exactly
--   `nestᵗ` of the step function per instant, over a clean four-instant
--   sweep, against a `widthCount` of 4.
--
--   PER INSTANT — FAILS, and the excess is the DELIVERY COUNT.  The
--   same scan node folds once per DELIVERY, and each fold pays the
--   nesting again.  `pFan n` gives the node exactly `n` deliveries per
--   arrival out of a source that holds no `scanᵉ` at all, so `nestᵉ`
--   cannot see them: the stored tower height climbs by `n` per instant
--   while `widthCount` stays 3 for every n.  The minimal `foldStep`
--   pass count `wNeed` follows it one for one — 1, 2, 3 at n = 1, 2, 3
--   — so n = 4 demands four passes against a budget of three.
--
-- STORIES PER INSTANT = DELIVERIES × NESTING, not nesting.  `pFan2 n`
-- puts both factors in one family: the fn2 step at n deliveries climbs
-- 2n stories in one instant (0 → 2, 0 → 4, 0 → 6 at n = 1, 2, 3)
-- against a `widthCount` of 4.
--
-- AND THE DELIVERY COUNT IS NOT SYNTACTIC.  That is the whole point:
-- `frameBlowup` already spends `D̂ c = 2 ^ (2 ^ cReg c)` on it, because
-- Fold-Count-Probe and Delivery-Law-Prediction measured one cascade's
-- deliveries DOUBLY exponential in the shared-slot count.  `pFan`'s
-- fan-out is only the cheapest way to exhibit the same excess with
-- every other quantity held still.
--
-- HOW THE TOWER IS MEASURED, since the numeral is not available.  One
-- deepening fold adds a CONSTANT number of syntax nodes to the stored
-- accumulator (`mAcc` below: 3, 24, 45, 66, 87, 108 at n = 0 … 5) and
-- EXPONENTIATES its width, so the width numeral leaves the machine at
-- four folds while the syntax stays tiny.  `mNest` reads `nestᵉ` of the
-- stored value — the tower HEIGHT the width numeral would have — and it
-- is calibrated against the numeral wherever the numeral exists:
-- `wNeed` is 1 at height 1 (W⁺ = 6), 2 at height 2 (W⁺ = 3072), and 3
-- at height 3 (W⁺ has 932 digits against `iterFold 20 2 1`'s 522).
--
-- PROVENANCE is Instant-Height's three-state: `refl` (pinned below),
-- `compiled` (probe/Nest-Count-Main.agda through the GHC backend), and
-- NOT MEASURED with the wall recorded.
--
-- Standalone, so src/Main.agda never reaches it.
------------------------------------------------------------------
module Nest-Count-Probe where

open import Data.Nat.DivMod using (_/_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤ᵇ_; _⊔_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; tabulate)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel)
open import Rx.Exp
open import Rx.Evaluator using (Slots; Slot; scripted; shared; Sched; EvalSt;
                                LiveSource; NodeState; scan-st; take-st;
                                merge-st; concat-st; switch-st; exhaust-st)
open import Verify-Budget-Sufficient.Caps using (foldStep; iterFold)

open import Mint-Loop-Shapes using (accV; seedO; pL²; pL³;
                                    insG; insG²; insG³; mS; stAt)
open import Charge-Probe using (deepScan; wrap3; progD; progDT; progW; pF1; pF2;
                                Γ₀; Γ₁; ins₀; insD₂)
open import Instant-Height-Probe using (ticker; pμ2; pμD; wStore; wNeed)

------------------------------------------------------------------
-- (1) THE SYNTACTIC MEASURE.  `nestᵉ` is the deepest chain of `scanᵉ`
-- nodes through subterms AND through step functions — the fn2 pattern,
-- where the nesting lives inside a `Fn` rather than in the program's
-- spine.  It is trivially ≤ sizeᵉ (one `suc` per scanᵉ node, and `⊔`
-- where sizeᵉ sums), which is what makes it affordable as a count
------------------------------------------------------------------

mutual
  nestᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  nestᵉ (input i)       = 0
  nestᵉ (ofᵉ ts)        = nestᵗˢ ts
  nestᵉ emptyᵉ          = 0
  nestᵉ (mapᵉ f e)      = nestᵗ f ⊔ nestᵉ e
  nestᵉ (takeᵉ c e)     = nestᵗ c ⊔ nestᵉ e
  nestᵉ (scanᵉ f z e)   = suc (nestᵗ f ⊔ nestᵗ z ⊔ nestᵉ e)
  nestᵉ (mergeAllᵉ e)   = nestᵉ e
  nestᵉ (concatAllᵉ e)  = nestᵉ e
  nestᵉ (switchAllᵉ e)  = nestᵉ e
  nestᵉ (exhaustAllᵉ e) = nestᵉ e
  nestᵉ (μᵉ e)          = nestᵉ e
  nestᵉ (varᵉ x)        = 0
  nestᵉ (deferᵉ e)      = nestᵉ e

  nestᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  nestᵗ (varᵗ x)      = 0
  nestᵗ unit̂          = 0
  nestᵗ (bool̂ _)      = 0
  nestᵗ (nat̂ _)       = 0
  nestᵗ (pairᵗ a b)   = nestᵗ a ⊔ nestᵗ b
  nestᵗ (fstᵗ p)      = nestᵗ p
  nestᵗ (sndᵗ p)      = nestᵗ p
  nestᵗ (inlᵗ a)      = nestᵗ a
  nestᵗ (inrᵗ a)      = nestᵗ a
  nestᵗ (caseᵗ s l r) = nestᵗ s ⊔ nestᵗ l ⊔ nestᵗ r
  nestᵗ (ifᵗ c a b)   = nestᵗ c ⊔ nestᵗ a ⊔ nestᵗ b
  nestᵗ (primᵗ _ a)   = nestᵗ a
  nestᵗ (strmᵗ e)     = nestᵉ e

  nestᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestᵗˢ []       = 0
  nestᵗˢ (y ∷ ys) = nestᵗ y ⊔ nestᵗˢ ys

-- the slot telescope's own nesting, mirroring slotsCeil clause for clause
slotNest : ∀ {n} {Γ : Ctx n} {u} → Slot Γ u → ℕ
slotNest (scripted _) = 0
slotNest (shared d)   = nestᵉ d

slotsNestgo : ∀ {n} {Γ : Ctx n} → Slots Γ → List (Fin n) → ℕ
slotsNestgo sl []       = 0
slotsNestgo sl (i ∷ is) = slotNest (sl i) ⊔ slotsNestgo sl is

slotsNest : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNest {n = n} sl = slotsNestgo sl (tabulate {n = n} (λ i → i))

-- THE COUNT UNDER TEST
widthCount : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Slots Γ → ℕ
widthCount e sl = suc (nestᵉ e + slotsNest sl)

------------------------------------------------------------------
-- (2) THE TOWER-HEIGHT PROXY.
--
-- `mNest` is Charge-Probe's `mW` with `nestᵉ` in place of `pWᵛ`: the
-- tallest tower height the pre-cascade state stores.  It exists because
-- the width numeral does not: one deepening fold adds a constant number
-- of nodes and exponentiates the width, so at four folds the numeral is
-- a tower of height four and no harness forms it, while `nestᵉ` of the
-- same value is 4.  `mAcc` is the same walk reading `sizeᵛ`, so the
-- syntax cost per fold is on the record beside the height
------------------------------------------------------------------

nestᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
nestᵛ unitᵗ    _        = 0
nestᵛ boolᵗ    _        = 0
nestᵛ natᵗ     _        = 0
nestᵛ (s ×ᵗ t) (a , b)  = nestᵛ s a ⊔ nestᵛ t b
nestᵛ (s +ᵗ t) (inj₁ a) = nestᵛ s a
nestᵛ (s +ᵗ t) (inj₂ b) = nestᵛ t b
nestᵛ (obs t)  e        = nestᵉ e

nodeN : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeN (scan-st {t} v)   = nestᵛ t v
nodeN (concat-st q _ _) = foldr (λ o m → nestᵉ o ⊔ m) 0 q
nodeN (take-st _)       = 0
nodeN (merge-st _ _)    = 0
nodeN (switch-st _ _)   = 0
nodeN (exhaust-st _ _)  = 0

liveN : ∀ {n} {Γ : Ctx n} → LiveSource Γ → ℕ
liveN l = foldr (λ tv m → nestᵛ (LiveSource.elemTy l) (proj₂ tv) ⊔ m) 0
                (LiveSource.pending l)

mNest : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mNest fuel e ins =
  let (sched , st) = stAt fuel e ins
  in foldr (λ kv m → nodeN (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveN l ⊔ m) 0 (Sched.live sched)

sizeN : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
sizeN (scan-st {t} v)   = sizeᵛ t v
sizeN (concat-st q _ _) = foldr (λ o m → sizeᵉ o ⊔ m) 0 q
sizeN (take-st _)       = 0
sizeN (merge-st _ _)    = 0
sizeN (switch-st _ _)   = 0
sizeN (exhaust-st _ _)  = 0

mAcc : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mAcc fuel e ins =
  let (sched , st) = stAt fuel e ins
  in foldr (λ kv m → sizeN (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)

-- S ; the tower height entering instant id ; the height leaving it ;
-- and the stored accumulator's SYNTAX at both ends
nrow : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → List ℕ
nrow id e ins = mS id e ins ∷ mNest id e ins ∷ mNest (suc id) e ins
              ∷ mAcc id e ins ∷ mAcc (suc id) e ins ∷ []

digitsGo : ℕ → ℕ → ℕ
digitsGo zero       m = 0
digitsGo (suc fuel) m = if m ≤ᵇ 9 then 1 else suc (digitsGo fuel (m / 10))

dig : ℕ → ℕ
dig = digitsGo 1000000

------------------------------------------------------------------
-- (3) THE FAMILIES.
--
-- `deep2` is Mult-Width-Probe §7's `fn2` — a step function with TWO
-- nested `scanᵉ` nodes over the plug, doubly exponential in one
-- application.  `deepScan` (Charge-Probe's, = §7's `fn1`) is the same
-- shape one nesting shallower.
--
-- `fanN n` gives a scan node EXACTLY n deliveries per arrival, out of
-- syntax that holds no `scanᵉ` — so it moves the DELIVERY count while
-- leaving `nestᵉ` and `slotsNest` where they are.
--
-- AND THE BURST IS DISCARDED, which is what makes the deep rungs
-- runnable at all: a program ending in `mergeAllᵉ` unwraps the stored
-- accumulator into `outWᵉ`-many payloads, so it cannot be run past the
-- instant where the WIDTH leaves the machine — two folds.  A `mapᵉ` to
-- a constant drops the observable without entering it, so the store
-- still grows and the run survives to sixteen folds
------------------------------------------------------------------

W2 : ∀ {n} {Γ : Ctx n} {Θ} → Fn Γ [] [] Θ (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
W2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

wrapE : ∀ {n} {Γ : Ctx n} {Θ} → Exp Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) natᵗ
      → Exp Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) natᵗ
wrapE e = mergeAllᵉ (scanᵉ W2 seedO e)

accSrc : ∀ {n} {Γ : Ctx n} {Θ} → Exp Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) natᵗ
accSrc = mergeAllᵉ (ofᵉ (accV ∷ []))

deep2 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deep2 = strmᵗ (wrapE (wrapE accSrc))

copiesN : ∀ {n} {Γ : Ctx n} {Θ} → ℕ → Exp Γ [] [] Θ natᵗ
        → List (Tm Γ [] [] Θ (obs natᵗ))
copiesN zero    e = []
copiesN (suc j) e = strmᵗ e ∷ copiesN j e

fanN : ∀ {n} {Γ : Ctx n} {Θ} → ℕ → Exp Γ [] [] Θ natᵗ → Exp Γ [] [] Θ natᵗ
fanN k e = mergeAllᵉ (ofᵉ (copiesN k e))

-- THE BREAKER: n deliveries per instant into a deepening scan
pFan : ℕ → Closed Γ₁ natᵗ
pFan k = mapᵉ (nat̂ 0) (scanᵉ deepScan seedO (fanN k (input fz)))

-- the same at the fn2 nesting, so DELIVERIES × NESTING is one family
pFan2 : ℕ → Closed Γ₁ natᵗ
pFan2 k = mapᵉ (nat̂ 0) (scanᵉ deep2 seedO (fanN k (input fz)))

-- the fn2 shape under the μ ticker: ONE delivery per instant, so this
-- is the per-APPLICATION half of the claim, isolated
pμD2M : Closed Γ₀ natᵗ
pμD2M = mapᵉ (nat̂ 0) (scanᵉ deep2 seedO ticker)

-- the tripling scan at the same fan-out, whose per-fold factor is 3
-- rather than an exponential: it climbs no tower stories at all
pTupM : ℕ → Closed Γ₁ natᵗ
pTupM k = mapᵉ (nat̂ 0) (scanᵉ wrap3 seedO (fanN k (input fz)))

------------------------------------------------------------------
-- (4) THE COUNT ON EVERY FAMILY.  All `refl` — it is syntax
------------------------------------------------------------------

_ : widthCount progDT insD₂ ∷ widthCount progW insD₂
  ∷ widthCount pF1 insG    ∷ widthCount pF2 insG²
  ∷ widthCount pμ2 ins₀    ∷ widthCount pμD ins₀
  ∷ widthCount (pL² 2) insG² ∷ widthCount (pL³ 0) insG³
  ∷ widthCount progD ins₀  ∷ []
  ≡ 3 ∷ 4 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 4 ∷ 2 ∷ 3 ∷ []
_ = refl

-- AND IT DOES NOT MOVE WITH THE FAN-OUT, which is the whole finding:
-- `pFan 1` and `pFan 5` deliver once and five times per instant and
-- carry the same count
_ : widthCount (pFan 1) insD₂ ∷ widthCount (pFan 2) insD₂
  ∷ widthCount (pFan 3) insD₂ ∷ widthCount (pFan 4) insD₂
  ∷ widthCount (pFan 5) insD₂ ∷ []
  ≡ 3 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ []
_ = refl

_ : widthCount pμD2M ins₀ ∷ widthCount (pFan2 1) insD₂
  ∷ widthCount (pFan2 2) insD₂ ∷ widthCount (pFan2 3) insD₂ ∷ []
  ≡ 4 ∷ 4 ∷ 4 ∷ 4 ∷ []
_ = refl

_ : widthCount (pTupM 1) insD₂ ∷ widthCount (pTupM 8) insD₂ ∷ []
  ≡ 2 ∷ 2 ∷ []
_ = refl

------------------------------------------------------------------
-- (5) THE GATE ON EVERY INSTANT-HEIGHT ROW.  `wNeed S W⁺ W` is that
-- probe's own minimal `foldStep` pass count, read on its own compiled
-- (W, W⁺, S) triples; the count is the `widthCount` pinned above.
-- EVERY MEASURED ROW FITS, and most with two passes to spare
--
--   family / id      S       W        W⁺      wNeed   widthCount
--   progDT  0       20       1         6         1        3
--   progDT  1       24       6      3072         1        3
--   progDT  2       45    3072    ⟨932d⟩         1        3
--   progW   0       20       1         9         1        4
--   pF1     0       10       1         9         1        2
--   pF1     1       87       9        81         1        2
--   pF1     2      843      81       729         1        2
--   pF2     0       10       1        81         1        2
--   pμ2     0       24       3         9         1        2
--   pμ2     1       87       9        27         1        2
--   pμ2     2      276      27        81         1        2
--   pμ2     3      843      81       243         1        2
--   pμD     0       24       6      3072         1        3
--   pμD     1       45    3072    ⟨932d⟩         1        3
--   pL² 2   0       18       1       144         1        4
--   pL² 2   1       18     144       144         0        4
--   pL³ 0   0        3       1         8         1        2
--   pL³ 0   1        2       8         8         0        2
--   progD   0       45    3072      3072         0        3
------------------------------------------------------------------

_ : wNeed 20 6 1 ∷ wNeed 24 3072 6 ∷ wNeed 20 9 1 ∷ wNeed 10 9 1
  ∷ wNeed 87 81 9 ∷ wNeed 843 729 81 ∷ wNeed 10 81 1 ∷ []
  ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
_ = refl

_ : wNeed 24 9 3 ∷ wNeed 87 27 9 ∷ wNeed 276 81 27 ∷ wNeed 843 243 81
  ∷ wNeed 18 144 1 ∷ wNeed 18 144 144 ∷ wNeed 3 8 1 ∷ wNeed 2 8 8
  ∷ wNeed 45 3072 3072 ∷ []
  ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []
_ = refl

-- the two rows whose W⁺ is not a numeral: `foldStep 45 3072` is a
-- 5081-digit numeral where W⁺ has 932, so one pass covers both
_ : dig (foldStep 45 3072) ≡ 5081
_ = refl

------------------------------------------------------------------
-- (5b) THE CALIBRATION OF THE HEIGHT COLUMN AGAINST INSTANT-HEIGHT'S
-- OWN ROWS.  `mNest` is believed only because it reproduces the
-- deepening families' known behaviour: one delivery, one story
-- (compiled)
--
--   family / id    S     N(id)   N(id+1)   acc(id)   acc(id+1)
--   progDT  0     20       0        1          3        24
--   progDT  1     24       1        2         24        45
--   pμD     0     24       1        2         24        45
--   pμD     1     45       2        3         45       885
--   progW   0     20       0        1          3        87
--   pF1     0     10       0        0          3        87
--   pF2     0     10       0        0          3       843
--
-- progDT and pμD are Instant-Height's `wNeed = 1` rows and they store
-- exactly one new story per instant; pF1 and pF2 are its multiplicative
-- rows and they store NONE, which is why one pass covers 1 ↦ 9 and
-- 1 ↦ 81 there.  The height column and the pass count agree on every
-- row where both are known
------------------------------------------------------------------

------------------------------------------------------------------
-- (6) THE PER-APPLICATION HALF, AND IT HOLDS EXACTLY.
--
-- `pμD2M` folds the fn2 step ONCE per instant off the μ ticker.  The
-- stored tower height climbs by exactly `nestᵗ deep2 = 2` per instant,
-- over four instants, against a `widthCount` of 4 — Mult-Width-Probe
-- §7's "two nested scanᵉ nodes cost exactly two foldSteps", now
-- measured on a RUN rather than on one `applyFn`
--
--   id    S    N(id)   N(id+1)   acc(id)   acc(id+1)     ΔN
--    0   38      2        4         38        73          2
--    1   73      4        6         73       108          2
--    2  108      6        8        108       143          2
--    3  143      8       10        143       178          2
--
-- (compiled; the width numeral at height 4 is already out of reach)
------------------------------------------------------------------

_ : nestᵗ (deep2 {Γ = Γ₀}) ∷ nestᵗ (deepScan {Γ = Γ₀}) ∷ nestᵗ (wrap3 {Γ = Γ₀}) ∷ []
  ≡ 2 ∷ 1 ∷ 0 ∷ []
_ = refl

------------------------------------------------------------------
-- (7) THE PER-INSTANT HALF, AND IT FAILS.  `pFan n`, compiled:
--
--   n     S    N(0)   N(1)   acc(0)   acc(1)    W⁺           wNeed  wc
--   1    20     0      1        3       24       6             1     3
--   2    20     0      2        3       45    3072             2     3
--   3    20     0      3        3       66  ⟨932 digits⟩       3     3
--   4    20     0      4        3       87   NOT MEASURED     ≥4     3
--   5    20     0      5        3      108   NOT MEASURED     ≥5     3
--
-- and it repeats at the next instant, so it is not a base artefact:
-- `pFan 3` at id 1 goes 3 → 6 at S = 66.
--
-- THE CALIBRATION, which is what licenses reading the height column as
-- a pass count: `wNeed` and ΔN agree wherever the numeral exists.  At
-- n = 3 the numeral exists on BOTH sides — W⁺ has 932 digits and
-- `iterFold 20 2 1` has 522, so two passes are short and three are the
-- minimum, which is ΔN = 3 exactly.
--
-- SO n = 4 DEMANDS FOUR PASSES AGAINST A BUDGET OF THREE.  The count
-- cannot see the fan-out: `fanN` holds no `scanᵉ`, `nestᵉ (pFan n)` is
-- 2 for every n, and the slot telescope is a single scripted input.
--
-- NOT MEASURED: W⁺ at n ≥ 4.  One more deepening fold puts the width
-- at 2 ^ ⟨932-digit⟩, i.e. a numeral with about 10^931 digits; the RUN
-- reaches it (acc(1) = 87 nodes, one second) but no harness forms the
-- numeral.  The height is what is reported instead, which is the
-- 457bb52 discipline: a tower is not a numeral
------------------------------------------------------------------

-- the budget at n = 3, both sides pinned: two passes are 522 digits
_ : dig (iterFold 20 2 1) ≡ 522
_ = refl

-- and the demand there is the compiled 932.  522 < 932, so the third
-- pass is forced — `wNeed` = 3 = ΔN, the count's exact ceiling
_ : (932 ≤ᵇ 522) ≡ false
_ = refl

-- the two rungs whose W⁺ IS a numeral, pinned end to end
_ : wNeed 20 6 1 ∷ wNeed 20 3072 1 ∷ []
  ≡ 1 ∷ 2 ∷ []
_ = refl

------------------------------------------------------------------
-- (8) DELIVERIES × NESTING, in one family.  `pFan2 n` is the fn2 step
-- at n deliveries, and the stored height climbs by 2n per instant
-- against a `widthCount` of 4 (compiled):
--
--   n     S    N(0)   N(1)   acc(0)   acc(1)    ΔN    widthCount
--   1    34     0      2        3       38       2        4
--   2    34     0      4        3       73       4        4
--   3    34     0      6        3      108       6        4
--
-- so the product is the law and neither factor alone is: n = 3 breaches
-- by 6 against 4, and the same n = 3 breaches by 3 against 3 one
-- nesting shallower (§7).
--
-- AND THE CONTRAST, so the finding is read as a statement about the
-- TOWER and not about width in general: the tripling scan `wrap3`
-- climbs NO stories at any fan-out — `pTupM 8` stores height 0 out of
-- eight deliveries, at an accumulator of 68883 nodes — because its
-- per-fold factor is 3 rather than an exponential.  Its width is
-- 3 ^ 8 = 6561, which TWO `foldStep 10` passes cover, and two passes go
-- on covering it to n ≈ 211
------------------------------------------------------------------

_ : wNeed 10 6561 1 ≡ 2
_ = refl

_ : (3 ^ 8 ≤ᵇ iterFold 10 2 1) ≡ true
_ = refl

------------------------------------------------------------------
-- (9) THE RULED COUNT, AND IT PASSES EVERY ROW.  The design session's
-- reading of §7/§8 is that the per-instant story count is
-- DELIVERIES × NESTING and the deliveries are already paid for, so the
-- count becomes
--
--     widthCount c = D̂ c * suc (cNest c)      D̂ c = 2 ^ (2 ^ cReg c)
--
-- with `cNest` a new Caps field carrying `nestᵉ e + slotsNest sl` from
-- the entry syntax — i.e. `suc cNest` is exactly the refuted count of §4,
-- now a FACTOR rather than the whole thing.
--
-- THE GATE IS RUN AT THE MEASURED REGISTRY, not at capsAt's.  `mReg id`
-- is the registrations the pre-cascade state actually holds, and
-- `capsAt`'s own cReg dominates it (the base is `suc (sizeᵉ + slotsSize)`
-- and frameBlowup only grows it), so a row that fits at the measured R
-- fits at the cap.  `mFolds id` is the cascade's real delivery count,
-- reported beside it so the TIGHT law `demand ≤ D * suc cNest` — the one
-- §7/§8 actually measured — can be read off the same table.
--
--   family / id     R    D     S    suc cNest  demand  D*suc  D̂ R
--   progDT 0        1    1    20        3        1       3      4
--   progDT 1        1    1    24        3        1       3      4
--   progDT 2        0    1    45        3        1       3      2
--   progW  0        1    1    20        4        1       4      4
--   pF1    0        3    4    10        2        1       8    256
--   pF1    1        3    4    87        2        1       8    256
--   pF1    2        3    4   843        2        1       8    256
--   pF2    0        5   10    10        2        1      20   2^32
--   pmu2   0        1    1    24        2        1       2      4
--   pmu2   1        1    1    87        2        1       2      4
--   pmu2   2        1    1   276        2        1       2      4
--   pmu2   3        1    1   843        2        1       2      4
--   pmuD   0        1    1    24        3        1       3      4
--   pmuD   1        1    1    45        3        1       3      4
--   pL² 2  0        5   21    18        4        1      84   2^32
--   pL² 2  1       19  153    18        4        0     612   ⟨tower⟩
--   pL³ 0  0        7   50     3        2        1     100  2^128
--   pL³ 0  1       15  114     2        2        0     228   ⟨tower⟩
--   progD  0        0    0    45        3        0       0      2
--   pFan 1 0        1    1    20        3        1       3      4
--   pFan 2 0        2    2    20        3        2       6     16
--   pFan 3 0        3    3    20        3        3       9    256
--   pFan 4 0        4    4    20        3        4      12  65536
--   pFan 5 0        5    5    20        3        5      15   2^32
--   pFan 3 1        3    3    66        3        3       9    256
--   pFan2 1 0       1    1    34        4        2       4      4
--   pFan2 2 0       2    2    34        4        4       8     16
--   pFan2 3 0       3    3    34        4        6      12    256
--   pmuD2M 0        1    1    38        4        2       4      4
--   pmuD2M 1        1    1    73        4        2       4      4
--   pmuD2M 2        1    1   108        4        2       4      4
--   pmuD2M 3        1    1   143        4        2       4      4
--   pTupM 8 0       8    8    10        2        0      16  2^256
--
-- (R, D, S: compiled, probe/Nest-Count-Main.agda.  The demand column is
-- §5's `wNeed` on the Instant-Height rows and §7/§8's ΔN on the fan-out
-- families, both already measured.)
--
-- NO ROW BREACHES, on EITHER form.  The tight `D * suc cNest` is worst
-- at ratio 1/2 — `pFan2 n` demands 2n against 4n, and `pmuD2M` demands 2
-- against 4 — and the ruled `D̂ * suc cNest` has the whole delivery tower
-- on top of that.  `progD 0` is the only row where the tight form is
-- TIGHT rather than slack, and only because it delivers zero times and
-- demands zero stories; the ruled form gives it 6.
------------------------------------------------------------------

D̂ᶜ : ℕ → ℕ
D̂ᶜ R = 2 ^ (2 ^ R)

-- the gate: does the measured demand fit the ruled count at registry R?
gate : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → ℕ → Exp Γ Δᵍ Δ Θ t → Slots Γ → Bool
gate R demand e sl = demand ≤ᵇ D̂ᶜ R * widthCount e sl

-- the Instant-Height rows, at their own R and their own wNeed
_ : gate 1 1 progDT insD₂ ∷ gate 1 1 progDT insD₂ ∷ gate 0 1 progDT insD₂
  ∷ gate 1 1 progW insD₂
  ∷ gate 3 1 pF1 insG ∷ gate 3 1 pF1 insG ∷ gate 3 1 pF1 insG
  ∷ gate 5 1 pF2 insG²
  ∷ gate 1 1 pμ2 ins₀ ∷ gate 1 1 pμ2 ins₀ ∷ gate 1 1 pμ2 ins₀ ∷ gate 1 1 pμ2 ins₀
  ∷ gate 1 1 pμD ins₀ ∷ gate 1 1 pμD ins₀
  ∷ gate 5 1 (pL² 2) insG² ∷ gate 19 0 (pL² 2) insG²
  ∷ gate 7 1 (pL³ 0) insG³ ∷ gate 15 0 (pL³ 0) insG³
  ∷ gate 0 0 progD ins₀ ∷ []
  ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true
  ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
_ = refl

-- the fan-out family, whose demand is n and whose registry is n
_ : gate 1 1 (pFan 1) insD₂ ∷ gate 2 2 (pFan 2) insD₂
  ∷ gate 3 3 (pFan 3) insD₂ ∷ gate 4 4 (pFan 4) insD₂
  ∷ gate 5 5 (pFan 5) insD₂ ∷ gate 3 3 (pFan 3) insD₂ ∷ []
  ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
_ = refl

-- deliveries × nesting, the family that broke the syntactic count
_ : gate 1 2 (pFan2 1) insD₂ ∷ gate 2 4 (pFan2 2) insD₂
  ∷ gate 3 6 (pFan2 3) insD₂
  ∷ gate 1 2 pμD2M ins₀ ∷ gate 1 2 pμD2M ins₀
  ∷ gate 1 2 pμD2M ins₀ ∷ gate 1 2 pμD2M ins₀
  ∷ gate 8 0 (pTupM 8) insD₂ ∷ []
  ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
_ = refl

-- AND THE TIGHT FORM TOO, where the ruled one has the delivery tower to
-- spare: `demand ≤ D * suc cNest` on every row whose D is nonzero.  The
-- two worst are pinned — pFan2 3 (6 against 12) and pmuD2M (2 against 4)
_ : (6 ≤ᵇ 3 * widthCount (pFan2 3) insD₂) ∷ (2 ≤ᵇ 1 * widthCount pμD2M ins₀)
  ∷ (5 ≤ᵇ 5 * widthCount (pFan 5) insD₂) ∷ []
  ≡ true ∷ true ∷ true ∷ []
_ = refl

------------------------------------------------------------------
-- WHAT THIS DOES AND DOES NOT SAY.
--
-- It does NOT touch the SIZE count: `sizeCount` reads cWid and drives
-- `iterSize`, which multiplies rather than exponentiates, and
-- Instant-Height's (e4) rows already show 0, 1 or 2 passes against
-- allowances in the millions.  The finding is confined to the WIDTH
-- count.
--
-- It does NOT say the width axis is unboundable.  It says the bound
-- cannot be `suc (nestᵉ + slotsNest)`, because the real per-instant
-- story count is `deliveries × nesting` and the delivery count is the
-- quantity `frameBlowup` already pays `D̂ c = 2 ^ (2 ^ cReg c)` for.
--
-- IT IS MEASURED AT THE TIGHT ADMISSIBLE CAPS (`mS`), and for the WIDTH
-- axis alone that denominator has an asymmetry the other probes' does
-- not, because cSize is `foldStep`'s BASE: a LARGER cSize makes each
-- pass cover MORE real folds, and `capsAt`'s own cSize is enormous.  So
-- the rows above refute the count at the tight caps, and the question
-- the design session has to answer is whether the recurrence's own
-- cSize buys the difference back.  What follows is arithmetic on
-- `capsAt` rather than a measurement — NOT machine-checked, and stated
-- so the ruling can be made on it rather than around it.
--
-- IN TOWER HEIGHTS.  Write H_S(id) and H_W(id) for the heights of
-- `cSize (capsAt e sl id)` and `cWid (capsAt e sl id)`.  `capsAt-tower`
-- already fixes the size axis at H_S(id) = (7 + sz) + 4·id — slope
-- FOUR.  Under the split ruling the width axis becomes
--
--     H_W(id+1)  =  max (H_W(id)) (H_S(id))  +  widthCount
--
-- because `iterFold S j w` is j stories over a base of height H_S and a
-- seed of height H_W.  So H_W tracks H_S and inherits ITS slope: the
-- width cap climbs FOUR stories an instant however small widthCount is,
-- and `widthCount` only sets the constant offset.  That is real
-- headroom, and it moves the breach: at `pFan`'s own caps the three
-- passes cover FOUR real folds rather than three, because base 44
-- multiplies an exponent by 1.64 where base 2 does not.
--
-- BUT THE SLOPE IS WHAT THE DEMAND HAS TO BEAT, AND IT IS A CONSTANT.
-- The real width's height climbs by `deliveries × nesting` per instant,
-- measured above, and that number is bounded by nothing in the caps —
-- `pFan n` has it at n for every n at a fixed program shape.  Whenever
-- it exceeds the cap's own slope the cap is overtaken, whatever head
-- start the base gave it: with the slope at four, `pFan 5` (ΔN = 5,
-- measured) climbs faster than `capsAt` can and no constant widthCount
-- repairs it, since raising widthCount raises the OFFSET and the slope
-- only once it passes four.
--
-- SO THE SHAPE OF THE REPAIR IS NOT A CONSTANT.  Either the width count
-- reads the same delivery bound the size count does (`D̂ c`, which
-- Width-Count-Probe prices at zero extra stories on its own — it is the
-- chargePoly FACTOR that cost the fifth story, not `D̂`), or the width
-- axis stops exponentiating per pass.  Both are the design session's
-- call, and neither is this probe's to make
------------------------------------------------------------------
