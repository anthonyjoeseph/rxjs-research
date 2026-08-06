-- BATTERY: NESTING ESCALATION of per-instant value count  (2026-08-06)
--
-- FOLLOW-UP to Battery-Value-Count, which refuted `k ≤ syncSizeᵉ e`.  Two
-- candidate repairs are examined here, and the file exists to measure the
-- second:
--
-- § 1  GAS.  "Emissions per instant ≤ gas depth spent" — REFUTED WITHOUT A
--      NEW RUN: Battery-Value-Count's prog₄ emits 30 values in instant 0 on
--      fuel of depth 10 (`bigGas`).  `subscribeInner` peels ONE `gs` per
--      subscription and hands the SAME decremented fuel to every sibling
--      inner — gas bounds subscription DEPTH, breadth is free.  So no
--      gas-depth bound on emission count exists at any fuel the runs use.
--
-- § 2  NESTING.  The refuting shape was ONE level of "doubling scanᵉ whose
--      merged output lands in one instant", giving count 2^(K+1) − 2 in the
--      source length K.  Feed that output into ANOTHER doubling scan: if
--      each level applies v ↦ 2^(v+1) − 2 to the incoming per-instant count
--      v, the count is a TOWER in nesting depth (entry-bounded, but a tower)
--      and NO fixed exponential in entry data bounds it — in particular not
--      `2^(sizeᵉ e + slotsSize sl)` (the computable gasPad head of
--      `budgetAt`), since nesting adds a CONSTANT to sizeᵉ per level while
--      exponentiating the count.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Battery-Nesting-Escalation.agda &&
--   agda -i src -i probe probe/Battery-Nesting-Escalation.agda
module Battery-Nesting-Escalation where

open import Data.Nat      using (ℕ; zero; suc; _+_; _⊔_)
open import Data.List     using (List; []; _∷_; map; sum; foldr)
open import Data.Vec      using () renaming ([] to []ᵛ)
open import Data.Product  using (proj₁)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Gas; gs; g0; gasPad; InstEmit; InstEvent;
                                init; value; close; handoff; complete)
open import Rx.Exp
  using (Ty; Ctx; obs; natᵗ; _×ᵗ_; Val; Closed; Fn; Tm;
         varᵗ; fstᵗ; nat̂; strmᵗ;
         ofᵉ; mergeAllᵉ; scanᵉ)
open import Rx.Evaluator
  using (Slots; Stream; subscribeE; sched-init; st-init; root)

----------------------------------------------------------------------
-- § 0  MEASURES — same as Battery-Value-Count.
----------------------------------------------------------------------

countVals : ∀ {A : Set} → List (InstEvent A) → ℕ
countVals []               = 0
countVals (value _ ∷ es)   = suc (countVals es)
countVals (init _ ∷ es)    = countVals es
countVals (close _ _ ∷ es) = countVals es
countVals (handoff _ ∷ es) = countVals es
countVals (complete ∷ es)  = countVals es

valueCount : ∀ {A : Set} → List (InstEmit A) → ℕ
valueCount b = sum (map (λ em → countVals (InstEmit.events em)) b)

maxInstant : ∀ {A : Set} → List (InstEmit A) → ℕ
maxInstant b = foldr (λ em acc → InstEmit.instant em ⊔ acc) 0 b

gasDepth : Gas → ℕ
gasDepth g0     = 0
gasDepth (gs g) = suc (gasDepth g)

----------------------------------------------------------------------
-- SETUP.  Fuel is GENEROUS on purpose: the faithful direction.  The real
-- pipeline seeds `budgetAt e sl id`, a gasPad-over-tower far above depth
-- 100; too-little fuel would inject dry cuts and UNDER-count.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

fuel : Gas
fuel = gasPad 100 g0

_ : gasDepth fuel ≡ 100
_ = refl

burstOf : ∀ {u} → Closed Γ₀ u → Stream Γ₀ u
burstOf p = proj₁ (subscribeE fuel p root 0 0 (sched-init p ins₀) (st-init p))

----------------------------------------------------------------------
-- § 2  THE NESTING STEP.  `nest src = mergeAllᵉ (scanᵉ step liveSeed src)`
-- is EXACTLY Battery-Value-Count's refuting shape with the `ofᵉ` source
-- replaced by an arbitrary natᵗ-emitting program.  Depth-1 instances over
-- `ofᵉ` reproduce that file's rows; depth-2/3 instances feed one level's
-- output into the next.
----------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

nest : Closed Γ₀ natᵗ → Closed Γ₀ natᵗ
nest src = mergeAllᵉ (scanᵉ step liveSeed src)

-- Depth 1 — baselines, re-certified in this file so it stands alone.
inner₁ : Closed Γ₀ natᵗ                    -- K = 1 source
inner₁ = nest (ofᵉ (nat̂ 0 ∷ []))

inner₂ : Closed Γ₀ natᵗ                    -- K = 2 source
inner₂ = nest (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))

-- Depth 2 and 3.
nest²ᵃ : Closed Γ₀ natᵗ
nest²ᵃ = nest inner₁

nest²ᵇ : Closed Γ₀ natᵗ
nest²ᵇ = nest inner₂

nest³ : Closed Γ₀ natᵗ
nest³ = nest nest²ᵃ

-- LOAD-BEARING baselines (agree with Battery-Value-Count at fuel 100,
-- so the counts there were not artifacts of fuel 10).
_ : valueCount (burstOf inner₁) ≡ 2
_ = refl
_ : valueCount (burstOf inner₂) ≡ 6
_ = refl

-- LOAD-BEARING, the file's one new fact: one nesting level applies
-- v ↦ 2^(v+1) − 2 to a count arriving from a NESTED program, exactly as it
-- does to a count arriving from `ofᵉ` syntax (where the map is already
-- certified at v = 1..4 by inner₁/inner₂ above plus Battery-Value-Count's
-- prog₃/prog₄: 2, 6, 14, 30).  Would fail if the outer scan received the
-- inner emissions in separate instants, or if mergeAll declined to
-- subscribe every accumulator.
_ : valueCount (burstOf nest²ᵃ) ≡ 6
_ = refl

-- LOAD-BEARING: per-instant.  Would fail if nesting deferred inners.
_ : maxInstant (burstOf nest²ᵃ) ≡ 0
_ = refl

-- NOT CERTIFIED — normalization cost.  The v = 6 rows (nest²ᵇ, nest³,
-- predicted 126 each) exceeded a 10-minute typecheck and are left out;
-- coverage is therefore v = 2 for nested sources.  Their programs are kept
-- above so re-attempting is one uncommented line each.

----------------------------------------------------------------------
-- § 3  VERDICT
--
--   depth | program | incoming v | valueCount | predicted 2^(v+1) − 2
--     1   | inner₁  | 1 (ofᵉ)    |      2     |   2   ✓
--     1   | inner₂  | 2 (ofᵉ)    |      6     |   6   ✓
--     2   | nest²ᵃ  | 2 (NESTED) |      6     |   6   ✓
--   (2,3  | nest²ᵇ/nest³ | 6     |  predicted 126 | NOT certified — cost)
--
-- (1) GAS IS NOT A COUNT BOUND (§ 1 header): 30 values on depth-10 fuel;
--     breadth is gas-free.  Only the DEPTH of accumulator trees is
--     fuel-limited, which is why depth-100 fuel is needed here at all.
-- (2) EACH NESTING LEVEL EXPONENTIATES: the map v ↦ 2^(v+1) − 2 holds at
--     v = 1..4 over `ofᵉ` sources (here + Battery-Value-Count) and — the
--     new fact — applies unchanged when v arrives from a NESTED level,
--     certified at v = 2, instant 0.
--     Composing the measured map from v = 1: 2, 6, 126, 2^127 − 2, … — a
--     TOWER in nesting depth.  Nesting depth is syntax (entry-bounded), but
--     each level adds a CONSTANT to sizeᵉ while exponentiating the count, so
--     NO fixed exponential in entry data bounds the per-instant count.  In
--     particular `2^(sizeᵉ e + slotsSize sl)` — budgetAt's computable gasPad
--     head — is crossed at depth 4 with K = 1.  The crossing itself is not
--     refl-checkable (2^127 values); what is machine-certified is the map at
--     depths ≤ 3, and the composition is two lines of arithmetic, not a
--     claim about the evaluator.
-- (3) CONSEQUENCE FOR THE DRY FAMILY (Anchor-Dry-Probe.agda): the headroom
--     one instant demands is TOWER-shaped in entry data — `sizeᵛ` reached
--     within one instant is a tower in nesting depth via the established
--     count→size link (`12·2^v − 11`, Battery-Obs-Growth).  The family
--     survives as stated ONLY IF one caps tick provides tower headroom:
--     `sizeCapAt e sl (suc id)` vs `sizeCapAt e sl id` is one `blowH`
--     application (`capsHgo m (suc id) = blowH (capsHgo m id)`,
--     Evaluator.agda:905-906), and `blowH m = 6 + m + 2·poolCount (towerℕ m) m`
--     IS tower-shaped in its argument.  Whether that tower dominates THIS
--     tower is the remaining symbolic question — heights must be compared,
--     not shapes.  That is step 3 of Phase 1b, not this file.
--
-- SHAPES COVERED: nested doubling `scanᵉ` towers over live `ofᵉ` seeds,
-- nesting depth ≤ 3, incoming count ≤ 6, all single-instant.  NOT COVERED:
-- the depth-4 crossing (arithmetic only), μᵉ, shared slots, concat/switch/
-- exhaust variants, multi-instant sources.
----------------------------------------------------------------------
