-- ══════════════════════════════════════════════════════════════════
-- THE ARRIVAL-KEYED SCAN HEAD, READ ALONG THE AXIS ITS OTHER PROBE
-- HOLDS STILL — how fast the STEP FUNCTION duplicates, rather than how
-- long the script is.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THIS AXIS AND NOT THE OTHER ONE.  `Probed.Scan-Arr-Clos-Key`
-- lengthens a cold script under a step naming its accumulator TWICE:
-- the delivery then doubles per value while the key gains two, so the
-- grant gains two bits per value against a demand of one and the
-- margin widens.  That reading is about the pairing of those two
-- rates, and neither is forced.  Here the source is an `ofᵉ` of bare
-- naturals, whose key gains ONE per value, and the step names its
-- accumulator FOUR times, so the demand gains two bits per value
-- against a grant of one.
--
-- WHAT THE ROWS THEREFORE MEASURE.  Not a crossing: the grant starts
-- ahead by the step function's own written size, which the key charges
-- once, so the rows are green throughout.  What they measure is the
-- SIGN of the margin's derivative, which is the whole question — the
-- fit holds for all programs only if the demand's per-value rate is
-- dominated by the key's, and these rows are LOAD-BEARING because they
-- show it is not.  A row fails as soon as the head start is spent.
--
-- WHAT IS NOT COVERED.  The crossing itself, and this is a boundary
-- rather than a gap: the delivered depth is the size of an actual
-- substituted term, so a row at the crossing is a term of some 2^40
-- nodes on the cheapest member of the family — raising the duplication
-- raises the head start faster than it raises the rate.  Nor is a
-- source whose key gains nothing per value: every synchronous value is
-- written down somewhere the closure measure reads.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: subscribeE-nest-arr-scan @b3dbe3
module Probed.Scan-Arr-Margin where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Val; Fn; Tm; natᵗ; obs; _×ᵗ_; scanᵉ; mergeAllᵉ; emptyᵉ; ofᵉ;
         input; varᵗ; fstᵗ; nat̂; strmᵗ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nestCapsOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

-- both slots empty: the source is written into the program, so the
-- telescope contributes a constant to every row
slots : Slots Γ₂
slots fzero        = scripted (cold [] [])
slots (fsuc fzero) = scripted (cold [] [])

-- k values delivered synchronously, each costing ONE unit of key
lits : ℕ → List (Tm Γ₂ [] [] [] natᵗ)
lits zero    = []
lits (suc k) = nat̂ k ∷ lits k

-- the step names its accumulator FOUR times -- two additive slots in
-- each of two nested `scanᵉ` layers -- so one application quadruples
-- the delivered depth where the probe next door doubles it
deepen4 : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen4 = strmᵗ (mergeAllᵉ nothing
            (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                   (fstᵗ (varᵗ (here refl)))
                   (mergeAllᵉ nothing
                     (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                            (fstᵗ (varᵗ (here refl)))
                            (input (fsuc fzero))))))

prog : ℕ → Closed Γ₂ (obs natᵗ)
prog k = scanᵉ deepen4 (strmᵗ emptyᵉ) (ofᵉ (lits k))

gas : Gas
gas = gasPad 400 g0

row : ℕ → ℕ × ℕ
row k =
  let p = prog k
      r = subscribeE gas p root 0 0 (sched-init p slots) (st-init p)
  in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))
   , arrD (nestUnit p slots) (nestDᵉ p) (closSizeᵉ (slotClos slots) p)

-- THE TWO COLUMNS, AT ZERO THROUGH EIGHT DELIVERED VALUES.  The left
-- is the delivered nesting, the right the grant `NestArrAt` allows.
figures : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)
figures = row 0 , row 1 , row 2 , row 3 , row 4

figures≡ : figures ≡ ((0 , 1310720) , (2 , 2621440) , (10 , 5242880) , (42 , 10485760) , (170 , 20971520))
figures≡ = refl

figuresHi : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)
figuresHi = row 5 , row 6 , row 7 , row 8

figuresHi≡ : figuresHi ≡ ((682 , 41943040) , (2730 , 83886080) , (10922 , 167772160) , (43690 , 335544320))
figuresHi≡ = refl

-- THE RATES, WHICH ARE THE FINDING.  The delivered depth is `4d + 2`
-- per value and the grant exactly doubles, so the margin loses a
-- factor of two per value: four hundred thousand times over at zero
-- values, seven thousand at eight.  Nothing here is upward-closed --
-- a row fails as soon as the head start the step function's own
-- written size buys is spent.
key : ℕ × ℕ × ℕ
key = closSizeᵉ (slotClos slots) (prog 0)
    , closSizeᵉ (slotClos slots) (prog 4)
    , closSizeᵉ (slotClos slots) (prog 8)

key≡ : key ≡ (19 , 23 , 27)
key≡ = refl

-- THE PREMISES, PINNED RATHER THAN ASSUMED, at the widest row.  The
-- size cap is the arrival's own closure size, the smallest the
-- closure premise takes, so there is no slack in the choice; `B` is
-- `nestDᵉ` of the arrival exactly.
cap : Caps
cap = caps (closSizeᵉ (slotClos slots) (prog 8)) 4000 4000

premises : (nestValOK? cap (obs (obs natᵗ)) (prog 8) ≡ true)
         × (nestClosOK? cap slots (prog 8) ≡ true)
         × (nestCapsOK? cap (sched-init (prog 8) slots) (st-init (prog 8)) ≡ true)
premises = refl , refl , refl

-- and the burst really is eight values wide, in ONE subscribe frame,
-- so the fold count is the axis these rows move
burst≡8 : length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)}
            (proj₁ (subscribeE gas (prog 8) root 0 0
                      (sched-init (prog 8) slots) (st-init (prog 8)))))) ≡ 8
burst≡8 = refl

fit0 : (proj₁ (row 0) ≤ᵇ proj₂ (row 0)) ≡ true
fit0 = refl

fit4 : (proj₁ (row 4) ≤ᵇ proj₂ (row 4)) ≡ true
fit4 = refl

fit8 : (proj₁ (row 8) ≤ᵇ proj₂ (row 8)) ≡ true
fit8 = refl
