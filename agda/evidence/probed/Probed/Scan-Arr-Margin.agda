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
-- lengthens a cold script under a step naming its accumulator TWICE.
-- That reading is about the pairing of two rates and neither is
-- forced.  Here the source is an `ofᵉ` of bare naturals, whose key
-- gains ONE per value, and the step names its accumulator FOUR times,
-- so the demand gains two bits per value against a written size of
-- one — the worst pairing the family offers.
--
-- WHAT THE ROWS THEREFORE MEASURE: the SIGN of the margin's
-- derivative, which is the whole question.  The grant is read over
-- `suc W` copies of the arrival's closure size, so its exponent is a
-- PRODUCT of the width and the size and grows quadratically in the
-- value count, while the demand gains a fixed two bits each.  Nineteen
-- bits of grant against zero of demand, a hundred and fifteen against
-- eight, two hundred and forty-three against sixteen.  LOAD-BEARING:
-- were the key read at the arrival alone the exponent would be flat in
-- the width and every one of these rows would fail past the head start.
--
-- THE WIDTH IS A LOWER BOUND AND NOT THE MEASURE.  `descW` is sealed,
-- so it cannot be evaluated here; the burst it joins over is exactly
-- the length pinned below, and the grant is monotone in the width, so
-- a fit at this width is a fit at the real one.
--
-- WHAT IS NOT COVERED, and it is a boundary rather than a gap: any
-- source whose key gains nothing per value — every synchronous value
-- is written down somewhere the closure measure reads — and the
-- interaction with a SHARED slot, whose key is read through the
-- telescope rather than off the term.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: subscribeE-nest-arr-scan @10d2d8
module Probed.Scan-Arr-Margin where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _*_; _≤ᵇ_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁)
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
open import Refuted.Demand-Programs using (Γ₂)

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

-- the width the grant is read at, and it is a LOWER bound rather than
-- the measure itself: `descW` is sealed and cannot be evaluated here,
-- while the burst it joins over is exactly this length, so a fit at
-- this width is a fit at the real one.
wid : ℕ → ℕ
wid k =
  let p = prog k
      r = subscribeE gas p root 0 0 (sched-init p slots) (st-init p)
  in length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))

delivered : ℕ → ℕ
delivered k =
  let p = prog k
      r = subscribeE gas p root 0 0 (sched-init p slots) (st-init p)
  in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))

-- the key the grant is actually read at: `suc W` copies of the
-- arrival's closure size
keyW : ℕ → ℕ
keyW k = suc (wid k) * closSizeᵉ (slotClos slots) (prog k)

grant : ℕ → ℕ
grant k = arrD (nestUnit (prog k) slots) (nestDᵉ (prog k)) (keyW k)

-- THE DELIVERED DEPTHS, AT ZERO THROUGH EIGHT VALUES.  Four
-- accumulator copies over an `ofᵉ` of bare naturals: `4d + 2` per
-- value, so the demand's exponent grows by two bits per value.
lo : ℕ × ℕ × ℕ × ℕ × ℕ
lo = delivered 0 , delivered 1 , delivered 2 , delivered 3 , delivered 4

hi : ℕ × ℕ × ℕ × ℕ
hi = delivered 5 , delivered 6 , delivered 7 , delivered 8

delivered≡ : lo ≡ (0 , 2 , 10 , 42 , 170)
delivered≡ = refl

deliveredHi≡ : hi ≡ (682 , 2730 , 10922 , 43690)
deliveredHi≡ = refl

-- AND THE KEY, WHICH IS THE FINDING.  Reading the grant over the
-- width makes the exponent the PRODUCT of the width and the arrival's
-- closure size, so it grows quadratically in the value count where
-- the demand grows by a fixed two bits each -- 19, 115, 243 against
-- demands of 0, 8 and 16 bits.  The margin's derivative has the sign
-- the statement needs, which is what the unscaled key did not.
keys : ℕ × ℕ × ℕ
keys = keyW 0 , keyW 4 , keyW 8

keys≡ : keys ≡ (19 , 115 , 243)
keys≡ = refl

widths : ℕ × ℕ × ℕ
widths = wid 0 , wid 4 , wid 8

widths≡ : widths ≡ (0 , 4 , 8)
widths≡ = refl

-- the unscaled sizes the product is built from, so the two factors
-- are separable in the reading above
sizes : ℕ × ℕ × ℕ
sizes = closSizeᵉ (slotClos slots) (prog 0)
      , closSizeᵉ (slotClos slots) (prog 4)
      , closSizeᵉ (slotClos slots) (prog 8)

sizes≡ : sizes ≡ (19 , 23 , 27)
sizes≡ = refl

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

fit0 : (delivered 0 ≤ᵇ grant 0) ≡ true
fit0 = refl

fit4 : (delivered 4 ≤ᵇ grant 4) ≡ true
fit4 = refl

fit8 : (delivered 8 ≤ᵇ grant 8) ≡ true
fit8 = refl
