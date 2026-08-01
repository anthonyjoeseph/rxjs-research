------------------------------------------------------------------
-- THE SLOT-FUEL AXIS: the entry width ceiling does NOT cost two tower
-- stories per syntax node.  It costs two per node PER FUEL LEVEL, and
-- the fuel is the SLOT COUNT — so the honest base height is a PRODUCT,
-- not a multiple, of the program's size.
--
-- WHAT THIS IS AGAINST.  The full-width-restructure ruling (2026-08-01)
-- prices capsAt's base cWid — the static widths, paid once at entry —
-- at tower height `3 + 2 * sz`, off Mult-Width-Probe §3's rate of TWO
-- stories per syntax node (iterFold-tower≤).  `base-2sz-fits` then makes
-- caps-fuel-root an EQUALITY: `3 + ((3 + 2*sz + 4) + 4*1) = (7 + sz)*2`,
-- zero margin, and budgetAt does not move.
--
-- THAT RATE IS COUNTED ON THE PROGRAM'S OWN SYNTAX AND MISSES THE SLOT
-- TELESCOPE.  `outWᵉ` / `innWᵉ` / `dWᵉ` reach a shared slot by SPENDING
-- FUEL — `outWᵉ (suc j) sl (input i) | shared d = outWᵉ j sl d` — and the
-- fuel every consumer instantiates is `n`, the slot count.  So a slot def
-- is re-entered once per fuel level, and a def that exponentiates
-- exponentiates AGAIN at the next level.  Nothing forbids the cycle: a
-- shared def is a `Closed Γ t` and may reference any `input`, including
-- one whose def references it back.
--
-- MEASURED HERE, on a two-slot cycle plus two DUMMY scripted slots (whose
-- only job is to raise `n`, at one node of `slotsSize` apiece):
--
--   outWᵉ 1 insC (input 0) = 256          -- one level, computed
--   outWᵉ 3 insC (input 0) ≥ 2 ^ (2 ^ 256)
--   outWᵉ 4 insC d0        ≥ 2 ^ (2 ^ (2 ^ (2 ^ 256)))
--
-- — FOUR stories off a 50-node telescope, and `slotsPW n sl` reads
-- exactly this number, so it is capsAt's base cWid TODAY, not a
-- consequence of any new ceiling.
--
-- THE RATE, and why it refutes the linear price.  `levelStep` /
-- `wrapStep` are the two structural steps: one `wrap` (a scanᵉ whose
-- step function mentions the accumulator twice, unwrapped by a
-- mergeAllᵉ — Frame-Work-Probe's deepScan shape) buys ONE story and costs
-- FOURTEEN syntax nodes; one dummy slot buys ONE MORE FUEL LEVEL and
-- costs ONE node.  So a def of k wraps in a 2-cycle with n−2 dummies has
--
--     sz      = 1 + 2 * (10 + 14 * k) + (n − 2)  =  19 + 28k + n
--     stories ≥ k * (n − 1)
--
-- and the slope in sz is k — UNBOUNDED.  At k = 8, n = 100 the demand is
-- already 792 stories against the 689 that `3 + 2 * sz` allows at
-- sz = 343.  The base height is QUADRATIC in the program, not linear.
--
-- WHAT IT DOES NOT SAY.  It does not refute the multiplicative engine
-- (Mult-Width-Probe §2's four-story slope is about frameStep and is
-- untouched), and it does not refute the ceiling as a DESIGN — it prices
-- it.  Two ways out, and they are a design ruling rather than a grind:
-- either budgetAt's `(7 + sz)` constant rises to something quadratic
-- (impl-only, but it moves the evaluator's fuel), or the width measures'
-- slot descent stops spending generic fuel `n` and starts DROPPING
-- VISITED SLOTS the way the evaluator's own connect does (`unconn`), in
-- which case each def is entered once and the linear rate is real.
--
-- The (k, n) row above is ARITHMETIC ON TWO PROVEN STEPS, not a
-- constructed program: `wrapStep` and `levelStep` are general, the
-- 4-slot instance is `refl`-checked, and the 100-slot instance is not
-- built here.  Standalone, so src/Main.agda never reaches it.  Fast.
------------------------------------------------------------------
module Slot-Fuel-Probe where


open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤ᵇ⇒≤; ≤-trans; ≤-refl; ≤-reflexive; *-identityˡ; *-identityʳ;
         *-monoˡ-≤; *-monoʳ-≤; *-mono-≤; ^-monoʳ-≤; m≤m⊔n; m≤n⊔m; m≤m*n; m≤n+m; m≤m+n)
open import Data.List using (List; []; _∷_)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim using (hot)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_;
                           input; ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂;
                           fstᵗ; varᵗ; sizeᵉ)
open import Rx.Evaluator using (Slots; scripted; shared; slotsSize)
open import Rx.Frame-Width using (outWᵉ; innWᵉ; innWᵗ)

Γ₄ : Ctx 4
Γ₄ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

accV : ∀ {Θ} → Tm Γ₄ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seedO : ∀ {Θ} → Tm Γ₄ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

W2 : Fn Γ₄ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
W2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

base0 : Closed Γ₄ natᵗ
base0 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

mix : Closed Γ₄ natᵗ → Closed Γ₄ natᵗ
mix e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ strmᵗ base0 ∷ []))

wrap : Closed Γ₄ natᵗ → Closed Γ₄ natᵗ
wrap e = mergeAllᵉ (scanᵉ W2 seedO e)

d0 d1 : Closed Γ₄ natᵗ
d0 = wrap (mix (input (fs fz)))
d1 = wrap (mix (input fz))

insC : Slots Γ₄
insC fz               = shared d0
insC (fs fz)          = shared d1
insC (fs (fs fz))     = scripted (hot [])
insC (fs (fs (fs fz))) = scripted (hot [])

-- the two defs are small
_ : sizeᵉ d0 ≡ 24
_ = refl

_ : slotsSize insC ≡ 50
_ = refl

-- ONE FUEL LEVEL, MEASURED
in0 in1 : Closed Γ₄ natᵗ
in0 = input fz
in1 = input (fs fz)

_ : outWᵉ 1 insC in0 ≡ 256
_ = refl

-- ONE FUEL LEVEL EXPONENTIATES, structurally: no numeral is formed
levelStep : ∀ (q : ℕ) (e : Closed Γ₄ natᵗ) →
  2 ^ (outWᵉ (suc q) insC e) ≤ outWᵉ (suc q) insC (wrap (mix e))
levelStep q e = ≤-trans A (≤-trans B C)
  where
  X = outWᵉ (suc q) insC e
  M = outWᵉ (suc q) insC (mix e)
  I = innWᵉ (suc q) insC (scanᵉ W2 seedO (mix e))
  x≤M : X ≤ M
  x≤M = ≤-trans (m≤m⊔n X 2) (m≤m+n (X ⊔ 2) (1 * (X ⊔ 2)))
  2≤M : 2 ≤ M
  2≤M = ≤-trans (m≤n⊔m X 2) (m≤m+n (X ⊔ 2) (1 * (X ⊔ 2)))
  A : 2 ^ X ≤ 2 ^ M
  A = ^-monoʳ-≤ 2 x≤M
  B : 2 ^ M ≤ I
  B = ≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ M))))
              (*-monoʳ-≤ (2 ^ M) (s≤s z≤n))
  C : I ≤ outWᵉ (suc q) insC (wrap (mix e))
  C = ≤-trans (≤-reflexive (sym (*-identityˡ I)))
              (*-monoˡ-≤ I (≤-trans (≤ᵇ⇒≤ 1 2 _) 2≤M))

-- ONE WRAP, WITHOUT THE MIX: the same story, so a def may stack them
1≤2^ : ∀ (x : ℕ) → 1 ≤ 2 ^ x
1≤2^ zero    = ≤-refl
1≤2^ (suc x) = ≤-trans (1≤2^ x) (m≤m+n (2 ^ x) (2 ^ x + 0))

wrapStep : ∀ (q : ℕ) (e : Closed Γ₄ natᵗ) → 1 ≤ outWᵉ (suc q) insC e →
  2 ^ (outWᵉ (suc q) insC e) ≤ outWᵉ (suc q) insC (wrap e)
wrapStep q e h =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ X))))
                   (*-monoʳ-≤ (2 ^ X) (s≤s z≤n)))
          (≤-trans (≤-reflexive (sym (*-identityˡ (2 ^ X * R))))
                   (*-monoˡ-≤ (2 ^ X * R) h))
  where
  X = outWᵉ (suc q) insC e
  R = innWᵗ (suc q) insC W2 + innWᵗ (suc q) insC (seedO {[]})
      + innWᵉ (suc q) insC e + 1

wrapPos : ∀ (q : ℕ) (e : Closed Γ₄ natᵗ) → 1 ≤ outWᵉ (suc q) insC e →
  1 ≤ outWᵉ (suc q) insC (wrap e)
wrapPos q e h = ≤-trans (1≤2^ (outWᵉ (suc q) insC e)) (wrapStep q e h)

-- and the fuel axis: ONE STORY PER SLOT, at a def of one wrap
stepA : ∀ (q : ℕ) → 2 ^ (outWᵉ (suc q) insC in1) ≤ outWᵉ (suc (suc q)) insC in0
stepA q = levelStep q in1

stepB : ∀ (q : ℕ) → 2 ^ (outWᵉ (suc q) insC in0) ≤ outWᵉ (suc (suc q)) insC in1
stepB q = levelStep q in0

towerFuel : ∀ (q : ℕ) →
  2 ^ (2 ^ (outWᵉ (suc q) insC in0)) ≤ outWᵉ (suc (suc (suc q))) insC in0
towerFuel q = ≤-trans (^-monoʳ-≤ 2 (stepB q)) (stepA (suc q))

_ : sizeᵉ (mix in1) ≡ 10
_ = refl

_ : sizeᵉ (wrap (mix in1)) ≡ 24
_ = refl

_ : sizeᵉ (wrap (wrap (mix in1))) ≡ 38
_ = refl

-- THE HEIGHT ARITHMETIC.  A def of k wraps costs 10 + 14k nodes and buys
-- k stories per fuel level; a dummy scripted slot costs ONE node and buys
-- one more fuel level.  At k wraps and n slots (two shared, n-2 dummy)
--     sz     = 1 + 2 * (10 + 14 * k) + (n - 2)   = 19 + 28k + n
--     stories >= k * (n - 1)
-- so the slope in sz is k, unbounded.  At k = 8, n = 100 it is already
-- past the 3 + 2*sz the ruling priced
_ : (8 * 99 ≤ᵇ 3 + 2 * (19 + 28 * 8 + 100)) ≡ false
_ = refl

_ : 19 + 28 * 8 + 100 ≡ 343
_ = refl

_ : 8 * 99 ≡ 792
_ = refl

_ : 3 + 2 * 343 ≡ 689
_ = refl

-- AND THE QUANTITY capsAt's BASE ALREADY READS.  `slotsPW n sl` is
-- `pWᵉ n sl d` on every shared def, so the base cWid IS this number
_ : outWᵉ 1 insC in1 ≡ 256
_ = refl

t3 : 2 ^ (2 ^ 256) ≤ outWᵉ 3 insC in0
t3 = towerFuel 0

t4 : 2 ^ (2 ^ (2 ^ 256)) ≤ outWᵉ 4 insC in1
t4 = ≤-trans (^-monoʳ-≤ 2 t3) (stepB 2)

t5 : 2 ^ (2 ^ (2 ^ (2 ^ 256))) ≤ outWᵉ 4 insC d0
t5 = ≤-trans (^-monoʳ-≤ 2 t4) (levelStep 3 in1)
