------------------------------------------------------------------
-- THE COUNT MAY NOT READ cWid.  Refuted 2026-08-01, symbolically, on
-- the way into the D̂ / chargePoly assembly — before any of it was
-- built, which is what the probe-before-grind rule is for.
--
-- THE RULING UNDER TEST.  frameBlowup c = frameStep (D̂ c * chargePoly c) c
-- with D̂ c = 2 ^ (2 ^ cReg c) and
--
--     chargePoly c = cSize c * (1 + suc (cSize c ^ 2))
--                  + suc (cWid c * suc (cSize c))
--
-- — one subscribe's walk half plus ONE delivery's frame half.  The
-- frame half reads cWid, and that is the fatal clause.
--
-- WHY.  frameStep's WIDTH component is `iterFold`, and one fold
-- EXPONENTIATES a width (foldStep S w = S ^ suc w).  So j folds put the
-- width under a TOWER OF HEIGHT j — `iterFold-tower` below, proven, not
-- estimated.  cSize's component is `iterSize`, which only MULTIPLIES
-- per fold, so it stays a single exponential in the count; that
-- asymmetry is exactly why capsAt-tower bounds cSize and cReg and says
-- nothing about cWid.
--
-- Now let the count read cWid.  Then the count at instant id+1 is at
-- least the width at instant id, which is at least towerℕ (count at
-- instant id): the count ITERATES THE TOWER FUNCTION, one application
-- per instant.  `two-instants` below is that statement, proven for any
-- count P with cWid c ≤ P c — no other property of P is used, so this
-- kills every chargePoly with a cWid summand, not just the one above.
--
-- WHAT IT COSTS.  capsAt-tower's height stops being linear in the
-- instant, and caps-fuel-root — the ONLY consumer, at id = 1 — needs
-- `capsH e sl 1 ≤ 11 + 2·sz` against budgetAt's own tower of height
-- (7+sz)·2.  With the cWid summand, capsH e sl 1 is at least
-- 1 + 2 ^ (2 ^ (1 + sz)), which is 17 at the SMALLEST program there
-- is (sz = 1) against the 13 the root fuel allows.  Refl-checked
-- below.  So the ruling does not shift the margin, it removes the
-- linear-height statement altogether.
--
-- WHAT IS FINE, AND IT IS WORTH SAYING SEPARATELY: the DELIVERY bound
-- on its own is FREE.  `D̂-tower` shows 2 ^ (2 ^ cReg) lands in
-- towerℕ (2 + m) — the very level blowup-tower's `J≤P` already puts
-- the old `2 ^ cReg * 2 ^ cReg * cSize` at.  Swapping the delivery
-- bound to a 2-tower costs ZERO stories.  It is the chargePoly FACTOR
-- that pushes the count to towerℕ (3 + m) and hence the slope to five,
-- and `slope-fits` says a slope of five needs sz ≥ 2 — false on the
-- smallest programs.
--
-- AND THE FIFTH STORY LOOKS AVOIDABLE: `sq-fits` shows a SQUARE of the
-- delivery bound still fits in towerℕ (2 + m), provided blowup-tower's
-- hypothesis is tightened from `cReg c ≤ towerℕ m` to
-- `suc (cReg c) ≤ towerℕ m`.  So a charge factor bounded by D̂ itself
-- is affordable inside the existing four stories; a charge factor
-- bounded only by a polynomial in cSize is a separate question, since
-- nothing relates cSize to cReg.
--
-- Standalone (arithmetic on the recurrence alone, no evaluator), so
-- src/Main.agda never reaches it — and it must not rot, because it is
-- the reason the frame half of the charge is not in the count.
------------------------------------------------------------------
module Width-Count-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; ^-monoʳ-≤; ^-monoˡ-≤; n≤1+n;
         *-monoʳ-≤; *-identityʳ; +-identityʳ; +-monoʳ-≤; ^-distribˡ-+-*)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import Rx.Exp       using (Ctx; Closed; natᵗ; emptyᵉ; sizeᵉ)
open import Rx.Evaluator using (Slots; slotsSize)
open import Verify-Budget-Sufficient
  using (Caps; caps; frameStep; foldStep; iterFold; iterFold-suc;
         iterSize; iterSize-2^; iterSize-infl; towerℕ)

------------------------------------------------------------------
-- (1) ONE INSTANT PUTS THE WIDTH UNDER A TOWER OF HEIGHT j.
--
-- The whole refutation is this lemma.  foldStep S w = S ^ suc w is at
-- least 2 ^ w, so j of them from a seed of 1 is towerℕ j.
------------------------------------------------------------------

iterFold-tower : ∀ (S j w : ℕ) → 2 ≤ S → 1 ≤ w → towerℕ j ≤ iterFold S j w
iterFold-tower S zero    w hS hw = hw
iterFold-tower S (suc j) w hS hw =
  ≤-trans (^-monoʳ-≤ 2 (iterFold-tower S j w hS hw))
  (≤-trans (^-monoʳ-≤ 2 (n≤1+n (iterFold S j w)))
  (≤-trans (^-monoˡ-≤ (suc (iterFold S j w)) hS)
           (≤-reflexive (sym (iterFold-suc S j w)))))

-- read off the recurrence: the width at the end of an instant that
-- spent j folds is at least towerℕ j
frameStep-wid-tower : ∀ (c : Caps) (j : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cWid c →
  towerℕ j ≤ Caps.cWid (frameStep j c)
frameStep-wid-tower c j hS hW =
  iterFold-tower (Caps.cSize c) j (Caps.cWid c) hS hW

-- the SIZE component, for contrast: one exponential in the count, not
-- a tower.  (This direction is the lower bound; capsAt-tower's upper
-- bound is the matching one, and both are single exponentials.)
frameStep-size-2^ : ∀ (c : Caps) (j : ℕ) → 1 ≤ Caps.cSize c →
  2 ^ j ≤ Caps.cSize (frameStep j c)
frameStep-size-2^ c j hS =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ j))))
                   (*-monoʳ-≤ (2 ^ j) hS))
          (iterSize-2^ (Caps.cSize c) j (Caps.cSize c) hS)

-- and one instant never shrinks the size, so the second instant's
-- hypotheses are supplied by the first
frameStep-size-infl : ∀ (c : Caps) (j : ℕ) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cSize (frameStep j c)
frameStep-size-infl c j hS = iterSize-infl (Caps.cSize c) hS j (Caps.cSize c)

------------------------------------------------------------------
-- (2) SO A COUNT THAT READS cWid ITERATES THE TOWER FUNCTION.
--
-- Stated for an ARBITRARY count P, using only `cWid c ≤ P c`.  Two
-- instants of a recurrence driven by such a P leave the size above
-- towerℕ (suc (P c)) — the height has gained a whole tower rather
-- than a constant number of stories.
------------------------------------------------------------------

blow : (Caps → ℕ) → Caps → Caps
blow P c = frameStep (P c) c

two-instants : ∀ (P : Caps → ℕ) → (∀ c → Caps.cWid c ≤ P c) →
  ∀ (c : Caps) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cWid c →
  towerℕ (suc (P c)) ≤ Caps.cSize (blow P (blow P c))
two-instants P wid≤ c hS hW =
  ≤-trans (^-monoʳ-≤ 2 (≤-trans (frameStep-wid-tower c (P c) hS hW)
                                (wid≤ (blow P c))))
          (frameStep-size-2^ (blow P c) (P (blow P c)) 1≤S₁)
  where
  1≤S : 1 ≤ Caps.cSize c
  1≤S = ≤-trans (s≤s z≤n) hS
  1≤S₁ : 1 ≤ Caps.cSize (blow P c)
  1≤S₁ = ≤-trans 1≤S (frameStep-size-infl c (P c) 1≤S)

------------------------------------------------------------------
-- (3) THE ROOT MARGIN, AS A FUNCTION OF THE SLOPE.
--
-- capsAt-tower's height is capsH e sl id = (3 + σ + sz) + σ * id for a
-- per-instant slope σ (the tree has σ = 4, hence the literal 7).
-- caps-fuel-root needs `3 + capsH e sl 1 ≤ (7 + sz) * 2`, and that
-- inequality is exactly `2 * σ ≤ 8 + sz`.
------------------------------------------------------------------

slope-fits : ∀ (σ sz : ℕ) → 2 * σ ≤ 8 + sz →
  3 + ((3 + σ + sz) + σ * 1) ≤ (7 + sz) * 2
slope-fits σ sz h =
  ≤-trans (≤-reflexive (solve 2 (λ s z → con 3 :+ ((con 3 :+ s :+ z) :+ s :* con 1)
                                           := (con 6 :+ z) :+ con 2 :* s)
                              refl σ sz))
  (≤-trans (+-monoʳ-≤ (6 + sz) h)
           (≤-reflexive (solve 1 (λ z → (con 6 :+ z) :+ (con 8 :+ z)
                                          := (con 7 :+ z) :* con 2)
                               refl sz)))

-- σ = 4, the tree today: fits at every sz, with sz stories to spare
_ : (3 + ((3 + 4 + 0) + 4 * 1) ≤ᵇ (7 + 0) * 2) ≡ true
_ = refl

-- σ = 5 — one extra story — already fails at the SMALLEST program
-- there is.  sz = 1 is not hypothetical: `emptyᵉ` over an empty slot
-- telescope measures exactly 1, computed here rather than argued
Γ₀ : Ctx 0
Γ₀ = []ᵛ

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

sl₀ : Slots Γ₀
sl₀ ()

_ : sizeᵉ e₀ + slotsSize sl₀ ≡ 1
_ = refl

_ : (3 + ((3 + 5 + 1) + 5 * 1) ≤ᵇ (7 + 1) * 2) ≡ false
_ = refl

-- and only comes back at sz ≥ 2
_ : (3 + ((3 + 5 + 2) + 5 * 1) ≤ᵇ (7 + 2) * 2) ≡ true
_ = refl

-- WITH THE cWid SUMMAND there is no σ at all: by (2) the height at
-- instant 1 is at least 1 + P(base), and P(base) ≥ D̂(base) =
-- 2 ^ (2 ^ cReg), with the base cReg = suc sz.  At sz = 1 that is
-- 1 + 2 ^ (2 ^ 2) = 17 against the 11 + 2 * sz = 13 the root fuel
-- allows
_ : (1 + 2 ^ (2 ^ 2) ≤ᵇ 11 + 2 * 1) ≡ false
_ = refl

------------------------------------------------------------------
-- (4) WHAT THE DELIVERY BOUND COSTS ON ITS OWN: NOTHING.
--
-- blowup-tower's count step `J≤P` puts the OLD count
-- `2 ^ cReg * 2 ^ cReg * cSize` at towerℕ (2 + m).  The 2-tower lands
-- at the same level, in one line — so replacing the (measured-false,
-- Delivery-Law-Prediction §5) squared-subset bound by D̂ is free.
------------------------------------------------------------------

D̂ : Caps → ℕ
D̂ c = 2 ^ (2 ^ Caps.cReg c)

D̂-tower : ∀ (m R : ℕ) → R ≤ towerℕ m → 2 ^ (2 ^ R) ≤ towerℕ (2 + m)
D̂-tower m R h = ^-monoʳ-≤ 2 (^-monoʳ-≤ 2 h)

-- AND IT COVERS EVERY MEASURED FAMILY, by numeral comparison rather
-- than by re-running an evaluator — the Fold-Count arithmetic economy.
-- Entry cReg on the mint ladders is 2L + 1; the worst D at each L is
-- Mint-Loop-Probe's / Mint-Loop-Frames' / Delivery-Law-Prediction's
_ : (5      ≤ᵇ 2 ^ (2 ^ 3))  ≡ true      -- L = 1, D saturates at 5
_ = refl
_ : (27     ≤ᵇ 2 ^ (2 ^ 5))  ≡ true      -- L = 2, saturates at 27
_ = refl
_ : (269    ≤ᵇ 2 ^ (2 ^ 7))  ≡ true      -- L = 3, saturates at 269
_ = refl
_ : (26362  ≤ᵇ 2 ^ (2 ^ 9))  ≡ true      -- L = 4, k = 5, still climbing
_ = refl
_ : (41510  ≤ᵇ 2 ^ (2 ^ 11)) ≡ true      -- L = 5, k = 2, deepest measured
_ = refl

-- and the row that BREAKS the bound in the tree today.  D(5,5) is the
-- increment law's value, exact on both measurable rungs
-- (Delivery-Law-Prediction §5): it passes 4 ^ 11 and does not come
-- close to the 2-tower
_ : (4514934 ≤ᵇ 2 ^ 11 * 2 ^ 11)  ≡ false
_ = refl
_ : (4514934 ≤ᵇ 2 ^ (2 ^ 11))     ≡ true
_ = refl

-- AND A SQUARE OF IT STILL FITS, at one bit of extra hypothesis: the
-- level's registration bound has to be STRICT (`suc cReg ≤ towerℕ m`
-- rather than `cReg ≤ towerℕ m`).  This is the shape of the repair
-- that would keep the slope at four while the count carries a charge
-- factor — provided the factor is itself under D̂, which nothing in
-- the tree currently supplies for a polynomial in cSize
2^suc : ∀ (R : ℕ) → 2 ^ R + 2 ^ R ≡ 2 ^ suc R
2^suc R = cong (2 ^ R +_) (sym (+-identityʳ (2 ^ R)))

sq-fits : ∀ (R T : ℕ) → suc R ≤ T → 2 ^ (2 ^ R) * 2 ^ (2 ^ R) ≤ 2 ^ (2 ^ T)
sq-fits R T h =
  ≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (2 ^ R) (2 ^ R))))
          (^-monoʳ-≤ 2 (≤-trans (≤-reflexive (2^suc R)) (^-monoʳ-≤ 2 h)))
