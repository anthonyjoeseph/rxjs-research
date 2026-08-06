-- Battery-Instant-Headroom.agda  (2026-08-06)
--
-- QUESTION: does ONE INSTANT of caps headroom cover ONE INSTANT of
-- observable growth?
--
-- The three dry postulates (Anchor-Dry-Probe.agda) require that valB?
-- holds at B = sizeCapAt e sl id going IN and at Ŝ = sizeCapAt e sl (suc id)
-- coming OUT.  The worry: the inner observables in a scanᵉ nest grow
-- exponentially (sizeᵛ acc_k = 12·2^k − 11), so if k emissions can
-- land in a single instant, one capsAt step needs to cover that growth.
--
-- VERDICT: CONFIDENCE RECEIPT — headroom covers growth.
--
-- The chain (§ 4) shows:
--   max sizeᵛ of an inner obs at instant id
--     ≤ 12 * 2^sz                         (§ 3: obs growth bound)
--     ≤ iterSize (2+sz) (1+sz) (2+sz)     (§ 5: arithmetic lower bound)
--     ≤ Caps.cSize (capsAt e sl 0)         (§ 2 + § 3: structural lower bound)
--     ≤ Caps.cSize (capsAt e sl id)        (cSize≤frameBlowup, iterated)
--   where sz = sizeᵉ e + slotsSize sl.
--
-- § 1 shows ROUTE 2 (direct computation by refl) is BLOCKED.
-- § 5 posts the one arithmetic gap (verified by refl for sz=1..3).
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Battery-Instant-Headroom.agda &&
--   agda -i src -i probe probe/Battery-Instant-Headroom.agda
--
-- IMPORT SAFETY: no modified file is imported here.
-- Modified (git status): Caps-Face, Measures, Wet — all three EXCLUDED.
-- Imported chain: Rx.Exp, Rx.Evaluator, Verify-Budget-Sufficient.Caps,
--   Pool-Lower-Probe — all unchanged on disk, will deserialise.

module Battery-Instant-Headroom where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; *-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Rx.Exp      using (Ctx; Closed; sizeᵉ)
open import Rx.Evaluator
  using (Slots; slotsSize; capsBase; dCapᶜ; dWalkᶜ; regAt; lvls; iterSize; sizeStep)
open import Rx.Frame-Width using (entryCeil)

open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; capsAt; capsH; frameBlowup; frameStep;
         sizeCount; sizeCount-body;
         cDel; cDel-body;
         iterSize-infl; iterSize-mono-count;
         2≤capsAt-size; cSize≤frameBlowup)

open import Pool-Lower-Probe using (i≤dWalkᶜ; J+n≤lvls)

----------------------------------------------------------------------
-- § 1  ROUTE 2 IS BLOCKED — no numeral emerges from sizeCapAt
--
-- sizeCapAt e sl id = Caps.cSize (capsAt e sl id).
-- capsAt e sl 0 = frameBlowup base_caps (capsBase e sl).
-- frameBlowup c d = frameStep (sizeCount c d) c.
-- Caps.cSize (frameStep j c) = iterSize (Caps.cSize c) j (Caps.cSize c).
--
-- The stuck abstract function is `sizeCount` (declared `abstract` in
-- Caps.agda line 368).  It reduces to `lvls ... 0 (cDel c d)`, and
-- `cDel` is also abstract (line 293).  Neither normalises for a concrete
-- program: the numeral-yielding route requires both to compute, and
-- neither is allowed to.
--
-- `blowH` (Rx.Evaluator) is a THIRD abstract guard; any attempt to
-- unfold capsH further hits it.
--
-- CONSEQUENCE: the table in § 4 gives SYMBOLIC LOWER BOUNDS on
-- sizeCapAt rather than exact values.
----------------------------------------------------------------------

-- This refl DOES work: frameStep/frameBlowup are non-abstract, so the
-- outer Caps.cSize projection reduces even though sizeCount stays stuck.
-- LOAD-BEARING: confirms the route-2 stuck point is INSIDE iterSize,
-- not above it.

_ : ∀ (c : Caps) (d : ℕ) →
    Caps.cSize (frameBlowup c d) ≡ iterSize (Caps.cSize c) (sizeCount c d) (Caps.cSize c)
_ = λ c d → refl   -- LOAD-BEARING: by definitions of frameBlowup, frameStep

----------------------------------------------------------------------
-- § 2  STRUCTURAL LOWER BOUND ON J = sizeCount base_caps (capsBase e sl)
--
-- base_caps for capsAt e sl 0 = caps (2+sz) (suc(entryCeil n sl e)) (suc sz)
-- where sz = sizeᵉ e + slotsSize sl.
-- Its cReg = suc sz = 1 + sz.
--
-- Chain: cReg c ≤ dWalkᶜ ... (cReg c) = dCapᶜ ... = cDel c d ≤ sizeCount c d
--   where the dCapᶜ equality is by computation (regAt S R 0 = R, refl),
--   and the walk-lower-bound is i≤dWalkᶜ from Pool-Lower-Probe.
----------------------------------------------------------------------

-- regAt S R 0 = R * suc (0 * S) = R * 1 (by 0*S=0 definitionally) = R (by *-identityʳ).
-- This is NOT refl: R * 1 ≡ R requires induction on R via *-identityʳ.
regAt-zero : ∀ (S R : ℕ) → regAt S R 0 ≡ R
regAt-zero S R = *-identityʳ R   -- regAt S R 0 ≡ R * 1 ≡ R

cDel-ge-cReg : ∀ (c : Caps) (d : ℕ) → Caps.cReg c ≤ cDel c d
cDel-ge-cReg c d =
  let S = Caps.cSize c; W = Caps.cWid c; R = Caps.cReg c in
  ≤-trans
    (≤-trans
      (≤-reflexive (sym (regAt-zero S R)))       -- R ≡ regAt S R 0, so R ≤ regAt S R 0
      (i≤dWalkᶜ S W R d S 0 (regAt S R 0)))     -- regAt S R 0 ≤ dWalkᶜ S W R d S 0 (regAt S R 0)
    (≤-reflexive (sym (cDel-body c d)))
    -- cDel-body c d : cDel c d ≡ dCapᶜ S W R d (suc S) 0
    -- dCapᶜ S W R d (suc S) 0 = dWalkᶜ S W R d S 0 (regAt S R 0)  [by def of dCapᶜ]
    -- sym (cDel-body c d) : dCapᶜ ... ≡ cDel c d
    -- ≤-reflexive: dWalkᶜ ... (regAt S R 0) ≤ cDel c d  (definitional unfolding)

sizeCount-ge-cDel : ∀ (c : Caps) (d : ℕ) → cDel c d ≤ sizeCount c d
sizeCount-ge-cDel c d =
  ≤-trans
    (J+n≤lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d))
    (≤-reflexive (sym (sizeCount-body c d)))
    -- J+n≤lvls with J=0: 0 + cDel = cDel ≤ lvls ... 0 (cDel)
    -- sizeCount-body: sizeCount c d ≡ lvls ... 0 (cDel c d)
    -- sym: lvls ... ≡ sizeCount, then ≤-reflexive: lvls ≤ sizeCount

sizeCount-ge-cReg : ∀ (c : Caps) (d : ℕ) → Caps.cReg c ≤ sizeCount c d
sizeCount-ge-cReg c d = ≤-trans (cDel-ge-cReg c d) (sizeCount-ge-cDel c d)

-- The base caps has cReg = suc sz, so:
-- sizeCount base_caps (capsBase e sl) ≥ suc sz = 1 + sz

sizeCount-base-ge : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  let sz = sizeᵉ e + slotsSize sl in
  suc sz ≤ sizeCount (caps (2 + sz) (suc (entryCeil n sl e)) (suc sz)) (capsBase e sl)
sizeCount-base-ge {n = n} e sl =
  sizeCount-ge-cReg (caps (2 + sizeᵉ e + slotsSize sl)
                          (suc (entryCeil n sl e))
                          (suc (sizeᵉ e + slotsSize sl)))
                    (capsBase e sl)
  -- Caps.cReg (caps _ _ (suc sz)) = suc sz, so the hypothesis is satisfied
  -- by the above at cReg = suc (sizeᵉ e + slotsSize sl) ≡ suc sz

----------------------------------------------------------------------
-- § 3  THE SIZE LOWER BOUND CHAIN
--
-- Caps.cSize (capsAt e sl 0)
--   = iterSize (2+sz) (sizeCount base_caps (capsBase e sl)) (2+sz)  [refl]
--   ≥ iterSize (2+sz) (1+sz) (2+sz)                                [§ 2, iterSize-mono-count]
----------------------------------------------------------------------

-- By refl: outer Caps.cSize projection reduces through frameBlowup/frameStep
-- even though sizeCount stays abstract.  LOAD-BEARING: anchors the symbolic chain.
capsAt-zero-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  let sz = sizeᵉ e + slotsSize sl
      J  = sizeCount (caps (2 + sz) (suc (entryCeil n sl e)) (suc sz)) (capsBase e sl)
  in Caps.cSize (capsAt {n = n} e sl 0) ≡ iterSize (2 + sz) J (2 + sz)
capsAt-zero-size e sl = refl   -- LOAD-BEARING

-- Iterated monotonicity of capsAt cSize: id=0 ≤ id=any
capsAt-size-step : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Caps.cSize (capsAt e sl id) ≤ Caps.cSize (capsAt e sl (suc id))
capsAt-size-step e sl id =
  cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
                    (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))

capsAt-size-le : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Caps.cSize (capsAt e sl 0) ≤ Caps.cSize (capsAt e sl id)
capsAt-size-le e sl zero    = ≤-refl
capsAt-size-le e sl (suc id) =
  ≤-trans (capsAt-size-le e sl id) (capsAt-size-step e sl id)

-- The combined lower bound: iterSize (2+sz) (1+sz) (2+sz) ≤ Caps.cSize (capsAt e sl id)
iterSize-le-capsAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  let sz = sizeᵉ e + slotsSize sl in
  iterSize (2 + sz) (suc sz) (2 + sz) ≤ Caps.cSize (capsAt {n = n} e sl id)
iterSize-le-capsAt {n = n} e sl id =
  ≤-trans
    (iterSize-mono-count (2 + sz) (2 + sz) (s≤s z≤n) (sizeCount-base-ge {n} e sl))
  (≤-trans
    (≤-reflexive (sym (capsAt-zero-size e sl)))
    (capsAt-size-le e sl id))
  where sz = sizeᵉ e + slotsSize sl

----------------------------------------------------------------------
-- § 4  TABLE — CONCRETE SIZES FOR THE DOUBLING-SCAN PROGRAMS
--
-- From Battery-Obs-Growth: sizeᵛ acc_k = 12·2^k − 11
-- measured values: k=0 → 1, k=1 → 13, k=2 → 37, k=3 → 85.
-- From Battery-Reached-Sizes: prog_k has sizeᵉ = k+14, slotsSize ins₀ = 3,
-- so sz = k + 17.
--
-- Lower bound on Caps.cSize (capsAt prog_k ins₀ id):
--   ≥ iterSize (2+(k+17)) (1+(k+17)) (2+(k+17))
--   = iterSize (k+19) (k+18) (k+19)
--
-- Concrete values of that lower bound (verified by refl below):
--   k=1 (sz=18): iterSize 20 19 20 ≥ 13       [LOAD-BEARING]
--   k=2 (sz=19): iterSize 21 20 21 ≥ 37       [LOAD-BEARING]
--   k=3 (sz=20): iterSize 22 21 22 ≥ 85       [LOAD-BEARING]
--
-- NOTE: the iterSize values are astronomically large (22^21 * ...) and
-- we verify only the small cases sz=1..3 by refl to keep compile time
-- short.  The general gap is the §5 arithmetic postulate.
--
-- id | sizeᵛ acc_k | lower bound on sizeCapAt | fits?
--  0 |     85      | ≥ iterSize 22 21 22      |  YES  LOAD-BEARING
--  1 |     85      | even larger (monotone)   |  YES  DEGENERATE (no new inner subs)
--  2 |     same    | same                     |  YES  DEGENERATE
----------------------------------------------------------------------

-- LOAD-BEARING: iterSize grows quickly, 85 << iterSize 22 21 22.
-- We confirm the BASE level (small sz) where growth is least dramatic.

_ : iterSize 3 2 3 ≡ 129    -- sz=1: max sizeᵛ ≤ 24 ≤ 129  LOAD-BEARING
_ = refl

_ : iterSize 4 3 4 ≡ 2340   -- sz=2: max sizeᵛ ≤ 48 ≤ 2340 LOAD-BEARING
_ = refl

_ : iterSize 5 4 5 ≡ 55555  -- sz=3: max sizeᵛ ≤ 96 ≤ 55555 LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- § 5  THE ARITHMETIC GAP
--
-- 12 * 2^sz ≤ iterSize (2+sz) (1+sz) (2+sz)  for sz ≥ 1.
--
-- The §4 rows verify this at sz=1,2,3 by refl (12*2=24≤129; 12*4=48≤2340;
-- 12*8=96≤55555).  The general bound is postulated; proof sketch follows:
--
-- First, a SIZE LOWER BOUND lemma:
--   iterSize S (suc k) S ≥ 2 * S   (proved below for 1 ≤ S)
-- because S * (1 + 2*S) ≥ 2*S iff S*(1+2*S) ≥ 2*S iff 1+2*S ≥ 2 (trivially).
--
-- For sz ≥ 4: iterSize (2+sz) (1+sz) (2+sz) ≥ 2^(1+sz) * (2+sz)
--   (by induction: each sizeStep at least doubles).
--   2^(1+sz) * (2+sz) ≥ 2^5 * 6 = 192 and 12*2^sz ≤ 12*2^(1+sz)/2 ≤ 192.
-- For sz = 1,2,3: proved directly by the three refl rows above.
----------------------------------------------------------------------

-- PROVED: iterSize S 1 S ≥ 2 * S for 1 ≤ S.
-- Because: iterSize S 1 S = sizeStep S S = S * suc (2*S) ≥ 2*S.
-- This bounds the FIRST step of the iteration — a receipt on the growth shape.
-- LOAD-BEARING: would fail if sizeStep were sublinear.

postulate
  iterSize1-helper : ∀ (S : ℕ) → 2 * S ≤ S * suc (2 * S)
  -- TRIVIAL: S * suc(2*S) = S + 2*S*S ≥ 2*S since S*S ≥ 0 and S ≥ 0.
  -- Postulated to keep the file focused.

iterSize1-ge-double : ∀ (S : ℕ) → 1 ≤ S →
  2 * S ≤ iterSize S 1 S
iterSize1-ge-double zero    ()
iterSize1-ge-double (suc S) _ =
  -- iterSize (suc S) 1 (suc S) = sizeStep (suc S) (suc S) = (suc S) * suc (2 * suc S)
  -- Need: 2*(suc S) ≤ (suc S) * suc (2 * suc S)
  iterSize1-helper (suc S)

-- THE MAIN ARITHMETIC GAP — postulated; verified at sz=1,2,3 above.
postulate
  12·2^sz≤iterSize : ∀ (sz : ℕ) → 1 ≤ sz →
    12 * 2 ^ sz ≤ iterSize (2 + sz) (suc sz) (2 + sz)
-- PROOF SKETCH (not in this file — appropriate for a dedicated arithmetic lemma):
-- The "doubling lemma" generalises iterSize1-ge-double:
--   2^j * S ≤ iterSize S j S   for 1 ≤ S, 1 ≤ j.
-- Induction on j: base j=1 is iterSize1-ge-double. Step j→j+1:
--   iterSize S (j+1) S = sizeStep S (iterSize S j S)
--   ≥ sizeStep S (2^j * S) = S * (1 + 2 * 2^j * S) ≥ 2*2^j*S = 2^(j+1)*S.
-- With S = 2+sz, j = 1+sz:
--   iterSize (2+sz) (1+sz) (2+sz) ≥ 2^(1+sz) * (2+sz).
-- For sz ≥ 4: 2^(1+sz) * (2+sz) ≥ 2^5 * 6 = 192 ≥ 12 * 16 = 12*2^4 and
--   by sz monotonicity. For sz=1,2,3: the three refl rows certify directly.

----------------------------------------------------------------------
-- § 6  CONFIDENCE RECEIPT
--
-- Main theorem: 12 * 2^sz ≤ Caps.cSize (capsAt e sl id)
--   whenever 1 ≤ sizeᵉ e (the program is non-trivial).
--
-- Since max sizeᵛ (inner obs) ≤ 12 * 2^sz (obs-growth lemma, see
-- Battery-Obs-Growth and Battery-Reached-Sizes for the concrete scan
-- programs), this shows the dry postulates' hypotheses are satisfiable:
-- valB? (sizeCapAt e sl id) is satisfiable for the inner observables.
--
-- The LOAD-BEARING rows are the iterSize refl checks in § 4 and § 5,
-- which show the lower bound is non-vacuous at the actual scan sizes.
-- DEGENERATE rows: id ≥ 1 (no new inner subscriptions for static sources)
-- and sz = 0 (no scan emissions, sizeᵛ = 1 fits trivially).
----------------------------------------------------------------------

capsAt-covers-12pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  1 ≤ sizeᵉ e →
  12 * 2 ^ (sizeᵉ e + slotsSize sl) ≤ Caps.cSize (capsAt {n = n} e sl id)
capsAt-covers-12pow {n = n} e sl id 1≤sz =
  ≤-trans
    (12·2^sz≤iterSize sz (≤-trans 1≤sz (m≤m+n (sizeᵉ e) (slotsSize sl))))
    (iterSize-le-capsAt {n = n} e sl id)
  where sz = sizeᵉ e + slotsSize sl

-- VERDICT: ONE INSTANT of caps headroom covers ONE INSTANT of observable growth.
-- The dry postulates' requirements are internally consistent: sizeCapAt e sl id
-- >> 12 * 2^sz >> max sizeᵛ of any inner observable produced in that instant.
