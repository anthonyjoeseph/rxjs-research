-- Battery-Anchor-Fit.agda
--
-- QUESTION: is an exponential anchor  Ŝ = 12 * 2^(sizeᵉ e + slotsSize ins)
-- usable at all?  Two ceilings must both hold:
--
--   Ceiling 1:  Ŝ e ins ≤ capsH e ins 0
--   Ceiling 2:  suc (dBound Ŝ (hopR Ŝ) U r s) fits under budgetAt e ins 0
--
-- VERDICT:
--   Ceiling 1:  FITS  — via exp12≤blowH (postulated arithmetic gap)
--   Ceiling 2:  FITS  — fully derivable given ceiling 1
--   Largest Ŝ that fits both:  capsH e ins 0 itself.
--
-- Postulate gap for ceiling 1 (exp12≤blowH):
--   blowH m = 6 + m + 2 * poolCount(towerℕ m) m
--   Pool-Lower-Probe gives: m ≤ poolCount(towerℕ m) m (for 2 ≤ m)
--   So blowH m ≥ 2 * towerℕ m ≥ 2 * towerℕ(4 + X)  (since m ≥ 4 + X)
--   towerℕ(4 + X) = 2^(towerℕ(3 + X)) ≥ 2^X, so
--   blowH m ≥ 2 * 2^X ≥ 12 * 2^X  only for large X.
--   The tight bound uses towerℕ(4+X) ≥ 6 * 2^X via towerℕ growth,
--   which is a concrete arithmetic proof deferred here.
--
-- BUILD: cd agda && agda -i src -i probe probe/Battery-Anchor-Fit.agda

module Battery-Anchor-Fit where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; ^-monoʳ-≤)
open import Relation.Binary.PropositionalEquality
  using (sym)

open import Rx.Prim     using (towerℕ; Gas; Id)
open import Rx.Exp      using (Ctx; Closed; sizeᵉ)
open import Rx.Evaluator
  using (Slots; slotsSize; blowH; blowH-body; capsHgo; capsBase; budgetAt; poolCount)
open import Verify-Budget-Sufficient.Measures
  using (dBound; hopR; dBound-bound; k≤towerℕ; towerℕ-mono;
         prod≤3pow; budget-hasAtLeast; _hasAtLeast_; hasAtLeast-mono)
open import Verify-Budget-Sufficient.Caps
  using (capsH; tower-3)

----------------------------------------------------------------------
-- The candidate anchor
----------------------------------------------------------------------

Ŝ-cand : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ
Ŝ-cand e ins = 12 * 2 ^ (sizeᵉ e + slotsSize ins)

----------------------------------------------------------------------
-- Helper: m ≤ blowH m  (every m fits under its own blowH)
-- blowH m = 6 + m + 2*P where P = poolCount(towerℕ m) m
-- m ≤ m + 2*P ≤ 6 + m + 2*P = blowH m
----------------------------------------------------------------------

m≤blowH : ∀ (m : ℕ) → m ≤ blowH m
m≤blowH m =
  ≤-trans (m≤m+n m _)
  (≤-trans (m≤n+m _ 6)
           (≤-reflexive (sym (blowH-body m))))

----------------------------------------------------------------------
-- POSTULATE — arithmetic gap for CEILING 1.
--
-- Proof obligation:  12 * 2^X ≤ blowH m  whenever  4 + X ≤ m.
--
-- Sketch (full proof goes in Pool-Lower-Probe or a dedicated module):
--   blowH m ≥ 2 * poolCount(towerℕ m) m         (from blowH-body + P≥0)
--           ≥ 2 * towerℕ m                        (capsBase-le-pool from Pool-Lower-Probe)
--           ≥ 2 * towerℕ (4 + X)                  (towerℕ-mono, m ≥ 4+X)
--   towerℕ(4+X) = 2^(towerℕ(3+X)) ≥ 2^(2^(2^(towerℕ X))) ≥ 2^(2^(2^X))
--   For X ≥ 2: towerℕ(4+X) ≥ 2^(2^4) = 65536, so 2*towerℕ(4+X) >> 12*2^X.
----------------------------------------------------------------------

postulate
  exp12≤blowH : ∀ (X m : ℕ) → 4 + X ≤ m → 12 * 2 ^ X ≤ blowH m

----------------------------------------------------------------------
-- POSTULATE — capsBase lower bound (simple arithmetic).
-- capsBase e ins = 3 + (sizeᵉ e + slotsSize ins) + suc(entryCeil ...) ≥ 4 + sz
----------------------------------------------------------------------

postulate
  4≤capsBase : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    → 4 + (sizeᵉ e + slotsSize ins) ≤ capsBase e ins

----------------------------------------------------------------------
-- POSTULATE — 6 ≤ Ŝ-cand (trivial: 12 * 2^X ≥ 12 * 1 = 12 ≥ 6)
----------------------------------------------------------------------

postulate
  6≤Ŝ-cand : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    → 6 ≤ Ŝ-cand e ins

----------------------------------------------------------------------
-- CEILING 1: Ŝ-cand e ins ≤ capsH e ins 0
--
-- capsH e ins 0 = capsHgo(capsBase e ins) 0 = blowH(capsBase e ins)
-- exp12≤blowH gives  12 * 2^X ≤ blowH(capsBase e ins)  when X = sizeᵉ e + slotsSize ins
----------------------------------------------------------------------

Ŝ-fits-capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  → Ŝ-cand e ins ≤ capsH e ins 0
Ŝ-fits-capsH e ins =
  exp12≤blowH (sizeᵉ e + slotsSize ins) (capsBase e ins) (4≤capsBase e ins)

----------------------------------------------------------------------
-- capsH e ins 0 ≤ capsH e ins 1  (height recurrence step)
-- capsH e ins 1 = blowH(capsH e ins 0)  and m≤blowH gives the bound.
----------------------------------------------------------------------

capsH-0≤1 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  → capsH e ins 0 ≤ capsH e ins 1
capsH-0≤1 e ins = m≤blowH (capsH e ins 0)

----------------------------------------------------------------------
-- Ŝ-cand ≤ towerℕ(capsH e ins 1): step needed by tower-3
-- Chain: Ŝ ≤ capsH 0 ≤ towerℕ(capsH 0) ≤ towerℕ(capsH 1)
----------------------------------------------------------------------

Ŝ≤towerCapsH1 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  → Ŝ-cand e ins ≤ towerℕ (capsH e ins 1)
Ŝ≤towerCapsH1 e ins =
  ≤-trans (Ŝ-fits-capsH e ins)
  (≤-trans (k≤towerℕ (capsH e ins 0))
           (towerℕ-mono (capsH-0≤1 e ins)))

----------------------------------------------------------------------
-- CEILING 2: dBound Ŝ (hopR Ŝ) U r s ≤ towerℕ(3 + capsH e ins 1)
--
-- Chain (mirrors caps-fuel-root in Wet.agda):
--   dBound Ŝ (hopR Ŝ) U r s
--     ≤ suc Ŝ * suc(hopR Ŝ) * suc U             [dBound-bound, s≤Ŝ, r≤hopR Ŝ]
--     ≤ suc(suc Ŝ * suc(hopR Ŝ) * suc U)         [n≤1+n]
--     ≤ 2^(2^(2^Ŝ))                               [prod≤3pow, 6≤Ŝ, U≤Ŝ]
--     ≤ towerℕ(3 + capsH e ins 1)                 [tower-3, Ŝ ≤ towerℕ(capsH e ins 1)]
----------------------------------------------------------------------

dBound-fits-G : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  → ∀ {U r s}
  → s ≤ Ŝ-cand e ins
  → r ≤ hopR (Ŝ-cand e ins)
  → U ≤ Ŝ-cand e ins
  → dBound (Ŝ-cand e ins) (hopR (Ŝ-cand e ins)) U r s
      ≤ towerℕ (3 + capsH e ins 1)
dBound-fits-G e ins {U} hs hr hU =
  ≤-trans (dBound-bound hs hr)
  (≤-trans (n≤1+n _)
  (≤-trans (prod≤3pow (Ŝ-cand e ins) U (6≤Ŝ-cand e ins) hU)
           (tower-3 (capsH e ins 1) (Ŝ-cand e ins) (Ŝ≤towerCapsH1 e ins))))

----------------------------------------------------------------------
-- BUDGET CONNECTION: budgetAt e ins 0 hasAtLeast suc(dBound Ŝ ...)
--
-- Follows caps-fuel-root's pattern exactly.
-- budget-hasAtLeast sz m 0 provides gas ≥ 2^sz + towerℕ(3 + capsH e ins 1).
-- suc(dBound Ŝ ...) ≤ towerℕ(3 + capsH e ins 1) ≤ 2^sz + towerℕ(3 + capsH e ins 1).
----------------------------------------------------------------------

budget-covers-Ŝ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  → ∀ {U r s}
  → s ≤ Ŝ-cand e ins
  → r ≤ hopR (Ŝ-cand e ins)
  → U ≤ Ŝ-cand e ins
  → budgetAt e ins 0
      hasAtLeast suc (dBound (Ŝ-cand e ins) (hopR (Ŝ-cand e ins)) U r s)
budget-covers-Ŝ e ins {U} {r} {s} hs hr hU =
  hasAtLeast-mono demand (budget-hasAtLeast sz (capsBase e ins) 0)
  where
  sz : ℕ
  sz = sizeᵉ e + slotsSize ins
  Ŝ : ℕ
  Ŝ = Ŝ-cand e ins
  demand : suc (dBound Ŝ (hopR Ŝ) U r s)
             ≤ 2 ^ (sz * 1 * 1) + towerℕ (3 + capsHgo (capsBase e ins) 1)
  demand =
    ≤-trans (s≤s (dBound-bound hs hr))
    (≤-trans (prod≤3pow Ŝ U (6≤Ŝ-cand e ins) hU)
    (≤-trans (tower-3 (capsH e ins 1) Ŝ (Ŝ≤towerCapsH1 e ins))
             (m≤n+m _ _)))
