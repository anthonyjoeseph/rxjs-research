------------------------------------------------------------------
-- THE TWO PIECES THE CONJUNCT PASS REPORTED AS MISSING, and neither is.
--
-- Deliverable 1 of the conjunct pass left two call sites behind
-- `level-TEMP` and reported the second as a genuine gap: "a payload
-- subscribe is a NESTING LEVEL and spends one, and the measure that
-- supplies that split does not exist."  It does — it is already proven
-- inside `one-level-supply` and thrown away on its last line.  § 1.
--
-- The other open item was the three SHARE heads, which cannot report in
-- a fresh-entry shape (their caller delegates its whole body to them, so
-- they inherit its `opIterD` conclusion) but also cannot convert one
-- (`entry-to-index` wants `suc (sizeAt S J) ≤ ops`, and the `input`
-- clause's `ops` is only ≥ 2).  The conversion they need is `op-step-mu`
-- with its receipt abstracted — the μ edge and the share edge are the
-- same edge, differing only in what they charge.  § 2.
------------------------------------------------------------------
module Payload-Share-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-assoc; +-monoʳ-≤; +-mono-≤;
         +-comm; m≤m+n; n≤1+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; sLvlD; opIterD; fIterD; opIterD-suc)
open import Verify-Budget-Sufficient.Caps
  using (sLvlD-mono; opIterD-infl; fIterD-infl)
open import Verify-Budget-Sufficient.Caps-Nest
  using (core; sizeAt-suc; nest; resid; resid≤slots)
open import Verify-Budget-Sufficient.Caps-Chain using (quad-arith)

open import Rx.Exp using (Ctx; Exp; syncSizeᵉ; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Prim using (Source)
open import Verify-Budget-Sufficient.Measures using (syncSize≤sizeᵉ)
open import Data.List using (List)

------------------------------------------------------------------
-- § 1.  THE PAYLOAD EDGE'S MEASURE, strict.
--
-- `one-level-supply` chains `x + y ≤ sizeAt S j + S ≤ S * suc (2 *
-- sizeAt S j) ≡ sizeAt S (suc j)` and only THEN weakens by `n≤1+n`.  So
-- the strict bound is the chain minus its last step, and the refreshed
-- budget `frameBud c j = suc (sizeAt S (suc j))` is a SUCCESSOR whose
-- predecessor is exactly what this bounds.  That is the split the
-- payload edge needs: the walk runs at `suc (sizeAt S (suc j))` and
-- hands the payload's own subscribe `sizeAt S (suc j)`.
------------------------------------------------------------------

one-level-supply-strict : ∀ (S j x y : ℕ) →
  1 ≤ S → x ≤ sizeAt S j → y ≤ S → x + y ≤ sizeAt S (suc j)
one-level-supply-strict S j x y 1≤S hx hy =
  ≤-trans (≤-trans (+-mono-≤ hx hy) (core S (sizeAt S j) 1≤S))
          (≤-reflexive (sym (sizeAt-suc S j)))

-- and in the shape the payload clause states it: this is
-- `refresh-supplies-nest` with the final `n≤1+n` dropped
refresh-supplies-nest-strict : ∀ {n} {Γ : Ctx n} (S j : ℕ) {Δᵍ Δ Θ t}
  (o : Exp Γ Δᵍ Δ Θ t) (sl : Slots Γ) (cs : List Source) →
  1 ≤ S → sizeᵉ o ≤ sizeAt S j → slotsSize sl ≤ S →
  nest o sl cs ≤ sizeAt S (suc j)
refresh-supplies-nest-strict S j o sl cs 1≤S hsz hsl =
  one-level-supply-strict S j (syncSizeᵉ o) (resid sl cs) 1≤S
    (≤-trans (syncSize≤sizeᵉ o) hsz)
    (≤-trans (resid≤slots sl cs) hsl)

------------------------------------------------------------------
-- § 2.  THE ENTRY EDGE, with its receipt abstracted.
--
-- `op-step-mu` is not really about μ: its proof spends the premise, then
-- `sLvlD-mono` under a bound called `quad`, then two `-infl` steps, then
-- `opIterD-suc`.  Only `quad` mentions the unfolding, and only to show
-- the receipt FITS the room `opIterD … (suc m) j` opens.  Abstract that
-- into a hypothesis and the same proof serves any edge that enters a
-- fresh subscribe — the μ unfolding (receipt `m₀ + suc (m₀ * m₀)`) and a
-- SHARE (receipt 1, the registration for the joining subscriber).
------------------------------------------------------------------

op-step-entry : ∀ (S W d k m j r j₁ : ℕ) → 2 ≤ S →
  j + r ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j)) →
  (j + r) + j₁ ≤ sLvlD S W d k (j + r) →
  j + (r + j₁) ≤ opIterD S W d k (suc m) j
op-step-entry S W d k m j r j₁ 2≤S fits sub =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j r j₁))) sub)
                   (≤-trans (sLvlD-mono d d k k 2≤S ≤-refl ≤-refl fits ≤-refl ≤-refl)
                            (≤-trans (opIterD-infl S W d k m (sLvlD S W d k J₀))
                                     (fIterD-infl S W d k (suc (widAt S W X)) X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  B  = sizeAt S j
  J₀ = suc (j + suc B * suc B)
  X  = opIterD S W d k m (sLvlD S W d k J₀)

-- THE SHARE EDGE is the receipt-1 instance, and its `fits` is free: one
-- registration sits inside the quadratic room for any cap.  Stated at
-- `suc j` rather than `j + 1` — that is the shape a clause presents, and
-- `_+_` recursing on its FIRST argument leaves `j + 1` stuck, so the
-- conversion belongs here once rather than at every call site.
share-fits : ∀ (S j : ℕ) → j + 1 ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j))
share-fits S j =
  ≤-trans (≤-reflexive (+-comm j 1))
          (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))

op-step-share : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ sLvlD S W d k (suc j) →
  j + suc j₁ ≤ opIterD S W d k (suc m) j
op-step-share S W d k m j j₁ 2≤S sub =
  op-step-entry S W d k m j 1 j₁ 2≤S (share-fits S j)
    (subst (λ x → x + j₁ ≤ sLvlD S W d k x) (sym (+-comm j 1)) sub)

------------------------------------------------------------------
-- § 3.  SO NEITHER OPEN ITEM IS A DESIGN GAP.
--
--   · the payload edge splits the REFRESHED budget, and § 1 bounds the
--     payload's nest by that budget's predecessor
--   · the three share heads keep their caller's `opIterD` conclusion and
--     close by § 2, which also subsumes `op-step-mu`
--
-- and `op-step-mu` should become the receipt-quadratic instance of
-- `op-step-entry` rather than a second copy of the same proof.
------------------------------------------------------------------
