------------------------------------------------------------------
-- THE LITERAL BURST'S ENTRY RECEIPT, and the one side condition the
-- existing gate does not supply.
--
-- `subscribeE-caps`'s `ofᵉ` clause is NOT an `op-step`/`op-step-eval`
-- shape: a literal burst subscribes nothing and pushes no source, so
-- there is no `suc (j₁ + j₂)` tail to match — its witness is a FLAT
-- `j₀ + 3`, with `j₀ = suc (sizeᵗˢ ts)` off `evalTms-caps`.
--
-- That makes `op-step-entry` the right gate (a fresh entry, receipt `r`,
-- then a subscribe at the level the receipt left), taken at `r := j₀ + 3`
-- and `j₁ := 0`.  Its "fits" premise is the part with no lemma behind it:
-- the receipt has to sit inside the quadratic room `op-step-entry` mints.
--
-- It fits with a lot to spare, and `2≤sizeAt` is what pays for it — the
-- same fact the payload edge's three rungs needed.  Room is quadratic and
-- the receipt is linear, so this is never tight; it is only unprovable if
-- the size cap can be small, which `2 ≤ S` forbids.
------------------------------------------------------------------
module Of-Fits-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-monoʳ-≤; +-monoˡ-≤;
         +-identityʳ; n≤1+n; m≤m*n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Rx.Evaluator using (sizeAt; sLvlD; opIterD)
open import Verify-Budget-Sufficient.Caps using (sLvlD-infl)
open import Verify-Budget-Sufficient.Caps-Chain
  using (2≤sizeAt; op-step-entry; op-step-share)

------------------------------------------------------------------
-- The receipt fits the room.  Stated at `j₀` rather than at `sizeᵗˢ ts`
-- so the clause can hand it whatever `evalTms-caps` actually returned,
-- and with the `+ 3` on the outside because `_+_` recurses on its FIRST
-- argument and a literal `j₀ + 3` would otherwise sit stuck.
------------------------------------------------------------------

of-fits : ∀ (S j j₀ : ℕ) → 2 ≤ S → j₀ ≤ sizeAt S j →
  j + (j₀ + 3) ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j))
of-fits S j j₀ 2≤S hj₀ =
  ≤-trans (+-monoʳ-≤ j room) (≤-reflexive (+-suc j (B′ * B′)))
  where
  B  = sizeAt S j
  B′ = suc B

  2≤B : 2 ≤ B
  2≤B = 2≤sizeAt S j 2≤S

  -- B + 3 ≤ B + suc B, because the cap is at least 2
  widen : B + 3 ≤ B + B′
  widen = +-monoʳ-≤ B (s≤s 2≤B)

  -- and `B + suc B` is `suc B + B`, which sits inside the square
  square : B + B′ ≤ B′ * B′
  square = ≤-trans (≤-reflexive (+-suc B B))
                   (+-monoʳ-≤ B′ (m≤m*n B B′))

  room : j₀ + 3 ≤ suc (B′ * B′)
  room = ≤-trans (≤-trans (≤-trans (+-monoˡ-≤ 3 hj₀) widen) square)
                 (n≤1+n (B′ * B′))

------------------------------------------------------------------
-- § 2.  THE TWO CLAUSES, at the gate.  Both are ENTRIES with a receipt
-- and NOTHING after it, so both take `op-step-entry` at `j₁ := 0` and
-- spend `sLvlD-infl` for its second premise.  The `+ 0` the conclusion
-- then carries is absorbed here rather than at the clause.
------------------------------------------------------------------

-- the literal burst: receipt `j₀ + 3`, no subscribe
of-step : ∀ (S W d k m j j₀ : ℕ) → 2 ≤ S → j₀ ≤ sizeAt S j →
  j + (j₀ + 3) ≤ opIterD S W d k (suc m) j
of-step S W d k m j j₀ 2≤S hj₀ =
  ≤-trans (≤-reflexive (cong (j +_) (sym (+-identityʳ (j₀ + 3)))))
          (op-step-entry S W d k m j (j₀ + 3) 0 2≤S
            (of-fits S j j₀ 2≤S hj₀)
            (≤-trans (≤-reflexive (+-identityʳ (j + (j₀ + 3))))
                     (sLvlD-infl S W d k (j + (j₀ + 3)))))

-- the parked body: receipt 1, the registration, and `share-fits` pays
-- its room for free inside `op-step-share`
defer-step : ∀ (S W d k m j : ℕ) → 2 ≤ S →
  j + 1 ≤ opIterD S W d k (suc m) j
defer-step S W d k m j 2≤S =
  op-step-share S W d k m j 0 2≤S
    (≤-trans (≤-reflexive (+-identityʳ (suc j)))
             (sLvlD-infl S W d k (suc j)))
