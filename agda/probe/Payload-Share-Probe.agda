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

open import Verify-Budget-Sufficient.Caps-Nest
  using (one-level-supply-strict; refresh-supplies-nest-strict)
open import Verify-Budget-Sufficient.Caps-Chain
  using (op-step-entry; share-fits; op-step-share; op-step-mu)

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

-- BOTH ROWS ARE NOW IN .Caps-Nest, next to the weak twins they sharpen:
-- `one-level-supply-strict` and `refresh-supplies-nest-strict`, imported
-- here so the probe states the finding rather than a second copy of it

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

-- BOTH ARE NOW IN .Caps-Chain, and `op-step-mu` is the receipt-quadratic
-- instance of `op-step-entry` rather than a second copy of its proof

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
