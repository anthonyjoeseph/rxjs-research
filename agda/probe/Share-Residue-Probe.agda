------------------------------------------------------------------
-- THE SHARE-RESIDUE PROBE: can the frame refresh SUPPLY the nesting
-- measure, once the measure carries the unconnected slots?
--
-- Mu-Nest-Probe fixed the measure: a subscribe is bounded by
--
--     nest b U = syncSizeᵉ b + Σ_{i ∈ U} syncSizeᵉ (def i)
--
-- with U the slots not yet in `connectedShares`.  What that probe did
-- NOT check — and what this one did, first, because it was the most
-- uncertain piece and the one that decided the whole approach — is
-- whether a frame's refreshed `k` dominates nest for the payloads that
-- frame subscribes.  The receipts a frame has are
--
--     sizeᵉ o      ≤ Caps.cSize (frameStep j c)  ≡  sizeAt S j   (valsCaps?)
--     slotsSize sl ≤ Caps.cSize c                ≡  S            (the clique's slSz)
--
-- so nest is bounded by `sizeAt S j + S` and NOT by `sizeAt S j` alone.
--
-- THE ANSWER IS YES, ONE SIZE LEVEL UP, and the positive half has
-- LANDED: `nest`, the residue and its lifecycle lemmas, the share edge's
-- step, and the frame row `refresh-supplies-nest` are all in
-- .Verify-Budget-Sufficient.Caps-Nest, and `fLvlD`'s `suc d` clause now
-- reads its k at `suc (sizeAt S (suc J))`.  What stays here is the
-- NEGATIVE row, which nothing in src can hold: the entry level cannot
-- pay, and not marginally — it needs `S ≤ 1` against the clique's own
-- `2 ≤ S`.  That is why the raise happened, so it is worth keeping
-- refuted rather than argued.
--
-- The reset question is also answered, and did not need answering:
-- `connectedShares` starts `[]` at `st-init` (Rx.Evaluator:934) and is
-- only ever CONSED to, at the single write in `sharedConnect` (:1338);
-- the only other mentions in the evaluator are the field declaration
-- (:286, "connect happens once, ever") and the `memberSource` read in
-- `subscribeSharedSlot` (:1363).  There is no per-instant reset, so the
-- residue does not return to full between instants — and does not have
-- to, because `Caps-Nest.resid≤slots` holds for EVERY cs, so the frame
-- row is uniform in whatever the connected set is at frame entry.  That
-- is strictly stronger than the reset premise.
------------------------------------------------------------------
module Share-Residue-Probe where

open import Data.Nat  using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥)

open import Rx.Evaluator using (sizeAt)

-- k at the entry level, `suc (sizeAt S J)`, is what `fLvlD` read before
-- the raise.  `sizeAt 2 0` is 2, so at S = 2, j = 0 the row demands
-- 2 + 2 ≤ 3 — the smallest witness there is
Entry-Level-Supply : Set
Entry-Level-Supply = ∀ (S j x y : ℕ) →
  2 ≤ S → x ≤ sizeAt S j → y ≤ S → x + y ≤ suc (sizeAt S j)

entry-level-absurd : Entry-Level-Supply → ⊥
entry-level-absurd H with H 2 0 2 2 (s≤s (s≤s z≤n)) ≤-refl ≤-refl
... | s≤s (s≤s (s≤s ()))
