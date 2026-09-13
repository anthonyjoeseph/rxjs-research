-- THE REFUTATION ROOT.  `make refuted` checks this module, and nothing
-- else reaches it: `make gate-heavy` compiles `src/Main.agda`, which cannot
-- import this tree, and `make wiring` scans `agda/src` only.
--
-- Naming each witness here is what keeps this tree honest: a refutation
-- that is not listed is not checked, exactly as in src/Main.agda.
--
-- Read the recovered witnesses' STATEMENTS and not their verdicts: each
-- killed a reading of a quantity the descent does not have, so what
-- transfers is the adversarial state a family was built to reach, never
-- the conclusion drawn from it.
--
-- RECOVERY: git show 919f115:agda/evidence/refuted/Refuted/
module Refuted.Main where

open import Refuted.Drain-Reachable using (drain-dry-free-false;
  drain-dry-free-inv-false)
-- the two figures are claimed beside the witness on purpose: an
-- inequality refutation dies quietly when a repair enlarges the right
-- side, and a pinned crossing fails by name instead
open import Refuted.Hop-Sum using (entry-hop-fits-false; carried-is; term-is)

open import Refuted.Rank-Entry using (dry-operator-false)
-- the three figures travel with the witness for the same reason: the
-- payload and the store both enter at the floor here, so a repair that
-- moved either would leave the crossing intact and say nothing
open import Refuted.Scan-Store using (scan-frame-carried-false;
  payload-is; store-is; out-is)
open import Refuted.Sync-Count using (sync-count-bounded-false)
