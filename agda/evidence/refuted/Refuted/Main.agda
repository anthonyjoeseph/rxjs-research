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

-- the second half is claimed separately because it is a different
-- claim, not a restatement: the crossing above kills the FIT, and the
-- three names below kill the tier's TOP LINE at the same witness
open import Refuted.Defer-Hop
  using (entry-hop-fits-defer-false; deferCarried-is; deferTerm-is;
         rank-sufficient-defer-false; deferDry-6; deferDry-50)

open import Refuted.Rank-Entry using (dry-operator-false)
open import Refuted.Sync-Count using (sync-count-bounded-false)
