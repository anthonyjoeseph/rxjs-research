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

open import Refuted.Burst-Nesting using (burst-under-emitter-false)
open import Refuted.Drain-Reachable using (drain-dry-free-false;
  drain-dry-free-inv-false)
open import Refuted.Rank-Entry using (dry-operator-false)
open import Refuted.Rank-Fold using (dry-operator-fold-false)
open import Refuted.Sync-Count using (sync-count-bounded-false)
