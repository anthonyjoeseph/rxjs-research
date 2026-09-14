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

-- the widest of them, and the only one taken against a statement `src`
-- declares a real BODY for.  Each reading is claimed beside its own dry
-- row because the finding is their ORDER, and the three witnesses beside
-- each other because they die to different repairs: a summing map clause
-- closes the first, leaves the fold exactly where it was, and does not
-- reach the gate at all — whose reading is ZERO, which is the clause the
-- unfolding equation is bought with
open import Refuted.Dry-Wrap using (rank-sufficient-false;
  rank-sufficient-false-fold; rank-sufficient-false-gate;
  nest-p; dry-p; nest-q; dry-q; nest-g; dry-g)

-- and the shape a frame shelf was about to be written in, taken before
-- the statement existed.  No figure is claimed beside it and that is the
-- difference from every witness above: the crossing is not a pair of
-- numerals that could drift apart under a repair, it is a RATE proven
-- for every burst length, so the witness cannot go quiet while the
-- mechanism under it stands
open import Refuted.Scan-Deepens using (scan-bounded-false)
