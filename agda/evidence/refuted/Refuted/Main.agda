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

-- the two dry rows travel with this witness for the opposite reason to
-- the figures below: they are what stops the crossings being read one
-- statement too high, since the leaf's conclusion survives both
open import Refuted.Fit-Cascade using (fit-preserved-false;
  carried-e₁; term-e₁; carried-s₁; term-s₁;
  carried-e₃; term-e₃; carried-s₃; term-s₃;
  carried-u₁; term-u₁; carried-u₃; term-u₃; dry₁; dry₃)
-- and the widest state-readable bound, whose own figures are claimed
-- because the pending reading at the door IS the crossing one arrival
-- later: a repair that kept it would leave this witness quiet
open import Refuted.Fit-Cascade using (fit-held-preserved-false;
  pend-e₁; pend-e₃; pend-s₁; store-s₁)

-- the two payload figures are claimed because the crossing is their
-- ORDER and nothing else: a repair that reads the template would move
-- the output one and leave the witness agreeing with itself
open import Refuted.Map-Template using (map-frame-carried-false;
  in-is; out-is; store-is)
-- and the two rows that keep the witness from being read wider than it
-- is: the walk's own bound at this very template, and the output
-- fitting under it.  A repair that pinned the bound would leave the
-- refutation standing and these two agreeing, which is the finding
open import Refuted.Map-Template using (caller-is; caller-fits)

open import Refuted.Rank-Entry using (dry-operator-false)
-- the three figures travel with the witness for the same reason: the
-- payload and the store both enter at the floor here, so a repair that
-- moved either would leave the crossing intact and say nothing
open import Refuted.Scan-Store using (scan-frame-carried-false;
  payload-is; store-is; out-is)
open import Refuted.Sync-Count using (sync-count-bounded-false)
