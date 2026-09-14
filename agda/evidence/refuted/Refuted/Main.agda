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

open import Refuted.Drain-Reachable using (drain-dry-free-false)
-- the two figures are claimed beside the witness on purpose: an
-- inequality refutation dies quietly when a repair enlarges the right
-- side, and a pinned crossing fails by name instead
open import Refuted.Hop-Sum using (entry-hop-fits-false; carried-is; term-is)

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

-- and the repair that finding was read as licensing, refuted in turn:
-- the four figures are claimed because the crossing is their ORDER, and
-- the two below them because a witness that killed the asymmetric form
-- as well would be saying something else entirely
open import Refuted.Map-Pinned using (map-frame-pinned-false;
  pin-bound-is; pin-in-is; pin-out-is; pin-store-is)
open import Refuted.Map-Pinned using (pin-source-is; pin-asym-fits)

open import Refuted.Rank-Entry using (dry-operator-false)
-- the three figures travel with the witness for the same reason: the
-- payload and the store both enter at the floor here, so a repair that
-- moved either would leave the crossing intact and say nothing
open import Refuted.Scan-Store using (scan-frame-carried-false;
  payload-is; count-is; store-is; out-is)

-- and the walk's own share leaf, refuted at the smallest share that
-- FOLDS.  The three figures are claimed because the crossing is their
-- ORDER and each is a different way a repair could make the witness
-- quiet: the dispatch has to reach a non-empty registry, the store the
-- chain is held to has to stay at one, and the chain's own payload at
-- its flattener has to stay at one.  The term figure is claimed for the
-- opposite reason — it is what says the machine is not dry here at all,
-- so the refuted point is legal under the hypothesis as written and
-- unreachable at every call site
open import Refuted.Share-Chain using (share-chain-hop-false;
  regs-is; store-is; chain-is; termFig-is)
