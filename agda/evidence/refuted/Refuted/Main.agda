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

-- and the repair that finding was read as licensing, refuted in turn:
-- the four figures are claimed because the crossing is their ORDER, and
-- the two below them because a witness that killed the asymmetric form
-- as well would be saying something else entirely
open import Refuted.Map-Pinned using (map-frame-pinned-false;
  pin-bound-is; pin-in-is; pin-out-is; pin-store-is)
open import Refuted.Map-Pinned using (pin-source-is; pin-asym-fits)

-- and the third candidate for what bounds the registry, the arrival's
-- own seed.  Its figures are claimed in pairs across the step, because
-- the finding is a CROSSING and not a height: the seed falls while the
-- registry rises, so a repair that moved only one end would leave a
-- witness reporting two numbers that no longer meet
open import Refuted.Arrival-Seed using (seed-preserved-false;
  seed-e₁; seed-s₁; pay-s₁; seed-store-s₁; reg-e₁; reg-s₁)
-- and the deeper program's four, which are what say the gap is a RATE:
-- same seed, registry one higher per flattener, so no constant slack
-- repairs it
open import Refuted.Arrival-Seed using (seed-e₃; seed-s₃; pay-s₃;
  seed-store-s₃; reg-e₃; reg-s₃)

-- and the narrowing that reading licensed, refuted in turn: the chains
-- ONE arrival reaches, priced against the value it actually carries.
-- The two figures per state are claimed because the crossing is their
-- ORDER; the reach and payload rows because they are what say each
-- narrowing did NO work — one chain reached and a payload at the floor,
-- so a repair that moved either would leave the witness silent
open import Refuted.Arrival-Filtered using (filtered-preserved-false;
  spend-e₁; grant-e₁; spend-s₁; grant-s₁; reached-s₁; payload-s₁;
  store-s₁; term-q₁)
-- and the deeper program's, which are what say the gap is a RATE here
-- too: same grant, spend one higher per flattener
open import Refuted.Arrival-Filtered using (spend-e₃; grant-e₃;
  spend-s₃; grant-s₃; reached-s₃; payload-s₃)

open import Refuted.Rank-Entry using (dry-operator-false)
-- the three figures travel with the witness for the same reason: the
-- payload and the store both enter at the floor here, so a repair that
-- moved either would leave the crossing intact and say nothing
open import Refuted.Scan-Store using (scan-frame-carried-false;
  payload-is; count-is; store-is; out-is)
open import Refuted.Sync-Count using (sync-count-bounded-false)

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

-- and the input bound's runtime arm, refuted at the smallest instance
-- the syntax admits.  Nothing is claimed beside the witness: the
-- crossing is a predicate that computes to `false`, so there is no
-- figure a repair could leave intact
open import Refuted.Inner-Floor using (inner-below-false)
