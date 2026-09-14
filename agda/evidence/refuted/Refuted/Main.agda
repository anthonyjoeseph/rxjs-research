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

-- and the shape that survived it, killed in turn.  The three figures
-- are claimed because the crossing is their ORDER: the depth walks in
-- on the entry store, survives one delivery, and is gone from the exit
-- store — so a repair moving any single end would leave a witness
-- reporting numbers that no longer meet.  It is beside the climb rather
-- than folded into it because the two die to different repairs: a
-- figure growing with the burst answers the climb and leaves this one
-- open at a burst of two, where the template deepens nothing
open import Refuted.Exit-Store using (exit-bounded-false;
  entry-is; kept-is; store-is)

-- and the repair that reads BOTH ends, refuted in turn at a template
-- whose two arms are the other two witnesses'.  Its four figures are
-- claimed because the finding is that the peak clears all of them at
-- once: a repair moving any single one would leave a witness reporting
-- numbers that no longer meet.  What is left after this is a factor in
-- the burst's LENGTH, which is the only quantity none of the three
-- reads
open import Refuted.Exit-Store using (both-ends-false;
  rise-tmpl-is; rise-entry-is; rise-store-is; interior-is)

-- and the one witness here that is not about a bound at all.  The
-- others kill a reading the descent does not have; this kills a
-- QUANTIFIER — the subscribe cycle's totality leaf claims a derivation
-- at every entry triple, and one clause of the machine reads that
-- triple against the term.  Its two figures are claimed because the
-- finding is that they never meet: the size the guard reads is fixed
-- by the program, the component it is read against is chosen by the
-- caller, and nothing in the statement relates them
open import Refuted.Totality-Entry using (subscribe-total-false;
  unfold-size; dry-entry)

-- and the same quantifier one cycle over, where the answer is not a
-- restatement of the entry but a premise about what a frame HANDS ON.
-- The two figures are claimed because the finding is that no program
-- can be shallow enough to escape: the inner is the emptiest there is
-- and the guard is strict, so a repair has to relate the two ends
-- rather than read either more carefully
open import Refuted.Hop-Unconditioned using (consume-total-false;
  inner-depth; dry-out)
