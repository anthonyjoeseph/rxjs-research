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
-- AND THREE WITNESSES LEFT WITH THE ARM THEY REACHED, WHICH IS HOW A
-- REFUTATION IS MEANT TO DIE.  They killed the top-line dry claim, the
-- hop's unconditioned premise and the totality leaf's entry quantifier
-- — three readings of a rank the run computed — and `src` can no longer
-- STATE any of them, because the run computes no rank.  What they were
-- evidence about is now a proof obligation rather than an answer the
-- machine gives, so there is nothing left for them to be false of.
--
-- RECOVERY: git show 919f115:agda/evidence/refuted/Refuted/
-- RECOVERY: git show ba1285b:agda/evidence/refuted/Refuted/Dry-Wrap.agda
module Refuted.Main where

-- the shape a frame shelf was about to be written in, taken before the
-- statement existed.  No figure is claimed beside it, and that is what
-- makes it the widest witness left here: the crossing is not a pair of
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

-- the entry bound the door was going to be paid out of, killed at the
-- other extreme from every witness the cutover retired: those were
-- adversarial in the entry or in the program, and this is neither.  Its
-- one figure is claimed because the rank the root builds is
-- NOUGHT wherever a program writes no observable, so the bound is a
-- demand on the entry rather than a property of the burst — and a
-- repair reading the value's TYPE leaves this row failing rather than
-- quietly agreeing
open import Refuted.Carried-Unranked using (carried-false; root-rank)

-- and the reading that survived THAT, killed at the one clause where the
-- entry invariant speaks about a symbol rather than a program.  Its two
-- figures are claimed because the finding is the gap between them: the
-- definition writes an observable and the reference standing for it
-- reads nought, so no repair reading the TERM can close this — which is
-- what says the conjunct owed is over the SCHEDULE
open import Refuted.Carried-Shared using (carried-shared-false;
  def-depth; ref-depth)

-- and the same crossing asked of a DERIVATION, which is the statement
-- the builder actually spends.  Its two figures are the sibling's, and
-- it is beside that witness rather than replacing it because the two
-- die to different events: the sibling expires when the cutover deletes
-- the machine it reads, and this one goes on holding against whatever
-- the relation is restated to say
open import Refuted.Carried-Derived using (carried-derived-false;
  derived-def-depth; derived-ref-depth)
