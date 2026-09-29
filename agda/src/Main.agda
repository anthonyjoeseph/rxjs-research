-- MAIN IS THE TOP-LINE PROOF (Anthony).  Three rules:
--
--   1. WHATEVER MAIN IMPORTS STICKS AROUND.  This list is the deletion
--      exemption — it is not a build convenience.  Everything else in
--      the repo exists only to serve one of these names, transitively,
--      and `make wiring` roots its reachability check right here.
--   2. NO BARE `open import`.  Individual definitions only, so that the
--      claim set is explicit and machine-readable rather than implied
--      by whatever a module happens to re-export.
--   3. MAIN IS NEVER TOUCHED WITHOUT ANTHONY'S EXPLICIT APPROVAL.
--
-- COVERAGE, and read this before trusting a green `make gate-heavy`: Agda
-- compiles exactly what is transitively imported, so this file defines
-- the build's coverage as well as its claim set.  Every module under
-- `agda/src` is currently reachable from a name below, which is what
-- `make wiring-gate` establishes in seconds and what makes a green heavy
-- gate a statement about the whole tree rather than about whichever part
-- of it this list happens to reach.
module Main where

------------------------------------------------------------------
-- THE THEOREM.  Four statements, and together they are the claim that
-- `batchSimultaneous` batches what plain rxjs would deliver, by
-- instant, without reordering and without waiting.
--
--   left-to-right      the batches, joined back up, are the values the
--                      program read as plain rxjs delivers, in order
--   timing-correct     the impl's instant stamps group emits exactly
--                      as the timed translation's packets do
--   batchable          at every fuel, the batched run is the spec's
--                      grouping of the run by instant
--   timed-faithful     the timed translation is itself faithful to the
--                      plain run, packets and END items dropped
--
-- EACH CLOSES A CHEAT THE OTHERS LEAVE OPEN.  Elaborating every program
-- to `empty` is trivially batched, and fails left-to-right.  Stamping
-- every emit with one instant, or each with its own, fails
-- timing-correct, since the packets are the translation's and not the
-- impl's to arrange.  `timed-faithful` is the translation's own
-- obligation, not the impl's: a translation to `empty` would make
-- timing-correct say nothing.
--
-- THE STATEMENTS MEET IN RAW VALUES, as a subscriber sees them.  No
-- envelope is compared anywhere; valueless emits contribute nothing.
------------------------------------------------------------------
open import Left-To-Right.Statement
  using (left-to-right)
open import Timed.Timing-Correct
  using (timing-correct)
open import Batchable.Statement
  using (batchable)
open import Timed.Faithful
  using (timed-faithful)

------------------------------------------------------------------
-- THE EVALUATOR-LEVEL CLAIMS ARE GONE, AND WHAT REMOVED THEM WAS NOT
-- A TIDY-UP.  Every one of them — the five fuel and unfolding claims,
-- determinacy, run monotonicity, the three timing claims — was stated
-- over a machine that does not mirror rxjs, so porting them across the
-- rewrite would carry a statement about the wrong semantics into a
-- tree built to have the right one.  They are owed again once the new
-- machine computes, and they will be stated over it rather than
-- transported.
--
-- RECOVERY: git show 8c1b5750^:agda/src/Rx/Evaluator-Theorems.agda
-- RECOVERY: git show 8c1b5750^:agda/src/Verify-Determinacy.agda
-- RECOVERY: git show 8c1b5750^:agda/src/Rx/Time-Theorems.agda
--   holds three of them.  Run monotonicity and the probe rows that were
--   its only instantiation never reached main, so nothing restores
--   them; that statement is owed again from scratch.
------------------------------------------------------------------
