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
-- Note what is NOT here: `Verify-Well-Formed`.  It is machinery, not a
-- claim, and it is reached the honest way —
-- `formal-verification-batchSimultaneous` consumes
-- `evaluate-well-formed`, which consumes the run's two derivations.  If any part
-- of that tower is NOT reachable from a name below, that is a finding to
-- wire, not a reason to re-add a bulk import.
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
-- THE THEOREM.  The verified object, end to end: for every program,
-- batching its rendered stream is spec-correct.
------------------------------------------------------------------
open import Verify-Batch-Simultaneous.The-Proof
  using (formal-verification-batchSimultaneous; batch-agreement)

open import Verify-Batch-Simultaneous.Batch-Theorems
  using (batch-online)

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
-- RECOVERY: git show b5601783:agda/src/Rx/Evaluator-Theorems.agda
-- RECOVERY: git show b5601783:agda/src/Verify-Determinacy.agda
-- RECOVERY: git show b5601783:agda/src/Verify-Run-Monotone.agda
-- RECOVERY: git show b5601783:agda/src/Rx/Time-Theorems.agda
--   holds all four, and the same sha's
--   `agda/evidence/probed/Probed/Run-Monotone.agda` the three rows that
--   were the only instantiation any of them ever had.
------------------------------------------------------------------
