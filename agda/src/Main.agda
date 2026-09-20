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
-- Note what is NOT here and no longer exists: the protocol face.  Its
-- one statement said no emit of a canonical run is rejected by the
-- automaton, and it was the single leaf the top line stood on; it was
-- also false against a slot table scripted at the envelope type.  What
-- replaces it is owed over the values once the plain machine computes,
-- so the top line below is a bare postulate meanwhile — the leaf-only
-- law, which forbids minting a leaf whose fit nothing can check.
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

open import Verify-Input-Well-Formed.Input-Well-Formed using (input-wellFormed)
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
