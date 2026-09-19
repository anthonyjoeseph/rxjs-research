------------------------------------------------------------------
-- THE BUG CACHE: every counterexample this campaign has discovered,
-- as one list the compiled runner walks.
--
-- APPEND-ONLY, via `scripts/gen-unit-tests.sh`.  A QuickCheck failure
-- becomes a row here; a bug that is later fixed just becomes a passing
-- guard that stays.  Nothing is ever deleted or rewritten, so the
-- corpus only grows and the invariant it carries is that EVERY row
-- holds -- `make bug-cache` is green exactly when no known
-- counterexample remains.  The whole file goes when
-- `Verify-Batch-Simultaneous.The-Proof` is discharged.
--
-- IT IS ONE FILE AGAIN, WHICH THE TYPE-LEVEL CACHE COULD NOT AFFORD.
-- A row used to be a `refl` over a whole `evaluate` run, so the
-- typechecker paid for every case on every gate run; the repair was one
-- module per case, riding Agda's per-module interface cache, and the
-- cost was a ledger of import-and-pin blocks growing beside a directory
-- of near-identical modules.  A row is now a value, and the run behind
-- it happens in a compiled binary at a speed no typechecker reaches, so
-- appending a case costs a list entry and nothing else.
--
-- A ROW IS A PROGRAM, NOT A CLAIM ABOUT ONE.  Both properties the
-- cache carries are checked of every row, so what a row has to say is
-- which run to make; the label is the seed that found it and means
-- nothing more.
--
-- THE CORPUS IS EMPTY, AND THAT IS A GENERATION CHANGE RATHER THAN A
-- CLEARED LEDGER.  Every row it held was a plain `Exp` program driven
-- by scripted slots, and a plain run carries no envelope, so none of
-- them is a case the batching question can even be asked of now that a
-- row is an author's `SExp` under `elaborate`; every one of them was
-- also driven by a SCRIPTED slot, which an elaborated telescope does
-- not admit -- a script at the envelope would be writing tokens by
-- hand -- so the tables could not be ported mechanically either.  What
-- they established
-- was agreement on the PLAIN tree, which is the oracle's question and
-- not this cache's.  Until the sweep refills it the invariant below
-- holds vacuously, which is worth knowing before reading a green.
--
-- THE IMPORT BLOCK IS MACHINE-OWNED, between the markers below.  A row
-- can mention any constructor the generator can emit, and nothing knows
-- which until the row exists, so the block is written WIDE before an
-- append and pruned by `make imports-fix` after -- a dead import is an
-- `imports-check` failure, and a missing one would make the very next
-- appended row unscopeable.  Edit the wide form in the generator, not
-- here; anything written between the markers by hand is overwritten.
--
-- RECOVERY: git show 0f4998f0:agda/src/Implementation/Unit-Test.agda
--   restores all eight plain rows, each with its scripted slot table.
------------------------------------------------------------------
module Implementation.Unit-Test where

open import Data.List using (List; [])

-- <<<IMPORTS
open import Implementation.Unit-Test.Prelude using (Case)
-- IMPORTS>>>

cases : List Case
cases =
  []
