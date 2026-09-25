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
-- A PROBE AND A ROW ARE ONE OBJECT AT TWO TIMES, SO THIS IS THE ONE
-- CORPUS (Anthony).  Every row passes once its bug is fixed and then
-- guards against regression.  A refutation of an envelope SHAPE is not a
-- row: the program that kills shape A passes under shape B, so it
-- cannot stay here failing without breaking the invariant.  It is a
-- dead-route entry in `Rx.Envelope`'s header citing the killing row by
-- index, which is stable because the corpus is append-only.
--
-- THE IMPORT BLOCK IS MACHINE-OWNED, between the markers below.  A row
-- can mention any constructor the generator can emit, and nothing knows
-- which until the row exists, so the block is written WIDE before an
-- append and pruned by `make imports-fix` after -- a dead import is an
-- `imports-check` failure, and a missing one would make the very next
-- appended row unscopeable.  Edit the wide form in the generator, not
-- here; anything written between the markers by hand is overwritten.
------------------------------------------------------------------
module Implementation.Unit-Test where

open import Data.List using (List; []; _∷_)

-- <<<IMPORTS
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.SExp using (inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; mergeAllˢ;
  switchAllˢ; exhaustAllˢ; varˢᵗ; natˢ; primˢ; pairˢ; strmˢ)
open import Rx.Exp using (add)

open import Rx.Prim using (hot; cold; after_,_)
open import Implementation.Unit-Test.Prelude using (Case; cached; mkSlots)
-- IMPORTS>>>

cases : List Case
cases =
  cached "two ofs in one delivery" 30
          (mergeAllˢ nothing (mapˢ (strmˢ (mergeAllˢ nothing (ofˢ (
              (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) ∷
              (strmˢ (ofˢ ((primˢ add (pairˢ (varˢᵗ (here refl)) (natˢ 1))) ∷ []))) ∷ []))))
            (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "one of, two values, per delivery" 30
          (mergeAllˢ nothing (mapˢ (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ (varˢᵗ (here refl)) ∷ [])))
            (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "the script merged with itself" 30
          (mergeAllˢ nothing (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (inputˢ zero)) ∷ [])))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "a share of the script merged with itself" 30
          (mergeAllˢ nothing (ofˢ ((strmˢ (inputˢ (suc zero))) ∷ (strmˢ (inputˢ (suc zero))) ∷ [])))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   (inputˢ zero)) ∷
  cached "a delivery subscribing the script again" 30
          (mergeAllˢ nothing (mapˢ (strmˢ (inputˢ zero)) (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a delivery switching to two ofs" 30
          (switchAllˢ (mapˢ (strmˢ (mergeAllˢ nothing (ofˢ (
              (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) ∷
              (strmˢ (ofˢ ((natˢ 7) ∷ []))) ∷ []))))
            (inputˢ zero)))
          (mkSlots (cold (3 ∷ []) ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "a delivery exhausting into two ofs" 30
          (exhaustAllˢ (mapˢ (strmˢ (mergeAllˢ (just 1) (ofˢ (
              (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) ∷
              (strmˢ (ofˢ ((natˢ 7) ∷ []))) ∷ []))))
            (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "take one of the script" 30
          (takeˢ (natˢ 1) (inputˢ zero))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  []
