------------------------------------------------------------------
-- THE BUG CACHE: every counterexample this campaign has discovered,
-- as one list the compiled runner walks.
--
-- APPEND-ONLY, via `scripts/gen-unit-tests.sh`.  A QuickCheck failure
-- becomes a row here; a bug that is later fixed just becomes a passing
-- guard that stays.  Nothing is ever deleted or rewritten, so the
-- corpus only grows and the invariant it carries is that EVERY row
-- holds -- `make bug-cache` is green exactly when no known
-- counterexample remains.  The whole file goes when the top-line
-- statement modules under `Left-To-Right`, `Timed` and `Batchable` are
-- discharged.
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
-- A ROW IS A PROGRAM, NOT A CLAIM ABOUT ONE.  Every property the
-- cache carries is checked of every row, so what a row has to say is
-- which run to make; the label is the seed that found it and means
-- nothing more.
--
-- A PROBE AND A ROW ARE ONE OBJECT AT TWO TIMES, SO THIS IS THE ONE
-- CORPUS (Anthony).  Every row passes once its bug is fixed and then
-- guards against regression.  A refutation of an InstEmit SHAPE is not a
-- row: the program that kills shape A passes under shape B, so it
-- cannot stay here failing without breaking the invariant.  It is a
-- dead-route entry in `SExp.InstEmit`'s header citing the killing row by
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
module CLI.Unit-Test where

open import Data.List using (List; []; _∷_)

-- <<<IMPORTS
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import SExp.Syntax using (inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ; varˢᵗ; natˢ;
  primˢ; pairˢ; fstˢ; sndˢ; strmˢ; μˢ; deferˢ; varˢ)
open import Rx.Exp using (add; mergeᶠ; switchᶠ; exhaustᶠ)

open import Rx.Prim using (hot; cold; after_,_)
open import CLI.Unit-Test.Prelude using (Case; cached; mkSlots; flatAllˢ)
-- IMPORTS>>>

cases : List Case
cases =
  cached "two ofs in one delivery" 30
          (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (flatAllˢ (mergeᶠ nothing) (ofˢ (
              (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) ∷
              (strmˢ (ofˢ ((primˢ add (pairˢ (varˢᵗ (here refl)) (natˢ 1))) ∷ []))) ∷ []))))
            (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "one of, two values, per delivery" 30
          (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ (varˢᵗ (here refl)) ∷ [])))
            (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "the script merged with itself" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (inputˢ zero)) ∷ [])))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "a share of the script merged with itself" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ (suc zero))) ∷ (strmˢ (inputˢ (suc zero))) ∷ [])))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   (inputˢ zero)) ∷
  cached "a delivery subscribing the script again" 30
          (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (inputˢ zero)) (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a delivery switching to two ofs" 30
          (flatAllˢ switchᶠ (mapˢ (strmˢ (flatAllˢ (mergeᶠ nothing) (ofˢ (
              (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) ∷
              (strmˢ (ofˢ ((natˢ 7) ∷ []))) ∷ []))))
            (inputˢ zero)))
          (mkSlots (cold (3 ∷ []) ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "a delivery exhausting into two ofs" 30
          (flatAllˢ exhaustᶠ (mapˢ (strmˢ (flatAllˢ (mergeᶠ (just 1)) (ofˢ (
              (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) ∷
              (strmˢ (ofˢ ((natˢ 7) ∷ []))) ∷ []))))
            (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ []))
                   emptyˢ) ∷
  cached "take one of the script" 30
          (takeˢ (natˢ 1) (inputˢ zero))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "seed 1 depth 1 case 108" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ (suc zero))) ∷ (strmˢ emptyˢ) ∷
            (strmˢ (ofˢ ((natˢ 5) ∷ (natˢ 3) ∷ []))) ∷ [])))
          (mkSlots (cold [] ((after 1 , 3) ∷ (after 0 , 7) ∷ []))
                   (ofˢ ((natˢ 5) ∷ (natˢ 7) ∷ []))) ∷
  cached "seed 6 depth 1 case 4" 30
          (flatAllˢ switchᶠ (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ emptyˢ) ∷ [])))
          (mkSlots (hot ((after 0 , 1) ∷ ((after 1 , 1) ∷ [])))
                   (emptyˢ)) ∷
  cached "seed 7 depth 1 case 12" 30
          (flatAllˢ exhaustᶠ (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (ofˢ ((natˢ 4) ∷ (natˢ 6) ∷ []))) ∷ [])))
          (mkSlots (cold [] ((after 0 , 8) ∷ ((after 0 , 8) ∷ [])))
                   ((inputˢ zero))) ∷
  cached "seed 2 depth 1 case 15" 30
          (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (ofˢ ((varˢᵗ (here refl)) ∷ []))) (inputˢ zero)))
          (mkSlots (hot ((after 0 , 2) ∷ ((after 1 , 5) ∷ [])))
                   ((ofˢ ((natˢ 9) ∷ [])))) ∷
  cached "seed 9 depth 1 case 2" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ (suc zero))) ∷ (strmˢ (ofˢ ((natˢ 9) ∷ (natˢ 9) ∷ []))) ∷ (strmˢ (inputˢ (suc zero))) ∷ [])))
          (mkSlots (cold [] ((after 1 , 1) ∷ ((after 0 , 0) ∷ [])))
                   ((ofˢ ((natˢ 5) ∷ [])))) ∷
  cached "seed 2 depth 1 timing-correct" 30
          (flatAllˢ switchᶠ (ofˢ ((strmˢ (inputˢ (suc zero))) ∷ (strmˢ emptyˢ) ∷ (strmˢ (inputˢ (suc zero))) ∷ [])))
          (mkSlots (hot ((after 0 , 6) ∷ []))
                   ((ofˢ ((natˢ 9) ∷ (natˢ 7) ∷ [])))) ∷
  cached "seed 1 depth 2 case 1" 30
          (flatAllˢ (mergeᶠ (just 2)) (ofˢ ((strmˢ (mapˢ (varˢᵗ (here refl)) (inputˢ (suc zero)))) ∷ (strmˢ (μˢ (deferˢ (varˢ (here refl))))) ∷ [])))
          (mkSlots (cold (2 ∷ []) ((after 0 , 9) ∷ []))
                   ((inputˢ zero))) ∷
  cached "seed 1 depth 2 case 1 at fuel 1" 1
          (flatAllˢ (mergeᶠ (just 2)) (ofˢ ((strmˢ (mapˢ (varˢᵗ (here refl)) (inputˢ (suc zero)))) ∷ (strmˢ (μˢ (deferˢ (varˢ (here refl))))) ∷ [])))
          (mkSlots (cold (2 ∷ []) ((after 0 , 9) ∷ []))
                   ((inputˢ zero))) ∷
  cached "seed 1 depth 2 case 1 at fuel 2" 2
          (flatAllˢ (mergeᶠ (just 2)) (ofˢ ((strmˢ (mapˢ (varˢᵗ (here refl)) (inputˢ (suc zero)))) ∷ (strmˢ (μˢ (deferˢ (varˢ (here refl))))) ∷ [])))
          (mkSlots (cold (2 ∷ []) ((after 0 , 9) ∷ []))
                   ((inputˢ zero))) ∷
  cached "seed 5 depth 2 fuel 4 timing-correct" 4
          (flatAllˢ exhaustᶠ (ofˢ ((strmˢ (scanˢ (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl))) (sndˢ (varˢᵗ (here refl))))) (natˢ 5) (ofˢ ((natˢ 3) ∷ (natˢ 9) ∷ [])))) ∷ (strmˢ (takeˢ (natˢ 5) (inputˢ zero))) ∷ [])))
          (mkSlots (cold (5 ∷ []) ((after 0 , 3) ∷ []))
                   (emptyˢ)) ∷
  cached "seed 5 depth 2 fuel 4 timing-correct, at fuel 30" 30
          (flatAllˢ exhaustᶠ (ofˢ ((strmˢ (scanˢ (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl))) (sndˢ (varˢᵗ (here refl))))) (natˢ 5) (ofˢ ((natˢ 3) ∷ (natˢ 9) ∷ [])))) ∷ (strmˢ (takeˢ (natˢ 5) (inputˢ zero))) ∷ [])))
          (mkSlots (cold (5 ∷ []) ((after 0 , 3) ∷ []))
                   (emptyˢ)) ∷
  cached "a cold under two takes in one merge" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (takeˢ (natˢ 1) (inputˢ zero))) ∷ (strmˢ (takeˢ (natˢ 2) (inputˢ zero))) ∷ [])))
          (mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a share of a cold merged with a take of itself" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ (suc zero))) ∷ (strmˢ (takeˢ (natˢ 1) (inputˢ (suc zero)))) ∷ [])))
          (mkSlots (cold (3 ∷ []) ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   (inputˢ zero)) ∷
  cached "a take of a cold exhausted beside an of" 30
          (flatAllˢ exhaustᶠ (ofˢ ((strmˢ (ofˢ ((natˢ 4) ∷ []))) ∷ (strmˢ (takeˢ (natˢ 2) (inputˢ zero))) ∷ [])))
          (mkSlots (cold (5 ∷ []) ((after 0 , 3) ∷ (after 1 , 8) ∷ []))
                   emptyˢ) ∷
  cached "an of buffered behind a take of a cold" 30
          (flatAllˢ (mergeᶠ (just 1)) (ofˢ ((strmˢ (takeˢ (natˢ 1) (inputˢ zero))) ∷ (strmˢ (ofˢ ((natˢ 7) ∷ []))) ∷ [])))
          (mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a cold buffered behind a take of itself" 30
          (flatAllˢ (mergeᶠ (just 1)) (ofˢ ((strmˢ (takeˢ (natˢ 1) (inputˢ zero))) ∷ (strmˢ (inputˢ zero)) ∷ [])))
          (mkSlots (cold (2 ∷ []) ((after 0 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a take of an of subscribed at each hot arrival, merged" 30
          (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (takeˢ (natˢ 1) (ofˢ ((natˢ 7) ∷ (varˢᵗ (here refl)) ∷ [])))) (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a take of an of subscribed at each hot arrival, switched" 30
          (flatAllˢ switchᶠ (mapˢ (strmˢ (takeˢ (natˢ 1) (ofˢ ((natˢ 7) ∷ (varˢᵗ (here refl)) ∷ [])))) (inputˢ zero)))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a take of a cold subscribed at each of its own arrivals" 30
          (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (takeˢ (natˢ 1) (inputˢ zero))) (inputˢ (suc zero))))
          (mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   (inputˢ zero)) ∷
  cached "a take of a deferred self merged with a hot" 12
          (μˢ (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (takeˢ (natˢ 1) (deferˢ (varˢ (here refl))))) ∷ []))))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a take of a deferred self merged with a cold" 12
          (μˢ (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (takeˢ (natˢ 1) (deferˢ (varˢ (here refl))))) ∷ []))))
          (mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a take of a scan of a cold merged with the cold" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (takeˢ (natˢ 1) (scanˢ (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl))) (sndˢ (varˢᵗ (here refl))))) (natˢ 0) (inputˢ zero)))) ∷ (strmˢ (inputˢ zero)) ∷ [])))
          (mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a take of a scan of an of beside a take of a cold" 30
          (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (takeˢ (natˢ 2) (scanˢ (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl))) (sndˢ (varˢᵗ (here refl))))) (natˢ 0) (ofˢ ((natˢ 3) ∷ (natˢ 4) ∷ (natˢ 5) ∷ []))))) ∷ (strmˢ (takeˢ (natˢ 1) (inputˢ zero))) ∷ [])))
          (mkSlots (cold [] ((after 0 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a scan fed back through a take of a deferred self, hot" 12
          (μˢ (scanˢ (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl))) (sndˢ (varˢᵗ (here refl))))) (natˢ 0) (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (takeˢ (natˢ 1) (deferˢ (varˢ (here refl))))) ∷ [])))))
          (mkSlots (hot ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "a scan fed back through a take of a deferred self, cold" 12
          (μˢ (scanˢ (primˢ add (pairˢ (fstˢ (varˢᵗ (here refl))) (sndˢ (varˢᵗ (here refl))))) (natˢ 0) (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (inputˢ zero)) ∷ (strmˢ (takeˢ (natˢ 1) (deferˢ (varˢ (here refl))))) ∷ [])))))
          (mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))
                   emptyˢ) ∷
  cached "the seeds 13..36 depth 2 sweep's counterexample" 30
          (takeˢ (natˢ 3) (flatAllˢ (mergeᶠ nothing) (ofˢ ((strmˢ (ofˢ ((natˢ 5) ∷ (natˢ 5) ∷ []))) ∷ (strmˢ (inputˢ (suc zero))) ∷ (strmˢ (inputˢ zero)) ∷ []))))
          (mkSlots (cold [] ((after 1 , 2) ∷ ((after 0 , 8) ∷ [])))
                   ((ofˢ ((natˢ 3) ∷ (natˢ 0) ∷ [])))) ∷
  []
