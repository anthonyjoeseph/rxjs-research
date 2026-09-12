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

open import Rx.Prim using (after_,_; hot; cold)
open import Rx.Exp using (input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; nat̂; primᵗ;
  pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; add; mul)
open import Rx.Slots using (scripted)

open import Implementation.Unit-Test.Prelude using (Case; cached)
-- IMPORTS>>>

cases : List Case
cases =
  cached "315" 30
          (mergeAllᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (takeᵉ (nat̂ 2) (mapᵉ (varᵗ (here refl)) (switchAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 3) ∷ (nat̂ 5) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 1) ∷ (nat̂ 3) ∷ []))) ∷ [])))))) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 3))) emptyᵉ)) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (input zero))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (exhaustAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 6) ∷ (nat̂ 6) ∷ []))) ∷ (strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 4) ∷ []))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (ofᵉ ((nat̂ 4) ∷ (nat̂ 8) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 8) ∷ (nat̂ 6) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 5) ∷ []))) ∷ (strmᵗ (input zero)) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 9) (input zero))) ∷ [])))) ∷ [])))) ∷ [])))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 4))) (input (suc zero)))) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 5) ∷ (nat̂ 8) ∷ []))) ∷ (strmᵗ (mapᵉ (varᵗ (here refl)) (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (mapᵉ (varᵗ (here refl)) emptyᵉ)))) ∷ [])))) ∷ (strmᵗ (takeᵉ (nat̂ 3) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (input zero)) ∷ (strmᵗ (input (suc zero))) ∷ []))))) ∷ (strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 1))) (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 0))) (input zero)))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (input zero)) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ [])))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 6))) (takeᵉ (nat̂ 3) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ emptyᵉ) ∷ [])))))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 8) ∷ (nat̂ 4) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (mapᵉ (varᵗ (here refl)) (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 7))) (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 5) ∷ (nat̂ 9) ∷ []))) ∷ []))))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) (input zero))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 6) (ofᵉ ((nat̂ 9) ∷ (nat̂ 1) ∷ [])))) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 1) (mapᵉ (varᵗ (here refl)) emptyᵉ))) ∷ []))))) ∷ [])))) ∷ [])))
          (λ { zero → scripted (hot ((after 2 , 0) ∷ [])) ; (suc zero) → scripted (cold (1 ∷ 2 ∷ 3 ∷ []) ((after 1 , 2) ∷ (after 2 , 6) ∷ (after 1 , 3) ∷ [])) ; (suc (suc ())) }) ∷
  cached "378" 30
          (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 0) ∷ (nat̂ 4) ∷ []))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (takeᵉ (nat̂ 1) (exhaustAllᵉ (ofᵉ ((strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 3) ∷ []))) ∷ (strmᵗ (input zero)) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 6) ∷ []))) ∷ [])))) ∷ [])))))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 7) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 6))) emptyᵉ)) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 5))) emptyᵉ)) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 7) (input (suc zero)))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 3) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 7) (mergeAllᵉ nothing (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (ofᵉ ((nat̂ 9) ∷ (nat̂ 4) ∷ []))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 0) ∷ []))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 0))) (input zero))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 8))) emptyᵉ)) ∷ [])))) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) emptyᵉ)) ∷ [])))) ∷ [])))) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (varᵗ (here refl)) (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 3))) (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) emptyᵉ))) ∷ (strmᵗ (takeᵉ (nat̂ 3) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 2) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ (strmᵗ (input (suc zero))) ∷ []))))) ∷ []))))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (varᵗ (here refl)) (mergeAllᵉ nothing (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (ofᵉ ((nat̂ 9) ∷ (nat̂ 5) ∷ []))) ∷ [])))) ∷ []))))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 2) (ofᵉ ((nat̂ 9) ∷ (nat̂ 0) ∷ [])))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 3) ∷ (nat̂ 8) ∷ []))) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 2) ∷ []))) ∷ [])))) ∷ [])))
          (λ { zero → scripted (cold (6 ∷ 7 ∷ 8 ∷ []) ((after 2 , 6) ∷ (after 2 , 4) ∷ (after 0 , 9) ∷ [])) ; (suc zero) → scripted (hot ((after 1 , 8) ∷ [])) ; (suc (suc ())) }) ∷
  []
