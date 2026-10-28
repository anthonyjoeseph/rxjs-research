{-# OPTIONS --guardedness #-}

-- THE THEOREM, OVER THE TABLE: what the pure semantics' run shows is what
-- a reader of the program's table, subscribed at the root, is told.
--
-- RECOVERY: git show 2f1bc862:agda-impl/adequacy/TableStep.agda restores the race bound at a merge's and a concat's frame, proven against the table from two per-node invariants
module adequacy.Table where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (_×_)

open import operation.PureObservable using (PureObs)
open import adequacy.Adequacy using (run)
open import denotation.MonotonicList.Events using (root)
open import denotation.Order using (Shows)
open import denotation.Table using (enter; ⟦_⟧ᵀ)
open import denotation.Table.Read using (Reads)

postulate
  adequacyᵀ : ∀ {A} (o : PureObs [] A) {is}
            → (Shows (run o) is → Reads (enter (⟦ o ⟧ᵀ []) root) is) × (Reads (enter (⟦ o ⟧ᵀ []) root) is → Shows (run o) is)
