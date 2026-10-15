{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- machine's prefixes is the meaning, observed at the root, with positions
-- forgotten down to ticks.  The meaning is `denotation.Denote`'s fold, so
-- a compositional proof about a program's meaning is a proof about what
-- the program does when run.
module adequacy.Adequacy where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])

open import operation.Machine using (module Machine)
open import operation.PureObservable using (PureObs)
open import denotation.MonotonicList using (ML; observe; root; ticks)
open import denotation.Order using (_≃_; limit)
open import denotation.Denote using (⟦_⟧)

-- The pure run: the limit of the machine's prefixes.
run : ∀ {A} → PureObs [] A → ML A
run {A} o = limit λ n → Machine.prefix A n o

-- Postulated bare until `denotation.Compositional` is proven: a proof
-- here is built on `MonotonicList`'s definition, which compositionality
-- may still move.
--
-- RECOVERY: git show 1222f49a restores the simulation this was proven
--   over (the adequacy Simulation, Carrier, Kept and Wait modules), the
--   stepper Unfold and its link to the fold, the positional Placed, the
--   per-observer Ghost and Spin checks, the limit's least-upper-bound
--   proof in the Order module, and the Placing check of the machine's
--   trace against the meaning's events, positions included, which the
--   bug cache also ran (a meaning silent where the machine works agrees
--   with it by ticks, and only positions see it).
postulate
  adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
