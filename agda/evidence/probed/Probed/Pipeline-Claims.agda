----------------------------------------------------------------------
-- THE TWO CLAIMS READ OFF THE PIPELINE RATHER THAN OFF A PROGRAM.
----------------------------------------------------------------------

-- WHY THESE TWO SHARE A FILE AND THE README FAMILY DOES NOT.  Both are
-- stated over the BATCHING side rather than over a canonical program,
-- so neither needs an evaluator harness to say something: the online
-- claim is plain list computation, and the id claim reads a finished
-- run's envelopes rather than its values.  That is also why they are
-- reachable while the readme instances are not -- neither has to route
-- a flattener through the frame dispatch to compute.
--
-- NOT REACHED: any program whose evaluation enters a flattening node,
-- for the reason the sibling probe records; a source firing past the
-- two ticks scripted below; and any batching input that a real run
-- produced, since the online rows are hand-written envelope lists
-- chosen to sit either side of a group boundary rather than taken
-- from an evaluation.

-- TARGET: batch-online @73ae89
-- TARGET: id-inheritance @c5b127
module Probed.Pipeline-Claims where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Vec using ([]; _∷_)   -- contexts are Vecs; ∷/[] overload per type
open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (InstEmit; _at_from_as_; init; value;
                           subscribe; delivery)
open import Rx.Exp using (natᵗ; Closed; nat̂; pairᵗ; primᵗ; varᵗ; add; input; mapᵉ)
open import Readme-Theorems using (hotOnce; oneSlot)
open import Verify-Batch-Simultaneous.Batch-Theorems using (batch-online)
open import Rx.Provenance-Theorems using (id-inheritance)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- 1.  ONLINE-NESS: A CLOSED GROUP IS NEVER REOPENED.
--
-- The envelopes are chosen to straddle a group boundary, which is the
-- only arrangement that can decide anything here.  `xs` CLOSES the
-- first instant -- a subscribe frame owes nothing, so its batch is
-- complete as soon as it is seen -- and then LEAVES THE SECOND INSTANT
-- OPEN, because the source has two live registrations and only one of
-- them has paid.  `ys` supplies the second payment.
--
-- LOAD-BEARING on exactly the qualification the statement carries: the
-- left side must contain the first group and must NOT contain the
-- still-growing second one.  A fold that leaked the open batch puts a
-- one-element group where the extension puts a two-element group, the
-- first differing entry is at that position, and no prefix exists --
-- which is the shape that refuted this claim's unqualified
-- predecessor.  A fold that dropped the closed group instead leaves
-- the left side empty and the row degenerates rather than failing, so
-- the non-emptiness of the left side is doing work too.
----------------------------------------------------------------------

xs₀ : List (InstEmit ℕ)
xs₀ = ((init 5 ∷ init 5 ∷ value 1 ∷ []) at 0 from 5 as subscribe)
    ∷ ((value 2 ∷ []) at 1 from 5 as delivery)
    ∷ []

ys₀ : List (InstEmit ℕ)
ys₀ = ((value 3 ∷ []) at 1 from 5 as delivery) ∷ []

row-online : Confirms (batch-online xs₀ ys₀)
row-online = refl ∷ []

----------------------------------------------------------------------
-- 2.  EVERY ID IS AN ARRIVAL'S, NEVER A FRESHLY MINTED ONE.
--
-- Read at a program WITH a source and at more than one instant, which
-- is what makes the claim say anything: a source-free program emits
-- only at the subscribe frame, so its id list is `0` and the
-- containment holds however the counter behaves.  Here the scripted
-- hot fires and a mapped leg carries the arrival onward, so the run
-- spans the subscribe frame and a delivery.
--
-- LOAD-BEARING on the horizon being a BOUND rather than a label: the
-- claim fails the moment any emit carries an instant above the fuel,
-- which is what a cascade minting its own id rather than inheriting
-- its trigger's would produce.
----------------------------------------------------------------------

mapped₀ : Closed (natᵗ ∷ []) natᵗ
mapped₀ = mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 100))) (input zero)

row-ids : Confirms (id-inheritance 1 mapped₀ (oneSlot (hotOnce 3)))
row-ids = here refl ∷ there (here refl) ∷ []
