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
-- AND THE ID ROW IS READ AT A SOURCE-FREE PROGRAM, WHICH IS WEAKER THAN
-- IT WAS AND IS THE STRONGEST SHAPE AVAILABLE.  The statement now
-- quantifies over an ENVELOPE-typed program, so a source has to reach
-- it through a slot at the envelope, and the only def a probe can put
-- there without forging a machine token is one the elaboration built --
-- which is already minted.  Run that way the decoded instant came back
-- equal to the def's own payload literal rather than to any frame,
-- which is what a decode reading one layer looks like when two are
-- present.  That is a finding about elaborating a slot and not about
-- this statement, so it is owed at the elaboration and recorded there;
-- the row below drops the source rather than standing on a program
-- whose envelope depth is in doubt.
--
-- NOT REACHED: any program whose evaluation enters a flattening node,
-- for the reason the sibling probe records; any program with a SOURCE
-- at all, for the reason above; and any batching input that a real run
-- produced, since the online rows are hand-written envelope lists
-- chosen to sit either side of a group boundary rather than taken
-- from an evaluation.

-- TARGET: batch-online @73ae89
-- TARGET: id-inheritance @76ab0d
module Probed.Pipeline-Claims where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Vec using ([]; _∷_)   -- contexts are Vecs; ∷/[] overload per type
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (InstEmit; _at_from_as_; init; value;
                           subscribe; delivery)
open import Rx.Exp using (Ctx; natᵗ; Closed)
open import Rx.SExp using (ofˢ; natˢ; emitᵗ)
open import Rx.Elaborate using (elaborate)
open import Rx.Slots using (Slots)

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
-- LOAD-BEARING on the horizon being a BOUND rather than a label, which
-- it still is at this program: the single emit carries instant 1
-- against `horizon 1`, so the id sits EXACTLY at the bound and one more
-- than the horizon admits would refute the row.  What a source would
-- have bought on top of that is a second instant, and the header above
-- says why none is available.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []

noSlots : Slots Γ₀
noSlots ()

free₀ : Closed Γ₀ (emitᵗ natᵗ)
free₀ = elaborate (ofˢ (natˢ 3 ∷ []))

row-ids : Confirms (id-inheritance 1 free₀ noSlots)
row-ids = there (here refl) ∷ []
