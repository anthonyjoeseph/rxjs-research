----------------------------------------------------------------------
-- THE ONLINE CLAIM, READ OFF THE PIPELINE RATHER THAN OFF A PROGRAM.
----------------------------------------------------------------------

-- WHY THIS ONE IS REACHABLE WHERE THE README FAMILY IS NOT.  It is
-- stated over the BATCHING side rather than over a canonical program,
-- so it needs no evaluator harness to say something: the claim is plain
-- list computation, and nothing has to route a flattener through the
-- frame dispatch to compute.
--
-- NOT REACHED: any batching input that a real run produced, since the
-- rows below are hand-written envelope lists chosen to sit either side
-- of a group boundary rather than taken from an evaluation.

-- TARGET: batch-online @73ae89
module Probed.Pipeline-Claims where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Vec using ([]; _∷_)   -- contexts are Vecs; ∷/[] overload per type
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (InstEmit; _at_from_as_; init; value;
                           subscribe; delivery)

open import Verify-Batch-Simultaneous.Batch-Theorems using (batch-online)

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
