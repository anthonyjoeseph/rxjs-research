----------------------------------------------------------------------
-- THE THREE UNIVERSAL LAWS, AT THE ONLY PROGRAMS THAT REDUCE.
----------------------------------------------------------------------

-- WHAT THIS FILE IS EVIDENCE ABOUT, AND WHAT IT IS EVIDENCE OF BEING
-- UNREACHABLE.  Each law below quantifies over the whole grammar, so a
-- row picks one program and reports that the law holds THERE.  Both
-- sides compute: the evaluator renders a run and
-- `spec-batchSimultaneous` groups it, so a wrong grouping is a
-- different list and `refl` fails.
--
-- AND THE PROGRAM IS FLATTENER-FREE FOR A REASON THAT IS ITSELF THE
-- FINDING.  `evaluate↓` reaches its result through the reducibility
-- witness, whose frame dispatch hands a `thru-outer` frame to a LIVE
-- POSTULATE -- so a program routing through any of the three
-- flatteners leaves that application STUCK in the normal form and no
-- `refl` can decide anything about it.  The seven quantified instances
-- of this family are each hard-wired to a merge, so none of them can
-- be instantiated at all while that postulate stands, and the same
-- blocks every downstream claim read off a flattening program.  This
-- is recorded here rather than in those statements' own headers
-- because it is a fact about the EVALUATOR rather than about any of
-- them; it is owed where the block is, and the block is the frame
-- dispatch.
--
-- NOT REACHED: every flattening program, for the reason above; any
-- type other than `natᵗ`; any source at all, since the rows below are
-- read at the subscribe frame where a source-free program emits
-- everything.

-- TARGET: readme-batch-order-is-delivery-order @784389
-- TARGET: readme-take-counts-values @b13b90
-- TARGET: readme-one-subscribe-one-batch @cf4ec0
module Probed.Readme-Claims where

open import Data.List using (_∷_; [])
open import Data.Vec using ([])     -- contexts are Vecs; ∷/[] overload per type
open import Data.Nat using (s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; ofᵉ)

open import Readme-Theorems using
  (noSlots;
   readme-batch-order-is-delivery-order; readme-take-counts-values;
   readme-one-subscribe-one-batch)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- TWO VALUES IN ONE SUBSCRIBE BURST, which is the smallest shape that
-- can tell grouping from ordering: a law that dropped one, added one,
-- or split the instant gives a different list at every row below.
pair₀ : Closed Γ₀ natᵗ
pair₀ = ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])

----------------------------------------------------------------------
-- 1.  BATCHING ONLY GROUPS.  LOAD-BEARING: flattening the batches must
-- give back the raw stream, so a grouping that lost or duplicated
-- either value comes apart under `concat`.
----------------------------------------------------------------------

row-order : Confirms (readme-batch-order-is-delivery-order 0 pair₀ noSlots)
row-order = refl

----------------------------------------------------------------------
-- 2.  TAKE COUNTS VALUES, NOT BATCHES.  The one point where the law
-- says something a batch-counting `take` would not: both values are in
-- ONE batch and k is 1, so the row cuts a batch in half and a `take`
-- keeping whole batches keeps both.
----------------------------------------------------------------------

row-take : Confirms (readme-take-counts-values 0 1 pair₀ noSlots)
row-take = refl

----------------------------------------------------------------------
-- 3.  ONE SUBSCRIBE IS ONE BATCH.  LOAD-BEARING rather than the
-- vacuous `0 ≤ 1`: this program EMITS at the subscribe frame, so the
-- length being bounded is a claim about the burst staying one group
-- and not about there being nothing to group.
----------------------------------------------------------------------

row-one-batch : Confirms (readme-one-subscribe-one-batch pair₀ noSlots)
row-one-batch = s≤s z≤n
