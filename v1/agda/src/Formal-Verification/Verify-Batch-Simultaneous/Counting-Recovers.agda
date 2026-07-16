-- HALF ONE of the proof: counting correctness. The batching machine,
-- fed the pipeline's emits BLIND (no clock, only init/close
-- registration counts), flushes exactly the groups the referee finds by
-- stamping the same emits and comparing clocks.
--
--   counting-recovers : … → impl-batchSimultaneous em e
--                         ≡ batchSpecL (stamped em e)
--
-- `counting-recovers` is a VALUE below, assembled from the (now proven)
-- `counting-factors` and three named postulates (see Roadmap.md §2):
--
--   1. counting-factors (PROVEN, Counting-Factors.agda) — the counting
--      pipeline reads only the TRACE: running the composed machine
--      equals a pure list function (`countBatches`) of the grouped
--      trace. Machine-composition commutation; no grammar involved.
--   2. counting-groups — the pure counting theorem: on any Accounted
--      grouped trace, countBatches equals batchSpecL of the positional
--      stamping. List induction with a window invariant; no machines,
--      no grammar.
--   3. compile-accounted — every compiled canonical program's grouped
--      trace IS Accounted. Grammar induction; the only place `e` and
--      `Canonical` matter.
--
-- The postulated `Accounted` is the interface between 2 and 3: the
-- protocol trace invariant the counting machine relies on. Its content
-- is settled by proving counting-groups first (what the window
-- invariant needs is what it says) — see the roadmap.
module Formal-Verification.Verify-Batch-Simultaneous.Counting-Recovers where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous
open import Formal-Verification.Verify-Batch-Simultaneous.Bridge
-- the counting reification (bItems / flushOf / collectB / countBatches)
-- and the PROVEN counting-factors both live here now
open import Formal-Verification.Verify-Batch-Simultaneous.Counting-Factors

------------------------------------------------------------------------
-- the two remaining factors

postulate
  -- the trace invariant the counting machine relies on (candidate
  -- content in Roadmap.md §2.2: per non-frame group, the first emit's
  -- root owes exactly the group's emit count under the running
  -- registration totals, so the window drains at the group boundary
  -- and never across it)
  Accounted : List (List (Emit Val)) → Set

  -- (2) the pure counting theorem (previously: the BatchImpl/endgame layer)
  counting-groups :
    (gs : List (List (Emit Val))) → Accounted gs
    → countBatches gs ≡ batchSpecL (stampFrom 0 gs)

  -- (3) canonical programs keep their books: grammar induction with
  -- per-operator preservation lemmas (previously: Protocol.agda's trace
  -- validity + ranked delivery)
  compile-accounted :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → Accounted (groupsOf (compile e) (flatten em))

------------------------------------------------------------------------
-- THE HALF, as their composition (impl-batchSimultaneous and stamped
-- unfold definitionally to the factored forms)

counting-recovers :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ batchSpecL (stamped em e)
counting-recovers em e can =
  trans (counting-factors em (compile e))
        (counting-groups (groupsOf (compile e) (flatten em))
                         (compile-accounted em e can))
