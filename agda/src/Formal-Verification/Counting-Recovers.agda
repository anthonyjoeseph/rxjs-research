-- HALF ONE of the proof: counting correctness. The batching machine,
-- fed the pipeline's emits BLIND (no clock, only init/close
-- registration counts), flushes exactly the groups the referee finds by
-- stamping the same emits and comparing clocks.
--
--   counting-recovers : … → impl-batchSimultaneous em e
--                         ≡ batchSpecL (stamped em e)
--
-- `counting-recovers` is a VALUE below, assembled from four named
-- postulates that factor the proof (see Roadmap.md §2 for the plan):
--
--   1. counting-factors — the counting pipeline reads only the TRACE:
--      running the composed machine equals a pure list function
--      (`countBatches`, defined here) of the grouped trace. Machine-
--      state induction; no grammar involved.
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
module Formal-Verification.Counting-Recovers where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous
open import Formal-Verification.Bridge

------------------------------------------------------------------------
-- the counting pipeline, reified as a pure function on the grouped
-- trace. `batchSimultaneousI` is batchSync ∘ endWith ∘ scan ∘ mergeMap;
-- on the trace side that is: the frame group becomes ONE syncB item,
-- every later emit its own asyncB item, endB last — then fold bStep and
-- collect the flushes.

bItems : List (List (Emit Val)) → List BItem
bItems []       = endB ∷ []
bItems (g ∷ gs) = syncB g ∷ (map asyncB (concatL gs) ++ (endB ∷ []))

flushOf : MemI → List (List Val)
flushOf m = maybe′ [] (λ vs → vs ∷ []) (MemI.cFlush m)

collectB : MemI → List BItem → List (List Val)
collectB m []       = []
collectB m (b ∷ bs) = flushOf (bStep m b) ++ collectB (bStep m b) bs

countBatches : List (List (Emit Val)) → List (List Val)
countBatches = collectB (mkMem [] nothing nothing) ∘′ bItems
  where
    _∘′_ : {A B C : Set} → (B → C) → (A → B) → A → C
    (g ∘′ f) x = g (f x)

------------------------------------------------------------------------
-- the three factors

postulate
  -- (1) the pipeline only sees the trace: machine-composition
  -- commutation, by induction on the input list with a state
  -- correspondence between the composed machine's state and
  -- (MemI × seen-first-input) folded over groups
  counting-factors :
    {n : ℕ} (em : Emissions n) (m : Inst n Val)
    → run (batchSimultaneousI m) (flatten em)
      ≡ countBatches (groupsOf m (flatten em))

  -- the trace invariant the counting machine relies on (candidate
  -- content in Roadmap.md §2.2: per non-frame group, the first emit's
  -- root owes exactly the group's emit count under the running
  -- registration totals, so the window drains at the group boundary
  -- and never across it)
  Accounted : List (List (Emit Val)) → Set

  -- (2) the pure counting theorem (v1: the BatchImpl/endgame layer)
  counting-groups :
    (gs : List (List (Emit Val))) → Accounted gs
    → countBatches gs ≡ batchSpecL (stampFrom 0 gs)

  -- (3) canonical programs keep their books: grammar induction with
  -- per-operator preservation lemmas (v1: Protocol.agda's trace
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

------------------------------------------------------------------------
-- tripwire: counting-factors holds BY COMPUTATION on the diamond — the
-- reification `countBatches` is the right one

private
  emX : Emissions 1
  emX = emissions ([] ∷ []) ((fzero , 5) ∷ [])

  eX : Exp 1
  eX = mergeE (srcE fzero) (mapE suc (srcE fzero))

  counting-factors-diamond :
    run (batchSimultaneousI (compile eX)) (flatten emX)
    ≡ countBatches (groupsOf (compile eX) (flatten emX))
  counting-factors-diamond = refl
