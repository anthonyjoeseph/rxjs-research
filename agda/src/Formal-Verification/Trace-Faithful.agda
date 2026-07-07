-- HALF TWO of the proof: trace faithfulness. Stamping the
-- implementation's trace yields EXACTLY the spec's timed denotation —
-- value for value, instant for instant, in order.
--
--   trace-faithful : … → stamped em e ≡ emits (⟦ e ⟧ em ρ₀ t₀)
--
-- `trace-faithful` is a VALUE below, assembled from the simulation
-- relation `Tracks` and its two named postulates (see Roadmap.md §3):
--
--   Tracks em m d — "machine m tracks denotation d in world em": for
--   EVERY spawn position j (0 = the real frame, j ≥ 1 = a synthesized
--   empty frame at input j, then the remaining inputs — spawnInput
--   semantics), m's grouped value trace from j, stamped positionally,
--   equals `emits (d (j , 0))`. The quantification over j is the
--   generalization that lets the joins' induction go through: a join
--   subscribes its inners at arbitrary positions, and Tracks is
--   exactly the statement it needs about each.
--
--   1. tracks-compile — every canonical program's compiled machine
--      tracks its denotation. Grammar induction (generalized over
--      share environments) with one lemma per operator: the only
--      place `e` and `Canonical` matter.
--   2. tracks-stamped — extraction at the root: the j = 0 case of
--      Tracks IS the theorem (the real frame is spawn position 0, and
--      `stamped` is the positional stamping of the grouped trace).
--      Near-definitional given the right definition of Tracks.
--
-- `Tracks` itself is postulated as an abstract Set for now — its
-- candidate definition is written out in Roadmap.md §3.1, and pinning
-- it down IS the first work item of this half: once Tracks is a real
-- definition, tracks-stamped should be a short proof, and the
-- per-operator lemmas acquire provable statements.
module Formal-Verification.Trace-Faithful where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous
open import Formal-Verification.Bridge

------------------------------------------------------------------------
-- the simulation relation, now DEFINED (Roadmap.md §3.1).
--
-- `spawnFlatten em j` is the input stream a machine spawned at position
-- j experiences: the j-th input, put through `spawnInput` (identity on
-- the real frame at j = 0, a synthesized empty frame at j ≥ 1), then the
-- strict suffix after it — exactly what a join hands a freshly
-- subscribed inner. Note `spawnFlatten em 0 ≡ flatten em` by
-- computation: `spawnInput (frame _) = frame _` and `drop 1` peels the
-- frame off, so position 0 is literally the real run.

spawnFlatten : {n : ℕ} → Emissions n → ℕ → List (In n)
spawnFlatten em j = spawnInput (at j (flatten em) end) ∷ drop (suc j) (flatten em)

-- machine m tracks denotation d in world em: for EVERY spawn position j,
-- m's grouped value trace from j, stamped positionally (first group at
-- tick j — the spawned machine's synchronous flush rides instant j),
-- equals the denotation subscribed at (j , 0). The ∀-over-j is what
-- makes the joins' induction go through: a join subscribes its inners at
-- arbitrary positions, and Tracks is exactly the per-inner statement.
Tracks : {n : ℕ} → Emissions n → Inst n Val → Inner → Set
Tracks em m d =
  (j : ℕ) → ltℕ j (length (flatten em)) ≡ true
  → stampFrom j (groupsOf m (spawnFlatten em j)) ≡ emits (d (j , 0))

postulate
  -- (1) the grammar induction — the only place `e` and `Canonical`
  -- matter (Roadmap.md §3.2)
  tracks-compile :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → Tracks em (compile e) (λ u → ⟦ e ⟧ em ρ₀ u)

-- (2) extraction at the root: spawn position 0 IS the real frame
-- (`spawnFlatten em 0 ≡ flatten em`), and `stampFrom 0` is `stamped`'s
-- clock, so the theorem is the j = 0 instance of Tracks. `flatten em`
-- always starts with the frame, so `ltℕ 0 (length …) ≡ true` is refl.
tracks-stamped :
  {n : ℕ} (em : Emissions n) (m : Inst n Val) (d : Inner)
  → Tracks em m d
  → stampFrom 0 (groupsOf m (flatten em)) ≡ emits (d t₀)
tracks-stamped em m d tr = tr 0 refl

------------------------------------------------------------------------
-- THE HALF (stamped unfolds definitionally to the factored form)

trace-faithful :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → stamped em e ≡ emits (⟦ e ⟧ em ρ₀ t₀)
trace-faithful em e can =
  tracks-stamped em (compile e) (λ u → ⟦ e ⟧ em ρ₀ u)
                 (tracks-compile em e can)

------------------------------------------------------------------------
-- tripwires: the Tracks DEFINITION is right — a spawned `of` emits
-- everything at its spawn tick, a spawned source sees only the strict
-- suffix. Checked at position 0 AND a later position, both sides
-- normalizing end to end. A refl here that could not fail would prove
-- nothing, so these are pinned against the concrete worlds below.

private
  emT : Emissions 1
  emT = emissions ([] ∷ []) ((fzero , 5) ∷ [])

  -- a spawned `of` at position 0: all values at tick 0
  of-tracks-0 :
    stampFrom 0 (groupsOf (compile (ofE (1 ∷ 2 ∷ []))) (spawnFlatten emT 0))
    ≡ emits (⟦ ofE (1 ∷ 2 ∷ []) ⟧ emT ρ₀ (0 , 0))
  of-tracks-0 = refl

  -- a spawned `of` at position 1: the synthesized frame flushes all
  -- values at tick 1 (the trigger's instant)
  of-tracks-1 :
    stampFrom 1 (groupsOf (compile (ofE (1 ∷ 2 ∷ []))) (spawnFlatten emT 1))
    ≡ emits (⟦ ofE (1 ∷ 2 ∷ []) ⟧ emT ρ₀ (1 , 0))
  of-tracks-1 = refl

  -- a spawned source at position 1 sees only what comes strictly after:
  -- the .next(5) has already passed, so it observes nothing
  src-tracks-1 :
    stampFrom 1 (groupsOf (compile (srcE fzero)) (spawnFlatten emT 1))
    ≡ emits (⟦ srcE fzero ⟧ emT ρ₀ (1 , 0))
  src-tracks-1 = refl
