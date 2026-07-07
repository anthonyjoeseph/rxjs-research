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

postulate
  -- the simulation relation (candidate definition: Roadmap.md §3.1)
  Tracks : {n : ℕ} → Emissions n → Inst n Val → Inner → Set

  -- (1) the grammar induction
  tracks-compile :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → Tracks em (compile e) (λ u → ⟦ e ⟧ em ρ₀ u)

  -- (2) extraction at the root (spawn position 0 = the real frame)
  tracks-stamped :
    {n : ℕ} (em : Emissions n) (m : Inst n Val) (d : Inner)
    → Tracks em m d
    → stampFrom 0 (groupsOf m (flatten em)) ≡ emits (d t₀)

------------------------------------------------------------------------
-- THE HALF (stamped unfolds definitionally to the factored form)

trace-faithful :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → stamped em e ≡ emits (⟦ e ⟧ em ρ₀ t₀)
trace-faithful em e can =
  tracks-stamped em (compile e) (λ u → ⟦ e ⟧ em ρ₀ u)
                 (tracks-compile em e can)
