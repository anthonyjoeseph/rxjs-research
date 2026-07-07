-- THE ENTRYPOINT. The one theorem this repository exists to prove:
--
--   formal-verification :
--     ∀ {n} (em : Emissions n) (e : Exp n) → Canonical e
--     → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
--
-- The clairvoyant referee (Spec/) and the blind machine
-- (Implementation/) agree on every program, on every run.
--
-- `formal-verification` is a VALUE, not a postulate: its proof term is
-- real, and every remaining gap is a named postulate below, consumed by
-- the proof. A postulate that cannot be proven as stated is a spec bug
-- to rework, not work around.
module Formal-Verification where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous

------------------------------------------------------------------------
-- the bridge between the two worlds: the implementation's protocol
-- trace, and the referee's clock stamped back onto it.
--
-- `trace` is DEFINED — it is just the compiled pipeline run over the
-- serialized world, before the batching machine consumes it.

trace : {n : ℕ} → Emissions n → Exp n → List (Emit Val)
trace em e = run (compile e) (flatten em)

postulate
  -- the validity domain (v1: Canonical + the fenced order corners):
  -- non-resetting shares, registration-canonical trees
  Canonical : {n : ℕ} → Exp n → Set

  -- the referee re-attaches the clock the Emissions define: frame
  -- values at t₀, async entry k's cascade at tick k+1, source i's
  -- completion cascade at tick K+1+i where K = length asyncs
  -- (v1: stamp / envOf's per-slot closes)
  stamp : {n : ℕ} → Emissions n → List (Emit Val) → List (Time × Val)

  -- THE TWO HALVES OF THE PROOF ------------------------------------

  -- (1) counting correctness: the batching machine, fed the pipeline's
  -- emits blind, flushes exactly the groups the referee finds by
  -- stamping the same emits and comparing clocks
  -- (v1: endgame — machine ≡ forgetT ∘ batchSpec ∘ stamp, proven for
  -- fragments; here stated over the full pipeline)
  counting-recovers :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → impl-batchSimultaneous em e ≡ batchSpecL (stamp em (trace em e))

  -- (2) trace faithfulness: stamping the implementation's trace yields
  -- EXACTLY the spec's timed denotation — value for value, instant for
  -- instant (v1: traceOf-ok + stamp-sound)
  trace-faithful :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → stamp em (trace em e) ≡ list (⟦ e ⟧ em ρ₀ t₀)

------------------------------------------------------------------------
-- THE THEOREM

formal-verification :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
formal-verification em e can =
  trans (counting-recovers em e can)
        (cong batchSpecL (trace-faithful em e can))

------------------------------------------------------------------------
-- sanity corollary: the diamond, verified. One source, two arms, one
-- batch per .next() — the program this project began with.

diamondE : Exp 1
diamondE = mergeE (srcE fzero) (mapE suc (srcE fzero))

postulate
  diamond-canonical : Canonical diamondE

diamond-verified :
  (em : Emissions 1)
  → impl-batchSimultaneous em diamondE ≡ spec-batchSimultaneous em diamondE
diamond-verified em = formal-verification em diamondE diamond-canonical
