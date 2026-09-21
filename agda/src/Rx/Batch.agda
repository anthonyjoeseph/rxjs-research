-- THE BATCHING OPERATOR, AS A PROGRAM.
--
-- `batchSimultaneousᵖ` is a former over the PLAIN tree: it takes a
-- stream of machine envelopes and hands back a stream of envelopes
-- carrying batched payloads.  It lives here rather than in a
-- verification module because it is an operator and not a claim -- the
-- harness runs it, and the proof quantifies over it.
--
-- IT IS STILL A POSTULATE.  Its home is the plain tree and its body is
-- a `scanᵉ` carrying the batcher's state with a `mapᵉ` projecting the
-- emit; see the PROOF-STATE row (tier 1, SHAPE).  Until that body
-- exists the harness typechecks against it but cannot RUN it: the GHC
-- backend has nothing to compile for a postulate.  That is deliberate
-- and known -- the wiring is what is being landed, not the operator.
--
-- IT MUST SUBSCRIBE NOTHING.  A `mergeAllᵉ` formulation moves the mint
-- counter and leaves every id downstream shifted by a renaming, so the
-- two runs the theorem compares would no longer share a scheduler.  A
-- scan plus a projection subscribes nothing and therefore mints
-- nothing.
module Rx.Batch where

open import Data.List using (List)

open import Rx.Exp      using (Ctx; Ty; Exp; listᵗ)
open import Rx.Envelope using (machineEmitᵗ)

postulate
  batchSimultaneousᵖ :
    ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
    → Exp Γ Δᵍ Δ Θ (machineEmitᵗ a)
    → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
