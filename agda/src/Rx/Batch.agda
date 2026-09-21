-- THE BATCHING OPERATOR, AS A PROGRAM.
--
-- `batchSimultaneousᵖ` is a former over the PLAIN tree: it takes a
-- stream of machine envelopes and hands back a stream of envelopes
-- carrying batched payloads.  It lives here rather than in a
-- verification module because it is an operator and not a claim -- the
-- harness runs it, and the proof quantifies over it.
--
-- IT IS A `scanᵉ` FOR THE STATE AND A `mergeAllᵉ` TO EMPTY FOR THE
-- SILENCE, and the second half is what took a while to arrive at.  A
-- batcher is one value in and ZERO OR ONE values out -- it accumulates
-- while an instant is open and emits when the instant closes -- while
-- `scanᵉ` is one in and one out.  The missing capability is DECLINING
-- to emit, and rxjs spells it `mergeMap` to `EMPTY`: map each carried
-- state to an inner observable that is either a singleton or empty,
-- and flatten.
--
-- THE OLD NOTE HERE SAID `mergeAllᵉ` WAS BARRED, AND THAT WAS WRONG.
-- It read "a `mergeAllᵉ` formulation moves the mint counter and leaves
-- every id downstream shifted by a renaming, so the two runs the
-- theorem compares would no longer share a scheduler."  Measured, it
-- does not: `subs-merge-all` and `subscribeInner⇓` mint at `nodeᵏ`
-- only, never at `sourceᵏ` or `regᵏ`, and node instances live in the
-- registry and never reach the wire.  Only `subs-defer` mints a
-- source, and a synchronous inner never goes through it.  `subs-scan`
-- mints a `nodeᵏ` too, so the shape the note recommended was paying
-- the same cost it warned about.  The probe is
-- `Probed.MergeMap-Empty`: an identity `mergeMap` around an elaborated
-- program decodes to the same stream as the program alone, and a
-- `mergeMap` to `emptyᵉ` decodes to nothing.
--
-- WHICH EMPTY, AND THE TWO ARE DELIBERATELY DIFFERENT.  This operator
-- lives BELOW the elaboration, on envelopes, so its silence is the
-- plain `emptyᵉ`, which emits nothing at all.  An author-facing
-- `filter` would live above it and use `emptyˢ`, which elaborates to
-- `ofᵖ frame []` and still brackets a subscribe frame -- an `init` and
-- a `complete` -- because in srxjs the inner EMPTY genuinely is
-- subscribed.  Using the simul one here would put a frame on the wire
-- for every value the batcher declines to emit.
module Rx.Batch where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp      using (Ctx; Ty; Exp; Tm; Fn; listᵗ; unitᵗ; _×ᵗ_; _+ᵗ_; varᵗ; unit̂; fstᵗ; sndᵗ; pairᵗ; nilᵗ; consᵗ;
  inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; eqᵘ; appendᵗ; renTm; strmᵗ; ofᵉ; emptyᵉ; mapᵉ; scanᵉ;
  mergeAllᵉ)
open import Rx.Envelope using (machineEmitᵗ; eventsᵛ; instantᵛ; splitEventsᵛ; reassembleᵛ)

------------------------------------------------------------------
-- The carrier.
------------------------------------------------------------------

-- THREE FIELDS, AND THE SECOND IS WHY NO TOKEN IS EVER WRITTEN.  The
-- open batch's values; the emit that OPENED it, or nothing yet; and
-- what this step wants to emit, or nothing.  Both optionals are
-- `unitᵗ +ᵗ _`, so the seed is `inlᵗ unit̂` twice and carries no
-- `uniqᵗ` at all -- which matters, because `uniqᵗ` has NO term former.
-- It is introduced only by `mintᵉ`'s binder, deliberately, so that no
-- program can write a token already in use.  A carrier that had to
-- hold a whole envelope at the seed would be unwritable for exactly
-- the reason forgery is; the case with no token is precisely the case
-- with nothing to emit, so EMPTY closes that hole and the bar stays
-- fully intact.  This operator never writes a token, it only forwards
-- one it received.
BatchStᵗ : Ty → Ty
BatchStᵗ a = listᵗ a
           ×ᵗ ((unitᵗ +ᵗ machineEmitᵗ a) ×ᵗ (unitᵗ +ᵗ machineEmitᵗ (listᵗ a)))

module _ {n} {Γ : Ctx n} {Δᵍ Δ : List Ty} where

  valuesᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (BatchStᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a)
  valuesᵇ st = fstᵗ st

  openerᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (BatchStᵗ a)
          → Tm Γ Δᵍ Δ Θ (unitᵗ +ᵗ machineEmitᵗ a)
  openerᵇ st = fstᵗ (sndᵗ st)

  pendingᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (BatchStᵗ a)
           → Tm Γ Δᵍ Δ Θ (unitᵗ +ᵗ machineEmitᵗ (listᵗ a))
  pendingᵇ st = sndᵗ (sndᵗ st)

  mkStᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (listᵗ a)
        → Tm Γ Δᵍ Δ Θ (unitᵗ +ᵗ machineEmitᵗ a)
        → Tm Γ Δᵍ Δ Θ (unitᵗ +ᵗ machineEmitᵗ (listᵗ a))
        → Tm Γ Δᵍ Δ Θ (BatchStᵗ a)
  mkStᵇ vs op pd = pairᵗ vs (pairᵗ op pd)

  -- this emit's own payloads, at the author's type
  payloadsᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a)
  -- `b` is pinned because only the payload component is used, so
  -- nothing else would determine the retagging type
  payloadsᵇ {a = a} e = fstᵗ (sndᵗ (splitEventsᵛ {b = a} (eventsᵛ e)))

  -- A FINISHED BATCH: one value event carrying the whole run of
  -- values, under the OPENING emit's own instant, source and kind.
  -- `reassembleᵛ` is what says an operator of this shape may change
  -- the payload type and nothing else; the bookkeeping is retagged at
  -- the batch type because an event's type mentions its payload.
  closeBatchᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a)
              → Tm Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
  closeBatchᵇ {a = a} b vs =
    reassembleᵛ b (fstᵗ sp) (consᵗ vs nilᵗ) (sndᵗ (sndᵗ sp))
    where
    sp = splitEventsᵛ {b = listᵗ a} (eventsᵛ b)

------------------------------------------------------------------
-- The step: a basic port of `stepBatch` from
-- typescript/src/batch-simultaneous.ts.
------------------------------------------------------------------

-- WHAT IT KEEPS: the batch is per INSTANT.  An emit at the instant the
-- batch was opened on extends it; an emit at a NEW instant closes the
-- old batch into the pending slot and opens a fresh one.  `eqᵘ` is the
-- only eliminator `uniqᵗ` has, and it is the whole of the grouping
-- rule.
--
-- WHAT IT DROPS, AND A READER SHOULD NOT MISTAKE THIS FOR THE FINISHED
-- OPERATOR.  Two things, both named rather than hidden:
--
--   (i) THE OWED/LIVE ARITHMETIC.  In the TypeScript a batch flushes
--       the moment an instant's obligations reach zero (`paidOff`),
--       which is `Rx.Protocol`'s automaton run in producing mode.
--       Here a batch closes only when a LATER instant arrives, so the
--       flush is late rather than absent.  The state has room for the
--       `live`/`owed` tables -- they are data, so they are `Ty`s --
--       and the pending slot is already the place a flush announces
--       itself, so adding it is filling fields in rather than changing
--       the shape.
--
--   (ii) THE FINAL FLUSH.  `foldBatch` ends with `flushBatch`, and a
--        `scanᵉ` has no end hook, so the last instant's batch is never
--        emitted.  That needs the source's own `complete` to be
--        treated as a flush trigger -- which is reachable, since
--        `splitEventsᵛ` already hands back the completion flag this
--        code currently ignores.
stepBatchᵇ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
           → Fn Γ Δᵍ Δ Θ (BatchStᵗ a ×ᵗ machineEmitᵗ a) (BatchStᵗ a)
stepBatchᵇ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {a = a} = body
  where
  P : Ty
  P = BatchStᵗ a ×ᵗ machineEmitᵗ a

  pr : Tm Γ Δᵍ Δ (P ∷ Θ) P
  pr = varᵗ (here refl)

  -- weaken past the variable a `caseᵗ` arm binds
  ↑ : ∀ {x r} → Tm Γ Δᵍ Δ (P ∷ Θ) r → Tm Γ Δᵍ Δ (x ∷ P ∷ Θ) r
  ↑ = renTm (λ z → z) (λ z → z) there

  stᵇ : Tm Γ Δᵍ Δ (P ∷ Θ) (BatchStᵗ a)
  stᵇ = fstᵗ pr

  emitᵇ : Tm Γ Δᵍ Δ (P ∷ Θ) (machineEmitᵗ a)
  emitᵇ = sndᵗ pr

  valsᵇ : Tm Γ Δᵍ Δ (P ∷ Θ) (listᵗ a)
  valsᵇ = payloadsᵇ emitᵇ

  -- nothing open yet: this emit opens the first batch, and there is
  -- nothing to hand on
  fresh : ∀ {x} → Tm Γ Δᵍ Δ (x ∷ P ∷ Θ) (BatchStᵗ a)
  fresh = mkStᵇ (↑ valsᵇ) (inrᵗ (↑ emitᵇ)) (inlᵗ unit̂)

  -- a batch is open, and `b` is the emit that opened it
  onOpen : Tm Γ Δᵍ Δ (machineEmitᵗ a ∷ P ∷ Θ) (BatchStᵗ a)
  onOpen =
    ifᵗ (primᵗ eqᵘ (pairᵗ (instantᵛ (↑ emitᵇ)) (instantᵛ b)))
        -- same instant: extend, keep the opener, emit nothing
        (mkStᵇ (appendᵗ (↑ (valuesᵇ stᵇ)) (↑ valsᵇ)) (inrᵗ b) (inlᵗ unit̂))
        -- new instant: close the old batch into the pending slot and
        -- open a fresh one on this emit
        (mkStᵇ (↑ valsᵇ) (inrᵗ (↑ emitᵇ))
               (inrᵗ (closeBatchᵇ b (↑ (valuesᵇ stᵇ)))))
    where
    b : Tm Γ Δᵍ Δ (machineEmitᵗ a ∷ P ∷ Θ) (machineEmitᵗ a)
    b = varᵗ (here refl)

  body : Tm Γ Δᵍ Δ (P ∷ Θ) (BatchStᵗ a)
  body = caseᵗ (openerᵇ stᵇ) fresh onOpen

------------------------------------------------------------------
-- The projection: this is where a step DECLINES to emit.
------------------------------------------------------------------

-- ONE INNER OBSERVABLE PER CARRIED STATE: a singleton when the step
-- closed a batch, `emptyᵉ` when it did not.  `mergeAllᵉ` then flattens,
-- and a step that declined contributes nothing to the stream at all.
-- This is `mergeMap` to `EMPTY`, which is how rxjs spells `filter`
-- when the predicate needs state.
flushOrEmptyᵇ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
              → Fn Γ Δᵍ Δ Θ (BatchStᵗ a) (Rx.Exp.obs (machineEmitᵗ (listᵗ a)))
flushOrEmptyᵇ = caseᵗ (pendingᵇ (varᵗ (here refl)))
                  (strmᵗ emptyᵉ)
                  (strmᵗ (ofᵉ (varᵗ (here refl) ∷ [])))

------------------------------------------------------------------

batchSimultaneousᵖ :
  ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ a)
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
batchSimultaneousᵖ e =
  mergeAllᵉ nothing (mapᵉ flushOrEmptyᵇ (scanᵉ stepBatchᵇ seed e))
  where
  seed = pairᵗ nilᵗ (pairᵗ (inlᵗ unit̂) (inlᵗ unit̂))
