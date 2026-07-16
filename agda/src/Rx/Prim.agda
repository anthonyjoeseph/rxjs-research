module Rx.Prim where

open import Data.Nat     using (ℕ)
open import Data.List    using (List)

------------------------------------------------------------------
-- Time, ids, emissions
------------------------------------------------------------------

Tick Fuel Ordinal : Set
Tick = ℕ ; Fuel = ℕ ; Ordinal = ℕ

postulate
  Id      : Set                     -- an INSTANT (one arrival's cascade); spec groups by this
  freshId : Tick → Ordinal → Id     -- deterministic minting from arrival identity
  Source  : Set                     -- a SOURCE observable; impl counts registrations of these

-- The protocol (v1's, with the instant id moved onto the emission).
-- Batching is decided downstream by counting registrations, never by
-- comparing clocks: init/close traffic maintains the live-registration
-- count per source, and for each arrival every live registration chain
-- of that source forwards EXACTLY ONE InstEmit (possibly valueless —
-- emits are emptied, never swallowed), so a batcher owes
-- count(source) emits for an instant and flushes when they've arrived.
data InstEvent (A : Set) : Set where
  init     : Source → InstEvent A   -- a registration chain of this source came alive
  value    : A → InstEvent A
  close    : Source → InstEvent A   -- a registration of this source ended (take cuts, switches away)
  complete : InstEvent A            -- the stream completes as part of THIS emit (concatAll grafts on it)

-- Everything is an InstEmit stream — including batchSimultaneous's
-- output (InstEmit (List A)): a batch keeps its instant id and stays a
-- protocol citizen, so a batched stream feeds every primitive again
-- (e.g. merge it with itself and batch once more).
record InstEmit (A : Set) : Set where
  constructor _at_from_
  field events  : List (InstEvent A)  -- everything caused by one incoming emit, COALESCED
        instant : Id                  -- the instant it belongs to
        source  : Source              -- the arrival's source (owed = its live-registration count)

------------------------------------------------------------------
-- Timed inputs (delta-encoded; real gap = suc wait, so per-source
-- strict monotonicity holds by construction; ticks are logical
-- order, not wall-clock — see timing-invariance)
------------------------------------------------------------------

record Timed (A : Set) : Set where
  constructor after_,_
  field wait : ℕ            -- gap = suc wait
        val  : A

data ObservableInput (A : Set) : Set where
  hot  : (async : List (Timed A))                 → ObservableInput A   -- anchor 0
  cold : (sync : List A) (async : List (Timed A)) → ObservableInput A   -- anchor = subscription tick