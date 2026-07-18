module Rx.Prim where

open import Data.Nat     using (ℕ; suc; _+_; _*_; ⌊_/2⌋)
open import Data.List    using (List)

------------------------------------------------------------------
-- Time, ids, emissions
------------------------------------------------------------------

Tick Fuel Ordinal : Set
Tick = ℕ ; Fuel = ℕ ; Ordinal = ℕ

Id : Set                            -- an INSTANT (one arrival's cascade); spec groups by this
Id = ℕ                              -- concrete so the spec can compare; harness compares up to renaming

-- deterministic, injective minting from arrival identity (Cantor
-- pairing): distinct (tick, ordinal) ⇒ distinct instant id, so the spec's
-- group-by-id never merges two cascades. The exact numerals are
-- irrelevant — the harness compares streams up to id renaming.
freshId : Tick → Ordinal → Id
freshId t o = ⌊ (t + o) * suc (t + o) /2⌋ + o

Source : Set                        -- a SOURCE observable; impl counts registrations of these
Source = ℕ                          -- concrete so the scheduler can mint & compare; the harness compares up to renaming anyway

-- The protocol (v1's, with the instant id moved onto the emission).
-- Batching is decided downstream by counting registrations, never by
-- comparing clocks: init/close traffic maintains the live-registration
-- count per source, and for each arrival every live registration chain
-- of that source forwards EXACTLY ONE InstEmit (possibly valueless —
-- emits are emptied, never swallowed), so a batcher owes
-- count(source) emits for an instant and flushes when they've arrived.
-- Writer-asserted facts (the reader checks, never reconstructs):
-- every mint site knows definitively whether it is a subscription
-- burst or an arrival delivery, and why a registration ended.
data EmitKind : Set where
  subscribe : EmitKind              -- a subscription's own burst — owes nothing, pays nothing
  delivery  : EmitKind              -- an arrival emit — pays the instant's owed count
  plumbing  : EmitKind              -- a share's connect burst forwarded up its first
                                    -- subscriber: real protocol traffic for the root's
                                    -- ledger, but its registrations belong to the share
                                    -- (they survive the subscriber), so the operators it
                                    -- flows through take no lifecycle signal from it

data CloseReason : Set where
  cut       : CloseReason           -- an operator ended it (take's cut, switch switching away)
  exhausted : CloseReason           -- the source ran dry on its own

data InstEvent (A : Set) : Set where
  init     : Source → InstEvent A   -- a registration chain of this source came alive
  value    : A → InstEvent A
  close    : Source → CloseReason → InstEvent A   -- a registration of this source ended
  handoff  : Source → InstEvent A   -- this share fans out next, still inside this instant
  complete : InstEvent A            -- the stream completes as part of THIS emit (concatAll grafts on it)

-- Everything is an InstEmit stream — including batchSimultaneous's
-- output (InstEmit (List A)): a batch keeps its instant id and stays a
-- protocol citizen, so a batched stream feeds every primitive again
-- (e.g. merge it with itself and batch once more).
record InstEmit (A : Set) : Set where
  constructor _at_from_as_
  field events  : List (InstEvent A)  -- everything caused by one incoming emit, COALESCED
        instant : Id                  -- the instant it belongs to
        source  : Source              -- the arrival's source (owed = its live-registration count)
        kind    : EmitKind            -- who minted it: a subscription or an arrival cascade

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