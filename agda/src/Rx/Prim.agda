module Rx.Prim where

open import Data.Nat     using (ℕ; zero; suc)
open import Data.List    using (List)

------------------------------------------------------------------
-- Time, ids, emissions
------------------------------------------------------------------

Tick Fuel Ordinal : Set
Tick = ℕ ; Fuel = ℕ ; Ordinal = ℕ

-- Sync-subscription gas: a DEDICATED lazy Peano numeral, deliberately
-- NOT ℕ.  The needed budget is a tower of exponentials (chained
-- obs-typed scans convert value count into subscription depth, one
-- exponentiation per scan — see Verify-Budget-Sufficient), and BUILTIN
-- ℕ compiles to a strict Integer that would have to materialize the
-- whole tower at the first pattern match.  A plain datatype compiles
-- to lazy Haskell constructors: a decrement peels one `gs` thunk, so
-- forcing is bounded by the work the machine actually does.
data Gas : Set where
  g0 : Gas
  gs : Gas → Gas

gasDouble : Gas → Gas
gasDouble g0     = g0
gasDouble (gs g) = gs (gs (gasDouble g))

gasPow2 : Gas → Gas                 -- 2^g, lazily
gasPow2 g0     = gs g0
gasPow2 (gs g) = gasDouble (gasPow2 g)

gasTower : ℕ → Gas                  -- tower of 2s of height h (tower 0 = 1)
gasTower zero    = gs g0
gasTower (suc h) = gasPow2 (gasTower h)

-- n literal-backed units in front of g.  The ℕ stays a GMP literal
-- (typechecker) / strict Integer (compiled), so each peel is an O(1)
-- decrement — a fast path covering every physically runnable
-- consumption, with the tower tail behind it never forced
gasPad : ℕ → Gas → Gas
gasPad zero    g = g
gasPad (suc n) g = gs (gasPad n g)

Id : Set                            -- an INSTANT (one arrival's cascade); spec groups by this
Id = ℕ                              -- concrete so the spec can compare; harness compares up to renaming
-- Ids mint from ARRIVAL POSITION: 0 is the subscribe frame, then
-- 1, 2, … per cascade (the drain counter).  Distinctness is
-- structural, instants strictly increase along the stream (the
-- Protocol's horizon check reads exactly this), and timing-invariance
-- holds up to ≡, not just ≈ — a retiming that preserves arbitration
-- order preserves the ids themselves.

Source : Set                        -- a SOURCE observable; impl counts registrations of these
Source = ℕ                          -- concrete so the scheduler can mint & compare; the harness compares up to renaming anyway

-- The protocol (v1's, with the instant id moved onto the emission).
-- Batching is decided downstream by counting registrations, never by
-- comparing clocks: init/close traffic maintains the live-registration
-- count per source, and for each arrival every live registration chain
-- of that source forwards EXACTLY ONE InstEmit (possibly valueless —
-- emits are emptied, never swallowed) — UNLESS an operator cuts it
-- mid-cascade before its turn: a cut chain delivers nothing (as in
-- rxjs), and its `close … cutPending` on the cutting emit tells the
-- batcher to cancel the emit it was owed.  So a batcher owes
-- count(source) emits for an instant, cancels one per cutPending, and
-- flushes when the remainder have arrived.
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
  cut        : CloseReason          -- an operator ended it (take's cut, switch switching
                                    -- away) AFTER it delivered this instant (or it was
                                    -- born mid-instant and owed nothing)
  cutPending : CloseReason          -- an operator ended it BEFORE it delivered the emit
                                    -- it owed this instant — the victim will never pay,
                                    -- so the reader cancels one owed count against it
                                    -- (a cut registration delivers NOTHING, as in rxjs:
                                    -- take(1)(merge(s,s)) — the second chain is silent)
  exhausted  : CloseReason          -- the source ran dry on its own
  dried      : CloseReason          -- the EVALUATOR ran out of sync fuel — the dry
                                    -- marker (Rx.Evaluator.dryBurst), never emitted by
                                    -- any machine rule.  Detection is by THIS REASON
                                    -- (hasDry), not by a sentinel source: Source is an
                                    -- unbounded ℕ and mints are breadth-many, so no
                                    -- numeric sentinel is collision-proof

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