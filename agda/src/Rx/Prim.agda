module Rx.Prim where

open import Data.Nat     using (ℕ)
open import Data.List    using (List)

------------------------------------------------------------------
-- Time, ids, emissions
------------------------------------------------------------------

Tick Fuel Ordinal : Set
Tick = ℕ ; Fuel = ℕ ; Ordinal = ℕ

Id : Set                            -- an INSTANT (one arrival's cascade); spec groups by this
Id = ℕ                              -- concrete so the spec can compare; harness compares up to renaming
-- Ids mint from ARRIVAL POSITION: 0 is the subscribe frame, then
-- 1, 2, … per cascade (the drain counter).  Distinctness is
-- structural, instants strictly increase along the stream (the
-- Protocol's horizon check reads exactly this), and timing-invariance
-- holds up to ≡, not just ≈ — a retiming that preserves arbitration
-- order preserves the ids themselves.
--
-- AND THE ORDER IS LOAD-BEARING, SO THIS IS NOT A TOKEN.  `Spec`
-- compares instants and does nothing else with one, which makes this
-- read as a type needing only decidable equality — and it is not one.
-- `Rx.Protocol` carries a freshness watermark and admits an emit only
-- when the watermark has not passed its instant, so the ORDER on this
-- type is what rejects a stream revisiting a departed instant.  A
-- carrier offering equality alone cannot state that check: the repair
-- would be a seen-set, retaining every past instant for the length of
-- the run where a watermark retains one position.  So the two ids of
-- this module are not a pair to treat alike — this one is an ordered
-- ARRIVAL POSITION and `Source` below is the token.

-- AND WHAT NEEDS THE ORDER IS THE CHECKER, NOT THE PIPELINE — WHICH IS
-- WHAT DECIDES THE OBJECT-LANGUAGE ENCODING.  The paragraph above is a
-- fact about `Rx.Protocol`, and `Rx.Protocol` is an ACCEPTANCE ORACLE:
-- it reads a finished stream and rules on whether the protocol was
-- obeyed.  Nothing in the batching pipeline the theorem is about ever
-- consults the order.  `Spec` groups by comparing instants for
-- equality; the implementation holds one open batch and asks only
-- whether the incoming instant equals the open one, flushing when it
-- does not.  So when the envelope is re-expressed as a TYPE of the
-- object language, its instant field stands at the unique primitive,
-- whose sole eliminator is a primitive equality, and nothing is lost —
-- the watermark stays where it already is, in a meta-level automaton
-- over meta-level emits, which is the only thing that could have
-- wanted a successor or a `≤` in the first place.  Read the two
-- paragraphs together: equality alone cannot state the CHECK, and
-- equality alone is all the RUN was ever asking for.

-- A TOKEN, AND THAT IS THE WHOLE OF WHAT ANYTHING ASKS OF IT.  `Spec`
-- binds this and copies it onto the batch envelope without ever
-- comparing it; `Rx.Protocol` compares it and never orders or computes
-- with it, a registration ledger being keyed by it and nothing more.
-- So ℕ is over-strong here in a way it is not for `Id` above, and the
-- over-strength is not free: every statement quantifying over streams
-- inherits obligations about ones carrying sources no mint could
-- produce.  The TypeScript counterpart is already typed as a number OR
-- a symbol; this module offers only the number.
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

-- AND WHAT AN EVALUATOR PUSHES IS NOT THAT, WHICH IS A STATEMENT
-- ABOUT LEVELS AND NOT ABOUT RICHNESS.  `InstEmit` is the PROTOCOL's
-- vocabulary: the spec reads one, batches by its `instant`, and hands
-- back another.  A machine running an ordinary rxjs pipeline pushes
-- something far smaller — a value, or the end of the stream — one at
-- a time and depth-first, with no envelope around it and no grouping
-- across a cascade.
--
-- SO THE PROTOCOL RIDES ON THE VALUES RATHER THAN ON THE CARRIER,
-- which is where the TypeScript keeps it: its operators are plain
-- rxjs and the envelope is the type flowing THROUGH them.  `emitᵗ` in
-- `Rx.Envelope` is that envelope at the object level and `toPlain`
-- puts it there, so a machine carrying one too would be holding the
-- same record twice, once at each level, with only the object-level
-- copy having a counterpart in the mirror.
--
-- THERE IS NO ERROR ARM BECAUSE THE PROTOCOL HAS NONE.  A stream here
-- ends by completing or by being closed from above, and closure is a
-- registration's business rather than an emission's.
data PlainEvent (A : Set) : Set where
  valueᵖ    : A → PlainEvent A
  completeᵖ : PlainEvent A            -- the stream ends here (concatAll grafts on it)

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
