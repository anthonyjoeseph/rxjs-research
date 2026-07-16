export type Provenance = number | symbol; // an INSTANT (one arrival's cascade); spec groups by this
export type SourceId = number | symbol; // a SOURCE observable; the impl counts registrations of these

// The protocol (v1's, with the instant id moved onto the emission).
// Batching is decided downstream by counting registrations, never by
// comparing clocks: init/close traffic maintains the live-registration
// count per source, and for each arrival every live registration chain
// of that source forwards EXACTLY ONE InstEmit (possibly valueless —
// emits are emptied, never swallowed), so a batcher owes count(source)
// emits for an instant and flushes when they've arrived.
export type InstEvent<A> =
  | { type: "init"; source: SourceId } // a registration chain of this source came alive
  | { type: "value"; value: A }
  | { type: "close"; source: SourceId } // a registration of this source ended (take cuts, switches away)
  | { type: "complete" }; // the stream completes as part of THIS emit (concatAll grafts on it)

// Everything is an InstEmit stream — including batchSimultaneous's
// output (InstEmit<A[]>): a batch keeps its instant id and stays a
// protocol citizen, so a batched stream feeds every primitive again
// (e.g. merge it with itself and batch once more).
export type InstEmit<A> = {
  events: InstEvent<A>[]; // everything caused by one incoming emit, COALESCED
  instant: Provenance; // the instant it belongs to
  source: SourceId; // the arrival's source (owed = its live-registration count)
};
