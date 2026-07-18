export type Provenance = number | symbol; // an INSTANT (one arrival's cascade); spec groups by this
export type SourceId = number | symbol; // a SOURCE observable; the impl counts registrations of these

// The protocol (v1's, with the instant id moved onto the emission).
// Batching is decided downstream by counting registrations, never by
// comparing clocks: init/close traffic maintains the live-registration
// count per source, and for each arrival every live registration chain
// of that source forwards EXACTLY ONE InstEmit (possibly valueless —
// emits are emptied, never swallowed), so a batcher owes count(source)
// emits for an instant and flushes when they've arrived.
// Writer-asserted facts (the reader checks, never reconstructs):
// every mint site knows definitively whether it is a subscription
// burst or an arrival delivery, and why a registration ended.
export type EmitKind = "subscribe" | "delivery" | "plumbing";
// subscribe: a subscription's own burst — owes nothing, pays nothing
// delivery: an arrival emit — pays the instant's owed count
// plumbing: a share's connect burst forwarded up its first subscriber —
//   real protocol traffic for the root's ledger, but its registrations
//   belong to the share (they survive the subscriber), so the operators
//   it flows through take no lifecycle signal from it
export type CloseReason = "cut" | "exhausted"; // cut: an operator ended it (take, switch); exhausted: the source ran dry

export type InstEvent<A> =
  | { type: "init"; source: SourceId } // a registration chain of this source came alive
  | { type: "value"; value: A }
  | { type: "close"; source: SourceId; reason: CloseReason } // a registration of this source ended
  | { type: "handoff"; source: SourceId } // this share fans out next, still inside this instant
  | { type: "complete" }; // the stream completes as part of THIS emit (concatAll grafts on it)

// Everything is an InstEmit stream — including batchSimultaneous's
// output (InstEmit<A[]>): a batch keeps its instant id and stays a
// protocol citizen, so a batched stream feeds every primitive again
// (e.g. merge it with itself and batch once more).
export type InstEmit<A> = {
  events: InstEvent<A>[]; // everything caused by one incoming emit, COALESCED
  instant: Provenance; // the instant it belongs to
  source: SourceId; // the arrival's source (owed = its live-registration count)
  kind: EmitKind; // who minted it: a subscription or an arrival cascade
};

// ---- pure protocol arithmetic, shared by every operator ----

// peel one emit into (bookkeeping, values, fin): the mirror of Agda's
// splitEvents. Reassembly is always `bookkeeping ++ frame events ++
// values ++ complete?` — Agda's normalized order, where a source's own
// close precedes the values it rode in with. The fin bit is a
// materialized `complete` event; between operators fin travels as rx
// completion instead, synchronously with the emit that closes the
// pipeline's last registration.
export const splitEmit = <A>(
  emit: InstEmit<A>,
): { bookkeeping: InstEvent<never>[]; values: A[]; fin: boolean } => ({
  bookkeeping: emit.events.filter(
    (ev): ev is InstEvent<never> =>
      ev.type !== "value" && ev.type !== "complete",
  ),
  values: emit.events.flatMap((ev) => (ev.type === "value" ? [ev.value] : [])),
  fin: emit.events.some((ev) => ev.type === "complete"),
});

export const reassemble = <B>(
  envelope: { instant: Provenance; source: SourceId; kind: EmitKind },
  bookkeeping: InstEvent<never>[],
  frameEvents: InstEvent<never>[],
  values: B[],
  fin: boolean,
): InstEmit<B> => ({
  events: [
    ...bookkeeping,
    ...frameEvents,
    ...values.map((value) => ({ type: "value", value }) as const),
    ...(fin ? [{ type: "complete" } as const] : []),
  ],
  instant: envelope.instant,
  source: envelope.source,
  kind: envelope.kind,
});

// flatten a subscription's sync burst into grafts for the emit that
// carries it (Agda's splitBurst): all bookkeeping in burst order, then
// all values, complete events absorbed into the done bit
export const flattenBurst = <A>(
  burst: InstEmit<A>[],
): { bookkeeping: InstEvent<never>[]; values: A[]; done: boolean } =>
  burst.reduce<{ bookkeeping: InstEvent<never>[]; values: A[]; done: boolean }>(
    (acc, emit) => {
      const parts = splitEmit(emit);
      return {
        bookkeeping: [...acc.bookkeeping, ...parts.bookkeeping],
        values: [...acc.values, ...parts.values],
        done: acc.done || parts.fin,
      };
    },
    { bookkeeping: [], values: [], done: false },
  );

const removeOneSource = (
  source: SourceId,
  open: SourceId[],
): SourceId[] => {
  const at = open.indexOf(source);
  return at === -1 ? open : [...open.slice(0, at), ...open.slice(at + 1)];
};

// the open-registration multiset after one emit's events: inits enlist,
// closes retire (clamped). This is TS's reading of Agda's fin bit — a
// pipeline rx-completes exactly when its last registration closes, so
// the multiset hitting empty ON an emit marks completion synchronously
// with it. Plumbing emits carry no lifecycle signal for the operators
// they flow through: pass trackPlumbing=false everywhere except the
// root's ledger.
export const openAfter = <A>(
  emit: InstEmit<A>,
  open: SourceId[],
  trackPlumbing: boolean,
): SourceId[] =>
  !trackPlumbing && emit.kind === "plumbing"
    ? open
    : emit.events.reduce(
        (acc, ev) =>
          ev.type === "init"
            ? [...acc, ev.source]
            : ev.type === "close"
              ? removeOneSource(ev.source, acc)
              : acc,
        open,
      );
