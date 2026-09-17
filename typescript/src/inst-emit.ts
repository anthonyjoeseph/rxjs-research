export type Provenance = number | symbol; // an INSTANT (one arrival's cascade); spec groups by this
export type SourceId = number | symbol; // a SOURCE observable; the impl counts registrations of these

// The instant every subscribe burst belongs to, and there is only ONE
// of it because no operator ever compares two. A burst minted inside an
// arrival's cascade is a GRAFT: the join that caused it reassembles it
// under the carrier's envelope, so the burst's own stamp is computed
// and then discarded. A burst minted outside one belongs to the root's
// subscribe frame, which is a single frame. Neither case can tell two
// subscribe instants apart, so an operator that READ an ambient
// "current instant" to fill this field was reading a cell whose value
// never reached an output -- and reading one is what would make these
// operators require a driver, rather than plain rxjs, to run at all.
export const SUBSCRIBE_FRAME: Provenance = Symbol("subscribe-frame");

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
export type CloseReason = "cut" | "cutPending" | "exhausted";
// cut: an operator ended it (take, switch) after it delivered this
//   instant, or it was born mid-instant and owed nothing
// cutPending: an operator ended it BEFORE it delivered the emit it owed
//   this instant — the victim never pays, the reader cancels one owed
//   count (a cut registration delivers NOTHING, as in rxjs)
// exhausted: the source ran dry on its own

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

// mergeAll a subscription's sync burst into grafts for the emit that
// carries it (Agda's splitBurst): all bookkeeping in burst order, then
// all values, complete events absorbed into the done bit
export const mergeAllBurst = <A>(
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

const removeOneSource = (source: SourceId, open: SourceId[]): SourceId[] => {
  const at = open.indexOf(source);
  return at === -1 ? open : [...open.slice(0, at), ...open.slice(at + 1)];
};

// ---- the cut ledger: writer-side bookkeeping for close reasons ----
// A cut names its victims among the registrations still open through an
// operator, and the reason is per victim (mirror of Agda's cutThrough
// against its delivered set and registration watermark): delivered this
// instant, or born this instant and owing nothing ⇒ "cut"; a
// pre-existing registration cut before its delivery ⇒ "cutPending",
// which the reader cancels one owed count against. The ledger tracks,
// per current instant, which still-open registrations have paid
// (cascades fold in registration order, so the earliest-registered of a
// source paid first) and which were born (registered latest). Plumbing
// emits carry no lifecycle signal.
export type CutLedger = {
  instant: Provenance | null;
  paid: SourceId[]; // still-open registrations that delivered this instant
  born: SourceId[]; // still-open registrations born this instant
};

export const emptyCutLedger: CutLedger = {
  instant: null,
  paid: [],
  born: [],
};

export const cutLedgerStep = <A>(
  emit: InstEmit<A>,
  ledger: CutLedger,
): CutLedger => {
  if (emit.kind === "plumbing") return ledger;
  const base =
    ledger.instant === emit.instant
      ? ledger
      : { instant: emit.instant, paid: [], born: [] };
  return emit.events.reduce<CutLedger>(
    (acc, ev) => {
      if (ev.type === "init") return { ...acc, born: [...acc.born, ev.source] };
      if (ev.type !== "close") return acc;
      // a closing registration leaves the ledger: the payer's own close
      // rides its paying emit; a dying newborn leaves born
      const inPaid = acc.paid.indexOf(ev.source);
      return inPaid === -1
        ? { ...acc, born: removeOneSource(ev.source, acc.born) }
        : {
            ...acc,
            paid: [...acc.paid.slice(0, inPaid), ...acc.paid.slice(inPaid + 1)],
          };
    },
    {
      instant: base.instant,
      paid: emit.kind === "delivery" ? [...base.paid, emit.source] : base.paid,
      born: base.born,
    },
  );
};

// the victims' closes, in registration order, one per open entry:
// within a source's occurrences the earliest paid(x) delivered and the
// latest born(x) were born this instant — both "cut"; the middle never
// paid this instant: "cutPending". A ledger from an older instant
// contributes nothing (nobody paid or was born this instant).
export const cutVictimCloses = (
  open: SourceId[],
  ledger: CutLedger,
  cuttingInstant: Provenance,
): InstEvent<never>[] => {
  const active = ledger.instant === cuttingInstant;
  const countOf = (xs: SourceId[], x: SourceId) =>
    xs.filter((s) => s === x).length;
  return open.map((x, at) => {
    // this entry's place among the occurrences of its own source, and
    // how many there are in all — both read off `open` directly, since
    // a tally carried along the walk is the same numbers kept in a cell
    const i = countOf(open.slice(0, at + 1), x);
    const total = countOf(open, x);
    const paid = active ? countOf(ledger.paid, x) : 0;
    const born = active ? countOf(ledger.born, x) : 0;
    const reason: CloseReason =
      i <= paid || i > total - born ? "cut" : "cutPending";
    return { type: "close", source: x, reason } as const;
  });
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
