import { EMPTY, Observable, concat } from "rxjs";
import {
  defer as rxDefer,
  filter,
  map as rxMap,
  merge,
  mergeAll,
  mergeMap,
  of as rxOf,
  scan as rxScan,
  takeUntil,
  takeWhile,
  tap,
} from "rxjs";
import {
  CutLedger,
  InstEmit,
  InstEvent,
  Provenance,
  SourceId,
  cutLedgerStep,
  cutVictimCloses,
  emptyCutLedger,
  mergeAllBurst,
  openAfter,
  reassemble,
  splitEmit,
} from "./inst-emit.js";
import {
  Marked,
  SYNC_END,
  UPSTREAM_DONE,
  channel,
  markSync,
} from "./constructors.js";

// ---- the one join engine: mergeAllAll/switchAll/exhaustAll ----
// (the TS mirror of Agda's subscribeAll + stepFrame thru-outer/from-inner)
//
// mergeAllAll carries rxjs's `concurrent` argument: undefined is
// Infinity, which is mergeAll; 1 is concatAll; k >= 2 is the bounded
// mergeMap(f, k) that has no name of its own in rxjs. There is no
// separate merge and concat op — they are two points of one operator's
// parameter, and the middle point is not reachable by combining them,
// because a bounded mergeAll assigns an arriving inner to the NEXT FREE
// lane and no static partition of the outer into k merges does that.
//
// The three ops differ ONLY in two decisions — what to do with a newly
// arrived inner (subscribe if a lane is free / park it / cut the
// current one / drop), and how to react when an inner finishes (mergeAll
// drains its queue into the freed lanes; the others just bookkeep) —
// plus the completion condition. Everything else is shared:
//
// - a subscribed inner's SYNC burst is captured and flattened into the
//   emit that carried it (Agda's splitBurst): all bookkeeping in walk
//   order, then all values — the id-inheritance that makes the diamond
//   batch. Inner complete events are absorbed into the done bit; the
//   join completes on its own terms.
// - an inner's completion is detected ON the emit that closes its last
//   registration (the open-source multiset — TS's reading of Agda's
//   threaded fin bit), so concat can graft the next inner's burst into
//   that very emit (completion cascades inherit). Plumbing emits are
//   excluded: a share's connect traffic opens nothing the join owns.
// - a cut inner (switch) contributes close…cut events for exactly the
//   registrations it still holds (Agda's cutThrough), and its teardown
//   cancels whatever it had scheduled (sweepLive).

// THE JOIN OWNS NO SUBSCRIPTION AND NO CELL: IT IS ONE FOLD. Every
// event — the outer's, every inner's, and the engine's own decisions —
// enters one ordered channel, and a single `scan` holds the whole
// machine: the lane table, the parked queue, whether the outer is
// finished, and the frame being assembled. Nothing is read out of a
// variable, so nothing can be read at the wrong moment.
//
// THE CHANNEL IS WHAT MAKES THE ORDER EXACT, and it is the part worth
// reading twice. Subscribing an inner is a PUSH, and the push is made
// from the fold's OUTPUT — so it happens after the item that caused it
// has already been folded, and before the next item upstream is
// released. The burst it releases therefore lands inside the frame that
// caused it, and whatever the fold reads next sees that burst already
// accounted for. That is also why a decision per arriving inner is a
// separate ITEM rather than a loop: at limit 1, the second inner's
// decision has to see whether the first survived its own burst, and
// only a separate fold step can.
type LaneId = number;

type Item<A> =
  // the outer's emit: the frame is built around it
  | { tag: "carrier"; emit: InstEmit<unknown> }
  // one inner observable the outer just delivered, offered to the
  // engine for its per-op decision
  | { tag: "accept"; obs: Observable<InstEmit<A>>; instant: Provenance }
  // the outer will deliver nothing further
  | { tag: "outerFin" }
  // one emit from a subscribed inner: a graft while it is still inside
  // its subscribe burst, a carrier of its own afterwards
  | { tag: "innerEmit"; lane: LaneId; emit: InstEmit<A> }
  // that inner's subscribe burst is over
  | { tag: "innerBoundary"; lane: LaneId }
  // that inner rx-completed
  | { tag: "innerDone"; lane: LaneId }
  // mergeAll: take one parked inner if a lane is free
  | { tag: "drain" }
  | { tag: "frameEnd"; fromOuter: boolean };

type JoinOp = "mergeAll" | "switch" | "exhaust";

// one subscribed inner, as the fold sees it
type Lane<A> = {
  id: LaneId;
  open: SourceId[]; // its live registrations — its fin bit
  ledger: CutLedger; // who paid / was born this instant, for cut reasons
  burst: InstEmit<A>[]; // its subscribe burst, until the boundary
  spent: boolean; // it rx-completed inside that burst
  live: boolean; // it survived past the boundary
  seated: boolean; // it holds a lane (rxjs's `concurrent` counts these)
};

// the whole machine. The first four fields are the engine, the next
// three are the frame under construction, and the last four are this
// step's OUTPUT — what the fold asks its own downstream to do.
type Engine<A> = {
  lanes: Lane<A>[];
  queue: Observable<InstEmit<A>>[]; // mergeAll only
  outerDone: boolean;
  nextId: LaneId;
  carrier?: InstEmit<unknown>;
  events: InstEvent<never>[];
  values: A[];
  done: boolean;
  out?: InstEmit<A>;
  subscribe: { id: LaneId; obs: Observable<InstEmit<A>> }[];
  cuts: LaneId[];
  needDrain: boolean;
};

const joinAll =
  (op: JoinOp, limit: number | undefined) =>
  <A>(
    outer: Observable<InstEmit<Observable<InstEmit<A>>>>,
  ): Observable<InstEmit<A>> =>
    rxDefer(() => {
      // the ordered channel every inner's traffic enters by. A push is
      // delivered synchronously, so push ORDER is output order.
      const [frames, frameSink] = channel<Observable<Item<A>>>();
      // a cut names its victim by lane; the victim is listening
      const [cuts, cutSink] = channel<LaneId>();

      const seated = (e: Engine<A>) => e.lanes.filter((l) => l.seated).length;
      // is there a free lane? an absent limit is rxjs's Infinity
      const hasRoom = (e: Engine<A>) =>
        limit === undefined || seated(e) < limit;
      const joinDone = (e: Engine<A>) =>
        e.outerDone && seated(e) === 0 && e.queue.length === 0;

      const openLane = (
        e: Engine<A>,
        obs: Observable<InstEmit<A>>,
      ): Engine<A> => ({
        ...e,
        nextId: e.nextId + 1,
        lanes: [
          ...e.lanes,
          {
            id: e.nextId,
            open: [],
            ledger: emptyCutLedger,
            burst: [],
            spent: false,
            live: false,
            seated: false,
          },
        ],
        subscribe: [...e.subscribe, { id: e.nextId, obs }],
      });

      // the per-op decision for one arriving inner observable. switch's
      // cut is a close for exactly the registrations the victim still
      // holds, with per-victim reasons from its ledger (paid/born this
      // instant ⇒ cut, else cutPending); the closes join the frame here,
      // ahead of the replacement's burst, and the victim's teardown
      // rides out on `cuts`.
      const accept = (
        e: Engine<A>,
        obs: Observable<InstEmit<A>>,
        cuttingInstant: Provenance,
      ): Engine<A> => {
        if (op === "mergeAll")
          return hasRoom(e)
            ? openLane(e, obs)
            : { ...e, queue: [...e.queue, obs] };
        if (op === "exhaust")
          return e.lanes.some((l) => l.seated) ? e : openLane(e, obs);
        const victim = e.lanes.find((l) => l.seated);
        return openLane(
          victim === undefined
            ? e
            : {
                ...e,
                lanes: e.lanes.filter((l) => l.id !== victim.id),
                cuts: [...e.cuts, victim.id],
                events: [
                  ...e.events,
                  ...cutVictimCloses(
                    victim.open,
                    victim.ledger,
                    cuttingInstant,
                  ),
                ],
              },
          obs,
        );
      };

      // A FRAME'S EVENTS ACCUMULATE IN ARRIVAL ORDER, which is why a cut
      // and a graft share one bucket: switch cuts the outgoing inner and
      // subscribes the replacement once PER inner the carrier holds, so
      // the close of the one and the init of the next interleave.
      // Bucketing the two kinds apart reads as tidier and emits every
      // cut ahead of every init, which is a different stream.
      const step = (prev: Engine<A>, item: Item<A>): Engine<A> => {
        const e: Engine<A> = {
          ...prev,
          out: undefined,
          subscribe: [],
          cuts: [],
          needDrain: false,
        };
        switch (item.tag) {
          case "carrier":
            return { ...e, carrier: item.emit, events: [], values: [] };
          case "accept":
            return accept(e, item.obs, item.instant);
          case "outerFin":
            return { ...e, outerDone: true };
          case "drain": {
            const [head, ...rest] = e.queue;
            return head === undefined || !hasRoom(e)
              ? e
              : { ...openLane({ ...e, queue: rest }, head), needDrain: true };
          }
          case "innerEmit": {
            const lane = e.lanes.find((l) => l.id === item.lane);
            if (lane === undefined) return e;
            const open = openAfter(item.emit, lane.open, false);
            const ledger = cutLedgerStep(item.emit, lane.ledger);
            const parts = splitEmit(item.emit);
            if (!lane.live)
              return {
                ...e,
                lanes: e.lanes.map((l) =>
                  l.id === lane.id
                    ? { ...l, open, ledger, burst: [...l.burst, item.emit] }
                    : l,
                ),
                events: [...e.events, ...parts.bookkeeping],
                values: [...e.values, ...parts.values],
              };
            const innerDone = parts.fin || open.length === 0;
            return {
              ...e,
              lanes: innerDone
                ? e.lanes.filter((l) => l.id !== lane.id)
                : e.lanes.map((l) =>
                    l.id === lane.id ? { ...l, open, ledger } : l,
                  ),
              carrier: item.emit,
              events: [],
              values: parts.values,
              needDrain: innerDone && op === "mergeAll",
            };
          }
          case "innerBoundary": {
            const lane = e.lanes.find((l) => l.id === item.lane);
            if (lane === undefined) return e;
            // the burst decided whether this inner survived it; only a
            // survivor takes a lane (Agda: it is spent inside its own
            // subscribe frame)
            const dead =
              lane.spent ||
              mergeAllBurst(lane.burst).done ||
              lane.open.length === 0;
            return {
              ...e,
              lanes: dead
                ? e.lanes.filter((l) => l.id !== lane.id)
                : e.lanes.map((l) =>
                    l.id === lane.id ? { ...l, live: true, seated: true } : l,
                  ),
            };
          }
          case "innerDone": {
            const lane = e.lanes.find((l) => l.id === item.lane);
            return lane === undefined || lane.live
              ? e
              : {
                  ...e,
                  lanes: e.lanes.map((l) =>
                    l.id === lane.id ? { ...l, spent: true } : l,
                  ),
                };
          }
          case "frameEnd": {
            const done = joinDone(e);
            if (e.carrier === undefined) return { ...e, done };
            const parts = splitEmit(e.carrier);
            // a join spent inside the subscribe frame (subscribe OR
            // plumbing carrier) materializes its complete right here
            // (Agda's pushBurst appends on fin′); a spent delivery
            // leaves that to the root, and an inner's own frame never
            // carries it
            const fin = item.fromOuter && done && e.carrier.kind !== "delivery";
            return {
              ...e,
              carrier: undefined,
              events: [],
              values: [],
              done,
              out: reassemble(
                e.carrier,
                parts.bookkeeping,
                e.events,
                e.values,
                fin,
              ),
            };
          }
        }
      };

      // one inner, as items. The only thing decided here is WHERE its
      // subscribe boundary falls, because everything after it opens a
      // frame of its own — an emit that finishes this inner can
      // subscribe the next. Everything else the inner knows about
      // itself is folded by the engine.
      const taggedInner = (
        lane: LaneId,
        innerObs: Observable<InstEmit<A>>,
      ): Observable<Item<A>> =>
        markSync(innerObs).pipe(
          takeUntil(cuts.pipe(filter((id) => id === lane))),
          rxScan<
            Marked<InstEmit<A>>,
            { live: boolean; item: Marked<InstEmit<A>> }
          >((acc, item) => ({ live: acc.live || item === SYNC_END, item }), {
            live: false,
            item: SYNC_END,
          }),
          mergeMap(({ live, item }): Observable<Item<A>> => {
            if (item === UPSTREAM_DONE)
              return rxOf<Item<A>>({ tag: "innerDone", lane });
            if (item === SYNC_END)
              return rxOf<Item<A>>({ tag: "innerBoundary", lane });
            const emit = item as InstEmit<A>;
            return live
              ? concat(
                  rxOf<Item<A>>({ tag: "innerEmit", lane, emit }),
                  rxOf<Item<A>>({ tag: "frameEnd", fromOuter: false }),
                )
              : rxOf<Item<A>>({ tag: "innerEmit", lane, emit });
          }),
        );

      // the outer needs no boundary of its own: its burst emits and its
      // later ones take the same path, which is exactly what replaying a
      // captured burst through one handler would do.
      const outerItems: Observable<Item<A>> = markSync(outer).pipe(
        mergeMap((item): Observable<Item<A>> => {
          if (item === UPSTREAM_DONE)
            return concat(
              rxOf<Item<A>>({ tag: "outerFin" }),
              rxOf<Item<A>>({ tag: "frameEnd", fromOuter: true }),
            );
          if (item === SYNC_END) return EMPTY;
          const parts = splitEmit(item);
          return concat<Item<A>[]>(
            rxOf<Item<A>>({ tag: "carrier", emit: item }),
            ...parts.values.map((obs) =>
              rxOf<Item<A>>({ tag: "accept", obs, instant: item.instant }),
            ),
            ...(parts.fin ? [rxOf<Item<A>>({ tag: "outerFin" })] : []),
            rxOf<Item<A>>({ tag: "frameEnd", fromOuter: true }),
          );
        }),
      );

      const initial: Engine<A> = {
        lanes: [],
        queue: [],
        outerDone: false,
        nextId: 0,
        events: [],
        values: [],
        done: false,
        subscribe: [],
        cuts: [],
        needDrain: false,
      };

      // the channel is subscribed FIRST, so that the outer's own
      // subscribe burst — which pushes into it while it is still
      // draining — has somewhere to land
      return merge(frames.pipe(mergeAll()), outerItems).pipe(
        rxScan<Item<A>, Engine<A>>(step, initial),
        // the fold's decisions, carried out in the order it made them.
        // Each push re-enters the fold before this call returns, which
        // is what puts a burst inside the frame that caused it.
        tap((state) => {
          for (const id of state.cuts) cutSink.next(id);
          for (const cmd of state.subscribe)
            frameSink.next(taggedInner(cmd.id, cmd.obs));
          if (state.needDrain) frameSink.next(rxOf<Item<A>>({ tag: "drain" }));
        }),
        takeWhile((state) => !state.done, true),
        filter((state) => state.out !== undefined),
        rxMap((state) => state.out as InstEmit<A>),
      );
    });

// `limit` is fixed when the pipeline is BUILT, never per subscription —
// that is what rxjs's `concurrent` argument is, and a limit that varied
// per subscription would be a capability the real operator lacks
export const mergeAllAll = (limit: number | undefined) =>
  joinAll("mergeAll", limit);
export const switchAll = joinAll("switch", undefined);
export const exhaustAll = joinAll("exhaust", undefined);
