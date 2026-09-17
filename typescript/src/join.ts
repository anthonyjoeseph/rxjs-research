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
import { SYNC_END, UPSTREAM_DONE, hot, markSync } from "./constructors.js";

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

// THE JOIN OWNS NO SUBSCRIPTION, AND A FRAME IS WHAT REPLACED IT. It
// used to subscribe its outer and every inner by hand, because the one
// thing it needs — an inner's subscribe burst, as a GROUP, grafted into
// the emit that caused it — was only observable from inside a
// subscriber. `markSync` makes that boundary a VALUE, so the whole
// engine is a fold: every event enters one ordered channel, a FRAME
// brackets a carrier emit together with whatever bursts its own
// decisions produced, and a `scan` at the end reassembles each frame
// into the single emit the protocol wants.
//
// THE CHANNEL IS WHAT MAKES THE ORDER EXACT, and it is the part worth
// reading twice. Subscribing an inner is a PUSH, made from a `defer`
// sitting between the carrier and the frame's end, so the burst it
// releases lands after the carrier has already reached the fold and
// before the end marker does. That is why a re-entrant push is safe
// here: the carrier is spent by the time anything it caused is emitted.
type Item<A> =
  // the emit a frame is built around: an outer emit, or one inner's
  // later delivery (which opens a frame of its own, since finishing an
  // inner can subscribe the next one)
  | { tag: "carrier"; emit: InstEmit<unknown>; values: A[] }
  // one emit of some inner's subscribe burst, belonging to whichever
  // frame was open when that inner was subscribed
  | { tag: "graft"; emit: InstEmit<A> }
  // switch's victims, ahead of the replacement's burst
  | { tag: "cut"; closes: InstEvent<never>[] }
  | { tag: "frameEnd"; fin: boolean; done: boolean };

type JoinOp = "mergeAll" | "switch" | "exhaust";

type InnerHandle<A> = {
  open: SourceId[]; // this inner's live registrations — its fin bit
  ledger: CutLedger; // who paid / was born this instant, for cut reasons
  burst: InstEmit<A>[]; // its subscribe burst, until the boundary
  spent: boolean; // it rx-completed inside that burst
  cut: () => void; // switch's teardown, through takeUntil
};

const joinAll =
  (op: JoinOp, limit: number | undefined) =>
  <A>(
    outer: Observable<InstEmit<Observable<InstEmit<A>>>>,
  ): Observable<InstEmit<A>> =>
    rxDefer(() => {
      let outerDone = false;
      const active: InnerHandle<A>[] = []; // mergeAll: up to `limit`; the rest at most one
      const queue: Observable<InstEmit<A>>[] = []; // mergeAll only

      // the ordered channel every inner's traffic enters by. A push is
      // delivered synchronously, so push ORDER is output order.
      const [frames, frameSink] = hot<Observable<Item<A>>>();

      // is there a free lane? an absent limit is rxjs's Infinity
      const hasRoom = () => limit === undefined || active.length < limit;

      const joinDone = () =>
        outerDone && active.length === 0 && queue.length === 0;

      const removeHandle = (handle: InnerHandle<A>) => {
        const at = active.indexOf(handle);
        if (at !== -1) active.splice(at, 1);
      };

      // one inner, as items. Everything before its boundary is a graft
      // for the open frame; everything after opens a frame of its own,
      // because an emit that finishes this inner can subscribe the next.
      const taggedInner = (
        handle: InnerHandle<A>,
        innerObs: Observable<InstEmit<A>>,
        cutSignal: Observable<void>,
      ): Observable<Item<A>> => {
        let live = false;
        return markSync(innerObs).pipe(
          takeUntil(cutSignal),
          mergeMap((item): Observable<Item<A>> => {
            if (item === UPSTREAM_DONE) {
              if (!live) handle.spent = true;
              return EMPTY;
            }
            if (item === SYNC_END) {
              live = true;
              // the burst decided whether this inner survived it; only a
              // survivor takes a lane (Agda: it is spent inside its own
              // subscribe frame)
              const done =
                handle.spent ||
                mergeAllBurst(handle.burst).done ||
                handle.open.length === 0;
              if (!done) active.push(handle);
              return EMPTY;
            }
            handle.open = openAfter(item, handle.open, false);
            handle.ledger = cutLedgerStep(item, handle.ledger);
            if (!live) {
              handle.burst = [...handle.burst, item];
              return rxOf<Item<A>>({ tag: "graft", emit: item });
            }
            const parts = splitEmit(item);
            const innerDone = parts.fin || handle.open.length === 0;
            return concat(
              rxOf<Item<A>>({
                tag: "carrier",
                emit: item,
                values: parts.values,
              }),
              rxDefer(() => {
                if (innerDone) {
                  removeHandle(handle);
                  if (op === "mergeAll") drainQueue();
                }
                return EMPTY;
              }),
              rxDefer(() =>
                rxOf<Item<A>>({
                  tag: "frameEnd",
                  fin: false,
                  done: joinDone(),
                }),
              ),
            );
          }),
        );
      };

      // subscribe an inner NOW: the push releases its burst into the
      // open frame, synchronously and in place
      const subscribeInner = (innerObs: Observable<InstEmit<A>>) => {
        const [cutSignal, cutSink] = hot<void>();
        const handle: InnerHandle<A> = {
          open: [],
          ledger: emptyCutLedger,
          burst: [],
          spent: false,
          cut: () => cutSink.next(undefined),
        };
        frameSink.next(taggedInner(handle, innerObs, cutSignal));
      };

      // mergeAll: subscribe parked inners while a lane is free. The
      // gate is hasRoom() and NOT "until one survives its burst" —
      // taggedInner pushes to `active` exactly when the inner is still
      // open, and it does so synchronously inside the push above, so at
      // limit 1 the two coincide and above 1 the loop keeps filling
      // lanes across several parked inners in one instant, which is what
      // mergeMap(f, k) does when several finish together
      const drainQueue = () => {
        while (queue.length > 0 && hasRoom()) {
          const nextInner = queue.shift();
          if (nextInner === undefined) break;
          subscribeInner(nextInner);
        }
      };

      // switch: end the current inner — a close for exactly the
      // registrations it still holds, per-victim reasons from its
      // ledger (paid/born this instant ⇒ cut, else cutPending),
      // teardown cancelling its schedule
      const cutCurrent = (cuttingInstant: Provenance) => {
        const current = active.shift();
        if (current === undefined) return;
        current.cut();
        const closes = cutVictimCloses(
          current.open,
          current.ledger,
          cuttingInstant,
        );
        if (closes.length > 0)
          frameSink.next(rxOf<Item<A>>({ tag: "cut", closes }));
      };

      // the per-op decision for one arriving inner observable
      const acceptInner = (
        innerObs: Observable<InstEmit<A>>,
        cuttingInstant: Provenance,
      ) => {
        switch (op) {
          case "mergeAll":
            if (!hasRoom()) queue.push(innerObs);
            else subscribeInner(innerObs);
            return;
          case "switch":
            cutCurrent(cuttingInstant);
            subscribeInner(innerObs);
            return;
          case "exhaust":
            if (active.length === 0) subscribeInner(innerObs); // else dropped: never subscribed
            return;
        }
      };

      // the outer needs no boundary of its own: its burst emits and its
      // later ones take the same path, which is exactly what the
      // hand-rolled version did by replaying the captured burst through
      // the same handler.
      const outerItems: Observable<Item<A>> = markSync(outer).pipe(
        mergeMap((item): Observable<Item<A>> => {
          if (item === UPSTREAM_DONE) {
            outerDone = true;
            return rxDefer(() =>
              rxOf<Item<A>>({ tag: "frameEnd", fin: false, done: joinDone() }),
            );
          }
          if (item === SYNC_END) return EMPTY;
          const parts = splitEmit(item);
          return concat(
            rxOf<Item<A>>({ tag: "carrier", emit: item, values: [] }),
            rxDefer(() => {
              for (const innerObs of parts.values)
                acceptInner(innerObs, item.instant);
              if (parts.fin) outerDone = true;
              return EMPTY;
            }),
            rxDefer(() => {
              const done = joinDone();
              // the carrying emit under the outer's envelope; a join
              // spent inside the subscribe frame (subscribe OR plumbing
              // carrier) materializes its complete right here (Agda's
              // pushBurst appends on fin′), a spent delivery leaves that
              // to the root
              return rxOf<Item<A>>({
                tag: "frameEnd",
                fin: done && item.kind !== "delivery",
                done,
              });
            }),
          );
        }),
      );

      // the channel is subscribed FIRST, so that the outer's own
      // subscribe burst — which pushes into it while it is still
      // draining — has somewhere to land
      return merge(frames.pipe(mergeAll()), outerItems).pipe(
        // A FRAME'S EVENTS ACCUMULATE IN ARRIVAL ORDER, which is the
        // whole reason a cut and a graft share one bucket: switch cuts
        // the outgoing inner and subscribes the replacement once PER
        // inner the carrier holds, so the close of the one and the init
        // of the next interleave. Bucketing the two kinds apart reads
        // as tidier and emits every cut ahead of every init, which is a
        // different stream.
        rxScan<
          Item<A>,
          {
            carrier?: InstEmit<unknown>;
            events: InstEvent<never>[];
            values: A[];
            done: boolean;
            out?: InstEmit<A>;
          }
        >(
          (state, item) => {
            const open = { ...state, out: undefined };
            switch (item.tag) {
              case "carrier":
                return {
                  carrier: item.emit,
                  events: [],
                  values: item.values,
                  done: false,
                };
              case "graft": {
                const parts = splitEmit(item.emit);
                return {
                  ...open,
                  events: [...state.events, ...parts.bookkeeping],
                  values: [...state.values, ...parts.values],
                };
              }
              case "cut":
                return { ...open, events: [...state.events, ...item.closes] };
              case "frameEnd": {
                if (state.carrier === undefined)
                  return { ...open, done: item.done };
                const parts = splitEmit(state.carrier);
                return {
                  carrier: undefined,
                  events: [],
                  values: [],
                  done: item.done,
                  out: reassemble(
                    state.carrier,
                    parts.bookkeeping,
                    state.events,
                    state.values,
                    item.fin,
                  ),
                };
              }
            }
          },
          { events: [], values: [], done: false },
        ),
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
