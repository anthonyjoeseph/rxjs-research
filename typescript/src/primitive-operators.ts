import {
  Observable,
  defer as rxDefer,
  map as rxMap,
  merge,
  mergeMap,
  of as rxOf,
  scan as rxScan,
  takeWhile,
} from "rxjs";
import {
  CutLedger,
  InstEmit,
  InstEvent,
  SourceId,
  cutLedgerStep,
  cutVictimCloses,
  emptyCutLedger,
  flattenBurst,
  openAfter,
  reassemble,
  splitEmit,
} from "./inst-emit.js";
import { Arrival, Driver } from "./driver.js";
import { captureSync, cold, hot } from "./constructors.js";

export { concatAll, exhaustAll, mergeAll, switchAll } from "./join.js";

// a one-shot subscription burst (Agda's oneShotBurst): a source that
// lives and dies inside its own subscribe frame — init, its values,
// close, complete — one emit, minting a fresh source per subscription
// and inheriting the instant live at subscribe time (id-inheritance).
export const of = <A>(driver: Driver, input: A[]): Observable<InstEmit<A>> =>
  rxDefer(() => {
    const source = driver.mintSourceId();
    return rxOf<InstEmit<A>>({
      events: [
        { type: "init", source },
        ...input.map((value) => ({ type: "value", value }) as const),
        { type: "close", source, reason: "exhausted" },
        { type: "complete" },
      ],
      instant: driver.currentInstant(),
      source,
      kind: "subscribe",
    });
  });

// oneShotBurst [] — init, close, complete, no values
export const empty = (driver: Driver): Observable<InstEmit<never>> =>
  of<never>(driver, []);

// The slot-telescope share (NOT default rxjs share()): all reset
// options are false by definition — connect once at the first
// subscription, never disconnect (an unobserved share keeps burning
// arrivals), latch completion forever. Mirrors Agda's
// subscribeSharedSlot + dispatchShare:
// - the connect burst flows up the FIRST subscriber only, retagged
//   plumbing (its registrations belong to the share, not to any
//   operator it flows through);
// - each upstream arrival emits the emptied pass-through with a
//   `handoff` announcement straight to the root (driver.pushChainEmit),
//   then one fan-out emit per subscriber, all in the same instant;
// - the completion latch flips BEFORE the final fan-out (a Subject
//   closes before delivering its completion): a subscriber joining
//   mid-final-cascade — or any time later — gets the immediate
//   init/close/complete one-shot, never a registration dropped
//   without its close. Completion is re-observable, values are not.
export const share = <A>(
  driver: Driver,
  obs: Observable<InstEmit<A>>,
  source: SourceId,
): Observable<InstEmit<A>> => {
  let connected = false;
  let completed = false;
  let upstreamOpen: SourceId[] = [];
  const [broadcast, broadcastSink] = hot<InstEmit<A>>();

  const latchedOneShot = (): InstEmit<A> => ({
    events: [
      { type: "init", source },
      { type: "close", source, reason: "exhausted" },
      { type: "complete" },
    ],
    instant: driver.currentInstant(),
    source,
    kind: "subscribe",
  });

  const initEmit = (extra: InstEvent<never>[]): InstEmit<A> => ({
    events: [{ type: "init", source }, ...extra],
    instant: driver.currentInstant(),
    source,
    kind: "subscribe",
  });

  const onUpstreamEmit = (emit: InstEmit<A>) => {
    const parts = splitEmit(emit);
    upstreamOpen = openAfter(emit, upstreamOpen, true);
    const fin = parts.fin || upstreamOpen.length === 0;
    // the chain's own emit, emptied of values, announcing the handoff —
    // it reaches the root directly (Agda foldPath's share-sink clause)
    driver.pushChainEmit({
      events: [...parts.bookkeeping, { type: "handoff", source }],
      instant: emit.instant,
      source: emit.source,
      kind: emit.kind,
    });
    if (fin) completed = true; // latch BEFORE the final fan-out
    broadcastSink.next({
      events: [
        ...(fin
          ? [{ type: "close", source, reason: "exhausted" } as const]
          : []),
        ...parts.values.map((value) => ({ type: "value", value }) as const),
      ],
      instant: emit.instant,
      source,
      kind: "delivery",
    });
    if (fin) broadcastSink.complete();
  };

  return cold<InstEmit<A>>((sink) => {
    if (completed) {
      sink.next(latchedOneShot());
      sink.complete();
      return () => {};
    }
    if (connected) {
      // live: join mid-flight, future values only
      sink.next(initEmit([]));
      const registration = captureSync(broadcast, sink);
      return () => registration.unsubscribe();
    }
    connected = true;
    const connect = captureSync(obs, {
      next: onUpstreamEmit,
      complete: () => {
        // fin rides the closing emit (the open multiset); the rx
        // completion itself is absorbed here
      },
    });
    // never disconnect: the upstream subscription is permanent
    for (const emit of connect.burst)
      upstreamOpen = openAfter(emit, upstreamOpen, true);
    const plumbed = connect.burst.map(
      (emit): InstEmit<A> => ({ ...emit, kind: "plumbing" }),
    );
    const burstFin =
      connect.completedSync ||
      flattenBurst(connect.burst).done ||
      (connect.burst.length > 0 && upstreamOpen.length === 0);
    if (burstFin) {
      // the def died inside its own connect burst: latch; this
      // registration closes in the same instant
      completed = true;
      sink.next(initEmit([{ type: "close", source, reason: "exhausted" }]));
      for (const emit of plumbed) sink.next(emit);
      sink.complete();
      return () => {};
    }
    sink.next(initEmit([]));
    const registration = captureSync(broadcast, sink);
    for (const emit of plumbed) sink.next(emit);
    return () => registration.unsubscribe();
  });
};

// a one-shot driver delivery at the NEXT tick, read per subscription —
// the async boundary under deferᵉ/μᵉ. Teardown cancels the pending
// hop (unsubscribing a not-yet-fired defer is free — Agda's sweepLive).
const oneShotArrival = (driver: Driver, tick: number): Observable<Arrival> =>
  cold<Arrival>((sink) =>
    driver.registerSource([
      {
        tick,
        fire: (arrival) => {
          sink.next(arrival);
          sink.complete();
        },
      },
    ]),
  );

// deferᵉ (NOT rxjs defer): lazy PLUS a one-tick hop, the body's
// emissions minting fresh ids (an async boundary). Mirrors Agda's
// deferᵉ clause: init in the subscriber's instant; when the hop fires
// the body is subscribed and its sync burst is grafted behind the
// hop's close into ONE delivery emit (Agda's thru-outer mergeᵒ walk) —
// the body thunk runs AT FIRE TIME, which is what breaks μ's
// unfolding regress: each unfolding costs a schedule hop.
export const defer = <A>(
  driver: Driver,
  compileBody: () => Observable<InstEmit<A>>,
): Observable<InstEmit<A>> =>
  rxDefer(() => {
    const source = driver.mintSourceId();
    return merge(
      rxOf<InstEmit<A>>({
        events: [{ type: "init", source }],
        instant: driver.currentInstant(),
        source,
        kind: "subscribe",
      }),
      oneShotArrival(driver, driver.currentTick() + 1).pipe(
        mergeMap(({ instant }) =>
          cold<InstEmit<A>>((sink) => {
            const capture = captureSync(compileBody(), sink);
            const flat = flattenBurst(capture.burst);
            sink.next(
              reassemble(
                { instant, source, kind: "delivery" },
                [{ type: "close", source, reason: "exhausted" }],
                flat.bookkeeping,
                flat.values,
                false,
              ),
            );
            if (capture.completedSync || flat.done) sink.complete();
            return () => capture.unsubscribe();
          }),
        ),
      ),
    );
  });

// map-f: map the value payloads, add no events, preserve fin — a pure
// per-emit transform (Agda stepFrame (map-f fn))
export const map = <A, B>(
  obs: Observable<InstEmit<A>>,
  fn: (a: A) => B,
): Observable<InstEmit<B>> =>
  obs.pipe(
    rxMap((emit) => {
      const { bookkeeping, values, fin } = splitEmit(emit);
      return reassemble(emit, bookkeeping, [], values.map(fn), fin);
    }),
  );

// take-f: forward the first `emissions` values, then cut. The cut emit
// carries the taken prefix plus a `close … cut` for EVERY registration
// still open through this operator (Agda's cutThrough) — tracked from
// the init/close bookkeeping that flowed through, this emit's own
// events applied first (a registration whose exhausted close rides the
// cutting emit is already closed, never closed twice) and plumbing
// excluded (a share's connect traffic is not ours to cut). Then the
// stream completes — rx teardown cancelling any scheduled deliveries
// (Agda's sweepLive). Count 0 is routed to `empty` by the compiler
// (Agda: take 0 never subscribes its source), so `emissions ≥ 1` here.
export const take = <A>(
  obs: Observable<InstEmit<A>>,
  emissions: number,
): Observable<InstEmit<A>> =>
  obs.pipe(
    rxScan<
      InstEmit<A>,
      {
        remaining: number;
        cut: boolean;
        open: SourceId[];
        ledger: CutLedger;
        out?: InstEmit<A>;
      }
    >(
      (state, emit) => {
        const { bookkeeping, values, fin } = splitEmit(emit);
        const open = openAfter(emit, state.open, false);
        const ledger = cutLedgerStep(emit, state.ledger);
        const taken = values.slice(0, state.remaining);
        const didCut = taken.length === state.remaining; // filled the quota
        if (!didCut)
          return {
            remaining: state.remaining - taken.length,
            cut: false,
            open,
            ledger,
            out: reassemble(emit, bookkeeping, [], taken, fin),
          };
        // per-victim reasons from the ledger (paid or born this
        // instant ⇒ cut, else cutPending); the cut RAISES fin on this
        // very emit (Agda take-f returns fin′ = true) — a downstream
        // join absorbs it, the root keeps it
        return {
          remaining: 0,
          cut: true,
          open: [],
          ledger,
          out: reassemble(
            emit,
            bookkeeping,
            cutVictimCloses(open, ledger, emit.instant),
            taken,
            true,
          ),
        };
      },
      { remaining: emissions, cut: false, open: [], ledger: emptyCutLedger },
    ),
    takeWhile((state) => !state.cut, true), // include the cutting emit, then complete
    rxMap((state) => state.out as InstEmit<A>), // the seed is never emitted, so out is set
  );

// scan-f: fold each emit's values through the accumulator, emitting one
// value per input value (the running acc), threading acc across emits
// (Agda stepFrame (scan-f fn nid), the nid's state delegated to rx scan)
export const scan = <A, B>(
  obs: Observable<InstEmit<A>>,
  initial: B,
  fn: (acc: B, cur: A) => B,
): Observable<InstEmit<B>> =>
  obs.pipe(
    rxScan<InstEmit<A>, { acc: B; out?: InstEmit<B> }>(
      (state, emit) => {
        const { bookkeeping, values, fin } = splitEmit(emit);
        const { acc, outs } = values.reduce(
          (s, cur) => {
            const acc = fn(s.acc, cur);
            return { acc, outs: [...s.outs, acc] };
          },
          { acc: state.acc, outs: [] as B[] },
        );
        return { acc, out: reassemble(emit, bookkeeping, [], outs, fin) };
      },
      { acc: initial },
    ),
    rxMap((state) => state.out as InstEmit<B>), // the seed is never emitted, so out is set
  );

// the ROOT materializes the fin bit as a `complete` EVENT on the
// DELIVERY emit that closes the last live registration (Agda
// foldPath's root clause — it only runs on arrival cascades; in the
// subscribe frame, complete events are minted in-band: one-shots at
// their mint site, take's cut and a spent join at the frame that
// raises fin, exactly Agda's pushBurst). Applied once, over the full
// root stream (pipeline output MERGED with the driver's chain emits:
// the ledger must see a share's plumbing inits AND the chain-emit
// closes that retire them). Appends at most once; a share's valueless
// chain traffic after root completion is left untouched, and a
// transient empty ledger inside the subscribe frame (a connect-died
// share's [init, close] before its plumbing burst) never triggers.
export const materializeCompletion = <A>(
  obs: Observable<InstEmit<A>>,
): Observable<InstEmit<A>> =>
  obs.pipe(
    rxScan<InstEmit<A>, { open: SourceId[]; done: boolean; out?: InstEmit<A> }>(
      (state, emit) => {
        const open = openAfter(emit, state.open, true);
        const alreadyFin = emit.events.some((ev) => ev.type === "complete");
        const materialize =
          !state.done &&
          !alreadyFin &&
          open.length === 0 &&
          emit.kind === "delivery";
        return {
          open,
          done: state.done || alreadyFin || materialize,
          out: materialize
            ? { ...emit, events: [...emit.events, { type: "complete" }] }
            : emit,
        };
      },
      { open: [], done: false },
    ),
    rxMap((state) => state.out as InstEmit<A>), // the seed is never emitted, so out is set
  );
