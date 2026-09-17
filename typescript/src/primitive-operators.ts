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
  mergeAllBurst,
  openAfter,
  reassemble,
  splitEmit,
} from "./inst-emit.js";
import { Arrival, Driver } from "./driver.js";
import { captureSync, cold, hot } from "./constructors.js";

export { exhaustAll, mergeAllAll, switchAll } from "./join.js";
import { mergeAllAll } from "./join.js";

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
    const plumbed = connect.burst.map((emit): InstEmit<A> => ({
      ...emit,
      kind: "plumbing",
    }));
    const burstFin =
      connect.completedSync ||
      mergeAllBurst(connect.burst).done ||
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
// hop's close into ONE delivery emit (Agda's thru-outer mergeAllᵒ walk) —
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
            const flat = mergeAllBurst(capture.burst);
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

// lift: THE pure-function former. A step reads an emit's VALUES and the
// state carried across emits, and returns the next state and the values
// to emit in their place. That is the whole interface, and what it
// EXCLUDES is the point: a step mints no registration, reads none of the
// bookkeeping, cannot end the stream and cannot see which instant it is
// in — so the emit's own events and its fin bit ride through untouched
// and the protocol is not something a program can write.
//
// Its Agda counterpart is a `Tm` of type (u × list s) → (u × list t)
// with a `Tm` seed, which is why the interface is an ARRAY in and an
// array out rather than one value at a time: `Tm` is first-order and
// total, so a step cannot be a callback the operator drives, and the
// value language already has fold over lists.
export const lift = <A, B, S>(
  obs: Observable<InstEmit<A>>,
  initial: S,
  step: (state: S, values: A[]) => { state: S; values: B[] },
): Observable<InstEmit<B>> =>
  obs.pipe(
    rxScan<InstEmit<A>, { state: S; out?: InstEmit<B> }>(
      (carried, emit) => {
        const { bookkeeping, values, fin } = splitEmit(emit);
        const next = step(carried.state, values);
        return {
          state: next.state,
          out: reassemble(emit, bookkeeping, [], next.values, fin),
        };
      },
      { state: initial },
    ),
    rxMap((carried) => carried.out as InstEmit<B>), // the seed is never emitted, so out is set
  );

// a lift that carries nothing. No Exp node compiles to this any more —
// a program's map is built from the lift NODE, in the term language —
// so what is left is the compiler's own use, mapping each emitted inner
// observable to its compilation.
export const map = <A, B>(
  obs: Observable<InstEmit<A>>,
  fn: (a: A) => B,
): Observable<InstEmit<B>> =>
  lift<A, B, null>(obs, null, (state, values) => ({
    state,
    values: values.map(fn),
  }));

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
//
// AND IT IS NOT A `lift`, WHICH IS THE PALETTE'S DIVIDING LINE DRAWN AT
// THE ONE OPERATOR THAT LOOKS LIKE IT SHOULD BE ONE.  `map` and `scan`
// are lifts because a step reading the values decides everything they
// emit.  This one reads the open-registration multiset and the cut
// ledger, MINTS bookkeeping (one close per victim, with a per-victim
// reason), and raises fin on the emit that cuts.  A lift whose step
// could do that would be a step handed source ids, close reasons and
// emit kinds -- the protocol's own vocabulary, in the value language,
// writable by a program.  So `take` stays a former of its own.
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

// expand: rxjs's recursive flattener, DERIVED rather than a former —
// every value emitted (the source's own and every projected one) is
// re-projected and merged, which is `mergeAll` over an outer whose
// inner is one value's whole expansion.
//
// AND IT IS BREADTH-FIRST, WHICH PLAIN RXJS IS NOT, AND THAT IS NOT A
// BUG TO FIX HERE.  The recursion must be guarded — nothing else stops
// it running at construction — and the only lazy former this language
// has is `defer`, which costs a schedule hop by design, since that hop
// is what breaks mu's unfolding regress.  So each level of the
// expansion lands in its own instant.  Plain rxjs subscribes the
// projection inside the frame that produced the value, so the whole
// expansion is ONE frame.
//
// The values agree as a multiset and disagree in order and, more to the
// point, in BATCHING: a countdown from three is one batch in rxjs and
// four here, one per tick.  Closing that gap means either a former of
// its own or a mu that unfolds without a hop, and both decide what
// every theorem above quantifies over — so neither is taken here.
export const expand = <A>(
  driver: Driver,
  project: (a: A) => Observable<InstEmit<A>>,
) => {
  // one value's expansion: the value, and the recursion on its
  // projection, as two inners of a single outer emit — so both are
  // subscribed inside the frame that carried the value and the join's
  // id-inheritance puts them in that emit's instant.
  function fromValue(a: A): Observable<InstEmit<A>> {
    return mergeAllAll(undefined)(
      of<Observable<InstEmit<A>>>(driver, [
        of<A>(driver, [a]),
        defer(driver, () => expandAll(project(a))),
      ]),
    );
  }
  function expandAll(src: Observable<InstEmit<A>>): Observable<InstEmit<A>> {
    return mergeAllAll(undefined)(map(src, fromValue));
  }
  return expandAll;
};
