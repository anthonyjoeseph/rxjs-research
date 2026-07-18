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
  EmitKind,
  InstEmit,
  InstEvent,
  Provenance,
  SourceId,
} from "./inst-emit.js";
import { Arrival, Driver } from "./driver.js";

// ---- per-emit plumbing: the mirror of Agda's pushBurst ∘ stepFrame ----
// A frame transforms the VALUE payloads of one emit; the bookkeeping
// (init/close/handoff) and the fin bit (a `complete` event) are peeled
// off first and re-attached after, so every frame reassembles an emit
// as `bookkeeping ++ frame events ++ values ++ complete?` — Agda's
// normalized order, where a source's own close precedes the values it
// rode in with. The fin bit is carried by a materialized `complete`
// event, present only in subscribe bursts of spent one-shots (of, empty,
// a spent cold); arrivals complete via rx and so never grow one here.

const splitEmit = <A>(
  emit: InstEmit<A>,
): { bookkeeping: InstEvent<never>[]; values: A[]; fin: boolean } => ({
  bookkeeping: emit.events.filter(
    (ev): ev is InstEvent<never> =>
      ev.type !== "value" && ev.type !== "complete",
  ),
  values: emit.events.flatMap((ev) => (ev.type === "value" ? [ev.value] : [])),
  fin: emit.events.some((ev) => ev.type === "complete"),
});

const reassemble = <B>(
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
// options are false by definition. Connects the underlying once, at
// the first subscription; never disconnects (an unobserved share keeps
// running); latches completion forever — a post-completion subscriber
// sees only an immediate close/complete, because completion is
// re-observable and values are not. Emits init/close per subscriber,
// and one upstream arrival fans out to every subscriber within the
// same instant. `source` stamps the fan-out emits — by convention the
// shared slot's index. The latch must flip BEFORE the final delivery
// fans out (as a Subject closes before delivering its completion, and
// as the Agda dispatchShare latches before its fan-out): a subscriber
// joining mid-final-cascade already gets the one-shot
// init/close/complete, never a registration dropped without its close.
// Protocol duties (mirror of Agda foldPath's share-sink clause): the
// upstream emit that triggers a fan-out passes through FIRST, emptied
// of values, with a `handoff` event for this share appended — the
// writer-asserted announcement that the fan-out follows in the same
// instant.  Fan-out emits are kind "delivery"; per-subscriber
// init/one-shot emits are kind "subscribe"; closes minted here (the
// def completing) carry reason "exhausted".
export declare const share: <A>(
  obs: Observable<InstEmit<A>>,
  source: SourceId,
) => Observable<InstEmit<A>>;

// a one-shot driver delivery at the NEXT tick, read per subscription —
// the async boundary under deferᵉ/μᵉ. Teardown cancels the pending
// hop (unsubscribing a not-yet-fired defer is free — Agda's sweepLive).
const oneShotArrival = (driver: Driver, tick: number): Observable<Arrival> =>
  new Observable<Arrival>((subscriber) =>
    driver.registerSource([
      {
        tick,
        fire: (arrival) => {
          subscriber.next(arrival);
          subscriber.complete();
        },
      },
    ]),
  );

// deferᵉ (NOT rxjs defer): lazy PLUS a one-tick hop, the body's
// emissions minting fresh ids (an async boundary). Mirrors Agda's
// deferᵉ clause: a one-shot source — init in the subscriber's
// instant, the body subscribed when the hop fires at tick + 1, close
// riding that arrival, the whole completing when the body does.
// The body thunk compiles AT FIRE TIME, which is what breaks μ's
// unfolding regress: each unfolding costs a schedule hop.
// ⚠ Known coalescing gap vs Agda until mergeAll lands: the close
// bookkeeping and the body's sync burst arrive as separate emits here,
// where Agda grafts them into ONE arrival emit (thru-outer mergeᵒ).
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
          merge(
            rxOf<InstEmit<A>>({
              events: [{ type: "close", source, reason: "exhausted" }],
              instant,
              source,
              kind: "delivery",
            }),
            rxDefer(compileBody),
          ),
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
// carries the taken prefix plus a `close … cut` for the still-live
// source (Agda's cutThrough), then the stream completes — rx teardown
// cancelling any scheduled deliveries (Agda's sweepLive). A source that
// already completed within this emit (a spent one-shot: `fin`) has no
// live registration to cut, so no close is added — it is simply
// truncated. Count 0 is routed to `empty` by the compiler (Agda: take 0
// never subscribes its source), so `emissions ≥ 1` here.
export const take = <A>(
  obs: Observable<InstEmit<A>>,
  emissions: number,
): Observable<InstEmit<A>> =>
  obs.pipe(
    rxScan<InstEmit<A>, { remaining: number; cut: boolean; out?: InstEmit<A> }>(
      (state, emit) => {
        const { bookkeeping, values, fin } = splitEmit(emit);
        const taken = values.slice(0, state.remaining);
        const didCut = taken.length === state.remaining; // filled the quota
        if (!didCut)
          return {
            remaining: state.remaining - taken.length,
            cut: false,
            out: reassemble(emit, bookkeeping, [], taken, fin),
          };
        const cutClose: InstEvent<never>[] = fin
          ? []
          : [{ type: "close", source: emit.source, reason: "cut" }];
        return {
          remaining: 0,
          cut: true,
          out: reassemble(emit, bookkeeping, cutClose, taken, fin),
        };
      },
      { remaining: emissions, cut: false },
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

export declare const mergeAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
export declare const switchAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
export declare const concatAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
export declare const exhaustAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
