import { Observable, Subject, defer, endWith, merge, of } from "rxjs";
import { InstEmit, InstEvent, SUBSCRIBE_FRAME, SourceId } from "./inst-emit.js";
import type { Driver } from "./driver.js";

// A minimal push sink — the only surface a producer needs. Kept to
// next/complete (never a raw rxjs Subscriber) so the rest of the impl
// stays clear of imperative rxjs internals; this file is the single
// place Subject / new Observable are allowed to appear.
export type Sink<A> = {
  next: (val: A) => void;
  complete: () => void;
};

// The push surface a LIVE source's registration is handed instead.
// `isLast` is the registration's own knowledge that this delivery
// spends the source, and it rides on the push rather than arriving as
// a separate `complete()` because the spent latch has to flip BEFORE
// the value fans out: a subscriber that joins during the final cascade
// must see a spent source, and an rx completion sent first would
// swallow the value it was meant to follow.
export type LiveSink<A> = {
  next: (val: A, isLast: boolean) => void;
};

// channel: one Subject behind a sink — the plumbing primitive. A push
// is delivered synchronously to whoever is listening, which is what
// makes push order output order; a push with no listener is dropped.
// This is NOT a source (it carries no lifecycle and mints nothing) —
// it is how one part of an operator hands work to another in order.
export const channel = <A>(): [Observable<A>, Sink<A>] => {
  const subject = new Subject<A>();
  return [
    subject.asObservable(),
    { next: (val) => subject.next(val), complete: () => subject.complete() },
  ];
};

// producer: a fresh imperative producer per subscription, returning its
// teardown — unsubscribing runs it, cancelling whatever the producer
// scheduled (Agda's sweepLive). Also plumbing: it carries no lifecycle
// and mints nothing.
export const producer = <A>(
  produce: (sink: Sink<A>) => () => void,
): Observable<A> =>
  new Observable<A>((subscriber) =>
    produce({
      next: (val) => subscriber.next(val),
      complete: () => subscriber.complete(),
    }),
  );

// bracketSync: the sync/async boundary WITHOUT subscribing, and the
// reason it works is rxjs's own subscribe ordering rather than any
// scheduler — which is what makes it legal here at all, since an
// operator of this implementation may never call `.subscribe`, that
// being the user's one entry point. `merge` subscribes its inputs in
// order, synchronously: it subscribes `src`, `src` drains its entire
// subscribe burst during that call, and only then is `of(SYNC_END)`
// subscribed and fires. So the marker lands exactly at the boundary,
// in the same frame, with no hop and no timing change.
//
// This is what lets an operator stop owning its upstream subscription:
// the split arrives as a VALUE in the stream, so a downstream `scan`
// regroups the burst where the operator used to accumulate it by hand.
// That pairing — bracket then read — is `batchSyncᵉ` followed by
// `mapᵉ`, which is why no new former is owed on the Agda side.
export const SYNC_END = Symbol("end-of-sync");
export const UPSTREAM_DONE = Symbol("upstream-done");
export type SyncEnd = typeof SYNC_END;
export type UpstreamDone = typeof UPSTREAM_DONE;
export type Bracketed<A> = A | SyncEnd;
export type Marked<A> = A | SyncEnd | UpstreamDone;

export const bracketSync = <A>(src: Observable<A>): Observable<Bracketed<A>> =>
  merge<Bracketed<A>[]>(src, of(SYNC_END));

// markSync: the boundary PLUS the source's own completion, for a
// consumer that has to tell "finished inside its own burst" from "still
// live" — a distinction `SYNC_END` alone cannot carry, since a stream
// that completes synchronously and one that merely falls quiet look
// identical at the marker. `endWith` fires on completion whenever it
// happens, so the ordering of the two markers IS the answer: before
// SYNC_END means the completion was synchronous.
export const markSync = <A>(src: Observable<A>): Observable<Marked<A>> =>
  merge<Marked<A>[]>(src.pipe(endWith(UPSTREAM_DONE)), of(SYNC_END));

// ---- the two SOURCE constructors ----
//
// A source is an `Observable<InstEmit<A>>` and not an `Observable<A>`,
// because what the protocol is about is a source's LIFECYCLE — its
// init, the registrations it opens, its close — and a bare value
// carries none of that. So both constructors MINT the source id and
// lay down the subscribe envelope themselves; a caller supplies only
// what the source has to say.
//
// They differ in exactly one place and everything else follows from
// it: WHEN the id is minted. A hot mints once, at construction, so
// every subscriber joins one live source. A cold mints per
// subscription, so its producer re-runs and its burst rides inside the
// subscriber's own instant (id-inheritance).

// Every subscription leads with its own init. `spent` folds in the
// close and the completion, which is the ONE-SHOT burst: a source with
// nothing left to deliver says everything it has to say inside the
// frame that subscribed to it (Agda's oneShotBurst).
const subscribeBurst = <A>(
  driver: Driver,
  source: SourceId,
  body: InstEvent<A>[],
  spent: boolean,
): InstEmit<A> => ({
  events: [
    { type: "init", source },
    ...body,
    ...(spent
      ? [
          { type: "close", source, reason: "exhausted" } as const,
          { type: "complete" } as const,
        ]
      : []),
  ],
  instant: SUBSCRIBE_FRAME,
  source,
  kind: "subscribe",
});

// hot: minted once and live whether or not anyone is subscribed — a
// delivery with no subscribers is dropped, and still costs fuel. A
// subscriber arriving after the source is spent gets the one-shot
// burst rather than a registration nothing would ever close, and the
// latch is what makes that true DURING the final cascade as well as
// after it (see `LiveSink`).
export const hot = <A>(
  driver: Driver,
  register: (source: SourceId, sink: LiveSink<InstEmit<A>>) => void,
): Observable<InstEmit<A>> => {
  const source = driver.mintSourceId();
  const [live, sink] = channel<InstEmit<A>>();
  let spent = false;
  register(source, {
    next: (emit, isLast) => {
      if (isLast) spent = true;
      sink.next(emit);
      if (isLast) sink.complete();
    },
  });
  return defer(() =>
    spent
      ? of(subscribeBurst<A>(driver, source, [], true))
      : merge(of(subscribeBurst<A>(driver, source, [], false)), live),
  );
};

// cold: a fresh source per subscription. `produce` is handed the id
// just minted and answers with the events that fire INSIDE the
// subscribe burst and, when the source outlives that burst, the
// registration that carries the rest. An absent `async` is what makes
// the source spent in its own burst — there is no other way to say it,
// which is why it is an absence rather than a flag.
export const cold = <A>(
  driver: Driver,
  produce: (source: SourceId) => {
    sync: InstEvent<A>[];
    async?: (sink: Sink<InstEmit<A>>) => () => void;
  },
): Observable<InstEmit<A>> =>
  defer(() => {
    const source = driver.mintSourceId();
    const { sync, async } = produce(source);
    const burst = subscribeBurst(driver, source, sync, async === undefined);
    return async === undefined
      ? of(burst)
      : merge(of(burst), producer<InstEmit<A>>(async));
  });
