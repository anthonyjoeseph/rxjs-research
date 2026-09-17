import { Observable, Subject, merge, of } from "rxjs";

// A minimal push sink — the only surface a source producer needs. Kept to
// next/complete (never a raw rxjs Subscriber) so the rest of the impl
// stays clear of imperative rxjs internals; these two constructors are
// the single place Subject / new Observable are allowed to appear.
export type Sink<A> = {
  next: (val: A) => void;
  complete: () => void;
};

// cold: a fresh producer per subscription. `produce` is handed this
// subscription's sink and returns its teardown — unsubscribing runs it,
// cancelling whatever the producer scheduled (Agda's sweepLive). A cold
// re-runs its producer on every subscribe, minting a fresh source each
// time (the caller's job); nothing is shared across subscribers.
export const cold = <A>(
  produce: (sink: Sink<A>) => () => void,
): Observable<A> =>
  new Observable<A>((subscriber) =>
    produce({
      next: (val) => subscriber.next(val),
      complete: () => subscriber.complete(),
    }),
  );

// hot: one shared Subject behind a next/complete sink. Deliveries are
// driven through the sink independently of subscription (a value with no
// subscriber is dropped, and still costs fuel); every subscriber shares
// the one live stream.
export const hot = <A>(): [Observable<A>, Sink<A>] => {
  const subject = new Subject<A>();
  return [
    subject.asObservable(),
    { next: (val) => subject.next(val), complete: () => subject.complete() },
  ];
};

// bracketSync: the sync/async boundary WITHOUT subscribing — the
// replacement for captureSync, and the reason it works is rxjs's own
// subscribe ordering rather than a scheduler. `merge` subscribes its
// inputs in order, synchronously: it subscribes `src`, `src` drains
// its entire subscribe burst during that call, and only then is
// `of(SYNC_END)` subscribed and fires. So the marker lands exactly at
// the boundary, in the same frame, with no hop and no timing change.
//
// This is what lets an operator stop owning its upstream subscription:
// the split arrives as a VALUE in the stream, so a downstream `scan`
// regroups the burst where the operator used to accumulate it by hand.
// That pairing — bracket then fold — is `batchSyncᵉ` followed by
// `liftᵉ`, which is why no new former is owed on the Agda side.
export const SYNC_END = Symbol("end-of-sync");
export type SyncEnd = typeof SYNC_END;
export type Bracketed<A> = A | SyncEnd;

export const bracketSync = <A>(src: Observable<A>): Observable<Bracketed<A>> =>
  merge<Bracketed<A>[]>(src, of(SYNC_END));

// captureSync: subscribe NOW, splitting the subscription at the
// sync/async boundary. Emissions delivered during the subscribe call
// itself land in `burst` (with completedSync when the source finished
// inside it); everything later goes to the caller's sink. This is how
// an operator flattens a subscription's sync burst into the emit that
// caused it (Agda's subscribeInner ∘ splitBurst) — and the third and
// last sanctioned use of raw rxjs subscription machinery in this file.
export type SyncCapture<A> = {
  burst: A[];
  completedSync: boolean;
  unsubscribe: () => void;
};

export const captureSync = <A>(
  obs: Observable<A>,
  onAsync: Sink<A>,
): SyncCapture<A> => {
  const burst: A[] = [];
  let sync = true;
  let completedSync = false;
  const subscription = obs.subscribe({
    next: (val) => {
      if (sync) burst.push(val);
      else onAsync.next(val);
    },
    complete: () => {
      if (sync) completedSync = true;
      else onAsync.complete();
    },
  });
  sync = false;
  return {
    burst,
    completedSync,
    unsubscribe: () => subscription.unsubscribe(),
  };
};
