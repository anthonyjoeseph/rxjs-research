import { Observable, Subject } from "rxjs";

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
