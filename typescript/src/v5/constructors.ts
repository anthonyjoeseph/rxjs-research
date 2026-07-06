/* eslint-disable @typescript-eslint/no-explicit-any */
import * as r from "rxjs";
import { v4 as uuid } from "uuid";
import Observable = r.Observable;
import Subject = r.Subject;
import {
  async,
  close,
  init,
  Instantaneous,
  InstClose,
  InstEmit,
  val,
} from "./types";
import { Observer, Subscription } from "rxjs";

export const cold = <T>(
  subscribe?: (
    this: Observable<T>,
    subscriber: r.Subscriber<T>,
  ) => r.TeardownLogic,
): Instantaneous<T> => {
  return r.defer(() => {
    const provenance = uuid() as unknown as symbol;
    const sub = uuid() as unknown as symbol;
    return r.concat(
      r.of(init<T>({ provenance, sub, children: [] })),
      new Observable(subscribe).pipe(
        r.map((value) => async<T>({ provenance, sub, child: val(value) })),
      ),
      r.of(async<T>({ provenance, sub, child: close })),
    );
  });
};

export class InstantSubject<T>
  extends Observable<InstEmit<T>>
  implements r.SubscriptionLike
{
  protected _provenance: symbol;
  public closed: boolean;
  internalSubject: Subject<InstEmit<T>>;

  constructor() {
    super();
    this.internalSubject = new Subject<InstEmit<T>>();
    this.closed = false;
    this._provenance = uuid() as unknown as symbol;
  }

  subscribe(
    observerOrNext?:
      Partial<Observer<InstEmit<T>>> | ((value: InstEmit<T>) => void) | null,
  ): Subscription;
  /** @deprecated Instead of passing separate callback arguments, use an observer argument. Signatures taking separate callback arguments will be removed in v8. Details: https://rxjs.dev/deprecations/subscribe-arguments */
  subscribe(
    next?: ((value: InstEmit<T>) => void) | null,
    error?: ((error: any) => void) | null,
    complete?: (() => void) | null,
  ): Subscription;
  subscribe(
    observerOrNext?:
      Partial<Observer<InstEmit<T>>> | ((value: InstEmit<T>) => void) | null,
    errorArg?: ((error: any) => void) | null,
    completeArg?: (() => void) | null,
  ): r.Subscription {
    const next =
      observerOrNext == null
        ? undefined
        : typeof observerOrNext === "function"
          ? observerOrNext
          : observerOrNext.next?.bind(observerOrNext);
    const error =
      typeof observerOrNext !== "function" && observerOrNext != null
        ? observerOrNext.error?.bind(observerOrNext)
        : (errorArg ?? undefined);
    const complete =
      typeof observerOrNext !== "function" && observerOrNext != null
        ? observerOrNext.complete?.bind(observerOrNext)
        : (completeArg ?? undefined);

    // each subscriber is its own registration: deliveries relayed through
    // it are restamped with its sub at the top level
    const sub = uuid() as unknown as symbol;
    return r
      .concat(
        r.of(init<T>({ provenance: this._provenance, sub, children: [] })),
        this.internalSubject.pipe(
          r.map((e): InstEmit<T> => ({ ...e, sub })),
        ),
        r.of(async<T>({ provenance: this._provenance, sub, child: close })),
      )
      .subscribe({
        next: (value) => {
          next?.(value);
        },
        error: (value) => {
          error?.(value);
        },
        complete: () => {
          complete?.();
        },
      });
  }

  unsubscribe(): void {
    this.closed = true;
    this.internalSubject.unsubscribe();
  }

  next(value: T) {
    this.internalSubject.next(
      async({ provenance: this._provenance, child: val(value) }),
    );
  }

  error(err: any) {
    this.internalSubject.error(err);
  }

  complete() {
    this.closed = true;
    this.internalSubject.complete();
  }
}
