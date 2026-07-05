import * as r from "rxjs";
import { v4 as uuid } from "uuid";
import Subject = r.Subject;
import {
  async,
  close,
  init,
  Instantaneous,
  InstClose,
  InstEmit,
  InstInit,
  InstVal,
  isInit,
  map as mapPrimitive,
  val,
  values,
} from "./types";

export const EMPTY = r.defer(() => of());

export const of = <As extends unknown[]>(
  ...a: As
): Instantaneous<As[number]> => {
  const provenance = uuid() as unknown as symbol;

  return r.of(
    init<As[number]>({
      provenance,
      children: [...a.map(val), close],
    }),
  );
};

/**
 * Turn a cold Instantaneous hot: one upstream subscription shared by all
 * subscribers (refcounted — upstream connects with the first subscriber and
 * disconnects when the last leaves, after which a new subscriber starts a
 * fresh life).
 *
 * Provenance: the first subscriber receives the upstream's own init (sync
 * values included); every later subscriber receives a REGISTRATION-ONLY
 * init carrying the same provenance — it must not re-observe values from
 * instants it missed (hot semantics), but downstream batching must still
 * learn that another subscription of this provenance exists.
 */
export const share = <A>(inst: Instantaneous<A>): Instantaneous<A> => {
  if ("internalSubject" in inst) {
    return inst;
  }
  type Life = {
    subj: Subject<InstEmit<A>>;
    registration: InstInit<A> | undefined;
    refCount: number;
    upstream: r.Subscription | undefined;
  };
  let current: Life | undefined;

  return new r.Observable<InstEmit<A>>((subscriber) => {
    if (current === undefined) {
      current = {
        subj: new Subject<InstEmit<A>>(),
        registration: undefined,
        refCount: 0,
        upstream: undefined,
      };
    }
    const life = current;
    life.refCount += 1;

    let inner: r.Subscription;
    if (life.registration !== undefined) {
      // late subscriber: same provenance, none of the missed values
      subscriber.next(
        init<A>({ provenance: life.registration.provenance, children: [] }),
      );
      inner = life.subj.subscribe(subscriber);
    } else {
      inner = life.subj.subscribe(subscriber);
      if (life.upstream === undefined) {
        life.upstream = inst.subscribe({
          next: (emit) => {
            if (life.registration === undefined && isInit(emit)) {
              life.registration = emit;
            }
            life.subj.next(emit);
          },
          error: (err) => {
            life.subj.error(err);
          },
          complete: () => {
            life.subj.complete();
          },
        });
      }
    }

    return () => {
      inner.unsubscribe();
      life.refCount -= 1;
      if (life.refCount === 0) {
        life.upstream?.unsubscribe();
        if (current === life) {
          current = undefined;
        }
      }
    };
  });
};

export const map =
  <A, B>(fn: (a: A) => B) =>
  (inst: Instantaneous<A>): Instantaneous<B> => {
    return inst.pipe(r.map((a) => mapPrimitive(a, fn) as InstEmit<B>));
  };

/**
 * The state primitive: threads an accumulator through the stream's values.
 * Provenance-transparent (time-preserving, one value in, one value out —
 * batchSimultaneous treats it exactly like map). State is per-subscription;
 * share(accumulate(...)) is how you deliberately share the accumulator.
 */
export const accumulate =
  <A>(initial: A) =>
  (inst: Instantaneous<(a: A) => A>): Instantaneous<A> =>
    r.defer(() => {
      let value = initial;
      return map<(a: A) => A, A>((fn) => {
        const newValue = fn(value);
        value = newValue;
        return newValue;
      })(inst);
    });

/**
 * NOTE: counts the values of a flat source (sync values in the init, one
 * value per async emission); values nested inside grouped inits produced by
 * the joins are not counted.
 */
export const take =
  (takeNum: number) =>
  <A>(inst: Instantaneous<A>): Instantaneous<A> =>
    r.defer(() => {
      let provenance: symbol | undefined;
      let remaining = takeNum;
      let closed = false; // a close has been delivered downstream
      let done = false; // stop pulling from the source
      return r.concat(
        inst.pipe(
          r.map((emit): InstEmit<A> => {
            if (isInit(emit)) {
              provenance = emit.provenance;
              const children = emit.children.flatMap(
                (child): (InstEmit<A> | InstVal<A> | InstClose)[] => {
                  if (closed) return [];
                  if (child.type === "value") {
                    if (remaining === 0) return [];
                    remaining -= 1;
                    return [child];
                  }
                  if (child.type === "close") {
                    closed = true;
                  }
                  return [child];
                },
              );
              if (remaining === 0 && !closed) {
                closed = true;
                children.push(close);
              }
              done = closed;
              return init({ provenance: emit.provenance, children });
            }
            if (emit.child?.type === "close") {
              closed = true;
              done = true;
            } else if (emit.child?.type === "value" && remaining > 0) {
              remaining -= 1;
              if (remaining === 0) {
                done = true;
              }
            }
            return emit;
          }),
          r.takeWhile(() => !done, true),
        ),
        r.defer(() => {
          if (closed || provenance === undefined) {
            return r.EMPTY;
          }
          closed = true;
          return r.of(async<A>({ provenance, child: close }));
        }),
      );
    });

export const fromInstantaneous: <A>(obs: Instantaneous<A>) => r.Observable<A> =
  r.pipe(
    r.mergeMap((emit) => {
      const allVals = values(emit);
      return r.of(...allVals);
    }),
  );
