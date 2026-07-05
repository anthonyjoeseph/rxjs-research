import * as r from "rxjs";
import { v4 as uuid } from "uuid";
import Observable = r.Observable;
import Subject = r.Subject;
import {
  async,
  close,
  init,
  Instantaneous,
  InstAsync,
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

export const share = <A>(inst: Instantaneous<A>): Instantaneous<A> => {
  if ("internalSubject" in inst) {
    return inst;
  }
  const subj = new Subject<InstEmit<A>>();
  let isSubscribed = false;
  let init: InstInit<A> | undefined;
  let subscription: r.Subscription;
  return r.defer(() => {
    if (init !== undefined) {
      return subj.pipe(
        r.startWith(init),
        r.finalize(() => {
          subscription?.unsubscribe();
        }),
      );
    }
    return r.merge(
      subj,
      r.defer(() => {
        if (!isSubscribed) {
          subscription = inst.subscribe({
            next: (emit) => {
              if (!init) {
                init = emit as InstInit<A>;
              }
              subj.next(emit);
            },
            error: (err) => {
              subj.error(err);
            },
            complete: () => {
              subj.complete();
            },
          });
          isSubscribed = true;
        }
        return r.EMPTY;
      }),
    );
  });
};

export const map =
  <A, B>(fn: (a: A) => B) =>
  (inst: Instantaneous<A>): Instantaneous<B> => {
    return inst.pipe(r.map((a) => mapPrimitive(a, fn) as InstEmit<B>));
  };

export const accumulate = <A>(
  initial: A,
): ((val: Instantaneous<(a: A) => A>) => Instantaneous<A>) => {
  let value = initial;
  return map((fn) => {
    const newValue = fn(value);
    value = newValue;
    return newValue;
  });
};

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
