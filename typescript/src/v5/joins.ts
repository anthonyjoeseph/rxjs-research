import * as r from "rxjs";
import {
  Instantaneous,
  InstEmit,
  init,
  async,
  close,
  isInit,
  InstAsync,
} from "./types";
import { batchSync } from "../batch-sync";
import { v4 as uuid } from "uuid";

/** how the children of a flipped init are combined: concurrently (merge,
 * the default), or serially (concat, for concatAll) */
type Combine = <T>(obs: r.Observable<T>[]) => r.Observable<T>;
const combineMerge: Combine = (obs) => r.merge(...obs);
const combineConcat: Combine = (obs) => r.concat(...obs);

const flipInside = <A>(
  emit: InstEmit<Instantaneous<A>>,
  combine: Combine = combineMerge,
): Instantaneous<A> => {
  if (emit.type === "async") {
    if (emit.child == null || emit.child.type === "close") {
      return r.of(emit as InstAsync<A>);
    }
    if (emit.child.type === "value") {
      return emit.child.value.pipe(
        batchSync(),
        r.map((batch) => {
          if (batch.type === "async") {
            return async({ provenance: emit.provenance, child: batch.value });
          }
          return init({ provenance: emit.provenance, children: batch.value });
        }),
      );
    }
    if (emit.child.type === "async") {
      return flipInside(emit.child).pipe(
        r.map((child) => async({ provenance: emit.provenance, child })),
      );
    }

    return r
      .merge(
        ...emit.child.children.map((child): r.Observable<InstEmit<A>> => {
          if (child.type === "close") {
            return r.of(emit as InstAsync<A>);
          }
          if (child.type === "value") {
            return child.value.pipe(
              batchSync(),
              r.map((batch) => {
                if (batch.type === "async") {
                  return async({
                    provenance: emit.provenance,
                    child: batch.value,
                  });
                }
                return init({
                  provenance: emit.provenance,
                  children: batch.value,
                });
              }),
            );
          }
          return flipInside(child).pipe(
            r.map((child) => {
              if (child.type === "init") {
                return init({ provenance: emit.provenance, children: [child] });
              }
              return async({ provenance: emit.provenance, child });
            }),
          );
        }),
      )
      .pipe(
        r.map((child) => {
          if (child.type === "init") {
            return init({ provenance: emit.provenance, children: [child] });
          }
          return async({ provenance: emit.provenance, child });
        }),
      );
  }

  if (emit.children.length === 0) {
    // nothing to flip yet, but downstream must still learn that this
    // subscription exists — batchSimultaneous counts subscriptions per
    // provenance to know how many branches of a diamond to wait for
    return r.of(init<A>({ provenance: emit.provenance, children: [] }));
  }

  return combine(
    emit.children.map((child): r.Observable<InstEmit<A>> => {
      if (child.type === "close") {
        return r.of(
          init<A>({ provenance: emit.provenance, children: [child] }),
        );
      }
      if (child.type === "value") {
        return child.value.pipe(
          batchSync(),
          r.map((batch) => {
            if (batch.type === "async") {
              return async({ provenance: emit.provenance, child: batch.value });
            }
            return init({ provenance: emit.provenance, children: batch.value });
          }),
        );
      }
      return flipInside(child).pipe(
        r.map((child) => {
          if (child.type === "init") {
            return init({ provenance: child.provenance, children: [child] });
          }
          return async({ provenance: child.provenance, child });
        }),
        r.map((child) => {
          if (child.type === "init") {
            return init({ provenance: emit.provenance, children: [child] });
          }
          return async({ provenance: emit.provenance, child });
        }),
      );
    }),
  );
};

/** the provenance that owns the delivered instant: follow the async chain
 * to the innermost emission — that is the window the delivery must count
 * against, however deeply the join's argument wrapped it */
const anchorProvenance = <A>(emit: InstEmit<A>): symbol => {
  if (
    emit.type === "async" &&
    emit.child != null &&
    emit.child.type !== "value" &&
    emit.child.type !== "close"
  ) {
    return anchorProvenance(emit.child);
  }
  return emit.provenance;
};

/** one async delivery from the parent stream: everything the flipped
 * emission produces synchronously — the freshly subscribed inners' sync
 * values, registrations and closes — forms ONE unit that inherits the
 * delivering instant (the blessed causal-batching semantics: an inner
 * spawned by an async trigger is simultaneous with it, siblings included).
 * Later emissions of long-lived inners pass through untouched. */
const unitDelivery = <A>(
  emit: InstEmit<Instantaneous<A>>,
): Instantaneous<A> => {
  const provenance = anchorProvenance(emit);
  return flipInside(emit).pipe(
    batchSync(),
    r.map((batched): InstEmit<A> => {
      if (batched.type === "async") {
        return batched.value;
      }
      if (batched.value.length === 1 && batched.value[0].type === "async") {
        // a routed close or an already-formed unit: untouched
        return batched.value[0];
      }
      return async({
        provenance,
        child: init({ provenance, children: batched.value }),
      });
    }),
  );
};

export const switchAll = <A>(
  insts: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> => {
  return insts.pipe(
    r.map((emit) => (isInit(emit) ? flipInside(emit) : unitDelivery(emit))),
    r.switchAll(),
  );
};

/** group the emissions that arrive synchronously at subscription into one
 * init tree per provenance, wrapped in a fresh subscription-instant init */
const groupSync = <A>(flipped: Instantaneous<A>): Instantaneous<A> =>
  flipped.pipe(
    batchSync(),
    r.map((batched): InstEmit<A> => {
      if (batched.type === "async") {
        return batched.value;
      }
      const groupedInits = Map.groupBy(batched.value, (e) => e.provenance);
      const inits = groupedInits.entries().map(([provenance, emits]) =>
        init({
          provenance,
          children: emits.flatMap((emit) =>
            emit.type === "init"
              ? emit.children
              : emit.child == null
                ? []
                : [emit.child],
          ),
        }),
      );
      return init({
        provenance: uuid() as unknown as symbol,
        children: [...inits, close],
      });
    }),
  );

export const mergeAll =
  (concurrency?: number) =>
  <A>(insts: Instantaneous<Instantaneous<A>>): Instantaneous<A> => {
    return insts.pipe(
      batchSync(),
      r.map((batchedParent): Instantaneous<A> => {
        if (batchedParent.type === "async") {
          return unitDelivery(batchedParent.value);
        }
        return groupSync(
          r.merge(...batchedParent.value.map((emit) => flipInside(emit))),
        );
      }),
      r.mergeAll(concurrency),
    );
  };

export const concatAll = <A>(
  insts: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> => {
  return insts.pipe(
    batchSync(),
    r.map((batchedParent): Instantaneous<A> => {
      if (batchedParent.type === "async") {
        return unitDelivery(batchedParent.value);
      }
      // synchronously delivered inners subscribe serially, each after the
      // previous completes — including the inners nested in a single init
      return groupSync(
        r.concat(
          ...batchedParent.value.map((emit) => flipInside(emit, combineConcat)),
        ),
      );
    }),
    // async-arriving inners queue behind whatever is still active
    r.mergeAll(1),
  );
};

export const exhaustAll = <A>(
  insts: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> => {
  return insts.pipe(
    batchSync(),
    r.map((batchedParent): Instantaneous<A> => {
      if (batchedParent.type === "async") {
        return unitDelivery(batchedParent.value);
      }
      // of the inners delivered synchronously at subscription, only the
      // first is subscribed; the rest arrive while it is active and are
      // dropped, mirroring rxjs exhaust semantics
      let taken = false;
      const pruned = batchedParent.value.map(
        (emit): InstEmit<Instantaneous<A>> => {
          if (!isInit(emit)) {
            return emit;
          }
          return init({
            provenance: emit.provenance,
            children: emit.children.filter((child) => {
              if (child.type !== "value") {
                return true;
              }
              if (taken) {
                return false;
              }
              taken = true;
              return true;
            }),
          });
        },
      );
      return groupSync(r.merge(...pruned.map((emit) => flipInside(emit))));
    }),
    // inners that arrive while one is active are dropped
    r.exhaustAll(),
  );
};
