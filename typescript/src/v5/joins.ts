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
import { registrationDeltas } from "./batch-simultaneous";
import { v4 as uuid } from "uuid";

/**
 * rxjs switchAll, plus the protocol obligation rxjs doesn't have: when a
 * LIVE inner is switched away (unsubscribed), downstream provenance memory
 * must learn its registrations ended — an unsubscription emits no closes
 * of its own, so we track each inner's registration balance and emit
 * synthesized closes (`init{p, [close]}`, registration-neutral in form)
 * at the switch. Natural completions balance themselves via the protocol
 * and are not touched.
 */
const switchWithCloses = <A>(
  outers: r.Observable<Instantaneous<A>>,
): Instantaneous<A> =>
  new r.Observable<InstEmit<A>>((observer) => {
    let current: r.Subscription | undefined;
    let balance = new Map<symbol, number>();
    let outerDone = false;
    let innerDone = true;
    const outerSub = outers.subscribe({
      next: (inner) => {
        const wasLive = current !== undefined && !innerDone;
        current?.unsubscribe();
        if (wasLive) {
          for (const [p, n] of balance) {
            for (let i = 0; i < n; i++) {
              observer.next(init<A>({ provenance: p, children: [close] }));
            }
          }
        }
        balance = new Map();
        innerDone = false;
        current = inner.subscribe({
          next: (e) => {
            registrationDeltas(e, balance);
            observer.next(e);
          },
          error: (err) => observer.error(err),
          complete: () => {
            innerDone = true;
            current = undefined;
            if (outerDone) {
              observer.complete();
            }
          },
        });
      },
      error: (err) => observer.error(err),
      complete: () => {
        outerDone = true;
        if (innerDone) {
          observer.complete();
        }
      },
    });
    return () => {
      current?.unsubscribe();
      outerSub.unsubscribe();
    };
  });

/** how the children of a flipped init are combined. Children are tagged:
 * close markers are protocol bookkeeping (the outer's own completion /
 * provenance decrements) and must always be delivered — only the "inner"
 * children participate in the join discipline. merge runs them
 * concurrently; concat serially after each completes (a close marker in
 * the chain correctly delays the outer's close past the last inner);
 * switch and exhaust mirror rxjs on a synchronous burst: each inner is
 * subscribed in arrival order, switch unsubscribing the previous (its
 * sync values pass, its async future dies), exhaust dropping an arrival
 * only while the previous inner is still active. */
type TaggedChild<T> = { kind: "close" | "inner"; obs: r.Observable<T> };
type Combine = <A>(
  children: TaggedChild<InstEmit<A>>[],
) => r.Observable<InstEmit<A>>;
const inners = <T>(children: TaggedChild<T>[]): r.Observable<T>[] =>
  children.filter((c) => c.kind === "inner").map((c) => c.obs);
const closes = <T>(children: TaggedChild<T>[]): r.Observable<T>[] =>
  children.filter((c) => c.kind === "close").map((c) => c.obs);
const combineMerge: Combine = (children) =>
  r.merge(...children.map((c) => c.obs));
const combineConcat: Combine = (children) =>
  r.concat(...children.map((c) => c.obs));
const combineSwitch: Combine = (children) =>
  r.merge(switchWithCloses(r.of(...inners(children))), ...closes(children));
const combineExhaust: Combine = (children) =>
  r.merge(r.of(...inners(children)).pipe(r.exhaustAll()), ...closes(children));

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
            if (batch.value.type === "init") {
              // a MID-STREAM subscription instant (a queued concat inner
              // subscribing at its predecessor's close): its subtree holds
              // fresh root causes, and async-wrapping it would coalesce
              // them into one inherited unit — keep it init-headed
              return init({
                provenance: emit.provenance,
                children: [batch.value],
              });
            }
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

    // the child is an init tree: flip it as a tree — PRESERVING its own
    // provenance layers (the inner init's provenance is the instant owner
    // that downstream window accounting keys on) — and wrap each emission
    // in this level's routing
    return flipInside(emit.child).pipe(
      r.map((child) => async({ provenance: emit.provenance, child })),
    );
  }

  if (emit.children.length === 0) {
    // nothing to flip yet, but downstream must still learn that this
    // subscription exists — batchSimultaneous counts subscriptions per
    // provenance to know how many branches of a diamond to wait for
    return r.of(init<A>({ provenance: emit.provenance, children: [] }));
  }

  return combine(
    emit.children.map((child): TaggedChild<InstEmit<A>> => {
      if (child.type === "close") {
        return {
          kind: "close",
          obs: r.of(
            init<A>({ provenance: emit.provenance, children: [child] }),
          ),
        };
      }
      if (child.type === "value") {
        return {
          kind: "inner",
          obs: child.value.pipe(
            batchSync(),
            r.map((batch) => {
              if (batch.type === "async") {
                if (batch.value.type === "init") {
                  // mid-stream subscription instant: keep init-headed
                  // (see the async-value branch above)
                  return init({
                    provenance: emit.provenance,
                    children: [batch.value],
                  });
                }
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
          ),
        };
      }
      return {
        kind: "inner",
        obs: flipInside(child).pipe(
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
        ),
      };
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
  return switchWithCloses(
    insts.pipe(
      r.map((emit) =>
        isInit(emit) ? flipInside(emit, combineSwitch) : unitDelivery(emit),
      ),
    ),
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
          // an init-headed emission is a MID-STREAM subscription instant
          // (a late burst, e.g. a queued concat inner subscribing): its
          // children are fresh root causes, exactly like the root burst —
          // only async-headed emissions are value-triggered unit deliveries
          return isInit(batchedParent.value)
            ? groupSync(flipInside(batchedParent.value))
            : unitDelivery(batchedParent.value);
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
        // mid-stream subscription instants stay bursts (see mergeAll)
        return isInit(batchedParent.value)
          ? groupSync(flipInside(batchedParent.value, combineConcat))
          : unitDelivery(batchedParent.value);
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
        // mid-stream subscription instants stay bursts (see mergeAll)
        return isInit(batchedParent.value)
          ? groupSync(flipInside(batchedParent.value, combineExhaust))
          : unitDelivery(batchedParent.value);
      }
      // rxjs exhaust semantics on the sync burst: inners are offered in
      // order, and an arrival is dropped only while the previous inner is
      // still active — an inner that completes synchronously (of, EMPTY)
      // frees the slot for the next one in the same burst
      return groupSync(
        r.merge(
          ...batchedParent.value.map((emit) =>
            flipInside(emit, combineExhaust),
          ),
        ),
      );
    }),
    // inners that arrive while one is active are dropped
    r.exhaustAll(),
  );
};
