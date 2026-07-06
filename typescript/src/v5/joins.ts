import * as r from "rxjs";
import {
  Instantaneous,
  InstEmit,
  init,
  async,
  close,
  isInit,
  InstAsync,
  InstInit,
  InstVal,
  InstClose,
} from "./types";
import { values } from "./types";
import { batchSync } from "../batch-sync";
import {
  RegBalance,
  registrationDeltas,
  registrationDeltasBySub,
} from "./batch-simultaneous";
import { v4 as uuid } from "uuid";

/**
 * One outer-level emission of a join over a stream-of-streams, classified
 * for the arrival serializers:
 *  - "inner": carries stream value(s) — participates in the join's
 *    discipline (queue / drop / switch). `neutral` is the arrival emission
 *    with its payload replaced by null: when the discipline SWALLOWS the
 *    subscription (concat queues, exhaust drops), the neutral still
 *    consumes the delivery's window slot at the arrival instant —
 *    otherwise the batch window downstream waits forever.
 *  - "forward": a valueless emission (a filtered trigger's null unit, a
 *    routed close) — protocol traffic, delivered at its own instant, never
 *    queued/dropped/switched on.
 */
type Arrival<A> =
  | {
      readonly kind: "inner";
      readonly obs: Instantaneous<A>;
      /** the arrival's PROTOCOL side — closes, registrations, the slot-
       * consuming async wrappers — with the stream values removed. Emitted
       * at the arrival instant when the discipline swallows the
       * subscription (concat queues, exhaust drops). */
      readonly neutral?: InstAsync<A>;
      /** the arrival's PAYLOAD side — the stream values with the protocol
       * closes removed (they were already delivered by the neutral).
       * Subscribed instead of `obs` when the arrival was queued. */
      readonly deferred?: Instantaneous<A>;
    }
  | { readonly kind: "forward"; readonly emit: InstEmit<A> };

/**
 * Split an arrival emission: keep = "protocol" keeps closes, registration
 * leaves, and the slot-consuming async wrappers (values dropped); keep =
 * "payload" keeps the stream values (closes, registration leaves, and
 * subtrees emptied by the strip are dropped entirely — a non-empty init
 * never registered, so an emptied husk must not be left to register).
 */
const stripArrival = (
  e: InstEmit<unknown>,
  keep: "protocol" | "payload",
): InstEmit<unknown> | null => {
  if (e.type === "init") {
    if (e.children.length === 0) {
      // an original registration leaf is protocol
      return keep === "protocol" ? e : null;
    }
    const children = e.children.flatMap(
      (c): (InstEmit<unknown> | InstVal<unknown> | InstClose)[] => {
        if (c.type === "value") {
          return keep === "payload" ? [c] : [];
        }
        if (c.type === "close") {
          return keep === "protocol" ? [c] : [];
        }
        const sub = stripArrival(c, keep);
        return sub === null ? [] : [sub];
      },
    );
    if (children.length === 0) {
      return null;
    }
    return init({
      provenance: e.provenance,
      sub: e.sub,
      children,
    });
  }
  const child =
    e.child == null
      ? null
      : e.child.type === "value"
        ? keep === "payload"
          ? e.child
          : null
        : e.child.type === "close"
          ? keep === "protocol"
            ? e.child
            : null
          : stripArrival(e.child, keep);
  if (child === null && keep === "payload") {
    // nothing but protocol below: drop the wrapper too — its window slot
    // belongs to the arrival instant (the neutral), not the deferred
    // subscription
    return null;
  }
  return async({
    provenance: e.provenance,
    sub: e.sub,
    child: child as InstAsync<unknown>["child"],
  });
};

const classifyArrival = <A>(emit: InstEmit<Instantaneous<A>>): Arrival<A> => {
  if (values(emit).length === 0) {
    // no stream value: nothing arrives — the emission's own provenance
    // structure (registrations, closes, null units) forwards as-is
    return { kind: "forward", emit: emit as unknown as InstEmit<A> };
  }
  if (emit.type !== "async") {
    return { kind: "inner", obs: unitDelivery(emit) };
  }
  const neutral = stripArrival(emit, "protocol") as InstAsync<A>;
  const payload = stripArrival(emit, "payload");
  return {
    kind: "inner",
    obs: unitDelivery(emit),
    neutral,
    ...(payload !== null
      ? {
          deferred: unitDelivery(payload as InstEmit<Instantaneous<A>>),
        }
      : {}),
  };
};

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
  outers: r.Observable<Arrival<A>>,
): Instantaneous<A> =>
  new r.Observable<InstEmit<A>>((observer) => {
    let current: r.Subscription | undefined;
    let balance: RegBalance = new Map();
    let outerDone = false;
    let innerDone = true;
    const outerSub = outers.subscribe({
      next: (arrival) => {
        if (arrival.kind === "forward") {
          observer.next(arrival.emit);
          return;
        }
        const inner = arrival.obs;
        const wasLive = current !== undefined && !innerDone;
        current?.unsubscribe();
        if (wasLive) {
          for (const [p, bySub] of balance) {
            for (const [s, n] of bySub) {
              for (let i = 0; i < n; i++) {
                // async-headed close: pure decrement (an init{p,[close]}
                // would register then close — net zero), carrying the
                // SUB of the stranded registration it ends
                observer.next(
                  async<A>({ provenance: p, sub: s, child: close }),
                );
              }
            }
          }
        }
        balance = new Map();
        innerDone = false;
        current = inner.subscribe({
          next: (e) => {
            // suppress the top-level flip wrapper: groupSync merges
            // same-provenance headers into ONE downstream registration,
            // so counting it per emission would synthesize bogus closes
            registrationDeltasBySub(
              e,
              balance,
              isInit(e) ? e.provenance : undefined,
            );
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

/**
 * Serial subscription with ADVANCEMENT GRAFTING: like r.concat, but when an
 * inner ends via an async event (its emission zeroes the running
 * registration balance — a take's val+close unit, a source's close), that
 * emission is held, the next inner is subscribed synchronously, and its
 * whole flush is grafted into the held emission as one unit: everything the
 * advancement unfolds (chained sync-closing inners included) inherits the
 * closing instant. An inner that closes init-headed (during the static
 * subscription burst) is never held — serial sync chains stay fragmented,
 * each cold its own cause.
 */
// graft the collected flushes into the INNERMOST unit of the held
// emission (outer async layers are join routing — the innermost
// provenance owns the closing instant the flushes must inherit).
// Shared by the sync-burst serializer (serialWithGraft) and the
// async-arrival serializer (serialArrivals).
const graftInner = <A>(
  e: InstAsync<A>,
  extra: (InstEmit<A> | InstVal<A>)[],
): InstAsync<A> => {
      if (e.child != null && e.child.type === "async") {
        return async<A>({
          provenance: e.provenance,
          sub: e.sub,
          child: graftInner(e.child, extra),
        });
      }
      // CANCEL close/re-subscription pairs: when the advancement flush
      // re-subscribes the very source whose close advanced the queue
      // (init{anchor, []} grafted — at ANY depth of the flush's wrapper
      // nesting), the registration continues: cancel it against an anchor
      // close — the unit-level literal close, or (for an already-completed
      // source whose re-subscription closed immediately) the flush's own
      // async{anchor, close}. Downstream window accounting then keeps its
      // count and the diamond keeps its width. Rebuild immutably —
      // subtrees can be shared across subscribers.
      type Child = InstEmit<A> | InstVal<A> | InstClose;
      const removeDeep = (
        list: Child[],
        pred: (c: Child) => boolean,
      ): [Child[], boolean] => {
        for (let i = 0; i < list.length; i++) {
          const c = list[i];
          if (pred(c)) {
            return [[...list.slice(0, i), ...list.slice(i + 1)], true];
          }
          if (c.type === "init") {
            const [sub, found] = removeDeep(c.children, pred);
            if (found) {
              return [
                [
                  ...list.slice(0, i),
                  init<A>({
                    provenance: c.provenance,
                    sub: c.sub,
                    children: sub,
                  }),
                  ...list.slice(i + 1),
                ],
                true,
              ];
            }
          }
        }
        return [list, false];
      };
      // a SELF-CONTAINED re-subscription lifecycle of the anchor source
      // (e.g. take(0) of the closed source: init{anchor, [close]}) nets
      // zero — downstream suppresses its header, so its close must go too
      const neutralizeLifecycles = (list: Child[]): Child[] =>
        list.flatMap((c): Child[] => {
          if (c.type !== "init") {
            return [c];
          }
          if (c.provenance === e.provenance) {
            const closeAt = c.children.findIndex((cc) => cc.type === "close");
            if (closeAt >= 0) {
              const rest = neutralizeLifecycles([
                ...c.children.slice(0, closeAt),
                ...c.children.slice(closeAt + 1),
              ]);
              // drop an emptied husk entirely — leaving init{anchor, []}
              // would read as a LIVE re-subscription and wrongly consume
              // the held emission's own close in the pairing below
              return rest.length === 0
                ? []
                : [
                    init<A>({
                      provenance: c.provenance,
                      sub: c.sub,
                      children: rest,
                    }),
                  ];
            }
          }
          return [
            init<A>({
              provenance: c.provenance,
              sub: c.sub,
              children: neutralizeLifecycles(c.children),
            }),
          ];
        });
      const isAnchorReg = (c: Child) =>
        c.type === "init" &&
        c.provenance === e.provenance &&
        c.children.length === 0;
      const isAnchorAsyncClose = (c: Child) =>
        c.type === "async" &&
        c.provenance === e.provenance &&
        c.child?.type === "close";
      let children2: Child[] = [
        ...(e.child == null
          ? []
          : e.child.type === "init"
            ? e.child.children
            : [e.child]),
        ...neutralizeLifecycles(extra as Child[]),
      ];
      let cancelledCloses = 0;
      for (;;) {
        let regSub: symbol | undefined;
        const [withoutReg, regFound] = removeDeep(children2, (c) => {
          if (isAnchorReg(c)) {
            regSub = (c as InstInit<A>).sub;
            return true;
          }
          return false;
        });
        if (!regFound) {
          break;
        }
        // partner preference: a deep anchor async-close FIRST — that is
        // the completed-source re-subscription's OWN close (the pair is
        // self-contained: born and closed inside this unit, no window
        // slot was ever awaited for it) — so it must carry the
        // re-subscription's OWN sub (an unrelated registration's close,
        // e.g. a dropped diamond branch's, must survive to reach the
        // accounting). Only a LIVE re-subscription (no async-close of its
        // own) pairs with a unit-level literal close — a PRE-EXISTING
        // registration continuing, whose (possibly swallowed) delivery
        // slot the accounting must still see: count it in `cancelled`
        // (that pairing is deliberately CROSS-identity: the close
        // advanced the queue, the re-subscription continues the slot).
        const [withoutClose, closeFound] = removeDeep(
          withoutReg,
          (c) =>
            isAnchorAsyncClose(c) &&
            ((c as InstAsync<A>).sub === undefined ||
              regSub === undefined ||
              (c as InstAsync<A>).sub === regSub),
        );
        if (closeFound) {
          children2 = withoutClose;
          continue;
        }
        const closeIdx = withoutReg.findIndex((c) => c.type === "close");
        if (closeIdx < 0) {
          break;
        }
        children2 = [
          ...withoutReg.slice(0, closeIdx),
          ...withoutReg.slice(closeIdx + 1),
        ];
        cancelledCloses += 1;
      }
      return async<A>({
        provenance: e.provenance,
        sub: e.sub,
        child: init<A>({
          provenance: e.provenance,
          sub: e.child?.type === "init" ? e.child.sub : e.sub,
          // grafted flushes arrive as per-emission fragments re-stating
          // their wrapper headers (init-headed, or relayed through async
          // routing chains) — canonicalize so downstream registration
          // counting sees each wrapper once
          children: canonAsyncSiblings(mergeSiblingInits(children2)),
          ...(cancelledCloses > 0 ? { cancelled: cancelledCloses } : {}),
        }),
      });
};

const serialWithGraft = <A>(
  inners: r.Observable<InstEmit<A>>[],
): r.Observable<InstEmit<A>> =>
  new r.Observable<InstEmit<A>>((observer) => {
    const queue = [...inners];
    let current: r.Subscription | undefined;
    let held: InstAsync<A> | undefined;
    let grafts: (InstEmit<A> | InstVal<A>)[] = [];
    let balance = 0;
    let innerDone = true;
    let advancing = false;

    const netDelta = (e: InstEmit<A>): number => {
      // every emission here is wrapped in the join's own provenance by
      // flipInside — pass it as the parent so the wrap itself isn't
      // re-counted per emission (only the inner's real registrations)
      let n = 0;
      const deltas = registrationDeltas(
        e,
        new Map(),
        e.type === "init" ? e.provenance : undefined,
      );
      for (const d of deltas.values()) {
        n += d;
      }
      return n;
    };

    const release = (): void => {
      if (held === undefined) {
        return;
      }
      const out = grafts.length === 0 ? held : graftInner(held, grafts);
      held = undefined;
      grafts = [];
      observer.next(out);
    };

    const advance = (): void => {
      advancing = true;
      while (innerDone && queue.length > 0) {
        innerDone = false;
        // per-inner balance: hold detection asks whether THIS inner's
        // registrations zeroed out — a previous inner's asymmetric noise
        // (dynamic-arrival units with suppressed headers) must not skew it
        balance = 0;
        current = queue.shift()!.subscribe({
          next: (e) => {
            const before = balance;
            balance += netDelta(e);
            if (held !== undefined && !advancing) {
              // the stream CONTINUED past the held emission without
              // completing: the hold was mistaken (a self-contained
              // cascade happened to zero the balance) — release it plain
              const h = held;
              held = undefined;
              observer.next(h);
            }
            if (held !== undefined) {
              // an advancement flush while a closing emission is held:
              // it belongs to the closing instant. UNWRAP the flip
              // wrapper (the balance was counted with it suppressed, and
              // registerSubtree would re-register it): children graft
              // directly, wrapper closes become decrement-only asyncs
              if (e.type === "init") {
                for (const c of e.children) {
                  grafts.push(
                    c.type === "close"
                      ? async<A>({
                          provenance: e.provenance,
                          sub: e.sub,
                          child: close,
                        })
                      : c,
                  );
                }
              } else {
                grafts.push(e);
              }
              return;
            }
            if (e.type === "async" && balance === 0 && before > 0) {
              // protocol: an emission CLOSING the last live registration
              // is followed synchronously by complete — hold it for
              // grafting (`before > 0`: a net-zero self-contained cascade
              // is not a close)
              held = e;
              return;
            }
            observer.next(e);
          },
          error: (err) => observer.error(err),
          complete: () => {
            innerDone = true;
            current = undefined;
            if (!advancing) {
              advance();
            }
          },
        });
      }
      advancing = false;
      release();
      if (innerDone && queue.length === 0) {
        observer.complete();
      }
    };

    advance();
    return () => current?.unsubscribe();
  });

const combineConcat: Combine = (children) =>
  serialWithGraft(children.map((c) => c.obs));

/**
 * The graft-aware replacement for r.mergeAll(1) at concatAll's OUTER level:
 * async-arriving inner streams queue behind the active one. When the active
 * inner ends via an async event (its closing emission zeroes the running
 * registration balance), the emission is held; an ALREADY-QUEUED inner then
 * subscribes synchronously and its flush grafts into the held emission —
 * the advancement inherits the closing instant, exactly like the sync-burst
 * serializer. An inner arriving after the close subscribes at its own
 * arrival instant (nothing held, no graft). At this level every emission is
 * a self-contained delivery (groupSync wrappers carry their own literal
 * close), so the balance counts registrationDeltas un-suppressed.
 */
const serialArrivals = <A>(
  outer: r.Observable<Arrival<A>>,
): Instantaneous<A> =>
  new r.Observable<InstEmit<A>>((observer) => {
    const queue: Instantaneous<A>[] = [];
    let outerDone = false;
    let current: r.Subscription | undefined;
    let held: InstAsync<A> | undefined;
    let grafts: (InstEmit<A> | InstVal<A>)[] = [];
    let balance = 0;
    let innerDone = true;
    let advancing = false;

    const netDelta = (e: InstEmit<A>): number => {
      let n = 0;
      for (const d of registrationDeltas(e, new Map()).values()) {
        n += d;
      }
      return n;
    };

    const release = (): void => {
      if (held === undefined) {
        return;
      }
      const out = grafts.length === 0 ? held : graftInner(held, grafts);
      held = undefined;
      grafts = [];
      observer.next(out);
    };

    const advance = (): void => {
      advancing = true;
      while (innerDone && queue.length > 0) {
        innerDone = false;
        balance = 0;
        current = queue.shift()!.subscribe({
          next: (e) => {
            const before = balance;
            balance += netDelta(e);
            if (held !== undefined && !advancing) {
              // the stream CONTINUED past the held emission without
              // completing: the hold was mistaken — release it plain
              const h = held;
              held = undefined;
              observer.next(h);
            }
            if (held !== undefined) {
              grafts.push(e);
              return;
            }
            if (e.type === "async" && balance === 0 && before > 0) {
              // protocol: an emission CLOSING the last live registration is
              // followed synchronously by complete — hold it for grafting.
              // (`before > 0` keeps a self-contained subscription flush —
              // one that registers and closes within one emission, or nets
              // zero through routing — from being mistaken for a close.)
              held = e;
              return;
            }
            if (advancing && e.type === "async") {
              // DRAIN GROUPING: everything one synchronous advancement
              // unfolds (a close draining several queued arrivals, each
              // completing synchronously) is ONE instant — hold the first
              // flush so the rest graft into it. The hold cannot outlive
              // the drain: release() runs at the advance loop's end, in
              // the same synchronous cascade.
              held = e;
              return;
            }
            observer.next(e);
          },
          error: (err) => observer.error(err),
          complete: () => {
            innerDone = true;
            current = undefined;
            if (!advancing) {
              advance();
            }
          },
        });
      }
      advancing = false;
      release();
      if (innerDone && outerDone && queue.length === 0) {
        observer.complete();
      }
    };

    const outerSub = outer.subscribe({
      next: (arrival) => {
        if (arrival.kind === "forward") {
          observer.next(arrival.emit);
          return;
        }
        if (innerDone) {
          // subscribed synchronously (now, or by the running advance loop)
          queue.push(arrival.obs);
          if (!advancing) {
            advance();
          }
          return;
        }
        // QUEUED behind a live inner: the arrival's protocol side (closes,
        // registrations, window slots) delivers at the arrival instant;
        // only the payload is deferred to the advancement
        if (arrival.neutral !== undefined) {
          observer.next(arrival.neutral);
        }
        if (arrival.deferred !== undefined) {
          queue.push(arrival.deferred);
        } else if (arrival.neutral === undefined) {
          queue.push(arrival.obs);
        }
      },
      error: (err) => observer.error(err),
      complete: () => {
        outerDone = true;
        if (innerDone && !advancing && queue.length === 0) {
          observer.complete();
        }
      },
    });

    return () => {
      outerSub.unsubscribe();
      current?.unsubscribe();
    };
  });

/**
 * The arrival-aware replacement for r.exhaustAll at exhaustAll's OUTER
 * level: an inner arriving while one is active is dropped — but its
 * delivery still consumes the window slot at the arrival instant (the
 * neutral), and valueless protocol traffic always forwards.
 */
const exhaustArrivals = <A>(
  outer: r.Observable<Arrival<A>>,
): Instantaneous<A> =>
  new r.Observable<InstEmit<A>>((observer) => {
    let current: r.Subscription | undefined;
    let innerDone = true;
    let outerDone = false;
    const outerSub = outer.subscribe({
      next: (arrival) => {
        if (arrival.kind === "forward") {
          observer.next(arrival.emit);
          return;
        }
        if (!innerDone) {
          // dropped — never subscribed, but the slot is consumed
          if (arrival.neutral !== undefined) {
            observer.next(arrival.neutral);
          }
          return;
        }
        innerDone = false;
        current = arrival.obs.subscribe({
          next: (e) => observer.next(e),
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
      outerSub.unsubscribe();
      current?.unsubscribe();
    };
  });
const combineSwitch: Combine = (children) =>
  r.merge(
    switchWithCloses(
      r.of(
        ...inners(children).map((obs) => ({ kind: "inner" as const, obs })),
      ),
    ),
    ...closes(children),
  );
const combineExhaust: Combine = (children) =>
  r.merge(r.of(...inners(children)).pipe(r.exhaustAll()), ...closes(children));

const flipInside = <A>(
  emit: InstEmit<Instantaneous<A>>,
  combine: Combine = combineMerge,
  /** the instant owner, when this subtree sits inside an already-formed
   * UNIT: a derived value found below belongs to the unit's instant, not
   * to the init that happens to hold it — freeze the anchor on crossing */
  anchor?: { provenance: symbol; sub?: symbol },
): Instantaneous<A> => {
  if (emit.type === "async") {
    if (emit.child == null || emit.child.type === "close") {
      return r.of(emit as InstAsync<A>);
    }
    if (emit.child.type === "value") {
      // a dynamically arrived inner
      return emit.child.value.pipe(
        batchSync(),
        r.map((batch) => {
          if (batch.type === "async") {
            return async({
              provenance: emit.provenance,
              sub: emit.sub,
              child: batch.value,
            });
          }
          // an inner that emits NOTHING at subscription (a protocol-less
          // stream like rxjs EMPTY) must not read as `init{trigger, []}` —
          // that shape is a REGISTRATION of the trigger source. A
          // value-less async is the neutral "no delivery" form.
          return batch.value.length === 0
            ? async({
                provenance: emit.provenance,
                sub: emit.sub,
                child: null,
              })
            : init({
                provenance: emit.provenance,
                sub: emit.sub,
                children: batch.value,
              });
        }),
      );
    }
    if (emit.child.type === "async") {
      return flipInside(emit.child, combineMerge, anchor).pipe(
        r.map((child) =>
          async({ provenance: emit.provenance, sub: emit.sub, child }),
        ),
      );
    }

    // the child is an init tree: flip it as a tree — PRESERVING its own
    // provenance layers (the inner init's provenance is the instant owner
    // that downstream window accounting keys on) — and wrap each emission
    // in this level's routing. Crossing into the unit freezes the anchor
    return flipInside(
      emit.child,
      combineMerge,
      anchor ?? { provenance: emit.provenance, sub: emit.sub },
    ).pipe(
      r.map((child) =>
        async({ provenance: emit.provenance, sub: emit.sub, child }),
      ),
    );
  }

  if (emit.children.length === 0) {
    // nothing to flip yet, but downstream must still learn that this
    // subscription exists — batchSimultaneous counts subscriptions per
    // provenance to know how many branches of a diamond to wait for
    return r.of(
      init<A>({
        provenance: emit.provenance,
        sub: emit.sub,
        children: [],
      }),
    );
  }

  return combine(
    emit.children.map((child): TaggedChild<InstEmit<A>> => {
      if (child.type === "close") {
        return {
          kind: "close",
          obs: r.of(
            init<A>({
              provenance: emit.provenance,
              sub: emit.sub,
              children: [child],
            }),
          ),
        };
      }
      if (child.type === "value") {
        const derived = child.derived === true;
        return {
          kind: "inner",
          obs: child.value.pipe(
            batchSync(),
            r.map((batch) => {
              if (batch.type === "async") {
                return async({
                  provenance: emit.provenance,
                  sub: emit.sub,
                  child: batch.value,
                });
              }
              // the inner's subscription flush. A DERIVED trigger value
              // (mapped from an upstream value) spawned this inner, so its
              // flush is one UNIT of the trigger's instant (async-wrapped —
              // the causation rule, transitively through sync bursts); the
              // instant owner is the frozen anchor when the value sat
              // inside an already-formed unit. A literal stream child
              // (merge/concat wiring) is static unfolding: init-headed,
              // each inner cold its own fresh cause.
              return derived
                ? async({
                    provenance: anchor?.provenance ?? emit.provenance,
                    sub: anchor !== undefined ? anchor.sub : emit.sub,
                    child: init({
                      provenance: anchor?.provenance ?? emit.provenance,
                      sub: anchor !== undefined ? anchor.sub : emit.sub,
                      children: batch.value,
                    }),
                  })
                : init({
                    provenance: emit.provenance,
                    sub: emit.sub,
                    children: batch.value,
                  });
            }),
          ),
        };
      }
      return {
        kind: "inner",
        // NO self-header rewrap: repeating the flipped emission's own
        // provenance as an extra layer made fragments of ONE registration
        // look like sibling double-registrations after groupSync
        // flattening. The flipped emissions carry their own heads; only
        // this level's routing wrap is added.
        obs: flipInside(child, combineMerge, anchor).pipe(
          r.map((flipped) => {
            if (flipped.type === "init") {
              return init({
                provenance: emit.provenance,
                sub: emit.sub,
                children: [flipped],
              });
            }
            return async({
              provenance: emit.provenance,
              sub: emit.sub,
              child: flipped,
            });
          }),
        ),
      };
    }),
  );
};

/** the node that owns the delivered instant: follow the async chain to
 * the innermost emission — that is the window the delivery must count
 * against, however deeply the join's argument wrapped it */
const anchorNode = <A>(emit: InstEmit<A>): InstEmit<A> => {
  if (
    emit.type === "async" &&
    emit.child != null &&
    emit.child.type !== "value" &&
    emit.child.type !== "close"
  ) {
    return anchorNode(emit.child);
  }
  return emit;
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
  const anchor = anchorNode(emit);
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
        provenance: anchor.provenance,
        sub: anchor.sub,
        // re-flipping a relayed unit fragments its subtrees into sibling
        // routing chains again — canonicalize so each wrapper header
        // counts once downstream
        child: init({
          provenance: anchor.provenance,
          sub: anchor.sub,
          children: canonAsyncSiblings(mergeSiblingInits(batched.value)),
        }),
      });
    }),
  );
};

export const switchAll = <A>(
  insts: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> => {
  return switchWithCloses(
    insts.pipe(
      r.map(
        (emit): Arrival<A> =>
          isInit(emit)
            ? // groupSync (as in the other joins) so the sync flush is ONE
              // emission with same-provenance headers merged — downstream
              // registration counting (and any enclosing serializer's
              // balance) sees each wrapper exactly once
              {
                kind: "inner",
                obs: groupSync(flipInside(emit, combineSwitch)),
              }
            : // a valueless arrival never switches the live inner away
              classifyArrival(emit),
      ),
    ),
  );
};

/**
 * Recursively merge same-provenance SIBLING init headers: flipping
 * fragments a group into one emission per child stream, each re-stating
 * the level's wrapper header — left as siblings they'd read as double
 * registrations. EMPTY inits are registration leaves (a hot source
 * subscribed twice really is two registrations) and never merge; async
 * children are opaque units and pass through.
 */
const mergeSiblingInits = <A>(
  children: (InstEmit<A> | InstVal<A> | InstClose)[],
): (InstEmit<A> | InstVal<A> | InstClose)[] => {
  type Group = {
    provenance: symbol;
    sub: symbol | undefined;
    hasClose: boolean;
    children: (InstEmit<A> | InstVal<A> | InstClose)[];
    cancelled: number;
  };
  type Item =
    | { kind: "other"; item: InstEmit<A> | InstVal<A> | InstClose }
    | { kind: "group"; group: Group };
  const order: Item[] = [];
  const open = new Map<symbol, Group>();
  for (const c of children) {
    if (c.type === "init" && c.children.length > 0) {
      const fragCloses = c.children.some((cc) => cc.type === "close");
      const g = open.get(c.provenance);
      // a single registration closes AT MOST ONCE: once the open group
      // carries a close, a further same-provenance sibling is a NEW
      // register+close lifecycle (a genuine second registration), not a
      // fragment of the first — start a fresh group
      if (g !== undefined && !g.hasClose) {
        g.children.push(...c.children);
        g.hasClose = fragCloses;
        g.cancelled += c.cancelled ?? 0;
        g.sub = g.sub ?? c.sub;
      } else {
        const fresh: Group = {
          provenance: c.provenance,
          sub: c.sub,
          hasClose: fragCloses,
          children: [...c.children],
          cancelled: c.cancelled ?? 0,
        };
        open.set(c.provenance, fresh);
        order.push({ kind: "group", group: fresh });
      }
    } else {
      order.push({ kind: "other", item: c });
    }
  }
  return order.map((entry) =>
    entry.kind === "other"
      ? entry.item
      : init({
          provenance: entry.group.provenance,
          sub: entry.group.sub,
          children: mergeSiblingInits(entry.group.children),
          ...(entry.group.cancelled > 0
            ? { cancelled: entry.group.cancelled }
            : {}),
        }),
  );
};

/**
 * Merge async-headed siblings that share an IDENTICAL routing chain
 * (the same async provenance path down to an init): they are per-emission
 * fragments of one relayed subtree, and their inner headers would
 * double-count downstream. The chains are rebuilt once around the fused
 * (sibling-merged) innermost init.
 */
const canonAsyncSiblings = <A>(
  children: (InstEmit<A> | InstVal<A> | InstClose)[],
): (InstEmit<A> | InstVal<A> | InstClose)[] => {
  type Link = { provenance: symbol; sub: symbol | undefined };
  type Parsed = { chain: Link[]; inner: InstInit<A> };
  const parse = (c: InstEmit<A> | InstVal<A> | InstClose): Parsed | null => {
    if (c.type !== "async") {
      return null;
    }
    const chain: Link[] = [];
    let cur: InstEmit<A> = c;
    while (cur.type === "async") {
      chain.push({ provenance: cur.provenance, sub: cur.sub });
      if (cur.child == null || cur.child.type === "value" || cur.child.type === "close") {
        return null;
      }
      if (cur.child.type === "init") {
        return { chain, inner: cur.child };
      }
      cur = cur.child;
    }
    return null;
  };
  type Group = {
    chain: Link[];
    provenance: symbol;
    sub: symbol | undefined;
    children: (InstEmit<A> | InstVal<A> | InstClose)[];
    cancelled: number;
  };
  type Item =
    | { kind: "other"; item: InstEmit<A> | InstVal<A> | InstClose }
    | { kind: "group"; group: Group };
  const order: Item[] = [];
  const groups = new Map<string, Group>();
  for (const c of children) {
    const parsed = parse(c);
    if (parsed === null) {
      order.push({ kind: "other", item: c });
      continue;
    }
    const sig =
      parsed.chain.map((l) => String(l.provenance)).join("|") +
      "→" +
      String(parsed.inner.provenance);
    const existing = groups.get(sig);
    if (existing !== undefined) {
      existing.children.push(...parsed.inner.children);
      existing.cancelled += parsed.inner.cancelled ?? 0;
      existing.sub = existing.sub ?? parsed.inner.sub;
    } else {
      const fresh: Group = {
        chain: parsed.chain,
        provenance: parsed.inner.provenance,
        sub: parsed.inner.sub,
        children: [...parsed.inner.children],
        cancelled: parsed.inner.cancelled ?? 0,
      };
      groups.set(sig, fresh);
      order.push({ kind: "group", group: fresh });
    }
  }
  return order.map((entry) => {
    if (entry.kind === "other") {
      return entry.item;
    }
    let node: InstEmit<A> = init({
      provenance: entry.group.provenance,
      sub: entry.group.sub,
      children: mergeSiblingInits(entry.group.children),
      ...(entry.group.cancelled > 0
        ? { cancelled: entry.group.cancelled }
        : {}),
    });
    for (let i = entry.group.chain.length - 1; i >= 0; i--) {
      node = async({
        provenance: entry.group.chain[i].provenance,
        sub: entry.group.chain[i].sub,
        child: node,
      });
    }
    return node;
  });
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
      // async-headed closes are pure decrements (e.g. synthesized at a
      // switch-away): folding one into a per-provenance init group would
      // add a registration and neutralize it — keep them as async
      // children, after the groups so their registrations exist first
      const isAsyncClose = (e: InstEmit<A>) =>
        e.type === "async" && e.child?.type === "close";
      const asyncCloses = batched.value.filter(isAsyncClose);
      const groupedInits = Map.groupBy(
        batched.value.filter((e) => !isAsyncClose(e)),
        (e) => e.provenance,
      );
      const inits = groupedInits.entries().map(([provenance, emits]) =>
        init({
          provenance,
          sub: emits.find((e) => e.sub !== undefined)?.sub,
          children: mergeSiblingInits(
            emits.flatMap((emit) =>
              emit.type === "init"
                ? emit.children
                : emit.child == null
                  ? []
                  : // an async-headed emission in the burst is a derived-
                    // spawned UNIT — keep the wrapper: it marks its subtree
                    // as inheriting the group's instant
                    [emit],
            ),
          ),
        }),
      );
      return init({
        provenance: uuid() as unknown as symbol,
        sub: uuid() as unknown as symbol,
        children: [...inits, ...asyncCloses, close],
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
          // every mid-stream emission is caused by an async event, and its
          // whole synchronous cascade inherits that event's instant
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
    r.map((batchedParent): Arrival<A> => {
      if (batchedParent.type === "async") {
        // async cascades collapse into their event's instant (see mergeAll)
        return classifyArrival(batchedParent.value);
      }
      // synchronously delivered inners subscribe serially, each after the
      // previous completes — including the inners nested in a single init
      return {
        kind: "inner",
        obs: groupSync(
          r.concat(
            ...batchedParent.value.map((emit) =>
              flipInside(emit, combineConcat),
            ),
          ),
        ),
      };
    }),
    // async-arriving inners queue behind whatever is still active; an
    // advancement caused by an async close grafts into the closing instant
    serialArrivals,
  );
};

export const exhaustAll = <A>(
  insts: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> => {
  return insts.pipe(
    batchSync(),
    r.map((batchedParent): Arrival<A> => {
      if (batchedParent.type === "async") {
        // async cascades collapse into their event's instant (see mergeAll)
        return classifyArrival(batchedParent.value);
      }
      // rxjs exhaust semantics on the sync burst: inners are offered in
      // order, and an arrival is dropped only while the previous inner is
      // still active — an inner that completes synchronously (of, EMPTY)
      // frees the slot for the next one in the same burst
      return {
        kind: "inner",
        obs: groupSync(
          r.merge(
            ...batchedParent.value.map((emit) =>
              flipInside(emit, combineExhaust),
            ),
          ),
        ),
      };
    }),
    // inners that arrive while one is active are dropped (their delivery
    // slots still consumed)
    exhaustArrivals,
  );
};
