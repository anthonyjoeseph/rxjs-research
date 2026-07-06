import * as r from "rxjs";
import { v4 as uuid } from "uuid";
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
import { RegBalance, registrationDeltasBySub } from "./batch-simultaneous";

export const EMPTY = r.defer(() => of());

export const of = <As extends unknown[]>(
  ...a: As
): Instantaneous<As[number]> => {
  const provenance = uuid() as unknown as symbol;

  // provenance is per-CALL (a reused cold is the same source — subscribing
  // it twice makes a diamond); sub is per-SUBSCRIPTION (each copy is its
  // own registration)
  return r.defer(() =>
    r.of(
      init<As[number]>({
        provenance,
        sub: uuid() as unknown as symbol,
        children: [...a.map(val), close],
      }),
    ),
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

    // each ref is its own REGISTRATION of the shared source: it re-states
    // the shared stream's protocol AS its own registration, so every node
    // along the share-provenance SPINE is restamped with the ref's sub
    // (top-level wrappers, unit inits, and same-provenance closes — e.g.
    // an upstream take's cut unit). Foreign-provenance subtrees (a complex
    // shared body relaying its inner sources' traffic) pass through
    // untouched — their subs belong to the single underlying
    // subscriptions, re-stated identically to every ref.
    const refSub = uuid() as unknown as symbol;
    const restampNode = (
      e: InstEmit<A> | InstVal<A> | InstClose,
      shareProv: symbol,
    ): InstEmit<A> | InstVal<A> | InstClose => {
      if (e.type === "init" && e.provenance === shareProv) {
        return {
          ...e,
          sub: refSub,
          children: e.children.map((c) => restampNode(c, shareProv)),
        };
      }
      if (e.type === "async" && e.provenance === shareProv) {
        return {
          ...e,
          sub: refSub,
          child:
            e.child == null
              ? null
              : (restampNode(e.child, shareProv) as InstAsync<A>["child"]),
        };
      }
      return e;
    };
    const restamp = (e: InstEmit<A>): InstEmit<A> => {
      const shareProv = life.registration?.provenance;
      return shareProv === undefined
        ? e
        : (restampNode(e, shareProv) as InstEmit<A>);
    };

    let inner: r.Subscription;
    if (life.registration !== undefined) {
      // late subscriber: same provenance, none of the missed values
      subscriber.next(
        init<A>({
          provenance: life.registration.provenance,
          sub: refSub,
          children: [],
        }),
      );
      inner = life.subj.pipe(r.map(restamp)).subscribe(subscriber);
    } else {
      inner = life.subj.pipe(r.map(restamp)).subscribe(subscriber);
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
 * take(n): counts values ANYWHERE in the emission trees (tree order =
 * batch order), truncating mid-emission — take SPLITS instants (ratified:
 * it counts values exactly like rxjs, never waiting for a "whole"
 * instant). On the cut it synthesizes protocol closes for EVERY live
 * registration it has passed downstream (tracked like switchWithCloses),
 * traveling WITH the final value in one unit so a concat advancement
 * coalesces into the closing instant.
 */
export const take =
  (takeNum: number) =>
  <A>(inst: Instantaneous<A>): Instantaneous<A> =>
    r.defer(() => {
      let remaining = takeNum;
      let closed = false; // everything closed downstream
      let done = false; // stop pulling from the source
      const balance: RegBalance = new Map();
      const pruneBalance = (): void => {
        for (const [p, bySub] of balance) {
          for (const [s, n] of bySub) {
            if (n <= 0) bySub.delete(s);
          }
          if (bySub.size === 0) balance.delete(p);
        }
      };

      /** truncate value nodes beyond `remaining`, walking in tree order;
       * registrations/closes pass through untouched */
      const truncChildren = (
        children: (InstEmit<A> | InstVal<A> | InstClose)[],
      ): (InstEmit<A> | InstVal<A> | InstClose)[] =>
        children.flatMap(
          (child): (InstEmit<A> | InstVal<A> | InstClose)[] => {
            if (child.type === "value") {
              if (remaining === 0) return [];
              remaining -= 1;
              return [child];
            }
            if (child.type === "close") return [child];
            return [truncEmit(child)];
          },
        );
      const truncEmit = (e: InstEmit<A>): InstEmit<A> => {
        if (e.type === "init") {
          return init({
            provenance: e.provenance,
            sub: e.sub,
            children: truncChildren(e.children),
          });
        }
        if (e.child == null || e.child.type === "close") return e;
        if (e.child.type === "value") {
          if (remaining === 0) {
            // a dropped value still consumed this delivery's window slot
            return async({
              provenance: e.provenance,
              sub: e.sub,
              child: null,
            });
          }
          remaining -= 1;
          return e;
        }
        return async({
          provenance: e.provenance,
          sub: e.sub,
          child: truncEmit(e.child),
        });
      };

      /** decrement-only closes for every live registration except
       * `excluding` (whose count is returned for literal placement) —
       * each close carries the SUB of the registration it ends */
      const closesFor = (excluding?: symbol): InstAsync<A>[] => {
        const out: InstAsync<A>[] = [];
        for (const [p, bySub] of balance) {
          if (p === excluding) continue;
          for (const [s, n] of bySub) {
            for (let i = 0; i < n; i++) {
              out.push(async<A>({ provenance: p, sub: s, child: close }));
            }
          }
        }
        balance.clear();
        return out;
      };

      /** the innermost non-routing level of an async emission — where the
       * cut's closes must live so they share the closing instant. The
       * anchor's own close is the well-trodden literal unit-close form;
       * other provenances get decrement-only asyncs. */
      const withClosesInnermost = (e: InstAsync<A>): InstAsync<A> => {
        if (e.child != null && e.child.type === "async") {
          return async<A>({
            provenance: e.provenance,
            sub: e.sub,
            child: withClosesInnermost(e.child),
          });
        }
        const base =
          e.child == null
            ? []
            : e.child.type === "init"
              ? e.child.children
              : [e.child];
        // the instant OWNER is the child init's provenance when present
        // (rebuilding with the routing wrapper's would clobber the anchor
        // downstream window accounting keys on)
        const anchor =
          e.child != null && e.child.type === "init"
            ? e.child.provenance
            : e.provenance;
        const anchorSub =
          e.child != null && e.child.type === "init" ? e.child.sub : e.sub;
        // literal closes attribute to the anchor init's OWN sub: place
        // only that registration's count (plus identity-less leftovers)
        // literally; other subs of the anchor provenance close as
        // sub-carrying decrement asyncs via closesFor
        const anchorBySub = balance.get(anchor);
        const ownCount =
          (anchorBySub?.get(anchorSub) ?? 0) +
          (anchorSub !== undefined ? (anchorBySub?.get(undefined) ?? 0) : 0);
        anchorBySub?.delete(anchorSub);
        anchorBySub?.delete(undefined);
        if (anchorBySub !== undefined && anchorBySub.size === 0) {
          balance.delete(anchor);
        }
        const ownCloses = Array.from({ length: ownCount }, () => close);
        return async<A>({
          provenance: e.provenance,
          sub: e.sub,
          child: init<A>({
            provenance: anchor,
            sub: anchorSub,
            children: [...base, ...ownCloses, ...closesFor()],
          }),
        });
      };

      return r.concat(
        inst.pipe(
          r.map((emit): InstEmit<A> => {
            const before = remaining;
            const truncated = truncEmit(emit);
            registrationDeltasBySub(truncated, balance);
            pruneBalance();
            const consumed = before > remaining;
            if (
              remaining === 0 &&
              !closed &&
              (consumed || takeNum === 0)
            ) {
              // THE CUT: the final value(s) and the closes for everything
              // still registered form one unit — one instant
              closed = true;
              done = true;
              if (truncated.type === "init") {
                // a burst cut: place a LITERAL close inside each live
                // registration's own init node — a header+close pair
                // survives every re-flip together, whereas an appended
                // async{p, close} would decrement while the fragmented
                // header stops registering
                const placeCloses = (e: InstEmit<A>): InstEmit<A> => {
                  if (e.type !== "init") {
                    if (e.child == null || e.child.type === "value" || e.child.type === "close") {
                      return e;
                    }
                    return async({
                      provenance: e.provenance,
                      sub: e.sub,
                      child: placeCloses(e.child),
                    });
                  }
                  const children = e.children.map((c) =>
                    c.type === "value" || c.type === "close"
                      ? c
                      : placeCloses(c),
                  );
                  const alreadyClosed = e.children.some(
                    (c) => c.type === "close",
                  );
                  // a literal close inside this init attributes to ITS
                  // registration: place one only when the live balance
                  // holds this node's sub (or an identity-less entry)
                  const bySub = balance.get(e.provenance);
                  const key =
                    bySub !== undefined && (bySub.get(e.sub) ?? 0) > 0
                      ? { k: e.sub }
                      : bySub !== undefined &&
                          (bySub.get(undefined) ?? 0) > 0
                        ? { k: undefined }
                        : undefined;
                  if (key !== undefined && !alreadyClosed) {
                    bySub!.set(key.k, bySub!.get(key.k)! - 1);
                    children.push(close);
                  }
                  return init({
                    provenance: e.provenance,
                    sub: e.sub,
                    children,
                  });
                };
                const placed = placeCloses(truncated) as InstInit<A>;
                pruneBalance();
                // leftovers (registrations without an init node here) fall
                // back to decrement-only asyncs
                return init({
                  provenance: placed.provenance,
                  sub: placed.sub,
                  children: [...placed.children, ...closesFor()],
                });
              }
              return withClosesInnermost(truncated);
            }
            if (!closed && balance.size === 0) {
              // every registration the source made has closed on its own
              closed = true;
              done = true;
            }
            return truncated;
          }),
          r.takeWhile(() => !done, true),
        ),
        r.defer(() => {
          // upstream completed without the cut: close whatever is left
          if (closed) return r.EMPTY;
          closed = true;
          const closes = closesFor();
          return closes.length === 0 ? r.EMPTY : r.of(...closes);
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
