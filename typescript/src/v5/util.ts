import { pipeWith } from "pipe-ts";
import * as r from "rxjs";
import { concatAll, exhaustAll, mergeAll, switchAll } from "./joins";
import { accumulate, EMPTY, map, of, take } from "./basic-primitives";
import { Instantaneous } from "./types";

export const merge = <A>(...as: Instantaneous<A>[]): Instantaneous<A> => {
  return pipeWith(of(...as), mergeAll());
};

export const concat = <A>(...as: Instantaneous<A>[]): Instantaneous<A> => {
  return pipeWith(of(...as), concatAll);
};

export const switchMap =
  <A, B>(fn: (a: A) => Instantaneous<B>) =>
  (inst: Instantaneous<A>): Instantaneous<B> => {
    return pipeWith(inst, map(fn), switchAll);
  };

export const mergeMap =
  <A, B>(fn: (a: A) => Instantaneous<B>) =>
  (inst: Instantaneous<A>): Instantaneous<B> => {
    return pipeWith(inst, map(fn), mergeAll());
  };

export const concatMap =
  <A, B>(fn: (a: A) => Instantaneous<B>) =>
  (inst: Instantaneous<A>): Instantaneous<B> => {
    return pipeWith(inst, map(fn), concatAll);
  };

export const exhaustMap =
  <A, B>(fn: (a: A) => Instantaneous<B>) =>
  (inst: Instantaneous<A>): Instantaneous<B> => {
    return pipeWith(inst, map(fn), exhaustAll);
  };

/**
 * Emit the source's values until the notifier fires, then complete —
 * derived entirely from the primitives: a stream-of-streams that starts
 * with the source and, on the notifier's first value, delivers EMPTY;
 * switchAll unsubscribes the source (synthesizing its protocol closes)
 * and completes when EMPTY does. NOTE: `switchAll(of(a, b))` would NOT
 * work — the switch would abandon `a` for `b` immediately at subscription.
 * (take counts flat sources, so the notifier should be flat.)
 */
export const takeUntil =
  (notifier: Instantaneous<unknown>) =>
  <A>(source: Instantaneous<A>): Instantaneous<A> =>
    pipeWith(
      merge<Instantaneous<A>>(
        of(source),
        pipeWith(
          notifier,
          take(1),
          map(() => EMPTY as Instantaneous<A>),
        ),
      ),
      switchAll,
    );

/**
 * rxjs `expand`, derived by STRUCTURAL RECURSION on mergeMap: every output
 * value `a` is re-emitted and `fn(a)`'s values are expanded further. The
 * recursion is lazy (each level's pipeline is built only when a value
 * arrives), so it terminates whenever the expansion chains do (fn must
 * eventually return EMPTY, as in rxjs). Under the causation rule a
 * synchronous expansion chain inherits its trigger's instant transitively —
 * the whole cascade is ONE batch.
 */
export const expand =
  <A>(fn: (a: A) => Instantaneous<A>) =>
  (source: Instantaneous<A>): Instantaneous<A> =>
    pipeWith(
      source,
      mergeMap(
        (a: A): Instantaneous<A> =>
          merge(of(a), pipeWith(fn(a), expand(fn))),
      ),
    );

export const scan =
  <A, B>(initial: B, fn: (acc: B, cur: A) => B) =>
  (ob: Instantaneous<A>): Instantaneous<B> => {
    return pipeWith(
      ob,
      map((a): ((b: B) => B) => {
        return (b: B): B => fn(b, a);
      }),
      accumulate(initial),
    );
  };

export const pairwise =
  <A>(initial: A) =>
  (a: Instantaneous<A>): Instantaneous<[A, A]> => {
    return pipeWith(
      a,
      map((newOne): ((a: [A, A]) => [A, A]) => {
        return ([, old]) => [old, newOne];
      }),
      accumulate([initial, initial]),
    );
  };

export const filter =
  <A, B extends A>(pred: (a: A) => a is B) =>
  (ob: Instantaneous<A>): Instantaneous<B> => {
    return pipeWith(
      ob,
      switchMap((a) => (pred(a) ? of(a) : r.EMPTY)),
    );
  };

export const bufferCount =
  <A>(count: number) =>
  (ob: Instantaneous<A>): Instantaneous<A[]> => {
    return pipeWith(
      ob,
      scan([] as A[], (acc, cur) =>
        acc.length === count ? [cur] : [...acc, cur],
      ),
      filter((arr): arr is A[] => arr.length === count),
    );
  };

export const buffer =
  <A>(until: Instantaneous<unknown>) =>
  (ob: Instantaneous<A>): Instantaneous<A[]> => {
    return pipeWith(
      merge<{ type: "emit"; value: A } | { type: "close" }>(
        pipeWith(
          ob,
          map((value) => ({ type: "emit" as const, value })),
        ),
        pipeWith(
          until,
          map(() => ({ type: "close" as const })),
        ),
      ),
      scan(
        { type: "closed" } as { type: "closed" } | { type: "open"; batch: A[] },
        (acc, cur) =>
          cur.type === "close"
            ? { type: "closed" as const }
            : {
                type: "open" as const,
                batch:
                  acc.type === "open" ? [...acc.batch, cur.value] : [cur.value],
              },
      ),
      filter((e): e is { type: "open"; batch: A[] } => e.type === "open"),
      map(({ batch }) => batch),
    );
  };
