import { pipeWith } from "pipe-ts";
import { EMPTY, map, of, take } from "../v5/basic-primitives";
import { InstantSubject } from "../v5/constructors";
import { Instantaneous } from "../v5/types";
import { merge, mergeMap } from "../v5/util";
import { mapTimed, mergeTimed, takeTimed, Time, TimedObs } from "./timed";

/**
 * A deep embedding of the primitive combinators. "batchSimultaneous behaves
 * correctly for any combination of the primitives" is a quantification over
 * these trees; the fast-check oracle samples them, and the Agda proof will
 * do induction on the same syntax.
 *
 * `src` refers to a shared root subject by index — the same index appearing
 * twice is exactly the diamond. Each `of` occurrence is its own root cause
 * (fresh provenance in rxjs, fresh origin in the model).
 */
export type Fn = { readonly op: "add" | "mul"; readonly k: number };
export const applyFn = (fn: Fn, n: number): number =>
  fn.op === "add" ? n + fn.k : n * fn.k;

export type Exp =
  | { readonly type: "src"; readonly index: number }
  | { readonly type: "of"; readonly values: readonly number[]; origin?: number }
  | { readonly type: "empty" }
  | { readonly type: "map"; readonly fn: Fn; readonly arg: Exp }
  | { readonly type: "take"; readonly count: number; readonly arg: Exp }
  | { readonly type: "merge"; readonly left: Exp; readonly right: Exp }
  // mergeMap with a pure inner: each trigger value v spawns of(...fns(v)).
  // THE BLESSED CAUSAL-BATCHING SEMANTICS (option 1, non-transitive):
  //  - an ASYNC trigger's inner inherits the trigger's exact (tick, origin)
  //    — the inner's values are simultaneous with the event that caused them
  //  - a SYNC-BURST trigger's inner is a fresh root cause (fresh origin at
  //    tick 0) — sibling inners subscribed in one burst never batch together
  | {
      readonly type: "mergeMap";
      readonly fns: readonly Fn[];
      readonly arg: Exp;
      origin?: number;
    };

/**
 * Assign each `of` / `mergeMap` occurrence a unique origin base, numbered in
 * subscription order (depth-first, left to right) so the model's tick-0
 * ordering matches the order rxjs delivers subscription-time batches.
 * Bases are spaced 1000 apart: a mergeMap's k-th sync-triggered inner takes
 * base + k + 1, staying ordered between its node and the next node.
 */
export const assignOrigins = (exp: Exp, firstOrigin: number): Exp => {
  let node = 0;
  const nextBase = () => firstOrigin + 1000 * node++;
  const go = (e: Exp): Exp => {
    switch (e.type) {
      case "src":
      case "empty":
        return e;
      case "of":
        return { ...e, origin: nextBase() };
      case "map":
        return { ...e, arg: go(e.arg) };
      case "take":
        return { ...e, arg: go(e.arg) };
      case "merge": {
        const left = go(e.left);
        const right = go(e.right);
        return { ...e, left, right };
      }
      case "mergeMap": {
        const origin = nextBase();
        return { ...e, origin, arg: go(e.arg) };
      }
    }
  };
  return go(exp);
};

/** one driver step: source `index` emits `value` (each step is one instant) */
export type SourceEvent = readonly [index: number, value: number];

export const sourceTimedLists = (
  numSources: number,
  events: readonly SourceEvent[],
): TimedObs<number>[] => {
  const lists: [Time, number][][] = Array.from(
    { length: numSources },
    () => [],
  );
  events.forEach(([index, value], k) => {
    lists[index].push([[k + 1, index], value]);
  });
  return lists;
};

/** the denotation: interpret an Exp as a timed list */
export const denote = (
  exp: Exp,
  sources: readonly TimedObs<number>[],
): TimedObs<number> => {
  switch (exp.type) {
    case "src":
      return sources[exp.index];
    case "of": {
      if (exp.origin === undefined) {
        throw new Error("denote: call assignOrigins first");
      }
      const origin = exp.origin;
      return exp.values.map((v) => [[0, origin], v] as const);
    }
    case "empty":
      return [];
    case "map":
      return mapTimed(denote(exp.arg, sources), (n) => applyFn(exp.fn, n));
    case "take":
      return takeTimed(denote(exp.arg, sources), exp.count);
    case "merge":
      return mergeTimed(denote(exp.left, sources), denote(exp.right, sources));
    case "mergeMap": {
      if (exp.origin === undefined) {
        throw new Error("denote: call assignOrigins first");
      }
      const triggers = denote(exp.arg, sources);
      const out: (readonly [Time, number])[] = [];
      let syncSeq = 0;
      for (const [t, v] of triggers) {
        const innerVals = exp.fns.map((f) => applyFn(f, v));
        if (t[0] === 0) {
          // sync-burst trigger: the inner is a fresh root cause
          syncSeq += 1;
          const origin = exp.origin + syncSeq;
          for (const w of innerVals) {
            out.push([[0, origin], w] as const);
          }
        } else {
          // async trigger: the inner inherits the trigger's instant
          for (const w of innerVals) {
            out.push([t, w] as const);
          }
        }
      }
      return out;
    }
  }
};

/** the implementation under test: interpret the same Exp with rxjs */
export const interpret = (
  exp: Exp,
  subjects: readonly InstantSubject<number>[],
): Instantaneous<number> => {
  switch (exp.type) {
    case "src":
      return subjects[exp.index];
    case "of":
      return of(...exp.values);
    case "empty":
      return EMPTY;
    case "map":
      return pipeWith(
        interpret(exp.arg, subjects),
        map((n: number) => applyFn(exp.fn, n)),
      );
    case "take":
      return pipeWith(interpret(exp.arg, subjects), take(exp.count));
    case "merge":
      return merge(
        interpret(exp.left, subjects),
        interpret(exp.right, subjects),
      );
    case "mergeMap":
      return pipeWith(
        interpret(exp.arg, subjects),
        mergeMap((n: number) => of(...exp.fns.map((f) => applyFn(f, n)))),
      );
  }
};

export const showExp = (exp: Exp): string => {
  switch (exp.type) {
    case "src":
      return `src${exp.index}`;
    case "of":
      return `of(${exp.values.join(",")})`;
    case "empty":
      return "empty";
    case "map":
      return `map(${exp.fn.op} ${exp.fn.k})(${showExp(exp.arg)})`;
    case "take":
      return `take(${exp.count})(${showExp(exp.arg)})`;
    case "merge":
      return `merge(${showExp(exp.left)}, ${showExp(exp.right)})`;
    case "mergeMap":
      return `mergeMap(v => of(${exp.fns
        .map((f) => `${f.op} ${f.k}`)
        .join(", ")}))(${showExp(exp.arg)})`;
  }
};
