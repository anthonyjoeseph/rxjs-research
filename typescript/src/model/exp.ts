import { pipeWith } from "pipe-ts";
import { EMPTY, map, of, share, take } from "../v5/basic-primitives";
import { InstantSubject } from "../v5/constructors";
import { concatAll, exhaustAll, mergeAll, switchAll } from "../v5/joins";
import { Instantaneous } from "../v5/types";
import { merge, mergeMap } from "../v5/util";
import {
  compareTime,
  mapTimed,
  mergeTimed,
  takeTimed,
  Time,
  TimedObs,
} from "./timed";

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
    }
  // let x = share(binding) in body — the body's shareRef occurrences all
  // subscribe ONE hot copy of the binding. The first subscriber (pre-order)
  // sees everything; later subscribers share the provenance but miss the
  // subscription-frame values (registration-only replay, hot semantics).
  | { readonly type: "letShare"; readonly binding: Exp; readonly body: Exp }
  | { readonly type: "shareRef"; first?: boolean }
  // THE JOIN PRIMITIVE, two-sorted: mergeAll consumes a stream-of-streams
  // expression. merge and mergeMap are DERIVED: merge(a,b) = mergeAll(ofS
  // [a,b]) and mergeMap(f) = mergeAll(mapS f) — kept above as aliases, with
  // the derivation laws checked by the oracle.
  | { readonly type: "mergeAll"; readonly outer: ExpS }
  // THE SERIAL JOINS, over a sync burst of inners (async outers are a
  // recorded frontier). All three mirror rxjs and need CLOSE TIMES:
  //  - concatAll subscribes each inner when the previous closes. An inner
  //    subscribed at an async close is a fresh root cause AT that tick
  //    (same tick, its own origin: ordered right after the close, never
  //    batched with it); a sync-closing chain stays in the subscription
  //    frame, each `of` its own instant.
  //  - switchAll subscribes burst inners in turn: every inner's
  //    subscription-frame emissions pass, only the last stays live.
  //  - exhaustAll walks the burst: an inner that closes within the frame
  //    frees the slot; the first inner with a pending close blocks — the
  //    rest are dropped entirely (never subscribed, never registered).
  | { readonly type: "concatAll"; readonly inners: readonly Exp[] }
  | { readonly type: "switchAll"; readonly inners: readonly Exp[] }
  | { readonly type: "exhaustAll"; readonly inners: readonly Exp[] };

export type ExpS =
  | { readonly type: "ofS"; readonly inners: readonly Exp[] }
  | {
      readonly type: "mapS";
      readonly fns: readonly Fn[];
      readonly arg: Exp;
      origin?: number;
    }
  // DYNAMIC INNER ARRIVAL: every trigger subscribes the enclosing letShare's
  // hot stream (mergeMap(v => x)). A late subscription sees only the suffix
  // strictly after its trigger instant — so the shared stream's events batch
  // with multiplicity equal to the number of triggers so far (growing as
  // subscribers arrive). Only valid inside a letShare body.
  | { readonly type: "mapShareS"; readonly arg: Exp };

/**
 * Assign each `of` / `mergeMap` occurrence a unique origin base, numbered in
 * subscription order (depth-first, left to right) so the model's tick-0
 * ordering matches the order rxjs delivers subscription-time batches.
 * Bases are spaced 1000 apart: a mergeMap's k-th sync-triggered inner takes
 * base + k + 1, staying ordered between its node and the next node.
 */
export const assignOrigins = (exp: Exp, firstOrigin: number): Exp => {
  let node = 0;
  let firstRefSeen = false;
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
      case "letShare": {
        const binding = go(e.binding);
        const body = go(e.body);
        return { ...e, binding, body };
      }
      case "shareRef": {
        const first = !firstRefSeen;
        firstRefSeen = true;
        return { ...e, first };
      }
      case "mergeAll": {
        // ofS allocates nothing itself (so the derivation law lines up
        // origin-for-origin with the derived merge); mapS allocates a base
        // exactly like mergeMap; mapShareS's hot inners carry the shared
        // stream's own origins, so nothing to allocate
        if (e.outer.type === "ofS") {
          return {
            ...e,
            outer: { ...e.outer, inners: e.outer.inners.map(go) },
          };
        }
        if (e.outer.type === "mapShareS") {
          return { ...e, outer: { ...e.outer, arg: go(e.outer.arg) } };
        }
        const origin = nextBase();
        return {
          ...e,
          outer: { ...e.outer, origin, arg: go(e.outer.arg) },
        };
      }
      case "concatAll":
      case "switchAll":
      case "exhaustAll":
        return { ...e, inners: e.inners.map(go) };
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

/**
 * A close tick: "frame" means the expression completes within its own
 * subscription instant (a sync burst — of, empty, take 0, a fully-taken
 * cold); a number is the tick of the async instant it completes at.
 * Serial joins thread closes into subscription ticks.
 */
export type CloseTick = "frame" | number;

const maxClose = (a: CloseTick, b: CloseTick): CloseTick =>
  a === "frame" ? b : b === "frame" ? a : Math.max(a, b);

type Denoted = {
  readonly list: TimedObs<number>;
  readonly close: CloseTick;
};

type Ctx = {
  readonly sources: readonly TimedObs<number>[];
  /** the tick at which source `index` completes (the driver completes all
   * subjects, in index order, after the last event) */
  readonly srcCloseTick: (index: number) => number;
  /** origins at or above this are cold-born (assigned by assignOrigins):
   * instants of `of` values and sync-spawned inners. A trigger at a
   * cold-born instant is a subscription-frame delivery WHEREVER it sits in
   * time (a queued concat inner's values are one); its spawned inners are
   * fresh root causes. Triggers at src-origin instants are driver events —
   * their inners inherit the instant. */
  readonly coldOriginMin: number;
  readonly shared?: Denoted;
};

/**
 * The denotation, subscription-time-parameterized: `subTick` is the tick
 * of the instant this expression is subscribed at (0 = the root
 * subscription). A cold `of` subscribed at a later tick is a fresh root
 * cause AT that tick — [subTick, ownOrigin] orders right after its cause
 * but never batches with it. Hot sources contribute only their suffix.
 */
const denoteC = (exp: Exp, ctx: Ctx, subTick: number): Denoted => {
  switch (exp.type) {
    case "src": {
      // a source that already completed at (or before) the subscription
      // instant closes within the frame — closes never point into the past
      const closeTick = ctx.srcCloseTick(exp.index);
      return {
        list: ctx.sources[exp.index].filter(([t]) => t[0] > subTick),
        close: closeTick > subTick ? closeTick : "frame",
      };
    }
    case "of": {
      if (exp.origin === undefined) {
        throw new Error("denote: call assignOrigins first");
      }
      const origin = exp.origin;
      return {
        list: exp.values.map((v) => [[subTick, origin], v] as const),
        close: "frame",
      };
    }
    case "empty":
      return { list: [], close: "frame" };
    case "map": {
      const arg = denoteC(exp.arg, ctx, subTick);
      return {
        list: mapTimed(arg.list, (n) => applyFn(exp.fn, n)),
        close: arg.close,
      };
    }
    case "take": {
      const arg = denoteC(exp.arg, ctx, subTick);
      if (exp.count === 0) {
        return { list: [], close: "frame" };
      }
      if (arg.list.length >= exp.count) {
        const closeAt = arg.list[exp.count - 1][0];
        return {
          list: takeTimed(arg.list, exp.count),
          close: closeAt[0] === subTick ? "frame" : closeAt[0],
        };
      }
      return arg;
    }
    case "merge": {
      const left = denoteC(exp.left, ctx, subTick);
      const right = denoteC(exp.right, ctx, subTick);
      return {
        list: mergeTimed(left.list, right.list),
        close: maxClose(left.close, right.close),
      };
    }
    case "letShare": {
      const shared = denoteC(exp.binding, ctx, 0);
      return denoteC(exp.body, { ...ctx, shared }, subTick);
    }
    case "shareRef": {
      if (ctx.shared === undefined) {
        throw new Error("denote: shareRef outside letShare");
      }
      // the first subscriber sees the subscription frame; later ones missed
      // it (registration-only replay) and see only the future
      const base =
        exp.first === true
          ? ctx.shared.list
          : ctx.shared.list.filter(([t]) => t[0] > 0);
      const sharedClose = ctx.shared.close;
      return {
        list: base.filter(([t]) => t[0] > subTick || subTick === 0),
        close:
          sharedClose !== "frame" && sharedClose > subTick
            ? sharedClose
            : "frame",
      };
    }
    case "mergeMap": {
      if (exp.origin === undefined) {
        throw new Error("denote: call assignOrigins first");
      }
      const arg = denoteC(exp.arg, ctx, subTick);
      return {
        list: denoteBind(exp.fns, arg.list, exp.origin, ctx.coldOriginMin),
        close: arg.close,
      };
    }
    case "mergeAll": {
      if (exp.outer.type === "ofS") {
        // a sync burst of inners, each its own root cause, merged in
        // subscription order
        return exp.outer.inners
          .map((inner) => denoteC(inner, ctx, subTick))
          .reduceRight<Denoted>(
            (acc, inner) => ({
              list: mergeTimed(inner.list, acc.list),
              close: maxClose(inner.close, acc.close),
            }),
            { list: [], close: "frame" },
          );
      }
      if (exp.outer.type === "mapShareS") {
        if (ctx.shared === undefined) {
          throw new Error("denote: mapShareS outside letShare");
        }
        // each trigger subscribes the hot stream late: it sees the suffix
        // strictly after its trigger instant; suffixes merge in trigger
        // (= subscription) order
        const sharedD = ctx.shared;
        const triggers = denoteC(exp.outer.arg, ctx, subTick);
        return {
          list: triggers.list
            .map(([t]) => sharedD.list.filter(([t2]) => compareTime(t, t2) < 0))
            .reduceRight<TimedObs<number>>(
              (acc, suffix) => mergeTimed(suffix, acc),
              [],
            ),
          close:
            triggers.list.length > 0
              ? maxClose(triggers.close, sharedD.close)
              : triggers.close,
        };
      }
      if (exp.outer.origin === undefined) {
        throw new Error("denote: call assignOrigins first");
      }
      const arg = denoteC(exp.outer.arg, ctx, subTick);
      return {
        list: denoteBind(
          exp.outer.fns,
          arg.list,
          exp.outer.origin,
          ctx.coldOriginMin,
        ),
        close: arg.close,
      };
    }
    case "concatAll": {
      // close-time threading: each inner subscribes when the previous
      // closes — in the same frame for a sync close, at the closing tick
      // for an async close
      let tick = subTick;
      let list: TimedObs<number> = [];
      for (const inner of exp.inners) {
        const d = denoteC(inner, ctx, tick);
        list = mergeTimed(list, d.list);
        if (d.close !== "frame") {
          tick = d.close;
        }
      }
      // "frame" is relative to an inner's OWN subscription: a last inner
      // closing in-frame after the queue advanced to `tick` closes at that
      // tick from the parent's point of view
      return { list, close: tick === subTick ? "frame" : tick };
    }
    case "switchAll": {
      // every burst inner's subscription-frame emissions pass; only the
      // last inner stays live past the frame
      const denoted = exp.inners.map((inner) => denoteC(inner, ctx, subTick));
      return denoted.reduce<Denoted>(
        (acc, d, k) =>
          k === denoted.length - 1
            ? { list: mergeTimed(acc.list, d.list), close: d.close }
            : {
                list: mergeTimed(
                  acc.list,
                  d.list.filter(([t]) => t[0] === subTick),
                ),
                close: acc.close,
              },
        { list: [], close: "frame" },
      );
    }
    case "exhaustAll": {
      // walk the burst: a frame-closing inner frees the slot; the first
      // inner with a pending close blocks, the rest are never subscribed
      let list: TimedObs<number> = [];
      let close: CloseTick = "frame";
      for (const inner of exp.inners) {
        const d = denoteC(inner, ctx, subTick);
        list = mergeTimed(list, d.list);
        close = d.close;
        if (d.close !== "frame") {
          break;
        }
      }
      return { list, close };
    }
  }
};

/** the denotation: interpret an Exp as a timed list. `coldOriginMin` is
 * the firstOrigin passed to assignOrigins (origins below it are sources) */
export const denote = (
  exp: Exp,
  sources: readonly TimedObs<number>[],
  srcCloseTick: (index: number) => number,
  coldOriginMin: number,
): TimedObs<number> =>
  denoteC(exp, { sources, srcCloseTick, coldOriginMin }, 0).list;

/** the blessed causal-batching rule, shared by mergeMap and mergeAll∘mapS:
 * triggers at driver-event (src-origin) instants are async causes — their
 * inners inherit the instant; triggers at cold-born instants are
 * subscription-frame deliveries wherever they sit in time — each spawned
 * inner is a fresh root cause at the trigger's tick */
const denoteBind = (
  fns: readonly Fn[],
  triggers: TimedObs<number>,
  originBase: number,
  coldOriginMin: number,
): TimedObs<number> => {
  const out: (readonly [Time, number])[] = [];
  let syncSeq = 0;
  for (const [t, v] of triggers) {
    const innerVals = fns.map((f) => applyFn(f, v));
    if (t[1] >= coldOriginMin) {
      syncSeq += 1;
      const origin = originBase + syncSeq;
      for (const w of innerVals) {
        out.push([[t[0], origin], w] as const);
      }
    } else {
      for (const w of innerVals) {
        out.push([t, w] as const);
      }
    }
  }
  return out;
};

/** the implementation under test: interpret the same Exp with rxjs */
export const interpret = (
  exp: Exp,
  subjects: readonly InstantSubject<number>[],
  shared?: Instantaneous<number>,
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
        interpret(exp.arg, subjects, shared),
        map((n: number) => applyFn(exp.fn, n)),
      );
    case "take":
      return pipeWith(interpret(exp.arg, subjects, shared), take(exp.count));
    case "merge":
      return merge(
        interpret(exp.left, subjects, shared),
        interpret(exp.right, subjects, shared),
      );
    case "letShare":
      return interpret(
        exp.body,
        subjects,
        share(interpret(exp.binding, subjects)),
      );
    case "shareRef": {
      if (shared === undefined) {
        throw new Error("interpret: shareRef outside letShare");
      }
      return shared;
    }
    case "mergeMap":
      return pipeWith(
        interpret(exp.arg, subjects, shared),
        mergeMap((n: number) => of(...exp.fns.map((f) => applyFn(f, n)))),
      );
    case "mergeAll": {
      if (exp.outer.type === "ofS") {
        // the primitive form, verbatim: mergeAll over an `of` of streams
        return pipeWith(
          of(...exp.outer.inners.map((i) => interpret(i, subjects, shared))),
          mergeAll(),
        );
      }
      if (exp.outer.type === "mapShareS") {
        if (shared === undefined) {
          throw new Error("interpret: mapShareS outside letShare");
        }
        const sharedStream = shared;
        return pipeWith(
          interpret(exp.outer.arg, subjects, shared),
          map(() => sharedStream),
          mergeAll(),
        );
      }
      const fns = exp.outer.fns;
      return pipeWith(
        interpret(exp.outer.arg, subjects, shared),
        map((n: number) => of(...fns.map((f) => applyFn(f, n)))),
        mergeAll(),
      );
    }
    case "concatAll":
      return pipeWith(
        of(...exp.inners.map((i) => interpret(i, subjects, shared))),
        concatAll,
      );
    case "switchAll":
      return pipeWith(
        of(...exp.inners.map((i) => interpret(i, subjects, shared))),
        switchAll,
      );
    case "exhaustAll":
      return pipeWith(
        of(...exp.inners.map((i) => interpret(i, subjects, shared))),
        exhaustAll,
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
    case "letShare":
      return `let x = share(${showExp(exp.binding)}) in ${showExp(exp.body)}`;
    case "shareRef":
      return "x";
    case "mergeAll":
      return exp.outer.type === "ofS"
        ? `mergeAll(of(${exp.outer.inners.map(showExp).join(", ")}))`
        : exp.outer.type === "mapShareS"
          ? `mergeAll(map(v => x)(${showExp(exp.outer.arg)}))`
          : `mergeAll(map(v => of(${exp.outer.fns
              .map((f) => `${f.op} ${f.k}`)
              .join(", ")}))(${showExp(exp.outer.arg)}))`;
    case "concatAll":
      return `concatAll(of(${exp.inners.map(showExp).join(", ")}))`;
    case "switchAll":
      return `switchAll(of(${exp.inners.map(showExp).join(", ")}))`;
    case "exhaustAll":
      return `exhaustAll(of(${exp.inners.map(showExp).join(", ")}))`;
  }
};
