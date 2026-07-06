import { pipeWith } from "pipe-ts";
import { EMPTY, map, of, share, take } from "../v5/basic-primitives";
import { InstantSubject } from "../v5/constructors";
import { concatAll, exhaustAll, mergeAll, switchAll } from "../v5/joins";
import { Instantaneous } from "../v5/types";
import { merge, mergeMap, scan } from "../v5/util";
import {
  compareSub,
  compareTime,
  deliveryOrder,
  entry,
  mapTimed,
  mergeTimed,
  takeTimed,
  Time,
  TimedEntry,
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
  | { readonly type: "src"; readonly index: number; slot?: number }
  | { readonly type: "of"; readonly values: readonly number[]; origin?: number }
  | { readonly type: "empty" }
  | { readonly type: "map"; readonly fn: Fn; readonly arg: Exp }
  | { readonly type: "take"; readonly count: number; readonly arg: Exp }
  // THE STATE PRIMITIVE (accumulate, via util.scan): time-preserving and
  // provenance-transparent — batching-wise exactly map. The accumulator
  // THREADS through the values in DELIVERY order (ratified 2026-07-06:
  // exactly rxjs scan — process emissions as they arrive), which is also
  // the batch order, so the fold reads as a left fold over each batch.
  // Step: acc' = fn(acc + cur).
  | {
      readonly type: "scan";
      readonly init: number;
      readonly fn: Fn;
      readonly arg: Exp;
    }
  | { readonly type: "merge"; readonly left: Exp; readonly right: Exp }
  // mergeMap with a pure inner: each trigger value v spawns of(...fns(v)).
  // THE CAUSATION RULE (fully transitive, ratified 2026-07-06): the inner's
  // values inherit the trigger value's exact Time, sync or async alike —
  // derivation creates simultaneity. Fresh instants are only the root
  // causes: each driver event, and each `of` occurrence at (static)
  // subscription. NODE REUSE IS SHARING: the same Exp node used twice is
  // one `of()` call subscribed twice — same origin, a cold diamond.
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
  | {
      readonly type: "shareRef";
      first?: boolean;
      refIndex?: number;
      slot?: number;
    }
  // THE JOIN PRIMITIVE, two-sorted: mergeAll consumes a stream-of-streams
  // expression. merge and mergeMap are DERIVED: merge(a,b) = mergeAll(ofS
  // [a,b]) and mergeMap(f) = mergeAll(mapS f) — kept above as aliases, with
  // the derivation laws checked by the oracle.
  | { readonly type: "mergeAll"; readonly outer: ExpS }
  // THE SERIAL JOINS. Without `trigger`: a sync burst of inners (outer =
  // of(i1..in)). All three mirror rxjs and need CLOSE TIMES:
  //  - concatAll subscribes each inner when the previous closes. An inner
  //    subscribed at an async close INHERITS the closing instant (the whole
  //    advancement cascade — chained frame-closing inners included — is one
  //    instant); a sync-closing chain in the static subscription frame
  //    stays fragmented, each `of` its own instant.
  //  - switchAll subscribes burst inners in turn: every inner's
  //    subscription-frame emissions pass, only the last stays live.
  //  - exhaustAll walks the burst: an inner that closes within the frame
  //    frees the slot; the first inner with a pending close blocks — the
  //    rest are dropped entirely (never subscribed, never registered).
  // WITH `trigger` (ASYNC OUTERS, 2026-07-06): the outer is
  // map(v => inners[|v| mod n])(trigger) — each trigger value picks an
  // inner from the palette, delivered at the trigger value's instant.
  //  - concatAll: an arrival while an inner is live queues; advancement
  //    subscribes the queued inner AT the closing instant (inheriting it —
  //    frame-closing chains collapse into the advancement instant).
  //  - switchAll: each arrival switches at its instant; the switched-away
  //    inner keeps only emissions strictly before the switch (the trigger
  //    chain subscribed earlier, so it fires first within the instant),
  //    plus its own subscription frame on a same-instant switch.
  //  - exhaustAll: an arrival while the live inner's close is at-or-after
  //    the arrival instant is dropped entirely.
  | {
      readonly type: "concatAll";
      readonly inners: readonly Exp[];
      readonly trigger?: Exp;
    }
  | {
      readonly type: "switchAll";
      readonly inners: readonly Exp[];
      readonly trigger?: Exp;
    }
  | {
      readonly type: "exhaustAll";
      readonly inners: readonly Exp[];
      readonly trigger?: Exp;
    };

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
  | { readonly type: "mapShareS"; readonly arg: Exp; slot?: number }
  // DYNAMIC COLD ARRIVAL: each trigger value picks an inner from the
  // palette (map(v => inners[|v| mod n])(arg)) and subscribes it at the
  // trigger value's instant — mergeMap over cold, src-derived inners.
  | {
      readonly type: "pickS";
      readonly inners: readonly Exp[];
      readonly arg: Exp;
    };

/** the deterministic palette pick shared by model and interpreter */
export const pickIndex = (v: number, n: number): number => ((v % n) + n) % n;

/** a ref tag encodes a subject subscription's ORDER in the subject's
 * subscriber list: tick * SLOT_SPAN + site-slot — subscriptions happen in
 * time order, and within one tick (the static frame, or several spawns in
 * one instant) in pre-order of their sites. The letShare regroup sorts the
 * fan-out block by tag; the share's CONNECTION is the first static ref's
 * slot when one exists (statically known — even when that ref contributes
 * no value to an instant), else the instant's minimum tag (the earliest
 * spawn covers every instant a later one sees). */
const SLOT_SPAN = 1 << 20;

/** the pre-order-first (= minimum-slot) STATIC shareRef in a letShare
 * body, if any — where the share connects when static refs exist */
const firstStaticRefSlot = (e: Exp): number | undefined => {
  switch (e.type) {
    case "shareRef":
      return e.slot;
    case "map":
    case "take":
    case "scan":
    case "mergeMap":
      return firstStaticRefSlot(e.arg);
    case "merge": {
      const l = firstStaticRefSlot(e.left);
      return l !== undefined ? l : firstStaticRefSlot(e.right);
    }
    case "mergeAll": {
      if (e.outer.type === "ofS") {
        for (const inner of e.outer.inners) {
          const s = firstStaticRefSlot(inner);
          if (s !== undefined) {
            return s;
          }
        }
        return undefined;
      }
      if (e.outer.type === "pickS") {
        // palette inners are SPAWNED per trigger value — their refs
        // subscribe dynamically, at the spawn tick; only the arg is
        // static wiring
        return firstStaticRefSlot(e.outer.arg);
      }
      // mapShareS spawns are DYNAMIC subscriptions, but its trigger may
      // hold static refs
      return firstStaticRefSlot(e.outer.arg);
    }
    case "concatAll":
    case "switchAll":
    case "exhaustAll": {
      if (e.trigger !== undefined) {
        // dynamic outer: inners are spawned per trigger value — only the
        // trigger subscribes statically
        return firstStaticRefSlot(e.trigger);
      }
      for (const inner of e.inners) {
        const s = firstStaticRefSlot(inner);
        if (s !== undefined) {
          return s;
        }
      }
      return undefined;
    }
    case "letShare":
      return firstStaticRefSlot(e.body);
    default:
      return undefined;
  }
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
  let firstRefSeen = false;
  let refCount = 0;
  // each src / shareRef OCCURRENCE is its own subscription site, numbered
  // in pre-order (= root subscription order = the source's subscriber
  // order for statically wired chains)
  let slotCount = 0;
  // node reuse is sharing: the same `of` node in two positions is ONE cold
  // call subscribed twice — it keeps one origin (and one output object, so
  // interpret can share the of() call by identity)
  const ofCache = new Map<Exp, Exp>();
  const nextBase = () => firstOrigin + 1000 * node++;
  const go = (e: Exp): Exp => {
    switch (e.type) {
      case "src":
        return { ...e, slot: slotCount++ };
      case "empty":
        return e;
      case "of": {
        const hit = ofCache.get(e);
        if (hit !== undefined) {
          return hit;
        }
        const out = { ...e, origin: nextBase() };
        ofCache.set(e, out);
        return out;
      }
      case "map":
        return { ...e, arg: go(e.arg) };
      case "take":
        return { ...e, arg: go(e.arg) };
      case "scan":
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
        return { ...e, first, refIndex: refCount++, slot: slotCount++ };
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
          // the mapShareS is itself a subject-subscription site (one
          // subscription per trigger value)
          return {
            ...e,
            outer: { ...e.outer, arg: go(e.outer.arg), slot: slotCount++ },
          };
        }
        if (e.outer.type === "pickS") {
          return {
            ...e,
            outer: {
              ...e.outer,
              inners: e.outer.inners.map(go),
              arg: go(e.outer.arg),
            },
          };
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
        return {
          ...e,
          inners: e.inners.map(go),
          ...(e.trigger !== undefined ? { trigger: go(e.trigger) } : {}),
        };
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
 * A subscription time: "root" is the static unfolding at tick 0 (each cold
 * a fresh root cause); a Time means the subscription was caused by that
 * async instant, and everything it unfolds inherits it (async collapse).
 */
export type SubTime = "root" | Time;

/**
 * A close time: "frame" means the expression completes within its own
 * subscription instant (a sync burst — of, empty, take 0, a fully-taken
 * cold); a Time is the async instant it completes at. Serial joins thread
 * closes into subscription times.
 */
export type CloseTime = "frame" | Time;

const tickOf = (s: SubTime): number => (s === "root" ? 0 : s[0]);

const maxClose = (a: CloseTime, b: CloseTime): CloseTime =>
  a === "frame" ? b : b === "frame" ? a : compareTime(a, b) >= 0 ? a : b;

/**
 * DELIVERY-KEY stamping for an inner subscribed at async time `at` inside
 * the chain `chainKey` (the spawning trigger / advancing closer):
 *  - its FRAME entries (at the subscription instant) are a synchronous
 *    cascade INSIDE that chain's delivery — their relative keys compose
 *    onto the chain's key;
 *  - its LATER entries deliver via their own late source subscriptions,
 *    whose global key is the relative key composed onto the inner's own
 *    subscription key [at, ...chainKey].
 * Composition is appending: a relative key's implicit root ([]) IS the
 * subscription context.
 */
const stampSub = <A>(
  list: TimedObs<A>,
  at: Time,
  chainKey: readonly number[],
  /** the ambient subscription tick: an arrival AT this tick happens
   * during the surrounding subscription cascade itself — it is part of
   * that frame (like a tick-0 arrival is part of the static unfolding),
   * so its key composes without a tick prefix */
  frameTick = 0,
  /** the SLOT of the trigger chain delivering this spawn: frame-composed
   * entries without a site of their own rank at the trigger's site (a
   * spawned cold's flush rides its trigger's subscriber position — the
   * letShare regroup compares slots to place a share's fan-out block) */
  frameSlot?: number,
): TimedObs<A> =>
  list.map(([t, v, m]): TimedEntry<A> => {
    if (t[0] > at[0] && at[0] > frameTick) {
      return entry(t, v, {
        ...m,
        sub: [...(m?.sub ?? []), at[0], ...chainKey],
      });
    }
    return entry(t, v, {
      ...m,
      sub: [...(m?.sub ?? []), ...chainKey],
      ...(frameSlot !== undefined && m?.slot === undefined
        ? { slot: frameSlot }
        : {}),
    });
  });

type Denoted = {
  readonly list: TimedObs<number>;
  readonly close: CloseTime;
  /** the subscription KEY (same scale as EntryMeta.sub, root-relative to
   * this denotation) of the CHAIN THAT DELIVERS the close event. An
   * advancement caused by this close is a synchronous cascade inside that
   * chain's delivery — its frame entries rank there, not at the closing
   * stream's subscription slot. Only meaningful when close is a Time. */
  readonly closeRank?: readonly number[];
};

/** the close-delivering chain's key as seen by a consumer that subscribed
 * the denoted stream at async time `at` inside chain `chainKey`
 * (at === undefined: subscribed in frame — pass the relative key through) */
const liftCloseRank = (
  d: Denoted,
  at: Time | undefined,
  chainKey: readonly number[],
  frameTick = 0,
): readonly number[] =>
  at === undefined
    ? (d.closeRank ?? [])
    : at[0] <= frameTick
      ? // a subscription at the ambient frame's tick is part of that
        // cascade (tick-0 = the static unfolding)
        [...(d.closeRank ?? []), ...chainKey]
      : [...(d.closeRank ?? []), at[0], ...chainKey];

type Ctx = {
  readonly sources: readonly TimedObs<number>[];
  /** the tick at which source `index` completes (the driver completes all
   * subjects, in index order, after the last event) */
  readonly srcCloseTick: (index: number) => number;
  readonly shared?: Denoted;
  /** the binding is a BARE subject (share(src) short-circuits — a subject
   * is already hot): each ref subscribes the SOURCE directly at its own
   * syntactic slot, so there is no consecutive fan-out block */
  readonly sharedDirect?: boolean;
};

/**
 * The denotation, subscription-time-parameterized. THE CAUSATION RULE,
 * fully transitive: at "root", each cold is its own instant [0, origin];
 * subscribed at an async Time (a value trigger or an async close), a cold's
 * values inherit that exact Time — derivation and advancement create
 * simultaneity. Hot sources contribute only their strict suffix.
 */
const denoteC = (exp: Exp, ctx: Ctx, subTime: SubTime): Denoted => {
  switch (exp.type) {
    case "src": {
      // a source that already completed at (or before) the subscription
      // instant closes within the frame — closes never point into the past.
      // A completion is its own instant [closeTick, index]
      const closeTick = ctx.srcCloseTick(exp.index);
      const subTick = tickOf(subTime);
      return {
        list: ctx.sources[exp.index]
          .filter(([t]) => t[0] > subTick)
          .map(([t, v]) => entry(t, v, { slot: exp.slot })),
        close: closeTick > subTick ? [closeTick, exp.index] : "frame",
        closeRank: [],
      };
    }
    case "of": {
      if (exp.origin === undefined) {
        throw new Error("denote: call assignOrigins first");
      }
      const at: Time = subTime === "root" ? [0, exp.origin] : subTime;
      return {
        list: exp.values.map((v) => [at, v] as const),
        close: "frame",
      };
    }
    case "empty":
      return { list: [], close: "frame" };
    case "map": {
      const arg = denoteC(exp.arg, ctx, subTime);
      return {
        list: mapTimed(arg.list, (n) => applyFn(exp.fn, n)),
        close: arg.close,
        closeRank: arg.closeRank,
      };
    }
    case "scan": {
      // the state primitive: a stateful fold threading through the
      // subscription's values in DELIVERY order (ratified 2026-07-06:
      // exactly like rxjs scan — process emissions as they arrive);
      // batching-wise exactly map — every Time is preserved
      const arg = denoteC(exp.arg, ctx, subTime);
      let acc = exp.init;
      return {
        list: deliveryOrder(arg.list).map(([t, v, m]) => {
          acc = applyFn(exp.fn, acc + v);
          return entry(t, acc, m);
        }),
        close: arg.close,
        closeRank: arg.closeRank,
      };
    }
    case "take": {
      const arg = denoteC(exp.arg, ctx, subTime);
      if (exp.count === 0) {
        return { list: [], close: "frame" };
      }
      if (arg.list.length >= exp.count) {
        // take counts in DELIVERY order (takeTimed sorts) — the cut falls
        // on the count-th ARRIVING value, even mid-instant
        const taken = takeTimed(arg.list, exp.count);
        const cut = taken[exp.count - 1];
        const closeAt = cut[0];
        return {
          list: taken,
          close: closeAt[0] === tickOf(subTime) ? "frame" : closeAt,
          // the cut travels WITH the final value — same delivering chain
          closeRank: cut[2]?.sub ?? [],
        };
      }
      return arg;
    }
    case "merge": {
      const left = denoteC(exp.left, ctx, subTime);
      const right = denoteC(exp.right, ctx, subTime);
      const close = maxClose(left.close, right.close);
      return {
        list: mergeTimed(left.list, right.list),
        close,
        closeRank: close === right.close ? right.closeRank : left.closeRank,
      };
    }
    case "letShare": {
      const shared = denoteC(exp.binding, ctx, "root");
      const sharedDirect = exp.binding.type === "src";
      const body = denoteC(exp.body, { ...ctx, shared, sharedDirect }, subTime);
      if (sharedDirect) {
        // no subject was inserted: refs are independent direct
        // subscriptions, already at their own slots — nothing to regroup
        return {
          list: body.list,
          close: body.close,
          closeRank: body.closeRank,
        };
      }
      // THE FAN-OUT REGROUP (delivery order): the share's subject fires
      // its subscribers CONSECUTIVELY, in subscription order (the ref
      // tags) — all share-derived values of an instant deliver as one
      // block at the share's CONNECTION rank. The connection is the
      // instant's minimum tag: the earliest subscriber covers every
      // instant a later one sees, so it is always present.
      const staticAnchor = firstStaticRefSlot(exp.body);
      const regrouped: TimedEntry<number>[] = [];
      let i = 0;
      const list = body.list;
      while (i < list.length) {
        let j = i;
        while (
          j < list.length &&
          compareTime(list[j][0], list[i][0]) === 0
        ) {
          j++;
        }
        const group = list.slice(i, j);
        const tagged = group.filter((e) => e[2]?.ref !== undefined);
        if (tagged.length === 0) {
          regrouped.push(...group);
        } else {
          const presentMin = Math.min(
            ...tagged.map((e) => e[2]?.ref ?? 0),
          );
          const minTag =
            staticAnchor !== undefined
              ? Math.min(staticAnchor, presentMin)
              : presentMin;
          const connectSub = Math.floor(minTag / SLOT_SPAN);
          // the connection's SITE slot breaks ties among entries of the
          // same frame: for a static (tick-0) connection that's the first
          // ref's pre-order site; for a DYNAMIC connection (a spawned
          // ref) it's the ref's site inside the spawned inner — the spawn
          // frame subscribes its sites in pre-order, so a sibling direct
          // subscription at a later site delivers after the share block
          const anchorSlot = minTag % SLOT_SPAN;
          const blockSub: readonly number[] =
            connectSub === 0 ? [] : [connectSub];
          const block = [...tagged]
            .sort((a, b) => (a[2]?.ref ?? 0) - (b[2]?.ref ?? 0))
            .map(([t, v, m]) =>
              // the whole block rides the SUBJECT's slot: every member
              // ranks at the connection sub, whatever its own spawn tick
              entry(t, v, { ...m, ref: undefined, sub: blockSub }),
            );
          let placed = false;
          for (const e of group) {
            if (e[2]?.ref !== undefined) {
              continue;
            }
            const subCmp = compareSub(e[2]?.sub, blockSub);
            const eSlot = e[2]?.slot ?? Infinity;
            if (
              !placed &&
              (subCmp > 0 || (subCmp === 0 && eSlot > anchorSlot))
            ) {
              placed = true;
              regrouped.push(...block);
            }
            regrouped.push(e);
          }
          if (!placed) {
            regrouped.push(...block);
          }
        }
        i = j;
      }
      return { list: regrouped, close: body.close, closeRank: body.closeRank };
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
      const subTick = tickOf(subTime);
      return {
        list: base
          .filter(([t]) => t[0] > subTick || subTick === 0)
          .map(([t, v, m]) =>
            ctx.sharedDirect === true
              ? // a direct subject subscription: this ref's own slot.
                // The binding's own delivery meta (sub/slot) describes
                // paths INSIDE the shared upstream — meaningless past the
                // subject boundary — so the ref constructs fresh meta.
                entry(t, v, { slot: exp.slot })
              : // a ref subscribes the subject at its SUBSCRIPTION tick —
                // 0 for static wiring, the spawn tick for a ref delivered
                // dynamically (a pickS palette / dynamic serial inner) —
                // at its own pre-order site (same tag scheme as mapShareS
                // spawns: a late connection ranks at connection time)
                entry(t, v, {
                  ref: subTick * SLOT_SPAN + (exp.slot ?? 0),
                }),
          ),
        close:
          sharedClose !== "frame" && sharedClose[0] > subTick
            ? sharedClose
            : "frame",
      };
    }
    case "mergeMap": {
      const arg = denoteC(exp.arg, ctx, subTime);
      return {
        list: denoteBind(exp.fns, arg.list),
        close: arg.close,
        closeRank: arg.closeRank,
      };
    }
    case "mergeAll": {
      if (exp.outer.type === "ofS") {
        // a burst of inners: static wiring — each subscribed at the same
        // SubTime (own instants at root, the inherited instant otherwise),
        // merged in subscription order
        return exp.outer.inners
          .map((inner) => denoteC(inner, ctx, subTime))
          .reduceRight<Denoted>(
            (acc, inner) => {
              const close = maxClose(inner.close, acc.close);
              return {
                list: mergeTimed(inner.list, acc.list),
                close,
                closeRank:
                  close === acc.close ? acc.closeRank : inner.closeRank,
              };
            },
            { list: [], close: "frame" },
          );
      }
      if (exp.outer.type === "mapShareS") {
        if (ctx.shared === undefined) {
          throw new Error("denote: mapShareS outside letShare");
        }
        // each trigger subscribes the hot stream late: it sees the suffix
        // strictly after its trigger instant. Late subscribers of a real
        // share SUBJECT deliver inside the subject's (early) fan-out slot,
        // appended after the static refs in trigger order — LATE ref tags
        // pull them into the letShare regroup block. Late subscribers of
        // a BARE subject (share(src) short-circuits) append to the
        // SOURCE's own list — a genuine late rank.
        const sharedD = ctx.shared;
        const direct = ctx.sharedDirect === true;
        const site = exp.outer.slot ?? 0;
        const triggers = denoteC(exp.outer.arg, ctx, subTime);
        return {
          list: triggers.list
            .map(([t]) =>
              direct
                ? stampSub(
                    sharedD.list.filter(([t2]) => compareTime(t, t2) < 0),
                    t,
                    [],
                    tickOf(subTime),
                  )
                : sharedD.list
                    .filter(([t2]) => compareTime(t, t2) < 0)
                    .map(([t2, v2, m2]) =>
                      entry(t2, v2, {
                        ...m2,
                        // this spawn subscribed the subject at the
                        // trigger's tick, at the mapShareS's site — a
                        // tick-0 spawn (an `of` trigger firing during the
                        // static frame) correctly sorts among the static
                        // refs by site order
                        ref: t[0] * SLOT_SPAN + site,
                        sub: [t[0]],
                      }),
                    ),
            )
            .reduceRight<TimedObs<number>>(
              (acc, suffix) => mergeTimed(suffix, acc),
              [],
            ),
          close:
            triggers.list.length > 0
              ? maxClose(triggers.close, sharedD.close)
              : triggers.close,
          closeRank:
            triggers.list.length > 0 &&
            maxClose(triggers.close, sharedD.close) === sharedD.close
              ? sharedD.closeRank
              : triggers.closeRank,
        };
      }
      if (exp.outer.type === "pickS") {
        // dynamic cold arrival: each trigger value subscribes its picked
        // inner at the trigger's instant (the causation rule); everything
        // merges, closing when the outer and every inner have closed.
        // DELIVERY ranks: a copy's frame emissions ride the trigger
        // chain's slot; its later emissions rank at its own (late) source
        // subscription.
        const inners = exp.outer.inners;
        const triggers = denoteC(exp.outer.arg, ctx, subTime);
        let close: CloseTime = triggers.close;
        let closeRank = triggers.closeRank;
        let list: TimedObs<number> = [];
        for (const [t, v, m] of triggers.list) {
          const trigKey = m?.sub ?? [];
          const d = denoteC(inners[pickIndex(v, inners.length)], ctx, t);
          list = mergeTimed(
            list,
            stampSub(d.list, t, trigKey, tickOf(subTime), m?.slot),
          );
          const dClose = d.close === "frame" ? t : d.close;
          const next = maxClose(close, dClose);
          if (next !== close) {
            closeRank = liftCloseRank(d, t, trigKey, tickOf(subTime));
          }
          close = next;
        }
        return { list, close: relCloseAt(close, subTime), closeRank };
      }
      const arg = denoteC(exp.outer.arg, ctx, subTime);
      return {
        list: denoteBind(exp.outer.fns, arg.list),
        close: arg.close,
        closeRank: arg.closeRank,
      };
    }
    case "concatAll": {
      if (exp.trigger !== undefined) {
        return denoteSerialDynamic(exp, ctx, subTime);
      }
      // close-time threading: each inner subscribes when the previous
      // closes — in the same frame for a sync close (static unfolding),
      // INHERITING the closing instant for an async close (the whole
      // advancement cascade is one instant). DELIVERY ranks: an inner
      // subscribed at an async close is a LATE source subscription — its
      // frame entries ride the closing chain's slot, its later entries
      // rank at its own subscription tick.
      let cur: SubTime = subTime;
      let curKey: readonly number[] = [];
      let list: TimedObs<number> = [];
      for (const inner of exp.inners) {
        const d = denoteC(inner, ctx, cur);
        const stamped =
          cur === subTime ? d.list : stampSub(d.list, cur as Time, curKey, tickOf(subTime));
        list = mergeTimed(list, stamped);
        if (d.close !== "frame") {
          // the key of the chain DELIVERING the close (the advancement
          // cascade is synchronous inside that delivery)
          curKey = liftCloseRank(
            d,
            cur === subTime ? undefined : (cur as Time),
            curKey,
            tickOf(subTime),
          );
          cur = d.close;
        }
      }
      // "frame" is relative to an inner's OWN subscription: a last inner
      // closing in-frame after the queue advanced closes at the advanced
      // instant from the parent's point of view
      return {
        list,
        close: cur === subTime ? "frame" : (cur as Time),
        closeRank: cur === subTime ? undefined : curKey,
      };
    }
    case "switchAll": {
      if (exp.trigger !== undefined) {
        return denoteSerialDynamic(exp, ctx, subTime);
      }
      // every burst inner's subscription-frame emissions pass; only the
      // last inner stays live past the frame
      const denoted = exp.inners.map((inner) => denoteC(inner, ctx, subTime));
      return denoted.reduce<Denoted>(
        (acc, d, k) =>
          k === denoted.length - 1
            ? {
                list: mergeTimed(acc.list, d.list),
                close: d.close,
                closeRank: d.closeRank,
              }
            : {
                list: mergeTimed(
                  acc.list,
                  d.list.filter(([t]) => t[0] === tickOf(subTime)),
                ),
                close: acc.close,
                closeRank: acc.closeRank,
              },
        { list: [], close: "frame" },
      );
    }
    case "exhaustAll": {
      if (exp.trigger !== undefined) {
        return denoteSerialDynamic(exp, ctx, subTime);
      }
      // walk the burst: a frame-closing inner frees the slot; the first
      // inner with a pending close blocks, the rest are never subscribed
      let list: TimedObs<number> = [];
      let close: CloseTime = "frame";
      let closeRank: readonly number[] | undefined;
      for (const inner of exp.inners) {
        const d = denoteC(inner, ctx, subTime);
        list = mergeTimed(list, d.list);
        close = d.close;
        closeRank = d.closeRank;
        if (d.close !== "frame") {
          break;
        }
      }
      return { list, close, closeRank };
    }
  }
};

/** a close within the subscription instant (or the static tick-0 frame) is
 * "frame" from the parent's point of view — matches take/concat's rule */
const relCloseAt = (c: CloseTime, subTime: SubTime): CloseTime =>
  c === "frame" || c[0] === tickOf(subTime) ? "frame" : c;

/**
 * THE SERIAL JOINS OVER AN ASYNC OUTER (map(v => inners[pick v])(trigger)).
 * Arrivals are the trigger's timed values; each subscribes / queues / drops
 * its picked inner per the join's discipline. Within one instant the trigger
 * chain fires BEFORE a live inner's own events (it subscribed earlier), so:
 * a concat arrival at the live inner's closing instant queues (and the
 * advancement then subscribes it AT that instant — the collapse rule); an
 * exhaust arrival at the closing instant is dropped; a switch at the
 * arrival instant silences the old inner's same-instant value.
 */
const denoteSerialDynamic = (
  exp: {
    readonly type: "concatAll" | "switchAll" | "exhaustAll";
    readonly inners: readonly Exp[];
    readonly trigger?: Exp;
  },
  ctx: Ctx,
  subTime: SubTime,
): Denoted => {
  const trig = denoteC(exp.trigger as Exp, ctx, subTime);
  const n = exp.inners.length;
  if (n === 0) {
    return { list: [], close: relCloseAt(trig.close, subTime) };
  }
  const arrivals = trig.list.map(
    ([t, v, m]) =>
      [
        t,
        exp.inners[pickIndex(v, n)],
        m?.sub ?? ([] as readonly number[]),
        m?.slot,
      ] as const,
  );
  let list: TimedObs<number> = [];

  if (exp.type === "switchAll") {
    let lastClose: CloseTime = "frame";
    let lastRank: readonly number[] | undefined;
    arrivals.forEach(([t, inner, trigSub, trigSlot], k) => {
      const d = denoteC(inner, ctx, t);
      const next = k + 1 < arrivals.length ? arrivals[k + 1][0] : null;
      const kept =
        next === null
          ? d.list
          : d.list.filter(
              ([t2]) =>
                compareTime(t2, next) < 0 || compareTime(t2, t) === 0,
            );
      list = mergeTimed(
        list,
        stampSub(kept, t, trigSub, tickOf(subTime), trigSlot),
      );
      if (next === null) {
        lastClose = d.close === "frame" ? t : d.close;
        // a FRAME-closing inner's close delivers inside the subscribing
        // (trigger) cascade itself
        lastRank =
          d.close === "frame" ? trigSub : liftCloseRank(d, t, trigSub, tickOf(subTime));
      }
    });
    return {
      list,
      close: relCloseAt(maxClose(trig.close, lastClose), subTime),
      closeRank: lastRank ?? trig.closeRank,
    };
  }

  if (exp.type === "exhaustAll") {
    // null = free NOW: a FRAME-closing inner (sync complete during its own
    // subscription) frees the slot even for a same-instant later arrival —
    // whereas an inner async-closing AT an arrival's instant is still live
    // when the trigger fires (the trigger chain subscribed earlier), so
    // that arrival drops
    let liveClose: Time | null = null;
    let liveRank: readonly number[] | undefined;
    for (const [t, inner, trigSub, trigSlot] of arrivals) {
      if (liveClose !== null && compareTime(liveClose, t) >= 0) {
        continue; // busy: dropped, never subscribed
      }
      const d = denoteC(inner, ctx, t);
      list = mergeTimed(
        list,
        stampSub(d.list, t, trigSub, tickOf(subTime), trigSlot),
      );
      liveClose = d.close === "frame" ? null : d.close;
      liveRank = d.close === "frame" ? trigSub : liftCloseRank(d, t, trigSub, tickOf(subTime));
    }
    return {
      list,
      close: relCloseAt(maxClose(trig.close, liveClose ?? "frame"), subTime),
      closeRank: liveRank ?? trig.closeRank,
    };
  }

  // concatAll
  let liveClose: Time | null = null;
  // the key of the chain that will DELIVER the close
  let liveRank: readonly number[] = [];
  const queue: Exp[] = [];
  const subscribeAt = (
    inner: Exp,
    at: Time,
    chainKey: readonly number[],
    chainSlot?: number,
  ): void => {
    const d = denoteC(inner, ctx, at);
    list = mergeTimed(
      list,
      stampSub(d.list, at, chainKey, tickOf(subTime), chainSlot),
    );
    liveClose = d.close === "frame" ? at : d.close;
    liveRank =
      d.close === "frame" ? chainKey : liftCloseRank(d, at, chainKey, tickOf(subTime));
  };
  /** advance the queue while the live inner closes strictly before `upTo`
   * (null = drain fully); each advancement subscribes AT the closing
   * instant — its frame rides the CLOSING chain's delivery slot — so
   * frame-closing chains collapse into it */
  const drain = (upTo: Time | null): void => {
    while (
      liveClose !== null &&
      queue.length > 0 &&
      (upTo === null || compareTime(liveClose, upTo) < 0)
    ) {
      subscribeAt(queue.shift() as Exp, liveClose, liveRank);
    }
  };
  for (const [t, inner, trigSub, trigSlot] of arrivals) {
    drain(t);
    const busy =
      queue.length > 0 ||
      (liveClose !== null && compareTime(liveClose, t) >= 0);
    if (busy) {
      queue.push(inner);
    } else {
      subscribeAt(inner, t, trigSub, trigSlot);
    }
  }
  drain(null);
  return {
    list,
    close: relCloseAt(maxClose(trig.close, liveClose ?? "frame"), subTime),
    closeRank: liveClose !== null ? liveRank : trig.closeRank,
  };
};

/** the denotation: interpret an Exp as a timed list */
export const denote = (
  exp: Exp,
  sources: readonly TimedObs<number>[],
  srcCloseTick: (index: number) => number,
): TimedObs<number> => denoteC(exp, { sources, srcCloseTick }, "root").list;

/** the causation rule, shared by mergeMap and mergeAll∘mapS: a spawned
 * inner's values inherit the trigger value's exact Time — always, sync or
 * async (fully transitive; ratified 2026-07-06) */
const denoteBind = (
  fns: readonly Fn[],
  triggers: TimedObs<number>,
): TimedObs<number> =>
  // spawned values deliver INLINE in their trigger's slot — same meta
  triggers.flatMap(([t, v, m]) => fns.map((f) => entry(t, applyFn(f, v), m)));

/** the implementation under test: interpret the same Exp with rxjs.
 * Node reuse is sharing: a reused `of` node is ONE of() call (one
 * provenance) subscribed from both positions — the cold diamond. */
export const interpret = (
  exp: Exp,
  subjects: readonly InstantSubject<number>[],
  shared?: Instantaneous<number>,
  ofCache: Map<Exp, Instantaneous<number>> = new Map(),
): Instantaneous<number> => {
  const go = (e: Exp, sh: Instantaneous<number> | undefined) =>
    interpret(e, subjects, sh, ofCache);
  switch (exp.type) {
    case "src":
      return subjects[exp.index];
    case "of": {
      const hit = ofCache.get(exp);
      if (hit !== undefined) {
        return hit;
      }
      const out = of(...exp.values);
      ofCache.set(exp, out);
      return out;
    }
    case "empty":
      return EMPTY;
    case "map":
      return pipeWith(
        go(exp.arg, shared),
        map((n: number) => applyFn(exp.fn, n)),
      );
    case "take":
      return pipeWith(go(exp.arg, shared), take(exp.count));
    case "scan":
      return pipeWith(
        go(exp.arg, shared),
        scan(exp.init, (acc: number, cur: number) => applyFn(exp.fn, acc + cur)),
      );
    case "merge":
      return merge(go(exp.left, shared), go(exp.right, shared));
    case "letShare":
      return go(exp.body, share(go(exp.binding, undefined)));
    case "shareRef": {
      if (shared === undefined) {
        throw new Error("interpret: shareRef outside letShare");
      }
      return shared;
    }
    case "mergeMap":
      return pipeWith(
        go(exp.arg, shared),
        mergeMap((n: number) => of(...exp.fns.map((f) => applyFn(f, n)))),
      );
    case "mergeAll": {
      if (exp.outer.type === "ofS") {
        // the primitive form, verbatim: mergeAll over an `of` of streams
        return pipeWith(
          of(...exp.outer.inners.map((i) => go(i, shared))),
          mergeAll(),
        );
      }
      if (exp.outer.type === "mapShareS") {
        if (shared === undefined) {
          throw new Error("interpret: mapShareS outside letShare");
        }
        const sharedStream = shared;
        return pipeWith(
          go(exp.outer.arg, shared),
          map(() => sharedStream),
          mergeAll(),
        );
      }
      if (exp.outer.type === "pickS") {
        const inners = exp.outer.inners.map((i) => go(i, shared));
        return pipeWith(
          go(exp.outer.arg, shared),
          map((v: number) => inners[pickIndex(v, inners.length)]),
          mergeAll(),
        );
      }
      const fns = exp.outer.fns;
      return pipeWith(
        go(exp.outer.arg, shared),
        map((n: number) => of(...fns.map((f) => applyFn(f, n)))),
        mergeAll(),
      );
    }
    case "concatAll":
    case "switchAll":
    case "exhaustAll": {
      const join =
        exp.type === "concatAll"
          ? concatAll
          : exp.type === "switchAll"
            ? switchAll
            : exhaustAll;
      const inners = exp.inners.map((i) => go(i, shared));
      if (exp.trigger === undefined) {
        return pipeWith(of(...inners), join);
      }
      // async outer: each trigger value picks an inner from the palette
      return pipeWith(
        go(exp.trigger, shared),
        map((v: number) => inners[pickIndex(v, inners.length)]),
        join,
      );
    }
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
    case "scan":
      return `scan(${exp.init}, (acc,v) => ${exp.fn.op} ${exp.fn.k} (acc+v))(${showExp(exp.arg)})`;
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
          : exp.outer.type === "pickS"
            ? `mergeAll(map(v => pick[${exp.outer.inners
                .map(showExp)
                .join(" | ")}])(${showExp(exp.outer.arg)}))`
            : `mergeAll(map(v => of(${exp.outer.fns
                .map((f) => `${f.op} ${f.k}`)
                .join(", ")}))(${showExp(exp.outer.arg)}))`;
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return exp.trigger === undefined
        ? `${exp.type}(of(${exp.inners.map(showExp).join(", ")}))`
        : `${exp.type}(map(v => pick[${exp.inners
            .map(showExp)
            .join(" | ")}])(${showExp(exp.trigger)}))`;
  }
};
