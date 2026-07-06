import fc from "fast-check";
import {
  assignOrigins,
  denote,
  Exp,
  Fn,
  interpret,
  showExp,
  SourceEvent,
  sourceTimedLists,
} from "../../model/exp";
import { batchSpec, valuesOf } from "../../model/timed";
import { InstantSubject } from "../constructors";
import { record } from "./helpers";

const NUM_SOURCES = 3;

const fnArb: fc.Arbitrary<Fn> = fc.record({
  op: fc.constantFrom("add" as const, "mul" as const),
  k: fc.integer({ min: -3, max: 3 }),
});

const valueArb = fc.integer({ min: -5, max: 9 });

/**
 * `flat` expressions are those the current `take` implementation counts
 * correctly (one value per emission); merges are excluded from take's
 * argument. Everything else composes freely. `extraLeaves` lets the
 * letShare body tier add `shareRef` (which is flat: the bindings below are
 * src-derived, one value per instant).
 */
const makeTiers = (
  extraLeaves: fc.Arbitrary<Exp>[],
  hotTriggerArb?: fc.Arbitrary<Exp>,
  withSerialJoins = false,
) =>
  fc.letrec<{ flat: Exp; exp: Exp }>((tie) => ({
    flat: fc.oneof(
      { depthSize: "small", withCrossShrink: true },
      fc.record({
        type: fc.constant("src" as const),
        index: fc.integer({ min: 0, max: NUM_SOURCES - 1 }),
      }),
      fc.record({
        type: fc.constant("of" as const),
        values: fc.array(valueArb, { maxLength: 3 }),
      }),
      fc.record({ type: fc.constant("empty" as const) }),
      ...extraLeaves,
      fc.record({
        type: fc.constant("map" as const),
        fn: fnArb,
        arg: tie("flat"),
      }),
      fc.record({
        type: fc.constant("take" as const),
        count: fc.integer({ min: 0, max: 4 }),
        arg: tie("flat"),
      }),
      // the state primitive: accumulator threads in delivery order
      // (non-flat args are generated in the share-free exp tier below)
      fc.record({
        type: fc.constant("scan" as const),
        init: valueArb,
        fn: fnArb,
        arg: tie("flat"),
      }),
    ),
    exp: fc.oneof(
      { depthSize: "small", withCrossShrink: true },
      tie("flat"),
      fc.record({
        type: fc.constant("map" as const),
        fn: fnArb,
        arg: tie("exp"),
      }),
      // NON-FLAT take (ratified: take splits instants): counts values
      // anywhere in emission trees — diamonds and joins. SHARE-FREE tier
      // only: a cut through a HOT join closes subscriptions whose
      // deliveries were re-routed as separate units, and "swallowed vs
      // re-routed delivery" isn't decidable at the emission level — a
      // recorded frontier.
      ...(withSerialJoins
        ? [
            fc.record({
              type: fc.constant("take" as const),
              count: fc.integer({ min: 0, max: 4 }),
              arg: tie("exp"),
            }) as fc.Arbitrary<Exp>,
            // NON-FLAT scan (ratified 2026-07-06, delivery order): the
            // accumulator threads through a diamond's values exactly as
            // they arrive — the model folds in the same delivery order
            // the batches read
            fc.record({
              type: fc.constant("scan" as const),
              init: valueArb,
              fn: fnArb,
              arg: tie("exp"),
            }) as fc.Arbitrary<Exp>,
          ]
        : []),
      fc.record({
        type: fc.constant("merge" as const),
        left: tie("exp"),
        right: tie("exp"),
      }),
      fc.record({
        type: fc.constant("mergeMap" as const),
        fns: fc.array(fnArb, { maxLength: 2 }),
        arg: tie("exp"),
      }),
      // the join primitive itself, over the stream-of-streams shapes
      fc.record({
        type: fc.constant("mergeAll" as const),
        outer: fc.oneof(
          fc.record({
            type: fc.constant("ofS" as const),
            inners: fc.array(tie("exp"), { maxLength: 3 }),
          }),
          fc.record({
            type: fc.constant("mapS" as const),
            fns: fc.array(fnArb, { maxLength: 2 }),
            arg: tie("exp"),
          }),
          ...(hotTriggerArb !== undefined
            ? [
                // dynamic inner arrival: each trigger subscribes the shared
                // stream late. Triggers come from the share-free tier: a
                // SELF-triggering hot join (triggers derived from the shared
                // stream's own source) makes the re-subscription's
                // registration indistinguishable from an empty-inner marker
                // at the emission-tree level — a recorded grammar frontier.
                fc.record({
                  type: fc.constant("mapShareS" as const),
                  arg: hotTriggerArb,
                }),
              ]
            : []),
        ),
      }),
      // the serial joins over a sync burst of inners (share-free tiers
      // only for now: shares under serial joins are a recorded frontier)
      ...(withSerialJoins
        ? [
            fc.record({
              type: fc.constant("concatAll" as const),
              inners: fc.array(tie("exp"), { maxLength: 3 }),
            }) as fc.Arbitrary<Exp>,
            fc.record({
              type: fc.constant("exhaustAll" as const),
              inners: fc.array(tie("exp"), { maxLength: 3 }),
            }) as fc.Arbitrary<Exp>,
            // switched-away inners may be LIVE: switchWithCloses
            // synthesizes closes for their stranded registrations
            fc.record({
              type: fc.constant("switchAll" as const),
              inners: fc.array(tie("exp"), { maxLength: 3 }),
            }) as fc.Arbitrary<Exp>,
            // ASYNC OUTERS (2026-07-06): each trigger value picks an inner
            // from the palette — concat queues (advancement inherits the
            // closing instant), switch switches, exhaust drops while busy.
            // UNFILTERED (2026-07-06, per-subscription identity): the
            // on-spine same-source-lifecycle ambiguity and the multi-copy
            // take slot attribution are both decided exactly by the
            // protocol's registration ids (InstInit/InstAsync.sub).
            fc.record({
              type: fc.constantFrom(
                "concatAll" as const,
                "switchAll" as const,
                "exhaustAll" as const,
              ),
              inners: fc.array(tie("exp"), { minLength: 1, maxLength: 2 }),
              trigger: tie("flat"),
            }) as fc.Arbitrary<Exp>,
            // dynamic COLD arrival for the merge join too: mergeMap over
            // palette-picked src-derived inners
            fc.record({
              type: fc.constant("mergeAll" as const),
              outer: fc.record({
                type: fc.constant("pickS" as const),
                inners: fc.array(tie("exp"), {
                  minLength: 1,
                  maxLength: 2,
                }),
                arg: tie("flat"),
              }),
            }) as fc.Arbitrary<Exp>,
          ]
        : []),
    ),
  }));

const { exp: expArb } = makeTiers([], undefined, true);
const shareRefLeaf = fc.constant({ type: "shareRef" } as Exp);
const { exp: bodyArb } = makeTiers([shareRefLeaf]);
// serial joins + non-flat take/scan over share refs (2026-07-06, enabled
// by per-subscription identity) — paired with TAKE-FREE bindings below:
// a dynamic trigger can subscribe a ref LATE, and a take-completed share
// would have reset into a fresh life the one-life model doesn't describe
// (same rule as the hot-inner tier)
const { exp: bodySerialArb } = makeTiers([shareRefLeaf], undefined, true);
// hot-join triggers may reference the shared stream ITSELF (feedback
// loops); source-derived triggers are filtered out below (upstream race)
const { exp: bodyHotArb } = makeTiers([shareRefLeaf], bodyArb);

/*
 * RESOLVED FRONTIERS (2026-07-06, per-subscription identity): two filters
 * used to guard the dynamic-arrival generators —
 *  - noSameSrcFrameLifecycles: an in-frame take(0) lifecycle of the
 *    trigger's own source landed on the arrival unit's anchor spine,
 *    indistinguishable from a routing re-statement carrying a real close;
 *  - hasMultiSrcTake: a non-flat take's cut across multiple live copies
 *    demanded opposite answers from identical counts.
 * Both are now decided exactly by the protocol's registration ids
 * (InstInit/InstAsync.sub, minted per actual subscription and preserved by
 * every re-statement): a same-source init with a foreign sub is a fresh
 * lifecycle (registers, nets zero), and a cut's extra closes match the
 * delivered-subs window memory per registration.
 */

/**
 * RECORDED FRONTIER (2026-07-06, delivery order): a shareRef inside a
 * take(0) closes IN FRAME — the share's refcount hits zero mid-unfolding
 * and the share RECONNECTS at the next ref's site, moving its slot in the
 * source's subscriber order. The model assumes one hot life with the
 * connection at the first ref's site (share lifecycle resets have always
 * been out of the model; syntactic pre-order sorting masked the order
 * consequence). Filtered from generated share bodies.
 */
const hasTransientRef = (e: Exp): boolean => {
  const containsRef = (x: Exp): boolean => {
    switch (x.type) {
      case "shareRef":
        return true;
      case "map":
      case "take":
      case "scan":
      case "mergeMap":
        return containsRef(x.arg);
      case "merge":
        return containsRef(x.left) || containsRef(x.right);
      case "letShare":
        return containsRef(x.binding) || containsRef(x.body);
      case "mergeAll":
        return x.outer.type === "ofS"
          ? x.outer.inners.some(containsRef)
          : x.outer.type === "pickS"
            ? x.outer.inners.some(containsRef) || containsRef(x.outer.arg)
            : containsRef(x.outer.arg);
      case "concatAll":
      case "switchAll":
      case "exhaustAll":
        return (
          x.inners.some(containsRef) ||
          (x.trigger !== undefined && containsRef(x.trigger))
        );
      default:
        return false;
    }
  };
  switch (e.type) {
    case "take":
      return e.count === 0
        ? containsRef(e.arg)
        : hasTransientRef(e.arg);
    case "map":
    case "scan":
    case "mergeMap":
      return hasTransientRef(e.arg);
    case "merge":
      return hasTransientRef(e.left) || hasTransientRef(e.right);
    case "letShare":
      return hasTransientRef(e.binding) || hasTransientRef(e.body);
    case "mergeAll":
      return e.outer.type === "ofS"
        ? e.outer.inners.some(hasTransientRef)
        : e.outer.type === "pickS"
          ? e.outer.inners.some(hasTransientRef) ||
            hasTransientRef(e.outer.arg)
          : hasTransientRef(e.outer.arg);
    case "concatAll":
    case "exhaustAll":
      return (
        e.inners.some(hasTransientRef) ||
        (e.trigger !== undefined && hasTransientRef(e.trigger))
      );
    case "switchAll":
      // a switched-away inner UNSUBSCRIBES its refs mid-run: the share's
      // refcount can hit zero and reconnect at a moved slot (the same
      // physics as the take(0) case above). Statically, every non-final
      // inner is switched away at frame; dynamically, every arrival
      // switches away the previous one.
      return e.trigger !== undefined
        ? e.inners.some(containsRef) || hasTransientRef(e.trigger)
        : e.inners.slice(0, -1).some(containsRef) ||
          e.inners.some(hasTransientRef);
    default:
      return false;
  }
};

const containsShareRef = (e: Exp): boolean => {
  switch (e.type) {
    case "shareRef":
      return true;
    case "map":
    case "take":
    case "scan":
    case "mergeMap":
      return containsShareRef(e.arg);
    case "merge":
      return containsShareRef(e.left) || containsShareRef(e.right);
    case "letShare":
      return containsShareRef(e.binding) || containsShareRef(e.body);
    case "mergeAll":
      return e.outer.type === "ofS"
        ? e.outer.inners.some(containsShareRef)
        : e.outer.type === "pickS"
          ? e.outer.inners.some(containsShareRef) ||
            containsShareRef(e.outer.arg)
          : containsShareRef(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return (
        e.inners.some(containsShareRef) ||
        (e.trigger !== undefined && containsShareRef(e.trigger))
      );
    default:
      return false;
  }
};

/**
 * RECORDED FRONTIER (2026-07-06, share-serial widening): a STATEFUL
 * non-flat operator (take's counting, scan's fold) over a share FAN-OUT
 * (a ref merged with other branches) consumes values in true delivery
 * order — which includes the fan-out regroup (all refs of an instant
 * deliver as one block at the connection rank). The model performs that
 * regroup lazily, once, at the letShare boundary, AFTER inner takes/scans
 * have already folded in pre-regroup order — so their computed VALUES
 * (not just display order) can differ. Fixing it needs eager tag
 * resolution (the connection anchor threaded through ctx into every
 * deliveryOrder consumer). Filtered: take/scan whose arg holds a ref
 * inside a join. (Flat ops over refs, and non-flat ops over ref-free
 * args, remain covered.)
 */
const hasStatefulOverRefJoin = (e: Exp): boolean => {
  const refUnderJoin = (x: Exp): boolean => {
    switch (x.type) {
      case "map":
      case "take":
      case "scan":
        return refUnderJoin(x.arg);
      case "merge":
        return (
          containsShareRef(x.left) ||
          containsShareRef(x.right)
        );
      case "mergeMap":
        return containsShareRef(x.arg);
      case "letShare":
        return refUnderJoin(x.binding) || refUnderJoin(x.body);
      case "mergeAll":
      case "concatAll":
      case "switchAll":
      case "exhaustAll":
        return containsShareRef(x);
      default:
        return false;
    }
  };
  switch (e.type) {
    case "take":
    case "scan":
      return refUnderJoin(e.arg) || hasStatefulOverRefJoin(e.arg);
    case "map":
    case "mergeMap":
      return hasStatefulOverRefJoin(e.arg);
    case "merge":
      return (
        hasStatefulOverRefJoin(e.left) || hasStatefulOverRefJoin(e.right)
      );
    case "letShare":
      return (
        hasStatefulOverRefJoin(e.binding) || hasStatefulOverRefJoin(e.body)
      );
    case "mergeAll":
      return e.outer.type === "ofS"
        ? e.outer.inners.some(hasStatefulOverRefJoin)
        : e.outer.type === "pickS"
          ? e.outer.inners.some(hasStatefulOverRefJoin) ||
            hasStatefulOverRefJoin(e.outer.arg)
          : hasStatefulOverRefJoin(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return (
        e.inners.some(hasStatefulOverRefJoin) ||
        (e.trigger !== undefined && hasStatefulOverRefJoin(e.trigger))
      );
    default:
      return false;
  }
};

/** guards for REF-SPAWNING dynamic outers (a serial join or pickS whose
 * inners contain a shareRef — each spawn subscribes the share LATE):
 *  - the UPSTREAM RACE (same physics as the mapShareS guard below): a
 *    trigger derived from the share's SOURCE wires the fresh ref
 *    subscription during the source event's own propagation, so whether
 *    it sees the current value depends on subject-broadcast order the
 *    model's strictly-after suffix idealizes away;
 *  - FEEDBACK-THROUGH-SERIAL-JOINS (recorded frontier, 2026-07-06): a
 *    trigger containing the ref ITSELF spawns another ref subscription
 *    mid-delivery of the very instant being fanned out — the regroup and
 *    strictly-after machinery don't describe a fan-out that grows while
 *    the instant is in flight (plain mapShareS feedback IS supported;
 *    the serial-join flavor is not yet modeled);
 *  - TICK-0 REF SPAWNS (recorded frontier, 2026-07-06): a trigger that
 *    can fire during the STATIC frame (a nonempty `of` in it) spawns
 *    refs in ARG-VALUE order, interleaved with static wiring — the model
 *    ranks tick-0 tags by palette SITE order, which can disagree. */
const hasUpstreamRaceSpawn = (e: Exp, bindingSrcs: Set<number>): boolean => {
  const containsNonemptyOf = (x: Exp): boolean => {
    switch (x.type) {
      case "of":
        return x.values.length > 0;
      case "map":
      case "take":
      case "scan":
      case "mergeMap":
        return containsNonemptyOf(x.arg);
      case "merge":
        return containsNonemptyOf(x.left) || containsNonemptyOf(x.right);
      case "letShare":
        return (
          containsNonemptyOf(x.binding) || containsNonemptyOf(x.body)
        );
      case "mergeAll":
        return x.outer.type === "ofS"
          ? x.outer.inners.some(containsNonemptyOf)
          : x.outer.type === "pickS"
            ? x.outer.inners.some(containsNonemptyOf) ||
              containsNonemptyOf(x.outer.arg)
            : containsNonemptyOf(x.outer.arg);
      case "concatAll":
      case "switchAll":
      case "exhaustAll":
        return (
          x.inners.some(containsNonemptyOf) ||
          (x.trigger !== undefined && containsNonemptyOf(x.trigger))
        );
      default:
        return false;
    }
  };
  const races = (trigger: Exp, inners: readonly Exp[]): boolean =>
    (srcIndicesOf(trigger).some((i) => bindingSrcs.has(i)) ||
      containsShareRef(trigger) ||
      containsNonemptyOf(trigger)) &&
    inners.some(containsShareRef);
  const walk = (x: Exp): boolean => {
    switch (x.type) {
      case "map":
      case "take":
      case "scan":
      case "mergeMap":
        return walk(x.arg);
      case "merge":
        return walk(x.left) || walk(x.right);
      case "letShare":
        return walk(x.binding) || walk(x.body);
      case "mergeAll":
        return x.outer.type === "ofS"
          ? x.outer.inners.some(walk)
          : x.outer.type === "pickS"
            ? races(x.outer.arg, x.outer.inners) ||
              x.outer.inners.some(walk) ||
              walk(x.outer.arg)
            : walk(x.outer.arg);
      case "concatAll":
      case "switchAll":
      case "exhaustAll":
        return (
          (x.trigger !== undefined && races(x.trigger, x.inners)) ||
          x.inners.some(walk) ||
          (x.trigger !== undefined && walk(x.trigger))
        );
      default:
        return false;
    }
  };
  return walk(e);
};

const srcIndicesOf = (e: Exp): number[] => {
  switch (e.type) {
    case "src":
      return [e.index];
    case "map":
    case "take":
    case "scan":
      return srcIndicesOf(e.arg);
    case "merge":
      return [...srcIndicesOf(e.left), ...srcIndicesOf(e.right)];
    case "mergeMap":
      return srcIndicesOf(e.arg);
    case "letShare":
      return [...srcIndicesOf(e.binding), ...srcIndicesOf(e.body)];
    case "mergeAll":
      return e.outer.type === "ofS"
        ? e.outer.inners.flatMap(srcIndicesOf)
        : e.outer.type === "pickS"
          ? [
              ...e.outer.inners.flatMap(srcIndicesOf),
              ...srcIndicesOf(e.outer.arg),
            ]
          : srcIndicesOf(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return [
        ...e.inners.flatMap(srcIndicesOf),
        ...(e.trigger !== undefined ? srcIndicesOf(e.trigger) : []),
      ];
    default:
      return [];
  }
};

const hotTriggerSrcs = (e: Exp): number[] => {
  switch (e.type) {
    case "map":
    case "take":
    case "scan":
      return hotTriggerSrcs(e.arg);
    case "merge":
      return [...hotTriggerSrcs(e.left), ...hotTriggerSrcs(e.right)];
    case "mergeMap":
      return hotTriggerSrcs(e.arg);
    case "letShare":
      return [...hotTriggerSrcs(e.binding), ...hotTriggerSrcs(e.body)];
    case "mergeAll":
      if (e.outer.type === "ofS") {
        return e.outer.inners.flatMap(hotTriggerSrcs);
      }
      if (e.outer.type === "mapShareS") {
        return srcIndicesOf(e.outer.arg);
      }
      if (e.outer.type === "pickS") {
        return [
          ...e.outer.inners.flatMap(hotTriggerSrcs),
          ...hotTriggerSrcs(e.outer.arg),
        ];
      }
      return hotTriggerSrcs(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return [
        ...e.inners.flatMap(hotTriggerSrcs),
        ...(e.trigger !== undefined ? hotTriggerSrcs(e.trigger) : []),
      ];
    default:
      return [];
  }
};

// share bindings stay src-derived (no sync-completing `of`/`empty`), so one
// hot life spans the whole run — the reset-on-completion path is covered by
// unit tests instead. Bodies with HOT INNERS (mapShareS) additionally need
// take-free bindings: a take-completed share resets, and a late trigger
// would start a fresh life the single-life model doesn't describe.
const makeBindingArb = (withTake: boolean) =>
  fc.letrec<{ flat: Exp }>((tie) => ({
    flat: fc.oneof(
      { depthSize: "small" },
      fc.record({
        type: fc.constant("src" as const),
        index: fc.integer({ min: 0, max: NUM_SOURCES - 1 }),
      }),
      fc.record({
        type: fc.constant("map" as const),
        fn: fnArb,
        arg: tie("flat"),
      }),
      ...(withTake
        ? [
            fc.record({
              type: fc.constant("take" as const),
              count: fc.integer({ min: 0, max: 4 }),
              arg: tie("flat"),
            }),
          ]
        : []),
    ),
  })).flat;

const topArb: fc.Arbitrary<Exp> = fc.oneof(
  { withCrossShrink: true },
  expArb,
  fc
    .record({
      type: fc.constant("letShare" as const),
      binding: makeBindingArb(true),
      body: bodyArb,
    })
    // in-frame transient refs (take(0)(x)) reset the share mid-unfolding
    // and move its connection slot — a recorded frontier
    .filter(({ body }) => !hasTransientRef(body)),
  // serial joins / non-flat take / dynamic outers over share refs:
  // take-free binding = one hot life spans the run (see bodySerialArb)
  fc
    .record({
      type: fc.constant("letShare" as const),
      binding: makeBindingArb(false),
      body: bodySerialArb,
    })
    .filter(
      ({ binding, body }) =>
        !hasTransientRef(body) &&
        !hasStatefulOverRefJoin(body) &&
        !hasUpstreamRaceSpawn(body, new Set(srcIndicesOf(binding))),
    ),
  fc
    .record({
      type: fc.constant("letShare" as const),
      binding: makeBindingArb(false),
      body: bodyHotArb,
    })
    .filter(({ binding, body }) => {
      // FEEDBACK LOOPS (triggers derived from the shared stream ITSELF,
      // rxjs expand-style) are supported: the subject snapshot makes them
      // strictly-after, and the trigger tier includes shareRef. But a
      // trigger derived from the share's SOURCE (upstream) races the
      // share's own delivery of the same event — the spawned subscription
      // is wired before the share delivers, so it sees the current value
      // (exactly as plain rxjs does), while the model's strictly-after
      // suffix excludes it. Modeling that needs per-value via-the-subject
      // path tracking: a recorded frontier.
      const bindingSrcs = new Set(srcIndicesOf(binding));
      return (
        hotTriggerSrcs(body).every((i) => !bindingSrcs.has(i)) &&
        !hasTransientRef(body)
      );
    }),
);

const eventsArb: fc.Arbitrary<SourceEvent[]> = fc.array(
  fc.tuple(fc.integer({ min: 0, max: NUM_SOURCES - 1 }), valueArb),
  { maxLength: 8 },
);

// DELIVERY ORDER (ratified 2026-07-06): batches read in raw arrival order —
// the model computes rxjs delivery order (subscription-key paths, close
// ranks, share fan-out regroup), so everything is exact-compare.

const runBoth = (exp0: Exp, events: readonly SourceEvent[]) => {
  const exp = assignOrigins(exp0, NUM_SOURCES);

  // the oracle. The driver completes the subjects in index order after the
  // last event, so source i closes at tick events.length + 1 + i.
  const sources = sourceTimedLists(NUM_SOURCES, events);
  const expected = valuesOf(
    batchSpec(denote(exp, sources, (i) => events.length + 1 + i)),
  );

  // the implementation
  const subjects = Array.from(
    { length: NUM_SOURCES },
    () => new InstantSubject<number>(),
  );
  const rec = record(interpret(exp, subjects));
  events.forEach(([index, value]) => subjects[index].next(value));
  subjects.forEach((s) => s.complete());

  return { exp, expected, rec };
};

describe("batchSimultaneous vs the timed-list oracle", () => {
  it("matches on random combinations of src/of/empty/map/take/merge", () => {
    fc.assert(
      fc.property(topArb, eventsArb, (exp0, events) => {
        const { exp, expected, rec } = runBoth(exp0, events);
        try {
          expect(rec.getError()).toBeUndefined();
          expect(rec.batches).toEqual(expected);
          expect(rec.isCompleted()).toBe(true);
        } catch (err) {
          throw new Error(
            `${showExp(exp)} with events ${JSON.stringify(events)}\n${String(err)}`,
          );
        }
      }),
      {
        numRuns: 500,
        // replay a recorded failure: FC_SEED=... FC_PATH=... jest oracle
        ...(process.env.FC_SEED !== undefined
          ? {
              seed: parseInt(process.env.FC_SEED, 10),
              path: process.env.FC_PATH,
              endOnFailure: true,
            }
          : {}),
      },
    );
  });

  // THE DERIVATION LAWS: merge and mergeMap are not primitives —
  // merge(a, b) = mergeAll(of(a, b)) and mergeMap(f) = mergeAll ∘ map(f).
  // Checked as program equivalences in both the model and the
  // implementation, on random subexpressions.
  it("derivation laws: merge = mergeAll∘of, mergeMap = mergeAll∘map", () => {
    fc.assert(
      fc.property(
        expArb,
        expArb,
        fc.array(fnArb, { maxLength: 2 }),
        eventsArb,
        (a, b, fns, events) => {
          const derivedMerge = runBoth(
            { type: "merge", left: a, right: b },
            events,
          );
          const primMerge = runBoth(
            { type: "mergeAll", outer: { type: "ofS", inners: [a, b] } },
            events,
          );
          expect(primMerge.rec.batches).toEqual(derivedMerge.rec.batches);
          expect(primMerge.expected).toEqual(derivedMerge.expected);

          const derivedMM = runBoth({ type: "mergeMap", fns, arg: a }, events);
          const primMM = runBoth(
            { type: "mergeAll", outer: { type: "mapS", fns, arg: a } },
            events,
          );
          expect(primMM.rec.batches).toEqual(derivedMM.rec.batches);
          expect(primMM.expected).toEqual(derivedMM.expected);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("pins dynamic inner arrival: multiplicities grow as triggers subscribe", () => {
    const src0: Exp = { type: "src", index: 0 };
    const src1: Exp = { type: "src", index: 1 };

    // let x = share(src1) in mergeAll(map(v => x)(src0)):
    // every src0 event adds a live subscription of x
    const grow: Exp = {
      type: "letShare",
      binding: src1,
      body: { type: "mergeAll", outer: { type: "mapShareS", arg: src0 } },
    };
    const growRun = runBoth(grow, [
      [0, 1], // trigger 1 subscribes x
      [1, 7], // one subscriber → [7]
      [0, 2], // trigger 2 subscribes x
      [1, 8], // two subscribers → [8, 8]
    ]);
    expect(growRun.rec.batches).toEqual([[7], [8, 8]]);
    expect(growRun.rec.batches).toEqual(growRun.expected);

    // and the hot-inner join batches with a direct reference (diamond):
    // merge(map(+1)(x), mergeAll(map(v => x)(src0)))
    const hotDiamond: Exp = {
      type: "letShare",
      binding: src1,
      body: {
        type: "merge",
        left: {
          type: "map",
          fn: { op: "add", k: 1 },
          arg: { type: "shareRef" },
        },
        right: { type: "mergeAll", outer: { type: "mapShareS", arg: src0 } },
      },
    };
    const hdRun = runBoth(hotDiamond, [
      [0, 1], // trigger subscribes x
      [1, 7], // ref sees 8, the trigger's subscription sees 7 — one batch
    ]);
    expect(hdRun.rec.batches).toEqual([[8, 7]]);
    expect(hdRun.rec.batches).toEqual(hdRun.expected);
  });

  it("pins n-ary mergeAll: a three-way diamond through the primitive", () => {
    const src0: Exp = { type: "src", index: 0 };
    const mul10: Fn = { op: "mul", k: 10 };
    const mul100: Fn = { op: "mul", k: 100 };
    const { expected, rec } = runBoth(
      {
        type: "mergeAll",
        outer: {
          type: "ofS",
          inners: [
            src0,
            { type: "map", fn: mul10, arg: src0 },
            { type: "map", fn: mul100, arg: src0 },
          ],
        },
      },
      [[0, 2]],
    );
    expect(rec.batches).toEqual([[2, 20, 200]]);
    expect(rec.batches).toEqual(expected);
  });

  it("pins the causation rule: fully transitive, sync or async alike", () => {
    const mul10: Fn = { op: "mul", k: 10 };
    const src0: Exp = { type: "src", index: 0 };

    // async trigger: the inner batches WITH its trigger
    {
      const { expected, rec } = runBoth(
        {
          type: "merge",
          left: src0,
          right: { type: "mergeMap", fns: [mul10], arg: src0 },
        },
        [[0, 5]],
      );
      expect(rec.batches).toEqual([[5, 50]]);
      expect(rec.batches).toEqual(expected);
    }

    // a SHARED cold (the same node = one of() call, subscribed twice):
    // sync-burst triggers' inners inherit the trigger's instant, and 1 and
    // 2 already share their of's instant — one batch, transitively
    {
      const o12: Exp = { type: "of", values: [1, 2] };
      const { expected, rec } = runBoth(
        {
          type: "merge",
          left: o12,
          right: { type: "mergeMap", fns: [mul10], arg: o12 },
        },
        [],
      );
      expect(rec.batches).toEqual([[1, 2, 10, 20]]);
      expect(rec.batches).toEqual(expected);
    }

    // INDEPENDENT colds (two distinct of nodes): separate root causes —
    // the left of and the right of never batch, but each trigger's inners
    // still inherit their own of's instant
    {
      const { expected, rec } = runBoth(
        {
          type: "merge",
          left: { type: "of", values: [1, 2] },
          right: {
            type: "mergeMap",
            fns: [mul10],
            arg: { type: "of", values: [1, 2] },
          },
        },
        [],
      );
      expect(rec.batches).toEqual([
        [1, 2],
        [10, 20],
      ]);
      expect(rec.batches).toEqual(expected);
    }

    // same wiring, same batch shape — whatever the source
    {
      const id: Fn = { op: "mul", k: 1 };
      const wiring = (x: Exp): Exp => ({
        type: "merge",
        left: x,
        right: { type: "mergeMap", fns: [id, mul10], arg: x },
      });
      const asyncRun = runBoth(wiring(src0), [[0, 5]]);
      expect(asyncRun.rec.batches).toEqual([[5, 5, 50]]);
      expect(asyncRun.rec.batches).toEqual(asyncRun.expected);

      const syncRun = runBoth(wiring({ type: "of", values: [5] }), []);
      expect(syncRun.rec.batches).toEqual([[5, 5, 50]]);
      expect(syncRun.rec.batches).toEqual(syncRun.expected);
    }
  });

  // Nested joins: when one ASYNC instant delivers multiple trigger values
  // (a nested join, or a diamond as the mergeMap argument), ALL sibling
  // inners inherit that instant — one batch. Realized by unitDelivery in
  // joins.ts: the whole sync flush of one async delivery forms one unit.
  it("nested joins: all sibling inners of one async instant inherit it", () => {
    const id: Fn = { op: "mul", k: 1 };
    const add100: Fn = { op: "add", k: 100 };
    const src0: Exp = { type: "src", index: 0 };
    const nested: Exp = {
      type: "mergeMap",
      fns: [id],
      arg: { type: "mergeMap", fns: [id, add100], arg: src0 },
    };

    const bare = runBoth(nested, [[0, 5]]);
    expect(bare.rec.batches).toEqual([[5, 105]]);
    expect(bare.rec.batches).toEqual(bare.expected);

    const diamond = runBoth({ type: "merge", left: src0, right: nested }, [
      [0, 5],
    ]);
    expect(diamond.rec.batches).toEqual([[5, 5, 105]]);
    expect(diamond.rec.batches).toEqual(diamond.expected);

    // a diamond as the trigger: both branch deliveries inherit the instant
    const diamondTrigger = runBoth(
      {
        type: "mergeMap",
        fns: [add100],
        arg: { type: "merge", left: src0, right: src0 },
      },
      [[0, 5]],
    );
    expect(diamondTrigger.rec.batches).toEqual([[105, 105]]);
    expect(diamondTrigger.rec.batches).toEqual(diamondTrigger.expected);
  });

  it("pins shared-pipeline diamonds (letShare)", () => {
    const mul10: Fn = { op: "mul", k: 10 };
    const add1: Fn = { op: "add", k: 1 };

    // let x = share(map(×10)(src0)) in merge(x, map(+1)(x)):
    // one upstream subscription, both refs batch per instant
    const e: Exp = {
      type: "letShare",
      binding: { type: "map", fn: mul10, arg: { type: "src", index: 0 } },
      body: {
        type: "merge",
        left: { type: "shareRef" },
        right: { type: "map", fn: add1, arg: { type: "shareRef" } },
      },
    };
    const { expected, rec } = runBoth(e, [[0, 5]]);
    expect(rec.batches).toEqual([[50, 51]]);
    expect(rec.batches).toEqual(expected);

    // a shared taken branch: closes for both refs at once
    const t: Exp = {
      type: "letShare",
      binding: { type: "take", count: 1, arg: { type: "src", index: 0 } },
      body: {
        type: "merge",
        left: { type: "shareRef" },
        right: { type: "shareRef" },
      },
    };
    const tRun = runBoth(t, [
      [0, 5],
      [0, 6],
    ]);
    expect(tRun.rec.batches).toEqual([[5, 5]]);
    expect(tRun.rec.batches).toEqual(tRun.expected);
  });

  it("pins serial-join laws: close-time threading", () => {
    const src0: Exp = { type: "src", index: 0 };
    const src1: Exp = { type: "src", index: 1 };

    // sync-closing chain: each cold inner is its own fresh instant
    const coldChain = runBoth(
      {
        type: "concatAll",
        inners: [
          { type: "of", values: [1, 2] },
          { type: "of", values: [3] },
        ],
      },
      [],
    );
    expect(coldChain.rec.batches).toEqual([[1, 2], [3]]);
    expect(coldChain.rec.batches).toEqual(coldChain.expected);

    // async close: the queued cold INHERITS the closing instant — the
    // take's final value and the advanced-to cold's values are one batch
    const takeThenCold = runBoth(
      {
        type: "concatAll",
        inners: [
          { type: "take", count: 1, arg: src0 },
          { type: "of", values: [7] },
        ],
      },
      [[0, 5]],
    );
    expect(takeThenCold.rec.batches).toEqual([[5, 7]]);
    expect(takeThenCold.rec.batches).toEqual(takeThenCold.expected);

    // ... and a diamond with the root sees the whole advancement cascade
    // in the root event's instant: [5, 5, 7]
    const takeThenColdDiamond = runBoth(
      {
        type: "merge",
        left: src0,
        right: {
          type: "concatAll",
          inners: [
            { type: "take", count: 1, arg: src0 },
            { type: "of", values: [7] },
          ],
        },
      },
      [[0, 5]],
    );
    expect(takeThenColdDiamond.rec.batches).toEqual([[5, 5, 7]]);
    expect(takeThenColdDiamond.rec.batches).toEqual(takeThenColdDiamond.expected);

    // a queued HOT inner subscribes late: suffix semantics — and a diamond
    // with the root sees multiplicity grow when the queue advances
    const lateDiamond = runBoth(
      {
        type: "merge",
        left: src0,
        right: {
          type: "concatAll",
          inners: [{ type: "take", count: 1, arg: src1 }, src0],
        },
      },
      [
        [1, 9], // closes the take: src0's second subscription begins
        [0, 5],
        [0, 6],
      ],
    );
    expect(lateDiamond.rec.batches).toEqual([[9], [5, 5], [6, 6]]);
    expect(lateDiamond.rec.batches).toEqual(lateDiamond.expected);

    // switch: every burst inner's frame values pass, only the last lives
    const switchBurst = runBoth(
      {
        type: "switchAll",
        inners: [{ type: "of", values: [1, 2] }, src0],
      },
      [[0, 5]],
    );
    expect(switchBurst.rec.batches).toEqual([[1, 2], [5]]);
    expect(switchBurst.rec.batches).toEqual(switchBurst.expected);

    // exhaust: a frame-closing inner frees the slot; the first pending
    // inner blocks the rest of the burst entirely
    const exhaustBurst = runBoth(
      {
        type: "exhaustAll",
        inners: [
          { type: "of", values: [1] },
          src0,
          { type: "of", values: [9] },
        ],
      },
      [[0, 5]],
    );
    expect(exhaustBurst.rec.batches).toEqual([[1], [5]]);
    expect(exhaustBurst.rec.batches).toEqual(exhaustBurst.expected);

    // a queued cold subscribing at an async close inherits the closing
    // instant, and its mergeMap inners inherit transitively — one batch
    const midStreamBurst = runBoth(
      {
        type: "mergeMap",
        fns: [{ op: "add", k: 100 }],
        arg: {
          type: "concatAll",
          inners: [src0, { type: "of", values: [0, 7] }],
        },
      },
      [],
    );
    expect(midStreamBurst.rec.batches).toEqual([[100, 107]]);
    expect(midStreamBurst.rec.batches).toEqual(midStreamBurst.expected);

    // intra-batch order is DELIVERY order (ratified 2026-07-06): the
    // concat branch (leftmost) subscribes src0 LATE — at event 1, when its
    // take(1) closes and the queue advances — so its subscription sits at
    // the END of the subject's list and its values deliver LAST at event 2
    // ([1, 0]), even though the branch reads first in the expression
    const lateOrder = runBoth(
      {
        type: "mergeAll",
        outer: {
          type: "ofS",
          inners: [
            {
              type: "concatAll",
              inners: [
                { type: "take", count: 1, arg: src0 },
                { type: "map", fn: { op: "add", k: 0 }, arg: src0 },
              ],
            },
            {
              type: "mergeAll",
              outer: {
                type: "mapS",
                fns: [{ op: "add", k: 1 }],
                arg: src0,
              },
            },
          ],
        },
      },
      [
        [0, 0],
        [0, 0],
      ],
    );
    expect(lateOrder.rec.batches).toEqual([
      [0, 1],
      [1, 0],
    ]);
    expect(lateOrder.rec.batches).toEqual(lateOrder.expected);

    // sources close at drive end (in index order): the queue advances
    // even with no take in sight
    const driveEndClose = runBoth(
      {
        type: "merge",
        left: src1,
        right: {
          type: "concatAll",
          inners: [src0, { type: "of", values: [7] }],
        },
      },
      [
        [0, 5],
        [1, 6],
      ],
    );
    expect(driveEndClose.rec.batches).toEqual([[5], [6], [7]]);
    expect(driveEndClose.rec.batches).toEqual(driveEndClose.expected);
  });

  it("pins feedback loops: a stream re-subscribing ITSELF on each value", () => {
    // let x = share(src0) in merge(x, mergeAll(map(v => x)(x))) — every
    // value of x subscribes x again (rxjs expand-style feedback). The
    // strictly-after rule makes it well-founded: a value never reaches
    // the subscription it spawned, so multiplicity grows by one per event
    const feedback: Exp = {
      type: "letShare",
      binding: { type: "src", index: 0 },
      body: {
        type: "merge",
        left: { type: "shareRef" },
        right: {
          type: "mergeAll",
          outer: { type: "mapShareS", arg: { type: "shareRef" } },
        },
      },
    };
    const run = runBoth(feedback, [
      [0, 5],
      [0, 7],
      [0, 9],
    ]);
    expect(run.rec.batches).toEqual([[5], [7, 7], [9, 9, 9]]);
    expect(run.rec.batches).toEqual(run.expected);
  });

  it("pins non-flat take: take SPLITS instants, counting like rxjs", () => {
    const src0: Exp = { type: "src", index: 0 };
    const diamond: Exp = { type: "merge", left: src0, right: src0 };

    // take(1) of a diamond emits ONE value, not the "whole instant"
    const one = runBoth({ type: "take", count: 1, arg: diamond }, [[0, 5]]);
    expect(one.rec.batches).toEqual([[5]]);
    expect(one.rec.batches).toEqual(one.expected);

    // take(3) cuts MID-BATCH at the second instant
    const three = runBoth({ type: "take", count: 3, arg: diamond }, [
      [0, 5],
      [0, 6],
    ]);
    expect(three.rec.batches).toEqual([[5, 5], [6]]);
    expect(three.rec.batches).toEqual(three.expected);
  });

  it("pins dynamic serial joins: async outers via trigger-picked inners", () => {
    const src0: Exp = { type: "src", index: 0 };
    const takeSrc1: Exp = {
      type: "take",
      count: 1,
      arg: { type: "src", index: 1 },
    };
    const nine: Exp = { type: "of", values: [9] };

    // concat: arrival while busy queues; the advancement subscribes the
    // queued inner AT the closing instant — [5, 9] is ONE batch
    const dynConcat = runBoth(
      { type: "concatAll", inners: [takeSrc1, nine], trigger: src0 },
      [
        [0, 0], // subscribes take(1)(src1)
        [0, 1], // of(9): busy — queued
        [1, 5], // inner emits 5 + closes; of(9) advances into the instant
      ],
    );
    expect(dynConcat.rec.batches).toEqual([[5, 9]]);
    expect(dynConcat.rec.batches).toEqual(dynConcat.expected);

    // switch: each arrival switches at its instant; a trigger sharing the
    // inner's source silences the old inner (the trigger chain subscribed
    // earlier, so the switch fires first within the instant)
    const selfInner: Exp = {
      type: "map",
      fn: { op: "add", k: 10 },
      arg: src0,
    };
    const dynSwitch = runBoth(
      { type: "switchAll", inners: [selfInner], trigger: src0 },
      [
        [0, 5],
        [0, 7],
        [0, 9],
      ],
    );
    expect(dynSwitch.rec.batches).toEqual([]);
    expect(dynSwitch.rec.batches).toEqual(dynSwitch.expected);

    // exhaust: arrivals while the inner is live are dropped entirely
    const dynExhaust = runBoth(
      { type: "exhaustAll", inners: [takeSrc1], trigger: src0 },
      [
        [0, 0], // subscribes take(1)(src1)
        [0, 0], // busy — dropped
        [1, 5], // inner emits 5 + closes
        [0, 0], // free again — re-subscribes
        [1, 6],
      ],
    );
    expect(dynExhaust.rec.batches).toEqual([[5], [6]]);
    expect(dynExhaust.rec.batches).toEqual(dynExhaust.expected);

    // pickS: mergeAll over dynamically arriving COLD src-derived inners —
    // the reused palette node is one cold stream subscribed twice
    const dynMerge = runBoth(
      {
        type: "mergeAll",
        outer: {
          type: "pickS",
          inners: [
            { type: "map", fn: { op: "add", k: 10 }, arg: { type: "src", index: 1 } },
            nine,
          ],
          arg: src0,
        },
      },
      [
        [0, 0], // subscribes map(+10)(src1)
        [0, 1], // of(9)
        [1, 5], // one live subscription: [15]
        [0, 0], // second subscription of the SAME inner
        [1, 7], // both live: [17, 17]
      ],
    );
    expect(dynMerge.rec.batches).toEqual([[9], [15], [17, 17]]);
    expect(dynMerge.rec.batches).toEqual(dynMerge.expected);
  });

  it("pins per-subscription identity: copies, lifecycles, cut attribution", () => {
    const src0: Exp = { type: "src", index: 0 };

    // TWO LIVE COPIES of a self-triggered dynamic serial join (of(0,0)
    // picks the same palette inner twice; the inner's trigger AND content
    // are src0). At src0's completion each copy's advancement grafts a
    // re-subscription of the already-completed src0 — a self-contained
    // register+close lifecycle inside the unit. Its close pairs with its
    // OWN registration (born-in-unit, matched by sub) instead of eating
    // the sibling copy's window slot, so the completion batch stays
    // whole: [0,0], not [0],[0]. (The latent bug found at seed 667319167.)
    const twoCopy = runBoth(
      {
        type: "mergeAll",
        outer: {
          type: "pickS",
          inners: [
            {
              type: "concatAll",
              inners: [
                {
                  type: "switchAll",
                  inners: [
                    { type: "of", values: [0] },
                    {
                      type: "mergeAll",
                      outer: { type: "ofS", inners: [src0] },
                    },
                  ],
                },
                src0,
              ],
              trigger: src0,
            },
          ],
          arg: { type: "of", values: [0, 0] },
        },
      },
      [
        [0, 0],
        [0, 0],
      ],
    );
    expect(twoCopy.rec.batches).toEqual([
      [0, 0],
      [0, 0],
      [0, 0],
    ]);
    expect(twoCopy.rec.batches).toEqual(twoCopy.expected);

    // ON-SPINE SAME-SOURCE LIFECYCLE (formerly filtered by
    // noSameSrcFrameLifecycles): take(0)(src0) spawned by a trigger
    // derived from src0 lands its register+close on the arrival unit's
    // anchor spine. Its foreign sub marks it a FRESH lifecycle (registers,
    // nets zero) rather than a routing re-statement carrying a real close
    // — the merge diamond neither fragments nor strands.
    const onSpine = runBoth(
      {
        type: "merge",
        left: src0,
        right: {
          type: "concatAll",
          inners: [{ type: "take", count: 0, arg: src0 }],
          trigger: src0,
        },
      },
      [
        [0, 5],
        [0, 7],
      ],
    );
    expect(onSpine.rec.batches).toEqual([[5], [7]]);
    expect(onSpine.rec.batches).toEqual(onSpine.expected);

    // MULTI-SRC TAKE COPIES in a dynamic palette (formerly filtered by
    // hasMultiSrcTake): two live copies of take(1)(merge(src1, src2));
    // each cut's extra closes consume only ITS OWN registrations' slots
    // (matched by sub against the window's delivered map) — one batch.
    const multiSrcTake = runBoth(
      {
        type: "merge",
        left: { type: "src", index: 1 },
        right: {
          type: "mergeAll",
          outer: {
            type: "pickS",
            inners: [
              {
                type: "take",
                count: 1,
                arg: {
                  type: "merge",
                  left: { type: "src", index: 1 },
                  right: { type: "src", index: 2 },
                },
              },
            ],
            arg: src0,
          },
        },
      },
      [
        [0, 0],
        [0, 0],
        [1, 5],
      ],
    );
    expect(multiSrcTake.rec.batches).toEqual([[5, 5, 5]]);
    expect(multiSrcTake.rec.batches).toEqual(multiSrcTake.expected);
  });

  it("pins drain grouping: one advancement drains many queued arrivals as one instant", () => {
    // the live inner's registration balance zeroed EARLY (its closing
    // traffic ended with net-zero feedback units), so no closing emission
    // was held — yet the completion's advancement drains BOTH queued
    // arrivals in one synchronous cascade: one instant, one batch.
    // (Found at seed 911823318 — a pre-existing bug: the drained flushes
    // used to fragment into [0],[0] when no window could group them.)
    const src0: Exp = { type: "src", index: 0 };
    const run = runBoth(
      {
        type: "concatAll",
        inners: [
          {
            type: "merge",
            left: src0,
            right: {
              type: "concatAll",
              inners: [
                {
                  type: "mergeAll",
                  outer: {
                    type: "ofS",
                    inners: [
                      {
                        type: "mergeMap",
                        fns: [],
                        arg: {
                          type: "concatAll",
                          inners: [src0],
                          trigger: { type: "of", values: [0] },
                        },
                      },
                    ],
                  },
                },
              ],
              trigger: src0,
            },
          },
          { type: "concatAll", inners: [{ type: "of", values: [0] }] },
        ],
        trigger: src0,
      },
      [
        [0, 0],
        [0, -1],
        [0, 3],
      ],
    );
    expect(run.rec.batches).toEqual([[-1], [3], [0, 0]]);
    expect(run.rec.batches).toEqual(run.expected);
  });

  it("pins the state primitive: accumulate is batching-transparent", () => {
    const src0: Exp = { type: "src", index: 0 };
    // acc' = (acc + v) * 2, starting at 1
    const scanned: Exp = {
      type: "scan",
      init: 1,
      fn: { op: "mul", k: 2 },
      arg: src0,
    };
    const bare = runBoth(scanned, [
      [0, 3],
      [0, 4],
    ]);
    expect(bare.rec.batches).toEqual([[8], [24]]);
    expect(bare.rec.batches).toEqual(bare.expected);

    // the diamond: scanned values stay simultaneous with their source
    const diamond = runBoth({ type: "merge", left: src0, right: scanned }, [
      [0, 3],
      [0, 4],
    ]);
    expect(diamond.rec.batches).toEqual([
      [3, 8],
      [4, 24],
    ]);
    expect(diamond.rec.batches).toEqual(diamond.expected);
  });

  it("agrees on the anchor law: batch(merge(a, a)) = map(x => [x, x])(a)", () => {
    fc.assert(
      fc.property(eventsArb, (events) => {
        const a: Exp = { type: "src", index: 0 };
        const diamond: Exp = { type: "merge", left: a, right: a };
        const { expected, rec } = runBoth(diamond, events);
        expect(rec.batches).toEqual(expected);
        // and the spec itself says: every batch is a doubled value
        expected.forEach((batch) => {
          expect(batch).toHaveLength(2);
          expect(batch[0]).toEqual(batch[1]);
        });
      }),
      { numRuns: 100 },
    );
  });
});
