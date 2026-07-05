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
  fc.letrec<{ flat: Exp; cold: Exp; exp: Exp }>((tie) => ({
    // `cold` expressions complete within their subscription frame — the only
    // inners a switchAll may SWITCH AWAY FROM today: unsubscribing a live
    // (src-backed) inner leaves its registration without a close in the
    // provenance memory (the unsubscribe-close protocol gap, a recorded
    // frontier)
    cold: fc.oneof(
      { depthSize: "small", withCrossShrink: true },
      fc.record({
        type: fc.constant("of" as const),
        values: fc.array(valueArb, { maxLength: 3 }),
      }),
      fc.record({ type: fc.constant("empty" as const) }),
      fc.record({
        type: fc.constant("map" as const),
        fn: fnArb,
        arg: tie("cold"),
      }),
      fc.record({
        type: fc.constant("take" as const),
        count: fc.integer({ min: 0, max: 4 }),
        arg: tie("cold"),
      }),
    ),
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
    ),
    exp: fc.oneof(
      { depthSize: "small", withCrossShrink: true },
      tie("flat"),
      fc.record({
        type: fc.constant("map" as const),
        fn: fnArb,
        arg: tie("exp"),
      }),
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
            // switched-away inners must be cold (see the `cold` tier note)
            fc
              .tuple(fc.array(tie("cold"), { maxLength: 2 }), tie("exp"))
              .map(([earlier, last]): Exp => ({
                type: "switchAll",
                inners: [...earlier, last],
              })),
          ]
        : []),
    ),
  }));

const { exp: expArb } = makeTiers([], undefined, true);
const shareRefLeaf = fc.constant({ type: "shareRef" } as Exp);
const { exp: bodyArb } = makeTiers([shareRefLeaf]);
const { exp: bodyHotArb } = makeTiers([shareRefLeaf], expArb);

const srcIndicesOf = (e: Exp): number[] => {
  switch (e.type) {
    case "src":
      return [e.index];
    case "map":
    case "take":
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
        : srcIndicesOf(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return e.inners.flatMap(srcIndicesOf);
    default:
      return [];
  }
};

const hotTriggerSrcs = (e: Exp): number[] => {
  switch (e.type) {
    case "map":
    case "take":
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
      return hotTriggerSrcs(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return e.inners.flatMap(hotTriggerSrcs);
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
  fc.record({
    type: fc.constant("letShare" as const),
    binding: makeBindingArb(true),
    body: bodyArb,
  }),
  fc
    .record({
      type: fc.constant("letShare" as const),
      binding: makeBindingArb(false),
      body: bodyHotArb,
    })
    .filter(({ binding, body }) => {
      // no self-triggering: hot-join triggers must not derive from the
      // shared stream's own source
      const bindingSrcs = new Set(srcIndicesOf(binding));
      return hotTriggerSrcs(body).every((i) => !bindingSrcs.has(i));
    }),
);

const eventsArb: fc.Arbitrary<SourceEvent[]> = fc.array(
  fc.tuple(fc.integer({ min: 0, max: NUM_SOURCES - 1 }), valueArb),
  { maxLength: 8 },
);

const hasShare = (e: Exp): boolean => {
  switch (e.type) {
    case "letShare":
      return true;
    case "map":
    case "take":
      return hasShare(e.arg);
    case "merge":
      return hasShare(e.left) || hasShare(e.right);
    case "mergeMap":
      return hasShare(e.arg);
    case "mergeAll":
      return e.outer.type === "ofS"
        ? e.outer.inners.some(hasShare)
        : e.outer.type === "mapShareS"
          ? true
          : hasShare(e.outer.arg);
    case "concatAll":
    case "switchAll":
    case "exhaustAll":
      return e.inners.some(hasShare);
    default:
      return false;
  }
};

// Intra-batch order for shared fan-out follows the DELIVERY TREE (a share's
// refs receive consecutively at the share's connection point), while the
// model idealizes flat pre-order. Membership and batch sequence are exact
// everywhere; share-containing programs compare batches up to intra-batch
// order (the exact fan-out order is pinned by unit tests in share.test.ts).
// (-0 normalizes to 0: the sort can't order them and toEqual distinguishes)
const canonBatches = (batches: number[][]): number[][] =>
  batches.map((b) => b.map((v) => (v === 0 ? 0 : v)).sort((x, y) => x - y));

const runBoth = (exp0: Exp, events: readonly SourceEvent[]) => {
  const exp = assignOrigins(exp0, NUM_SOURCES);

  // the oracle. The driver completes the subjects in index order after the
  // last event, so source i closes at tick events.length + 1 + i.
  const sources = sourceTimedLists(NUM_SOURCES, events);
  const expected = valuesOf(
    batchSpec(denote(exp, sources, (i) => events.length + 1 + i, NUM_SOURCES)),
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
          if (hasShare(exp)) {
            expect(canonBatches(rec.batches)).toEqual(canonBatches(expected));
          } else {
            expect(rec.batches).toEqual(expected);
          }
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

  it("pins the blessed causal-batching semantics (option 1)", () => {
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

    // sync-burst triggers: sibling inners are fresh causes, batch separately
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
      expect(rec.batches).toEqual([[1, 2], [10], [20]]);
      expect(rec.batches).toEqual(expected);
    }

    // same wiring, sync vs async source: the non-transitivity, pinned
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
      expect(syncRun.rec.batches).toEqual([[5], [5, 50]]);
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

    // async close: the queued cold subscribes AT the closing tick, as a
    // fresh instant ordered right after it (never batched with it)
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
    expect(takeThenCold.rec.batches).toEqual([[5], [7]]);
    expect(takeThenCold.rec.batches).toEqual(takeThenCold.expected);

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

    // a mid-stream subscription instant behaves exactly like the root one:
    // a queued cold's values are one instant, and their mergeMap inners
    // are FRESH root causes (never coalesced into one inherited unit)
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
    expect(midStreamBurst.rec.batches).toEqual([[100], [107]]);
    expect(midStreamBurst.rec.batches).toEqual(midStreamBurst.expected);

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
