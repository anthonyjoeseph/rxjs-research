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
 * argument. Everything else composes freely.
 */
const { exp: expArb } = fc.letrec<{ flat: Exp; exp: Exp }>((tie) => ({
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
  ),
}));

const eventsArb: fc.Arbitrary<SourceEvent[]> = fc.array(
  fc.tuple(fc.integer({ min: 0, max: NUM_SOURCES - 1 }), valueArb),
  { maxLength: 8 },
);

const runBoth = (exp0: Exp, events: readonly SourceEvent[]) => {
  const exp = assignOrigins(exp0, NUM_SOURCES);

  // the oracle
  const sources = sourceTimedLists(NUM_SOURCES, events);
  const expected = valuesOf(batchSpec(denote(exp, sources)));

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
      fc.property(expArb, eventsArb, (exp0, events) => {
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
      { numRuns: 500 },
    );
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
