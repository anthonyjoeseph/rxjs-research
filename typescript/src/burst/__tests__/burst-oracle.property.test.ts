/**
 * The burst oracle: random programs over the ratified grammar, run through
 * BOTH the live rxjs machinery (interp/core/machine) and the pure model
 * (model.ts = the Burst.agda transcription). They must agree exactly —
 * batch boundaries, contents, and intra-batch order.
 *
 * Generator restrictions (= the model's stated validity domain):
 *  - letShare sources are subject-backed (shareRef / map thereof) — no
 *    sync-completing shares, whose reset-and-replay lives are decided by
 *    Protocol.agda's operational layer, not the flat denotation;
 *  - switchAll/exhaustAll and concatAll-over-mapS are model-only for now
 *    (not yet reimplemented impl-side) and excluded.
 */
import fc from "fast-check";
import { DriverEvent, Exp, ExpS, Fn, InnerTemplate, modelBatches } from "../model";
import { implBatches } from "../interp";

const NUM_SLOTS = 3;

const fnArb: fc.Arbitrary<Fn> = fc.record({
  op: fc.constantFrom("add" as const, "mul" as const),
  k: fc.integer({ min: -3, max: 3 }),
});

const valueArb = fc.integer({ min: -5, max: 9 });

const slotArb = (max: number): fc.Arbitrary<number> =>
  fc.integer({ min: 0, max: max - 1 });

const templateArb = (numSlots: number): fc.Arbitrary<InnerTemplate> =>
  fc.oneof(
    fc.record({
      k: fc.constant("ofv" as const),
      extra: fc.array(valueArb, { maxLength: 2 }),
    }),
    fc.record({
      k: fc.constant("constOf" as const),
      vs: fc.array(valueArb, { maxLength: 2 }),
    }),
    fc.record({ k: fc.constant("refI" as const), slot: slotArb(numSlots) }),
    fc.record({ k: fc.constant("mapOfv" as const), f: fnArb }),
  );

const leafArb = (numSlots: number): fc.Arbitrary<Exp> =>
  fc.oneof(
    fc.record({
      k: fc.constant("of" as const),
      vs: fc.array(valueArb, { maxLength: 3 }),
    }),
    fc.constant({ k: "empty" } as Exp),
    fc.record({
      k: fc.constant("shareRef" as const),
      first: fc.constant(false),
      slot: slotArb(numSlots),
    }),
  );

const expArb = (numSlots: number, depth: number): fc.Arbitrary<Exp> => {
  if (depth === 0) return leafArb(numSlots);
  const sub = expArb(numSlots, depth - 1);
  return fc.oneof(
    { weight: 2, arbitrary: leafArb(numSlots) },
    {
      weight: 2,
      arbitrary: fc.record({ k: fc.constant("map" as const), f: fnArb, e: sub }),
    },
    {
      weight: 1,
      arbitrary: fc.record({
        k: fc.constant("take" as const),
        n: fc.integer({ min: 0, max: 4 }),
        e: sub,
      }),
    },
    {
      weight: 1,
      arbitrary: fc.record({ k: fc.constant("scan" as const), f: fnArb, e: sub }),
    },
    {
      weight: 3,
      arbitrary: fc
        .array(sub, { minLength: 2, maxLength: 3 })
        .map((es): Exp => ({ k: "mergeAll", s: { k: "ofS", es } })),
    },
    {
      weight: 2,
      arbitrary: fc
        .tuple(templateArb(numSlots), sub)
        .map(
          ([tmpl, e]): Exp => ({ k: "mergeAll", s: { k: "mapS", tmpl, e } }),
        ),
    },
    {
      weight: 2,
      arbitrary: fc
        .array(sub, { minLength: 2, maxLength: 2 })
        .map((es): Exp => ({ k: "concatAll", s: { k: "ofS", es } })),
    },
  );
};

/** letShare with a subject-backed source (the model's validity domain);
 * body slots: 0 = the share, 1..numSlots = the subjects */
const letShareArb: fc.Arbitrary<Exp> = fc
  .tuple(
    slotArb(NUM_SLOTS),
    fc.option(fnArb, { nil: undefined }),
    expArb(NUM_SLOTS + 1, 2),
  )
  .map(([srcSlot, f, body]): Exp => {
    const srcRef: Exp = { k: "shareRef", first: false, slot: srcSlot };
    const src: Exp = f === undefined ? srcRef : { k: "map", f, e: srcRef };
    return { k: "letShare", src, body };
  });

const programArb: fc.Arbitrary<Exp> = fc.oneof(
  { weight: 3, arbitrary: expArb(NUM_SLOTS, 3) },
  { weight: 1, arbitrary: letShareArb },
);

const driverArb: fc.Arbitrary<DriverEvent[]> = fc.array(
  fc.record({ slot: slotArb(NUM_SLOTS), value: valueArb }),
  { maxLength: 5 },
);

describe("burst oracle: impl ≡ model on random programs", () => {
  test("random combinator trees agree with the Burst.agda transcription", () => {
    fc.assert(
      fc.property(programArb, driverArb, (e, d) => {
        expect(implBatches(e, NUM_SLOTS, d)).toEqual(
          modelBatches(e, NUM_SLOTS, d),
        );
      }),
      { numRuns: 500 },
    );
  });
});
