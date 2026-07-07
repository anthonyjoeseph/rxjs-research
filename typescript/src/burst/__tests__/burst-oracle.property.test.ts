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
 *  - switchAll/exhaustAll over async outers (mapS) and concatAll-over-mapS
 *    are model-only for now (not yet reimplemented impl-side) and excluded;
 *    the static (ofS) serial joins ARE generated;
 *  - spawned refs of the bound share are excluded (upstream-race frontier —
 *    see templateArb's refIMin note).
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

/** refIMin: lowest slot a spawned-subscription template may reference.
 * Inside a letShare body it is 1 — spawning a ref of the BOUND SHARE
 * (slot 0) is the known upstream-race frontier: a trigger derived from the
 * share's source wires the spawned ref into the share's internal subject
 * before the share's own delivery arrives, so real rxjs delivers the
 * in-flight value to it, while the ratified strictly-after spec
 * (Burst.agda refView / Protocol.agda shareLives) says it misses it.
 * Excluded here; pinned as a documented divergence in burst-pinned. */
const templateArb = (
  numSlots: number,
  refIMin: number,
): fc.Arbitrary<InnerTemplate> =>
  fc.oneof(
    fc.record({
      k: fc.constant("ofv" as const),
      extra: fc.array(valueArb, { maxLength: 2 }),
    }),
    fc.record({
      k: fc.constant("constOf" as const),
      vs: fc.array(valueArb, { maxLength: 2 }),
    }),
    fc.record({
      k: fc.constant("refI" as const),
      slot: fc.integer({ min: refIMin, max: numSlots - 1 }),
    }),
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

const expArb = (
  numSlots: number,
  depth: number,
  refIMin = 0,
): fc.Arbitrary<Exp> => {
  if (depth === 0) return leafArb(numSlots);
  const sub = expArb(numSlots, depth - 1, refIMin);
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
        .tuple(templateArb(numSlots, refIMin), sub)
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
    {
      weight: 1,
      arbitrary: fc
        .array(sub, { minLength: 2, maxLength: 3 })
        .map((es): Exp => ({ k: "switchAll", s: { k: "ofS", es } })),
    },
    {
      weight: 1,
      arbitrary: fc
        .array(sub, { minLength: 2, maxLength: 3 })
        .map((es): Exp => ({ k: "exhaustAll", s: { k: "ofS", es } })),
    },
  );
};

/** letShare with a subject-backed source (the model's validity domain);
 * body slots: 0 = the share, 1..numSlots = the subjects */
const letShareArb: fc.Arbitrary<Exp> = fc
  .tuple(
    slotArb(NUM_SLOTS),
    fc.option(fnArb, { nil: undefined }),
    expArb(NUM_SLOTS + 1, 2, 1),
  )
  .map(([srcSlot, f, body]): Exp => {
    const srcRef: Exp = { k: "shareRef", first: false, slot: srcSlot };
    const src: Exp = f === undefined ? srcRef : { k: "map", f, e: srcRef };
    return { k: "letShare", src, body };
  });

/**
 * Registration-canonicity (the flat model's other validity condition, per
 * Burst.agda's INTRA-BATCH ORDER paragraph): the model's left-biased merge
 * is order-exact only when same-source ref arms appear in REGISTRATION
 * order. A DELAYED registration (a spawned refI subscription, or a static
 * ref behind a non-first concat leg) written pre-order-BEFORE a
 * frame-registered ref of the same source delivers in registration order
 * in reality (impl implements the ratified rank rule; see the pinned
 * ranked-over-subjects test) but in syntactic order in the flat model.
 * Filter: for every source, all frame-registered refs precede all delayed
 * refs in pre-order, and at most one delayed ref context per source.
 */
const isCanonical = (root: Exp): boolean => {
  let lsCounter = 0;
  const occs: { id: string; delayed: boolean }[] = [];
  const idOf = (slot: number, env: string[]): string =>
    slot < env.length ? env[slot] : `subj${slot - env.length}`;
  const walk = (e: Exp, env: string[], delayed: boolean): void => {
    switch (e.k) {
      case "shareRef":
        occs.push({ id: idOf(e.slot, env), delayed });
        return;
      case "letShare": {
        const id = `ls${lsCounter++}`;
        walk(e.src, env, delayed);
        walk(e.body, [id, ...env], delayed);
        return;
      }
      case "map":
      case "take":
      case "scan":
        walk(e.e, env, delayed);
        return;
      case "mergeAll":
      case "concatAll":
      case "switchAll":
      case "exhaustAll": {
        if (e.s.k === "ofS") {
          e.s.es.forEach((x, i) =>
            walk(x, env, delayed || (e.k === "concatAll" && i > 0)),
          );
        } else {
          walk(e.s.e, env, delayed);
          const t = e.s.tmpl;
          if (t.k === "refI")
            occs.push({ id: idOf(t.slot, env), delayed: true });
        }
        return;
      }
      case "of":
      case "empty":
        return;
    }
  };
  walk(root, [], false);
  const delayedSeen = new Map<string, number>();
  for (const o of occs) {
    if (o.delayed)
      delayedSeen.set(o.id, (delayedSeen.get(o.id) ?? 0) + 1);
    else if (delayedSeen.has(o.id)) return false; // static after delayed
  }
  for (const c of delayedSeen.values()) if (c > 1) return false;
  return true;
};

const programArb: fc.Arbitrary<Exp> = fc
  .oneof(
    { weight: 3, arbitrary: expArb(NUM_SLOTS, 3) },
    { weight: 1, arbitrary: letShareArb },
  )
  .filter(isCanonical);

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
