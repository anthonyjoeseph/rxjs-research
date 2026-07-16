/**
 * The GLOBAL oracle: random canonical programs run through BOTH the live
 * TypeScript rxjs machinery (interp/primitives/batchSimultaneous) AND the
 * Agda `impl-batchSimultaneous`, via the compiled Agda CLI (agda/_cli/Main,
 * built by `npm run agda:cli`). They must agree exactly — this checks that
 * the TS implementation faithfully mirrors the Agda implementation, with no
 * trusted hand-transcription in between.
 *
 * The Agda-`spec` arm is dropped for now (Anthony): once impl ≡ spec is
 * proven in Agda, TS-impl vs Agda-impl suffices. Since a shared bug agrees
 * between the two impls, this surfaces only genuine TS↔Agda drift.
 *
 * Batch mode: fast-check `sample`s N cases (seeded), we serialize them as
 * NDJSON, run the Agda CLI ONCE, and compare each result to the TS impl.
 */
import { execFileSync } from "child_process";
import { existsSync } from "fs";
import * as path from "path";
import fc from "fast-check";
import { DriverEvent, Exp, ExpS, Fn, InnerTemplate } from "../model";
import { implBatches } from "../interp";

const NUM_SLOTS = 3;

// values are ℕ-safe (non-negative): the Agda side is Val = ℕ, and batching /
// ordering behavior is value-agnostic, so this costs nothing in coverage.
const fnArb: fc.Arbitrary<Fn> = fc.record({
  op: fc.constantFrom("add" as const, "mul" as const),
  k: fc.integer({ min: 0, max: 3 }),
});

const valueArb = fc.integer({ min: 0, max: 9 });

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
    // refI spawns a ref of a SUBJECT (a subject index) — never the bound
    // share, so the upstream-race frontier is excluded by construction
    fc.record({
      k: fc.constant("refI" as const),
      slot: fc.integer({ min: 0, max: NUM_SLOTS - 1 }),
    }),
    fc.record({ k: fc.constant("mapOfv" as const), f: fnArb }),
  );

// a leaf reference: the first `numSlots - NUM_SLOTS` slots are letShare
// shares (de Bruijn `share`), the rest are driver subjects (`src`). Matches
// the Agda split srcE / shareE.
const refLeafArb = (numSlots: number): fc.Arbitrary<Exp> => {
  const shares = numSlots - NUM_SLOTS;
  return slotArb(numSlots).map((s): Exp =>
    s < shares
      ? { k: "share", first: false, slot: s }
      : { k: "src", slot: s - shares },
  );
};

const leafArb = (numSlots: number): fc.Arbitrary<Exp> =>
  fc.oneof(
    fc.record({
      k: fc.constant("of" as const),
      vs: fc.array(valueArb, { maxLength: 3 }),
    }),
    fc.constant({ k: "empty" } as Exp),
    refLeafArb(numSlots),
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
      arbitrary: fc.record({
        k: fc.constant("map" as const),
        f: fnArb,
        e: sub,
      }),
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
      arbitrary: fc.record({
        k: fc.constant("scan" as const),
        f: fnArb,
        e: sub,
      }),
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
        .map(([tmpl, e]): Exp => ({
          k: "mergeAll",
          s: { k: "mapS", tmpl, e },
        })),
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
    {
      weight: 1,
      arbitrary: fc
        .tuple(
          fc.constantFrom(
            "concatAll" as const,
            "switchAll" as const,
            "exhaustAll" as const,
          ),
          templateArb(numSlots, refIMin),
          sub,
        )
        .map(([k, tmpl, e]): Exp => ({ k, s: { k: "mapS", tmpl, e } })),
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
    const srcRef: Exp = { k: "src", slot: srcSlot }; // subject-backed binding
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
  // roots feeding a share: a DIRECT ref of a share's source inside the
  // letShare body interleaves with the share's fan-out block in the flat
  // model but delivers outside the block in reality (the ratified
  // block-at-connection-rank rule) — outside the flat model's domain
  const forbidden = new Set<string>();
  let sawForbidden = false;
  // subjects id as `subj<i>`; a share ids by its binder (de Bruijn `env`)
  const rootOf = (e: Exp, env: string[]): string | null =>
    e.k === "src"
      ? `subj${e.slot}`
      : e.k === "share"
        ? env[e.slot]
        : e.k === "map" || e.k === "scan" || e.k === "take"
          ? rootOf(e.e, env)
          : null;
  const walk = (e: Exp, env: string[], delayed: boolean): void => {
    switch (e.k) {
      case "src": {
        const id = `subj${e.slot}`;
        if (forbidden.has(id)) sawForbidden = true;
        occs.push({ id, delayed });
        return;
      }
      case "share": {
        const id = env[e.slot];
        if (forbidden.has(id)) sawForbidden = true;
        occs.push({ id, delayed });
        return;
      }
      case "letShare": {
        const id = `ls${lsCounter++}`;
        walk(e.src, env, delayed);
        const srcRoot = rootOf(e.src, env);
        if (srcRoot !== null) forbidden.add(srcRoot);
        walk(e.body, [id, ...env], delayed);
        if (srcRoot !== null) forbidden.delete(srcRoot);
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
          if (t.k === "refI") {
            const id = `subj${t.slot}`; // refI targets a subject index
            if (forbidden.has(id)) sawForbidden = true;
            occs.push({ id, delayed: true });
          }
        }
        return;
      }
      case "of":
      case "empty":
        return;
    }
  };
  walk(root, [], false);
  if (sawForbidden) return false;
  const delayedSeen = new Map<string, number>();
  for (const o of occs) {
    if (o.delayed) delayedSeen.set(o.id, (delayedSeen.get(o.id) ?? 0) + 1);
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

const CLI = path.resolve(__dirname, "../../../agda/_cli/Main");

type Case = { slots: number; exp: Exp; driver: DriverEvent[] };

/** run a batch of cases through the Agda impl-batchSimultaneous CLI */
const agdaBatch = (cases: Case[]): number[][][] => {
  const input = cases.map((c) => JSON.stringify(c)).join("\n") + "\n";
  const out = execFileSync(CLI, {
    input,
    encoding: "utf8",
    maxBuffer: 1 << 28,
  });
  return out
    .trim()
    .split("\n")
    .map((line) => JSON.parse(line) as number[][]);
};

describe("global oracle: TS impl ≡ Agda impl on random canonical programs", () => {
  test("TS batchSimultaneous matches the Agda impl-batchSimultaneous", () => {
    if (!existsSync(CLI))
      throw new Error(
        `Agda CLI not built at ${CLI} — run \`npm run agda:cli\` first.`,
      );
    const numRuns = Number(process.env.FC_NUM_RUNS ?? 500);
    const seed = Number(process.env.FC_SEED ?? 0);
    const cases: [Exp, DriverEvent[]][] = fc.sample(
      fc.tuple(programArb, driverArb),
      { numRuns, seed },
    );
    const agda = agdaBatch(
      cases.map(([exp, driver]) => ({ slots: NUM_SLOTS, exp, driver })),
    );
    for (let i = 0; i < cases.length; i++) {
      const [e, d] = cases[i];
      const ts = JSON.stringify(implBatches(e, NUM_SLOTS, d));
      const ag = JSON.stringify(agda[i]);
      if (ts !== ag)
        throw new Error(
          `TS↔Agda impl MISMATCH (seed=${seed}, case=${i})\n` +
            `  program = ${JSON.stringify(e)}\n` +
            `  driver  = ${JSON.stringify(d)}\n` +
            `  ts-impl   = ${ts}\n` +
            `  agda-impl = ${ag}`,
        );
    }
  });
});
