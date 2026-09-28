import type { Closed, Tm, Ty } from "./exp.js";
import { showVal } from "./exp.js";
import { genTestCases } from "./generator.js";
import { evaluatePlain } from "./plain-eval.js";
import type { TestCase } from "./prop-test.js";
import { SubscribeRule, TimedEmit, runTimed } from "./timed.js";

// THE TIMED TRANSLATION AGAINST GROUND TRUTH, on generated programs.
// Two checks per program:
//
//   faithful   the timed run's values, packets dropped, are the plain
//              run's values -- the packets ride along and change nothing
//   partition  two emits share a packet instant exactly when they share
//              a driver arrival, i.e. an rxjs call stack
//
//   node timed-fuzz.js [seeds]      the sweep (default 500 seeds)
//   node timed-fuzz.js --selftest   the refuted rules must be refuted
//
// A partition check is only load-bearing on a program whose emits span
// two or more arrivals, so those are counted separately.

const partitionOk = (emits: TimedEmit[]): boolean => {
  const byInstant = new Map<string, number>();
  const byArrival = new Map<number, string>();
  return emits.every(({ instant, arrival }) => {
    const a = byInstant.get(instant);
    const i = byArrival.get(arrival);
    byInstant.set(instant, arrival);
    byArrival.set(arrival, instant);
    return (
      (a === undefined || a === arrival) && (i === undefined || i === instant)
    );
  });
};

type Tally = {
  cases: number;
  unfaithful: number;
  mismatched: number;
  loadBearing: number;
};

const sweep = (seeds: number, rule: SubscribeRule, verbose: boolean): Tally =>
  Array.from({ length: seeds }, (_, i) => genTestCases(`s${i}`)).reduce<Tally>(
    (tally, cases, i) =>
      cases.reduce<Tally>((t, testCase, c) => {
        const plain = evaluatePlain(testCase).map(showVal);
        const timed = runTimed(testCase, rule);
        const faithful =
          JSON.stringify(timed.map((x) => x.value)) === JSON.stringify(plain);
        const ok = faithful && partitionOk(timed);
        if (!ok && verbose)
          console.log(
            `${faithful ? "MISMATCH" : "UNFAITHFUL"} s${i} case ${c}: ` +
              timed
                .map((x) => `${x.value}@${x.arrival}:${x.instant}`)
                .join("  "),
          );
        return {
          cases: t.cases + 1,
          unfaithful: t.unfaithful + (faithful ? 0 : 1),
          mismatched: t.mismatched + (faithful && !ok ? 1 : 0),
          loadBearing:
            t.loadBearing +
            (new Set(timed.map((x) => x.arrival)).size > 1 ? 1 : 0),
        };
      }, tally),
    { cases: 0, unfaithful: 0, mismatched: 0, loadBearing: 0 },
  );

// THE END MARKER IS LOAD-BEARING, and no generated program so far
// shows it: `concat(A.pipe(mergeMap(() => EMPTY)), of(7))` with A a hot
// firing once. The 7 is emitted in A's arrival, and only the inner
// flattener's END says so -- nothing it emits carries A's packet.
const nat: Ty = { type: "nat" };
const obsNat: Ty = { type: "obs", elem: nat };
const strm = (exp: Closed): Tm => ({ type: "strmT", ty: obsNat, exp });
const endDirected: TestCase = {
  ctx: [nat],
  slots: [
    { type: "scripted", input: { type: "hot", async: [{ wait: 0, val: 1 }] } },
  ],
  fuel: 3,
  exp: {
    type: "mergeAll",
    ty: nat,
    limit: 1,
    src: {
      type: "of",
      ty: obsNat,
      items: [
        strm({
          type: "mergeAll",
          ty: nat,
          src: {
            type: "map",
            ty: obsNat,
            fn: strm({ type: "empty", ty: nat }),
            src: { type: "input", ty: nat, index: 0 },
          },
        }),
        strm({
          type: "of",
          ty: nat,
          items: [{ type: "natT", ty: nat, val: 7 }],
        }),
      ],
    },
  },
};

const main = () => {
  const argv = process.argv.slice(2);
  if (argv[0] === "--selftest") {
    const directed = runTimed(endDirected);
    const directedOk =
      directed.length === 1 &&
      directed[0].arrival === 1 &&
      directed[0].instant === "H0.0";
    console.log(`END directed: ${JSON.stringify(directed)}`);
    const refuted = (["outer-packet", "lanes-only"] as const).map((rule) => {
      const t = sweep(200, rule, false);
      console.log(`${rule}: ${JSON.stringify(t)}`);
      return t.mismatched > 0;
    });
    if (!directedOk || refuted.includes(false)) {
      console.log("SELFTEST FAILED");
      process.exit(1);
    }
    console.log(
      "selftest ok: the END case holds and both refuted rules are refuted",
    );
    return;
  }
  const t = sweep(Number(argv[0] ?? 500), "last-seen", true);
  console.log(JSON.stringify(t));
  if (t.unfaithful > 0 || t.mismatched > 0) process.exit(1);
};

main();
