import type { Closed, Tm, Ty } from "./exp.js";
import { showVal } from "./exp.js";
import { genTestCases } from "./generator.js";
import { evaluatePlainArrivals } from "./plain-eval.js";
import type { TestCase } from "./prop-test.js";
import { SubscribeRule, TimedEmit, runTimed, switchOuters } from "./timed.js";

// THE TIMED TRANSLATION AGAINST GROUND TRUTH, on generated programs.
// Two checks per program:
//
//   faithful   the timed run's values, packets dropped, are the plain
//              run's values -- the packets ride along and change nothing
//   partition  two emits share a packet instant exactly when they share
//              a driver arrival, i.e. an rxjs call stack
//
//   node timed-fuzz.js [seeds] [rule]   the sweep (default 500, last-seen)
//   node timed-fuzz.js seeds rule --tail   every program's END made visible
//   ... --operator <op>                  that operator at every root
//   node timed-fuzz.js --selftest       the refuted rules must be refuted
//
// A partition check is only load-bearing on a program whose emits span
// two or more arrivals, so those are counted separately.
//
// Beside the two checks, every sweep reports how far the COMPUTED keys
// (`Key` in `timed.ts`) are from the driver's order: `keyMisordered`
// counts programs where emit order and key order disagree, and `ties`
// programs where a `max` met two instants under one key. A mismatch is
// split by what the program holds, since `max-key` is known to be
// approximate under `switchAll` (its END) and shared slots (their keys).

// A TIMED RUN HELD TO THE PLAIN ONE. The timed program may register
// sources of its own (a second copy of an outer, under `max-dup`), which
// spend fuel and add arrivals no plain emit is in; so it runs on spare
// fuel, stops at the plain run's length, and each emit is relabelled
// with the PLAIN run's arrival. Faithful is then value equality on that
// prefix, and every arrival below is ground truth. The spare is generous
// because copies NEST: an outer holding a `switchAll` copies that one's
// copy too, so `switchAll` stacked k deep over a `defer` runs 2^k hops.
const grounded = (
  testCase: TestCase,
  rule: SubscribeRule,
): { faithful: boolean; emits: TimedEmit[] } => {
  const plain = evaluatePlainArrivals(testCase);
  const timed = runTimed(
    testCase,
    rule,
    64 * (testCase.fuel + 1),
    plain.length,
  ).slice(0, plain.length);
  return {
    faithful:
      JSON.stringify(timed.map((x) => x.value)) ===
      JSON.stringify(plain.map((x) => showVal(x.value))),
    emits: timed.map((x, i) => ({ ...x, arrival: plain[i]?.arrival ?? -1 })),
  };
};

// emits are in time order, so adjacent pairs decide it: the same arrival
// must have the same key, a later one a strictly larger key
const cmpKey = (x: TimedEmit["key"], y: TimedEmit["key"]): number =>
  x.tick !== y.tick
    ? x.tick - y.tick
    : (x.ord.map((o, i) => o - (y.ord[i] ?? -Infinity)).find((d) => d !== 0) ??
      x.ord.length - y.ord.length);
const keysOk = (emits: TimedEmit[]): boolean =>
  emits.every((e, i) => {
    if (i === 0) return true;
    const c = cmpKey(emits[i - 1].key, e.key);
    return emits[i - 1].arrival === e.arrival ? c === 0 : c < 0;
  });

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
  keyMisordered: number;
  ties: number;
  // mismatched, split by what the program holds (a case may be both)
  withSwitch: number;
  withShared: number;
  withTie: number;
  // switchAll nodes in the program text, by where `max-dup` puts the
  // outer's second copy, and programs holding one it can place nowhere
  switchAfter: number;
  switchFirst: number;
  switchNone: number;
  programsNone: number;
};

// THE COMPLETION MADE VISIBLE. A generated program's own END is almost
// never read, so no sweep says whether its packet is right. With `tail`
// every program P runs as `concat(P.map(() => 0), of(7))`: the 7 is
// emitted in P's completion, and its packet is P's END.
const withTail = (testCase: TestCase): TestCase => ({
  ...testCase,
  exp: {
    type: "mergeAll",
    ty: nat,
    limit: 1,
    src: {
      type: "of",
      ty: obsNat,
      items: [
        strm({
          type: "map",
          ty: nat,
          fn: { type: "natT", ty: nat, val: 0 },
          src: testCase.exp,
        }),
        strm({
          type: "of",
          ty: nat,
          items: [{ type: "natT", ty: nat, val: 7 }],
        }),
      ],
    },
  },
});

const sweep = (
  seeds: number,
  rule: SubscribeRule,
  verbose: boolean,
  tail = false,
  operator?: string,
): Tally =>
  Array.from({ length: seeds }, (_, i) =>
    genTestCases(`s${i}`, operator),
  ).reduce<Tally>(
    (tally, cases, i) =>
      cases.reduce<Tally>((t, generated, c) => {
        const testCase = tail ? withTail(generated) : generated;
        const { faithful, emits: timed } = grounded(testCase, rule);
        const ok = faithful && partitionOk(timed);
        const mismatch = faithful && !ok;
        const sw =
          JSON.stringify(testCase.exp).includes('"switchAll"') ||
          testCase.slots.some(
            (sl) =>
              sl.type !== "scripted" &&
              JSON.stringify(sl).includes('"switchAll"'),
          );
        const sh = testCase.slots.some((sl) => sl.type !== "scripted");
        const tie = timed.some((x) => x.tie);
        const outers = switchOuters(testCase);
        const keyed = keysOk(timed);
        if (!keyed && verbose)
          console.log(
            `KEYS s${i} case ${c}${sw ? " [switch]" : ""}${sh ? " [shared]" : ""}: ` +
              timed
                .map(
                  (x) =>
                    `${x.value}@${x.arrival}:${x.instant}=${x.key.tick}/${x.key.ord.join(".")}`,
                )
                .join("  "),
          );
        if (!ok && verbose)
          console.log(
            `${faithful ? "MISMATCH" : "UNFAITHFUL"} s${i} case ${c}` +
              `${sw ? " [switch]" : ""}${sh ? " [shared]" : ""}${tie ? " [tie]" : ""}: ` +
              timed
                .map((x) => `${x.value}@${x.arrival}:${x.instant}`)
                .join("  "),
          );
        return {
          cases: t.cases + 1,
          unfaithful: t.unfaithful + (faithful ? 0 : 1),
          mismatched: t.mismatched + (mismatch ? 1 : 0),
          loadBearing:
            t.loadBearing +
            (new Set(timed.map((x) => x.arrival)).size > 1 ? 1 : 0),
          keyMisordered: t.keyMisordered + (keyed ? 0 : 1),
          ties: t.ties + (tie ? 1 : 0),
          withSwitch: t.withSwitch + (mismatch && sw ? 1 : 0),
          withShared: t.withShared + (mismatch && sh ? 1 : 0),
          withTie: t.withTie + (mismatch && tie ? 1 : 0),
          switchAfter: t.switchAfter + outers.after,
          switchFirst: t.switchFirst + outers.first,
          switchNone: t.switchNone + outers.none,
          programsNone: t.programsNone + (outers.none > 0 ? 1 : 0),
        };
      }, tally),
    {
      cases: 0,
      unfaithful: 0,
      mismatched: 0,
      loadBearing: 0,
      keyMisordered: 0,
      ties: 0,
      withSwitch: 0,
      withShared: 0,
      withTie: 0,
      switchAfter: 0,
      switchFirst: 0,
      switchNone: 0,
      programsNone: 0,
    },
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

// TWO INSTANTS AT ONE TICK, IN BOTH ORDERS. `mergeAll(1)` over an outer
// that emits inner A at tick 1 and inner B at tick 4, while A ends at
// tick 4 too. Which of B's arrival and A's END comes first decides
// where B is subscribed, and the tick cannot say which.
//
// laneLater: B comes from hot slot 2, A's tail from cold slot 1, whose
// ordinal is minted above every hot one -- so B arrives first, is
// queued, and is subscribed in A's END: its 9 shares the arrival of A's
// 2. outerLater: A is hot slot 1 and B comes from cold slot 2, so A
// ends first with nothing queued and B is subscribed on its own
// arrival: the 9 is alone.
const obsObsNat: Ty = { type: "obs", elem: obsNat };
const strmOO = (exp: Closed): Tm => ({ type: "strmT", ty: obsObsNat, exp });
const input = (index: number): Closed => ({ type: "input", ty: nat, index });
const nine: Closed = {
  type: "of",
  ty: nat,
  items: [{ type: "natT", ty: nat, val: 9 }],
};
const twoLanes = (a: Closed, bSlot: number): Closed => ({
  type: "mergeAll",
  ty: nat,
  limit: 1,
  src: {
    type: "mergeAll",
    ty: obsNat,
    src: {
      type: "of",
      ty: obsObsNat,
      items: [
        strmOO({ type: "map", ty: obsNat, fn: strm(a), src: input(0) }),
        strmOO({ type: "map", ty: obsNat, fn: strm(nine), src: input(bSlot) }),
      ],
    },
  },
});
const hotAt = (wait: number) => ({
  type: "scripted" as const,
  input: { type: "hot" as const, async: [{ wait, val: 1 }] },
});
const coldAt = (sync: number[], wait: number) => ({
  type: "scripted" as const,
  input: { type: "cold" as const, sync, async: [{ wait, val: 2 }] },
});
const laneLater: TestCase = {
  ctx: [nat, nat, nat],
  slots: [hotAt(0), coldAt([1], 2), hotAt(3)],
  fuel: 4,
  exp: twoLanes(input(1), 2),
};
const outerLater: TestCase = {
  ctx: [nat, nat, nat],
  slots: [hotAt(0), hotAt(3), coldAt([], 3)],
  fuel: 4,
  exp: twoLanes(input(1), 2),
};

// THE KEY GAP. Both of those orders are decided by a hot ordinal below
// a dynamic one. Here both sources are colds registered in the ROOT
// arrival, B's first, so both fire at tick 4 under one computed key,
// and the driver's registration counter -- which no translation sees
// -- sends B first: queued, then subscribed in A's END. `max-key` sees
// a tie, flags it, and picks the outer.
const sameArrival: TestCase = {
  ctx: [nat, nat, nat],
  slots: [hotAt(0), coldAt([1], 3), coldAt([], 3)],
  fuel: 3,
  exp: {
    type: "mergeAll",
    ty: nat,
    limit: 1,
    src: {
      type: "mergeAll",
      ty: obsNat,
      src: {
        type: "of",
        ty: obsObsNat,
        items: [
          strmOO({ type: "map", ty: obsNat, fn: strm(nine), src: input(2) }),
          strmOO({ type: "of", ty: obsNat, items: [strm(input(1))] }),
        ],
      },
    },
  },
};

// LEFT-MOST IN THE PROGRAM DOES NOT WIN. Hot 0 fires once, at tick 2,
// into two flat-maps onto colds 1 and 2, which fire 2 ticks after they
// are subscribed. The left one X sits behind a defer, so it subscribes to
// hot 0 at tick 1; the right one Y at the root, first. A hot delivers in
// SUBSCRIPTION order, so Y registers cold 2 before X registers cold 1,
// and both fire at tick 5: the 6 (arrival 3) comes before the 5 (arrival
// 4). `max-sub` ranks the two deliveries by the subscriptions; `max-left`
// ranks them by program site and orders the 5 first.
const flatMapHot = (s: number): Closed => ({
  type: "mergeAll",
  ty: nat,
  src: { type: "map", ty: obsNat, fn: strm(input(s)), src: input(0) },
});
// a cold with no sync prefix and one async value
const tail = (wait: number, val: number) => ({
  type: "scripted" as const,
  input: { type: "cold" as const, sync: [], async: [{ wait, val }] },
});
const both = (a: Closed, b: Closed): Closed => ({
  type: "mergeAll",
  ty: nat,
  src: { type: "of", ty: obsNat, items: [strm(a), strm(b)] },
});
const fanOut: TestCase = {
  ctx: [nat, nat, nat],
  slots: [hotAt(1), tail(2, 5), tail(2, 6)],
  fuel: 6,
  exp: both({ type: "defer", ty: nat, body: flatMapHot(1) }, flatMapHot(2)),
};

// THE SAME WITHOUT A DEFER. Hot 1 fires twice into a `switchAll` whose
// every lane flat-maps hot 0 onto cold 2, so the lane that hears hot 0
// subscribed to it in hot 1's second arrival; the right-hand flat-map
// onto cold 3 subscribed at the root. Hot 0 reaches the right one first:
// the 6 (arrival 4) before the 5 (arrival 5), both at tick 6.
const switchFan: TestCase = {
  ctx: [nat, nat, nat, nat],
  slots: [
    hotAt(3),
    {
      type: "scripted",
      input: {
        type: "hot",
        async: [
          { wait: 0, val: 1 },
          { wait: 0, val: 1 },
        ],
      },
    },
    tail(1, 5),
    tail(1, 6),
  ],
  fuel: 8,
  exp: both(
    {
      type: "switchAll",
      ty: nat,
      src: { type: "map", ty: obsNat, fn: strm(flatMapHot(2)), src: input(1) },
    },
    flatMapHot(3),
  ),
};

// A COMPLETION IS AFTER WHAT IT FOLLOWS. `mergeAll(1)` over three lanes:
// A ends at tick 1, which subscribes B, a `batchSync` over `of(cold 1)`.
// B's group leaves first, and the root flat-map subscribes cold 1; only
// then does B's held END complete it, subscribing C, which gives cold 2.
// Both colds fire at tick 4, cold 1 first. Ranked by the END's own place
// in B's burst, C's subscription would sort before the group's.
const burstEnd: TestCase = {
  ctx: [nat, nat, nat],
  slots: [tail(0, 1), tail(2, 5), tail(2, 6)],
  fuel: 8,
  exp: {
    type: "mergeAll",
    ty: nat,
    src: {
      type: "mergeAll",
      ty: obsNat,
      limit: 1,
      src: {
        type: "of",
        ty: obsObsNat,
        items: [
          strmOO({
            type: "map",
            ty: obsNat,
            fn: strm({ type: "empty", ty: nat }),
            src: input(0),
          }),
          strmOO({
            type: "map",
            ty: obsNat,
            fn: {
              type: "fstT",
              ty: obsNat,
              pair: { type: "varT", ty: nat, index: 0 },
            },
            src: {
              type: "batchSync",
              ty: nat,
              src: { type: "of", ty: obsNat, items: [strm(input(1))] },
            },
          }),
          strmOO({ type: "of", ty: obsNat, items: [strm(input(2))] }),
        ],
      },
    },
  },
};

// THE SHARE GAP. A share's frame is subscribed ONCE, by whichever
// subscriber connected it, but its packets are anchored on a hole that
// every subscriber fills with its own subscription. Two root subscribers
// of a share over cold 0 hear its one value in one arrival, and the late
// one's copy names its own subscription as the registering event. The
// connecting subscription is on no path a late subscriber's packet
// travels, so no substitution can give it. `max-key` keeps a key per
// arrival and passes here only by not looking at the trail.
const shareLate: TestCase = {
  ctx: [nat, nat],
  slots: [tail(1, 3), { type: "shared", def: input(0) }],
  fuel: 3,
  exp: both(input(1), input(1)),
};

// THE SWITCH GAP. `switchAll` over an outer whose one value (an empty
// inner) comes at tick 1 and which ends at tick 4 with no value, then a
// concat onto `of(7)`. The 7 is emitted in the outer's END, arrival 2,
// and only the outer's END says so; `max-key` cannot hand it to
// `switchAll` without cancelling a lane, so it names tick 1 instead.
// the outer, whose tick-4 source is slot `late`, behind `wrap`
const switchEndOn = (
  late: number,
  wrap = (e: Closed): Closed => e,
): Closed => ({
  type: "mergeAll",
  ty: nat,
  limit: 1,
  src: {
    type: "of",
    ty: obsNat,
    items: [
      strm({
        type: "switchAll",
        ty: nat,
        src: wrap({
          type: "mergeAll",
          ty: obsNat,
          src: {
            type: "of",
            ty: obsObsNat,
            items: [
              strmOO({
                type: "map",
                ty: obsNat,
                fn: strm({ type: "empty", ty: nat }),
                src: input(0),
              }),
              strmOO({
                type: "mergeAll",
                ty: obsNat,
                src: {
                  type: "map",
                  ty: obsObsNat,
                  fn: strmOO({ type: "empty", ty: obsNat }),
                  src: input(late),
                },
              }),
            ],
          },
        }),
      }),
      strm({
        type: "of",
        ty: nat,
        items: [{ type: "natT", ty: nat, val: 7 }],
      }),
    ],
  },
});
const switchEnd: TestCase = {
  ctx: [nat, nat],
  slots: [hotAt(0), hotAt(3)],
  fuel: 3,
  exp: switchEndOn(1),
};

// THE SAME OVER A COLD. The outer's tick-4 source is now a cold whose
// one value comes 3 ticks after it is subscribed, so a second copy of
// the outer is a second run registering a second source. Subscribed
// AFTER the real one its END would come an arrival late; `max-dup`
// subscribes it FIRST, so its source fires just before the real one's
// and its END names the instant the real END is in.
const switchEndCold: TestCase = {
  ...switchEnd,
  slots: [hotAt(0), tail(3, 1)],
};

// THE GAP LEFT. The outer sits behind a `defer`, so it schedules and a
// copy must go first, and its tick-4 source is a share over hot 1, so a
// copy subscribed first would connect it. `max-dup` makes no copy, and
// the 7 is named off the lanes, as under `max-sub`.
const switchEndShared: TestCase = {
  ctx: [nat, nat, nat],
  slots: [hotAt(0), hotAt(3), { type: "shared", def: input(1) }],
  fuel: 3,
  exp: switchEndOn(2, (e) => ({ type: "defer", ty: nat, body: e })),
};

// a directed case under one rule: whether its partition holds
const holds = (name: string, testCase: TestCase, rule: SubscribeRule) => {
  const { faithful, emits } = grounded(testCase, rule);
  const ok = faithful && partitionOk(emits);
  console.log(
    `${name} / ${rule}: ${ok ? "ok" : "MISMATCH"} ` +
      emits.map((x) => `${x.value}@${x.arrival}:${x.instant}`).join("  "),
  );
  return ok;
};

// a directed case under one rule: whether its partition holds AND its
// computed keys follow the arrivals
const keyed = (name: string, testCase: TestCase, rule: SubscribeRule) => {
  const { faithful, emits } = grounded(testCase, rule);
  const ok = faithful && partitionOk(emits) && keysOk(emits);
  console.log(
    `${name} / ${rule} keys: ${ok ? "ok" : "MISORDERED"} ` +
      emits
        .map(
          (x) => `${x.value}@${x.arrival}=${x.key.tick}/${x.key.ord.join(".")}`,
        )
        .join("  "),
  );
  return ok;
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
    // the 7 alone, in the arrival and under the instant `last-seen`
    // gives it, which the plain run's arrival is checked against
    const sw = (rule: SubscribeRule, name = "", c = switchEnd) => {
      const { faithful, emits: e } = grounded(c, rule);
      const ref = grounded(c, "last-seen").emits;
      console.log(`switch END${name} / ${rule}: ${JSON.stringify(e)}`);
      return (
        faithful &&
        e.length === 1 &&
        ref.length === 1 &&
        partitionOk(ref) &&
        e[0].arrival === ref[0].arrival &&
        e[0].instant === ref[0].instant
      );
    };
    const tiesOk =
      holds("laneLater", laneLater, "max-key") &&
      holds("outerLater", outerLater, "max-key") &&
      holds("laneLater", laneLater, "max-tick") &&
      !holds("outerLater", outerLater, "max-tick") &&
      !holds("laneLater", laneLater, "outer-packet") &&
      holds("outerLater", outerLater, "last-seen") &&
      holds("laneLater", laneLater, "last-seen");
    // the gaps are ASSERTED, so their comments go red when they close
    // `max-dup` closes it over a hot and over a cold, and not where the
    // outer both schedules and reaches a share
    const switchOk =
      runTimed(switchEnd, "last-seen")[0]?.instant === "H1.0" &&
      !sw("max-key") &&
      !sw("max-sub") &&
      sw("max-dup") &&
      !sw("max-sub", " (cold)", switchEndCold) &&
      sw("max-dup", " (cold)", switchEndCold) &&
      !sw("max-dup", " (shared)", switchEndShared);
    const keyGapOk =
      holds("sameArrival", sameArrival, "max-clock") &&
      !holds("sameArrival", sameArrival, "max-key") &&
      runTimed(sameArrival, "max-key").some((x) => x.tie);
    // `max-sub` closes it and orders both fan-outs and the held END;
    // `max-left` closes it and is refuted by both fan-outs
    const subOk =
      holds("laneLater", laneLater, "max-sub") &&
      holds("outerLater", outerLater, "max-sub") &&
      keyed("sameArrival", sameArrival, "max-sub") &&
      keyed("fanOut", fanOut, "max-sub") &&
      keyed("switchFan", switchFan, "max-sub") &&
      keyed("burstEnd", burstEnd, "max-sub") &&
      keyed("sameArrival", sameArrival, "max-left") &&
      !keyed("fanOut", fanOut, "max-left") &&
      !keyed("switchFan", switchFan, "max-left") &&
      !keyed("fanOut", fanOut, "max-key") &&
      !keyed("burstEnd", burstEnd, "max-key");
    const shareGapOk =
      !keyed("shareLate", shareLate, "max-sub") &&
      keyed("shareLate", shareLate, "max-key");
    // A FLATTENER THAT ECHOES ITS OUTER needs no rule of its own: every
    // directed case holds, the switch and share gaps included. One that
    // only MARKS its lanes' start and end cannot tell a queued lane from
    // one whose outer value came later, and has no instant for the
    // outer's own END
    const reportOk = [
      holds("laneLater", laneLater, "echo"),
      holds("outerLater", outerLater, "echo"),
      holds("sameArrival", sameArrival, "echo"),
      holds("fanOut", fanOut, "echo"),
      holds("switchFan", switchFan, "echo"),
      holds("burstEnd", burstEnd, "echo"),
      holds("shareLate", shareLate, "echo"),
      sw("echo"),
      sw("echo", " (cold)", switchEndCold),
      sw("echo", " (shared)", switchEndShared),
      holds("laneLater", laneLater, "markers"),
      !holds("outerLater", outerLater, "markers"),
      !sw("markers"),
    ].every((b) => b);
    const refuted = (["outer-packet", "lanes-only"] as const).map((rule) => {
      const t = sweep(200, rule, false);
      console.log(`${rule}: ${JSON.stringify(t)}`);
      return t.mismatched > 0;
    });
    if (
      !directedOk ||
      !tiesOk ||
      !switchOk ||
      !keyGapOk ||
      !subOk ||
      !shareGapOk ||
      !reportOk ||
      refuted.includes(false)
    ) {
      console.log("SELFTEST FAILED");
      process.exit(1);
    }
    console.log(
      "selftest ok: the END case holds, max-key orders both ties, the " +
        "switch and key gaps stand, max-sub closes the key gap, max-dup " +
        "closes the switch gap but for a scheduling outer over a share, the " +
        "share gap stands, and every refuted rule is refuted",
    );
    return;
  }
  const t = sweep(
    Number(argv[0] ?? 500),
    (argv[1] ?? "last-seen") as SubscribeRule,
    true,
    argv.includes("--tail"),
    argv.includes("--operator")
      ? argv[argv.indexOf("--operator") + 1]
      : undefined,
  );
  console.log(JSON.stringify(t));
  if (t.unfaithful > 0 || t.mismatched > 0) process.exit(1);
};

main();
