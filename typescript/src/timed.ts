import {
  EMPTY,
  Observable,
  Subject,
  concat,
  connect,
  defer as rxDefer,
  exhaustAll,
  filter,
  map as rxMap,
  merge,
  mergeAll,
  mergeMap,
  of as rxOf,
  scan as rxScan,
  share as rxShare,
  switchAll,
  take as rxTake,
} from "rxjs";
import {
  Closed,
  ObsVal,
  ScriptVal,
  Val,
  evalWith,
  showVal,
  toVal,
  unfoldMu,
} from "./exp.js";
import { PlainDriver, createPlainDriver, plainHop } from "./plain-driver.js";
import type { ObservableInput, TestCase, Timed } from "./prop-test.js";

// THE TIMED TRANSLATION: a plain run in which every value carries a
// TIMING PACKET naming the instant it was emitted in, put there by the
// translation and never read by an author's function. It is the
// executable reference for the packets the Agda top line compares the
// impl's instant stamps against, and `timed-fuzz.ts` checks it against
// the ground truth the driver already has: one arrival is one scheduled
// action, which is one rxjs call stack.
//
// Everything here is the plain leg's own rxjs, operator for operator,
// with the packet riding beside the value -- EXCEPT the flatteners,
// which multicast their outer with rxjs `connect`. That is the one
// capability `Exp` has no former for, and `timed-fuzz.ts --selftest`
// refutes the two translations that do without it.

// ---------------------------------------------------------------
// Packets.
// ---------------------------------------------------------------

// `hole`: the instant this stream was subscribed in, filled by whoever
// subscribed it. `abs`: a closed instant name -- a hot slot's tick, or
// anything a share or the root has closed. `rel`: an instant minted
// INSIDE this frame (a cold's async tick, a defer's hop), named by the
// path of (flattener position, inner index) segments down to it, since
// each subscription of a cold is its own schedule.
export type Pkt =
  | { t: "hole" }
  | { t: "abs"; name: string }
  | { t: "rel"; kind: string; path: string[] };
const HOLE: Pkt = { t: "hole" };

// a value, or the END marker a stream emits just before it completes,
// carrying the instant it completes in. A `take` cut emits none: its
// completion is its last value's instant.
export type Item = { p: Pkt; v: Val; end?: false } | { p: Pkt; end: true };
const val = (p: Pkt, v: Val): Item => ({ p, v });
const end = (p: Pkt): Item => ({ p, end: true });

// entering sub-frame `seg`, subscribed at instant `sp`
const subst = (seg: string, sp: Pkt, p: Pkt): Pkt =>
  p.t === "hole" ? sp : p.t === "rel" ? { ...p, path: [seg, ...p.path] } : p;

// a share connects once, so its own frame is unique: every relative
// name inside it closes there. A hole leaves it as a hole -- a connect
// burst goes to the subscriber whose subscription connected it.
const closeShare = (j: number, p: Pkt): Pkt =>
  p.t === "rel"
    ? { t: "abs", name: `Sh${j}/${p.path.join("/")}/${p.kind}` }
    : p;

export const rootName = (p: Pkt): string =>
  p.t === "hole"
    ? "S"
    : p.t === "abs"
      ? p.name
      : `S/${p.path.join("/")}/${p.kind}`;

const onPkt =
  (f: (p: Pkt) => Pkt) =>
  (x: Item): Item => ({ ...x, p: f(x.p) });

// append the END marker, carrying the last instant seen
const endAfter = (src: Observable<Item>): Observable<Item> =>
  concat(src.pipe(rxMap((x): Item | null => x)), rxOf<Item | null>(null)).pipe(
    rxScan(
      (st: { last: Pkt; out: Item | null }, x: Item | null) =>
        x === null
          ? { last: st.last, out: end(st.last) }
          : { last: x.p, out: x },
      { last: HOLE, out: null },
    ),
    filter((st) => st.out !== null),
    rxMap((st) => st.out as Item),
  );

// ---------------------------------------------------------------
// Scripted slots: `tickInput`, a packet per script position.
// ---------------------------------------------------------------

const resolveTicks = (anchor: number, timed: Timed<ScriptVal>[]) =>
  timed.reduce<{ tick: number; val: Val; k: number }[]>(
    (acc, { wait, val: v }, k) => {
      const prev = acc.length > 0 ? acc[acc.length - 1].tick : anchor;
      return [...acc, { tick: prev + wait + 1, val: toVal(v), k }];
    },
    [],
  );

// the plain leg's `plainInput`, with each value tagged: a hot's tick k
// is the absolute instant `Hi.k`; a cold's sync prefix is the hole (the
// subscriber's instant), and its async tick k is relative to the
// subscription that armed it.
const timedInput = (
  driver: PlainDriver,
  input: ObservableInput<ScriptVal>,
  index: number,
): Observable<Item> => {
  if (input.type === "hot") {
    const subject = new Subject<Item>();
    driver.registerSource(
      resolveTicks(0, input.async).map(({ tick, val: v, k }) => ({
        tick,
        fire: (isLast: boolean) => {
          const p: Pkt = { t: "abs", name: `H${index}.${k}` };
          subject.next(val(p, v));
          if (isLast) {
            subject.next(end(p));
            subject.complete();
          }
        },
      })),
      index,
    );
    return subject;
  }
  const s = input.sync.length;
  return endAfter(
    rxDefer(() =>
      merge(
        input.async.length === 0
          ? EMPTY
          : new Observable<Item>((sink) =>
              driver.registerSource(
                resolveTicks(driver.currentTick(), input.async).map(
                  ({ tick, val: v, k }) => ({
                    tick,
                    fire: (isLast: boolean) => {
                      sink.next(
                        val(
                          { t: "rel", kind: `C${index}.${s + k}`, path: [] },
                          v,
                        ),
                      );
                      if (isLast) sink.complete();
                    },
                  }),
                ),
              ),
            ),
        rxOf(...input.sync.map((x) => val(HOLE, toVal(x)))),
      ),
    ),
  );
};

// ---------------------------------------------------------------
// Flatteners.
// ---------------------------------------------------------------

// WHICH INSTANT AN INNER IS SUBSCRIBED IN is the whole difficulty. An
// unlimited flattener subscribes on the outer emission, so the outer
// value's own packet is the answer. A concurrency-limited `mergeAll`
// may instead QUEUE it and subscribe it when another inner completes,
// and no function of the lanes alone can tell the two apart: two
// programs differing only in their scripts' timing give identical lane
// streams (`timed-fuzz.ts` refutes both candidates).
//
// So the outer is multicast: its items reach the merged stream as
// BEATS at emission, each lane opens with a START at subscription, and
// the scan reads the subscribe instant off the merged order -- the last
// instant seen before the START. The outer's END beat is also what
// gives the flattener's own END.
//
// The rule is a parameter so the self-test can swap in the two refuted
// ones: `outer-packet` (the outer value's own packet) and `lanes-only`
// (the last instant seen, with no beats).
export type SubscribeRule = "last-seen" | "outer-packet" | "lanes-only";

type M =
  | { k: "beat"; p: Pkt }
  | { k: "start"; n: number; outer: Pkt }
  | { k: "item"; n: number; x: Item }
  | { k: "fin" };
type FlatSt = { last: Pkt; sps: Pkt[]; out: Item | null };

const flatten = (
  rule: SubscribeRule,
  how: "merge" | "switch" | "exhaust",
  limit: number | undefined,
  pos: string,
  outer: Observable<Item>,
  compileInner: (o: ObsVal) => Observable<Item>,
): Observable<Item> =>
  outer.pipe(
    connect((shared) => {
      const beats =
        rule === "lanes-only"
          ? EMPTY
          : shared.pipe(rxMap((x): M => ({ k: "beat", p: x.p })));
      const lanes = shared.pipe(
        filter((x): x is Item & { v: Val } => !x.end),
        rxScan(
          (acc: { n: number; x: Item & { v: Val } }, x) => ({
            n: acc.n + 1,
            x,
          }),
          { n: -1, x: { p: HOLE, v: null } },
        ),
        rxMap(({ n, x }) =>
          concat(
            rxOf<M>({ k: "start", n, outer: x.p }),
            compileInner(x.v as ObsVal).pipe(
              rxMap((y): M => ({ k: "item", n, x: y })),
            ),
          ),
        ),
      );
      const flat =
        how === "merge"
          ? lanes.pipe(mergeAll(limit ?? Infinity))
          : how === "switch"
            ? lanes.pipe(switchAll())
            : lanes.pipe(exhaustAll());
      return concat(merge(beats, flat), rxOf<M>({ k: "fin" })).pipe(
        rxScan(
          (st: FlatSt, m: M): FlatSt => {
            switch (m.k) {
              case "beat":
                return { ...st, last: m.p, out: null };
              case "start":
                return {
                  ...st,
                  sps: [...st.sps, rule === "outer-packet" ? m.outer : st.last],
                  out: null,
                };
              case "item": {
                const p = subst(`${pos}#${m.n}`, st.sps[m.n], m.x.p);
                return { ...st, last: p, out: m.x.end ? null : { ...m.x, p } };
              }
              case "fin":
                return { ...st, out: end(st.last) };
            }
          },
          { last: HOLE, sps: [], out: null },
        ),
        filter((st) => st.out !== null),
        rxMap((st) => st.out as Item),
      );
    }),
  );

// ---------------------------------------------------------------
// The translation.
// ---------------------------------------------------------------

// `pos` is the node's position within its frame: a flattener's segment
// and a defer's hop are named by it, so two in one frame never collide.
const compile = (
  rule: SubscribeRule,
  exp: Closed,
  env: Val[],
  driver: PlainDriver,
  slots: Observable<Item>[],
  pos: string,
): Observable<Item> => {
  const recur = (e: Closed, sub: string) =>
    compile(rule, e, env, driver, slots, `${pos}.${sub}`);
  const inner = (o: ObsVal) => compile(rule, o.exp, o.env, driver, slots, "");
  switch (exp.type) {
    case "input":
      return slots[exp.index];
    case "of":
      return rxOf(
        ...exp.items.map((it) => val(HOLE, evalWith(it, env))),
        end(HOLE),
      );
    case "empty":
      return rxOf(end(HOLE));
    case "map":
      return recur(exp.src, "s").pipe(
        rxMap((x) => (x.end ? x : val(x.p, evalWith(exp.fn, [x.v, ...env])))),
      );
    case "scan": {
      // an END passes with the state untouched; a value's output takes
      // that value's packet
      const init = evalWith(exp.init, env);
      return recur(exp.src, "s").pipe(
        rxScan(
          (acc: { s: Val; out: Item }, x: Item) => {
            if (x.end) return { s: acc.s, out: x };
            const s = evalWith(exp.fn, [[acc.s, x.v], ...env]);
            return { s, out: val(x.p, s) };
          },
          { s: init, out: end(HOLE) },
        ),
        rxMap((a) => a.out),
      );
    }
    case "take": {
      // THE END IS LAST, SO `take` COUNTS IT CORRECTLY: a source that
      // fills the quota is cut at its nth value, before any END; one
      // that does not passes its END as an item within the quota.
      const count = evalWith(exp.count, env);
      if (typeof count !== "bigint")
        throw new Error("take count did not evaluate to a nat");
      return count === 0n
        ? rxOf(end(HOLE))
        : recur(exp.src, "s").pipe(rxTake(Number(count)));
    }
    case "mergeAll":
      return flatten(rule, "merge", exp.limit, pos, recur(exp.src, "s"), inner);
    case "switchAll":
      return flatten(
        rule,
        "switch",
        undefined,
        pos,
        recur(exp.src, "s"),
        inner,
      );
    case "exhaustAll":
      return flatten(
        rule,
        "exhaust",
        undefined,
        pos,
        recur(exp.src, "s"),
        inner,
      );
    case "mu":
      return recur(unfoldMu(exp.body), "u");
    case "defer": {
      // the hop is an instant minted in this frame; the body is a
      // sub-frame subscribed in it
      const hop: Pkt = { t: "rel", kind: `D${pos}`, path: [] };
      return rxDefer(() =>
        plainHop(driver, driver.currentTick() + 1).pipe(
          mergeMap(() =>
            recur(exp.body, "b").pipe(
              rxMap(onPkt((p) => subst(`${pos}#d`, hop, p))),
            ),
          ),
        ),
      );
    }
    case "mint":
      return rxDefer(() =>
        compile(
          rule,
          exp.body,
          [Symbol("uniq"), ...env],
          driver,
          slots,
          `${pos}.m`,
        ),
      );
    case "batchSync":
      // the plain leg's, with the group in the subscribe instant and an
      // END seen inside the burst held until the group has left
      return rxDefer(() => {
        let sync = true;
        const burst: Val[] = [];
        let endP: Pkt | undefined;
        return merge(
          recur(exp.src, "s").pipe(
            mergeMap((x): Observable<Item> => {
              if (sync) {
                if (x.end) endP = x.p;
                else burst.push(x.v);
                return EMPTY;
              }
              return rxOf(x.end ? x : val(x.p, [x.v, []] as Val));
            }),
          ),
          rxDefer(() => {
            sync = false;
            return rxOf(
              ...(burst.length === 0
                ? []
                : [val(HOLE, [burst[0], burst.slice(1)] as Val)]),
              ...(endP ? [end(endP)] : []),
            );
          }),
        );
      });
    case "varE":
      throw new Error(
        "varE in a closed expression — generator/decoder invariant violated",
      );
  }
};

// ---------------------------------------------------------------
// Running it, with the ground truth beside each emit.
// ---------------------------------------------------------------

// `arrival` is the ground truth: the driver's scheduled action the
// value was emitted in, 0 for the root subscribe frame. `instant` is
// the packet's name, closed at the root.
export type TimedEmit = { value: string; instant: string; arrival: number };

export const runTimed = (
  testCase: TestCase,
  rule: SubscribeRule = "last-seen",
): TimedEmit[] => {
  const driver = createPlainDriver(testCase.slots.length);
  const slots = testCase.slots.reduce<Observable<Item>[]>(
    (prefix, slot, j) => [
      ...prefix,
      slot.type === "scripted"
        ? timedInput(driver, slot.input, j)
        : compile(rule, slot.def, [], driver, prefix, "").pipe(
            rxMap(onPkt((p) => closeShare(j, p))),
            rxShare({
              resetOnRefCountZero: false,
              resetOnComplete: false,
              resetOnError: false,
            }),
          ),
    ],
    [],
  );
  const out: TimedEmit[] = [];
  let arrival = 0;
  const sub = compile(rule, testCase.exp, [], driver, slots, "").subscribe(
    (x) => {
      if (!x.end)
        out.push({ value: showVal(x.v), instant: rootName(x.p), arrival });
    },
  );
  for (let spent = 0; spent < testCase.fuel; spent++) {
    arrival++;
    if (!driver.deliverNextArrival()) break;
  }
  sub.unsubscribe();
  return out;
};
