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
// with the packet riding beside the value -- EXCEPT the flatteners
// under the default rule, which multicast their outer with rxjs
// `connect`, the one capability `Exp` has no former for. The `max-`
// rules do without it by ORDERING packets instead of only naming them,
// and `timed-fuzz.ts --selftest` pins the two places `max-key` still
// falls short: `switchAll`'s own END, and two dynamic sources
// registered in one arrival firing at one tick. `max-sub` closes the
// second and meets the SHARE gap instead: a share's frame is anchored on
// every subscriber rather than on the one that connected it.

// ---------------------------------------------------------------
// Packets.
// ---------------------------------------------------------------

// `hole`: the instant this stream was subscribed in, filled by whoever
// subscribed it. `abs`: a closed instant name -- a hot slot's tick, or
// anything a share or the root has closed. `rel`: an instant minted
// INSIDE this frame (a cold's async tick, a defer's hop), named by the
// path of (flattener position, inner index) segments down to it, since
// each subscription of a cold is its own schedule.
//
// `max` is the subscribe instant of a queued inner under the `max-key`
// rule: whichever operand is LATER, decided only at the root, where
// every operand's key (below) is closed. A translation cannot compare
// inside a frame, since a key relative to a frame whose own instant is
// still a hole has no tick yet.
//
// `at` is an EVENT inside an instant: the one `trail` below the event
// `base`, in the depth-first order of that instant's rxjs call stack. It
// never changes a name or a key; only the `max-sub` and `max-left` rules
// read it, to order the dynamic sources one arrival registers.
export type Pkt =
  | { t: "hole" }
  | { t: "abs"; name: string; key?: Key; dyn?: Dyn }
  | { t: "rel"; kind: string; path: string[]; off: number; base: Pkt }
  | { t: "max"; a: Pkt; b: Pkt; tickOnly?: boolean }
  | { t: "at"; base: Pkt; trail: Atom[] };
const HOLE: Pkt = { t: "hole" };

// A TRAIL IS A PATH OF SIBLING RANKS down one call stack, compared
// lexicographically, a prefix first: the stack is walked depth-first, so
// an event precedes everything it causes, and all of that precedes its
// next sibling. A number ranks by program or emission order: the k-th
// synchronous emission, a hot's value before its END. A `Rank` is the
// rank at a FAN-OUT, a hot or shared slot delivering to each subscriber
// in the order they subscribed: `sub` is that subscriber's own
// subscription event (`max-sub`), `site` its place in the program, the
// frame segments down to it (`max-left`, the refuted "left-most wins").
type Rank = { sub: Pkt; site: string[] };
type Atom = number | Rank;
// after every event the one it follows causes: a completion, which runs
// once its last value's cascade has returned. `BURST` sits just below it,
// for `batchSync`'s group, which leaves after its source's sync phase.
const TOP = 1e9;
const BURST = TOP - 1;

const at = (base: Pkt, trail: Atom[]): Pkt =>
  base.t === "at"
    ? { t: "at", base: base.base, trail: [...base.trail, ...trail] }
    : { t: "at", base, trail };
// a fan-out's delivery to the subscriber whose frame this is
const RANK: Rank = { sub: HOLE, site: [] };

// AN INSTANT'S POSITION IN THE DRIVER'S ORDER, computed from the program
// and the scripts alone: (tick, ordinal), compared lexicographically, as
// `plain-driver.ts` arbitrates. A hot slot's ordinal is its index; a
// dynamic source (a cold's async tail, a defer's hop) is minted above
// every hot one in REGISTRATION order, which across arrivals is the
// order of the arrivals that registered it -- so its ordinal is its
// base's key. Within ONE arrival the driver's counter follows the call
// stack, so `max-sub` extends the ordinal by the registering event's
// trail; `max-key` does not, and gives two such sources equal keys.
export type Key = { tick: number; ord: number[] };
// minted `off` ticks after the instant `base` subscribed it
type Dyn = { off: number; base: Pkt };

// a value, or the END marker a stream emits just before it completes,
// carrying the instant it completes in. A `take` cut emits none: its
// completion is its last value's instant.
export type Item = { p: Pkt; v: Val; end?: false } | { p: Pkt; end: true };
const val = (p: Pkt, v: Val): Item => ({ p, v });
const end = (p: Pkt): Item => ({ p, end: true });

// entering sub-frame `seg`, subscribed at instant `sp`. A name's base
// is where its key is anchored, so it is filled like any other hole.
const subst = (seg: string, sp: Pkt, p: Pkt): Pkt => {
  switch (p.t) {
    case "hole":
      return sp;
    case "rel":
      return { ...p, path: [seg, ...p.path], base: subst(seg, sp, p.base) };
    case "abs":
      return p.dyn
        ? { ...p, dyn: { ...p.dyn, base: subst(seg, sp, p.dyn.base) } }
        : p;
    case "max":
      return { ...p, a: subst(seg, sp, p.a), b: subst(seg, sp, p.b) };
    case "at":
      return at(
        subst(seg, sp, p.base),
        p.trail.map((a) =>
          typeof a === "number"
            ? a
            : { sub: subst(seg, sp, a.sub), site: [seg, ...a.site] },
        ),
      );
  }
};

// a share connects once, so its own frame is unique: every relative
// name inside it closes there. A hole leaves it as a hole -- a connect
// burst goes to the subscriber whose subscription connected it. The
// KEY does not close: it stays anchored on the connecting subscriber's
// instant, which is a hole here and is filled by EVERY subscriber, so a
// late subscriber's key is wrong -- `timed-fuzz.ts` counts those cases.
// So is a late subscriber's trail, the same arrival or not, which
// `max-sub` reads: its `shareLate` case.
const closeShare = (j: number, p: Pkt): Pkt =>
  p.t === "rel"
    ? {
        t: "abs",
        name: `Sh${j}/${p.path.join("/")}/${p.kind}`,
        dyn: { off: p.off, base: closeShare(j, p.base) },
      }
    : p.t === "max"
      ? { ...p, a: closeShare(j, p.a), b: closeShare(j, p.b) }
      : p.t === "at"
        ? at(
            closeShare(j, p.base),
            p.trail.map((a) =>
              typeof a === "number" ? a : { ...a, sub: closeShare(j, a.sub) },
            ),
          )
        : p;

const cmpKey = (x: Key, y: Key): number => {
  if (x.tick !== y.tick) return x.tick - y.tick;
  const n = Math.min(x.ord.length, y.ord.length);
  for (let i = 0; i < n; i++)
    if (x.ord[i] !== y.ord[i]) return x.ord[i] - y.ord[i];
  return x.ord.length - y.ord.length;
};

const cmpSeq = (x: number[], y: number[]): number =>
  cmpKey({ tick: 0, ord: x }, { tick: 0, ord: y });

// THE ROOT'S READING of a packet: its name, its key, its trail, and
// whether some `max` met two DIFFERENT names under equal keys and had
// to guess. The trail is read only in modes `sub` and `left`, and is
// then flat: a rank is ENCODED (`encEv`, `encSite`), so each atom is a
// number or a self-delimiting number sequence.
type RAtom = number | number[];
export type Resolved = {
  name: string;
  key: Key;
  trail: RAtom[];
  tie: boolean;
};
type Mode = "key" | "sub" | "left";

// the root subscription is arrival 0, at tick 0, before every source
const ROOT_KEY: Key = { tick: 0, ord: [] };

// AN EVENT AS ONE NUMBER SEQUENCE whose lexicographic order is the
// event order, and which no other event's encoding extends: the tick,
// then the ordinal (self-delimiting given the tick: [] only at tick 0, a
// hot's [0, i], a dynamic source's [1, ...its registration's encoding]),
// then the trail, each atom behind a 1 and closed by a 0, so a shorter
// trail sorts first.
const encTrail = (trail: RAtom[]): number[] => [
  ...trail.flatMap((a) => [1, ...(typeof a === "number" ? [a] : a)]),
  0,
];
const encEv = (r: Resolved): number[] => [
  r.key.tick,
  ...r.key.ord,
  ...encTrail(r.trail),
];
// `max-left`'s rank: the lane indices down to the subscriber, a defer's
// body counting as the one lane it has
const encSite = (site: string[]): number[] => [
  ...site.flatMap((s) => {
    const n = s.slice(s.lastIndexOf("#") + 1);
    return [1, n === "d" ? 0 : Number(n)];
  }),
  0,
];

// A DYNAMIC SOURCE'S ORDINAL. Mode `key` gives it its registering
// arrival's key, so one arrival's registrations tie; `sub` and `left`
// give it its registering EVENT, trail included, which is what the
// driver's counter counts in.
const dynKey = (d: Dyn, mode: Mode): { key: Key; tie: boolean } => {
  const b = resolve(d.base, mode);
  return {
    key: {
      tick: b.key.tick + d.off,
      ord: mode === "key" ? [1, b.key.tick, ...b.key.ord] : [1, ...encEv(b)],
    },
    tie: b.tie,
  };
};

export const resolve = (p: Pkt, mode: Mode = "key"): Resolved => {
  switch (p.t) {
    case "hole":
      return { name: "S", key: ROOT_KEY, trail: [], tie: false };
    case "abs": {
      const k = p.dyn
        ? dynKey(p.dyn, mode)
        : { key: p.key ?? ROOT_KEY, tie: false };
      return { name: p.name, trail: [], ...k };
    }
    case "rel":
      return {
        name: `S/${p.path.join("/")}/${p.kind}`,
        trail: [],
        ...dynKey({ off: p.off, base: p.base }, mode),
      };
    case "max": {
      const a = resolve(p.a, mode);
      const b = resolve(p.b, mode);
      // `tickOnly` is the refuted `max-tick`: a tick alone, and a tie
      // goes to the lane
      const c = p.tickOnly
        ? a.key.tick > b.key.tick
          ? 1
          : -1
        : mode === "key"
          ? cmpKey(a.key, b.key)
          : cmpSeq(encEv(a), encEv(b));
      const win = c >= 0 ? a : b;
      return {
        ...win,
        tie: a.tie || b.tie || (c === 0 && a.name !== b.name),
      };
    }
    case "at": {
      const b = resolve(p.base, mode);
      if (mode === "key") return b;
      const ranks = p.trail.map((a) =>
        typeof a === "number"
          ? { atom: a, tie: false }
          : mode === "left"
            ? { atom: encSite(a.site), tie: false }
            : (() => {
                const s = resolve(a.sub, mode);
                return { atom: encEv(s), tie: s.tie };
              })(),
      );
      return {
        ...b,
        trail: [...b.trail, ...ranks.map((r) => r.atom)],
        tie: b.tie || ranks.some((r) => r.tie),
      };
    }
  }
};

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
          const p: Pkt = {
            t: "abs",
            name: `H${index}.${k}`,
            key: { tick, ord: [0, index] },
          };
          subject.next(val(p, v));
          if (isLast) {
            subject.next(end(p));
            subject.complete();
          }
        },
      })),
      index,
    );
    // a fan-out: every subscriber gets the value, then every one the END
    return subject.pipe(
      rxMap((x): Item => ({ ...x, p: at(x.p, [x.end ? 1 : 0, RANK]) })),
    );
  }
  const s = input.sync.length;
  // the k-th async tick's distance from the subscription, which the
  // script alone fixes
  const offs = resolveTicks(0, input.async).map((r) => r.tick);
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
                          {
                            t: "rel",
                            kind: `C${index}.${s + k}`,
                            path: [],
                            off: offs[k],
                            base: HOLE,
                          },
                          v,
                        ),
                      );
                      if (isLast) sink.complete();
                    },
                  }),
                ),
              ),
            ),
        rxOf(...input.sync.map((x, k) => val(at(HOLE, [k]), toVal(x)))),
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
//
// THE TWO `max-` RULES DO WITHOUT `connect`. A queued inner is
// subscribed either on its own outer emission, when nothing later has
// happened in the lanes, or inside the completion of the lane that
// freed a slot, whose END is then the last lane item and later than
// the emission. Either way its instant is the LATER of its outer
// value's packet -- which rides into the lane through the `map` that
// builds it, so no beat is needed -- and the last lane instant seen.
// `max-clock` reads "later" off the driver's arrival count, which only
// the harness has, so it tests the rule; `max-key` builds a `max`
// packet the root resolves by computed keys, which is what a
// translation could do. `max-tick` compares ticks alone and gives a
// tie to the lane; two instants share a tick in either order, so the
// self-test refutes it. The outer's END becomes one more lane, last
// in any queue and completing at once, so it moves no plain value and
// is what gives the flattener's own END -- except under `switchAll`,
// where a lane cancels the live one, so there the END is the last lane
// instant alone, which is wrong whenever the outer ends later.
//
// `max-sub` is `max-key` with the dynamic sources one arrival registers
// ordered too, by their registering EVENT (its trail), and with the lane
// operand taken just AFTER the last lane item, since a slot is freed by
// a completion, which runs once that item's cascade has returned.
// `max-left` is the same with a fan-out ranked by program site instead
// of by subscription, and the self-test refutes it.
export type SubscribeRule =
  | "last-seen"
  | "outer-packet"
  | "lanes-only"
  | "max-clock"
  | "max-key"
  | "max-tick"
  | "max-sub"
  | "max-left";
type FreeRule = "max-clock" | "max-key" | "max-tick" | "max-sub" | "max-left";

type N =
  | { k: "start"; n: number; outer: Pkt; at: number; endLane: boolean }
  | { k: "item"; n: number; x: Item }
  | { k: "fin" };
type FreeSt = {
  last: Pkt;
  // whether `last` is a lane's, rather than the flattener's own
  // subscription, which is no completion and precedes every lane
  seen: boolean;
  lastAt: number;
  sps: Record<number, Pkt>;
  out: Item | null;
};

const flattenFree = (
  rule: FreeRule,
  how: "merge" | "switch" | "exhaust",
  limit: number | undefined,
  pos: string,
  outer: Observable<Item>,
  compileInner: (o: ObsVal) => Observable<Item>,
  clock: () => number,
): Observable<Item> => {
  // only a limited merge ever queues; everything else subscribes on the
  // outer emission, whose packet is then exact
  const queues = how === "merge" && limit !== undefined;
  const lanes = outer.pipe(
    filter((x) => how !== "switch" || !x.end),
    rxScan((acc: { n: number; x: Item }, x: Item) => ({ n: acc.n + 1, x }), {
      n: -1,
      x: end(HOLE),
    }),
    rxMap(({ n, x }) => {
      const head = rxOf<N>({
        k: "start",
        n,
        outer: x.p,
        at: clock(),
        endLane: x.end === true,
      });
      return x.end
        ? head
        : concat(
            head,
            compileInner(x.v as ObsVal).pipe(
              rxMap((y): N => ({ k: "item", n, x: y })),
            ),
          );
    }),
  );
  const flat =
    how === "merge"
      ? lanes.pipe(mergeAll(limit ?? Infinity))
      : how === "switch"
        ? lanes.pipe(switchAll())
        : lanes.pipe(exhaustAll());
  return concat(flat, rxOf<N>({ k: "fin" })).pipe(
    rxScan(
      (st: FreeSt, m: N): FreeSt => {
        switch (m.k) {
          case "start": {
            const sp: Pkt = !queues
              ? m.outer
              : rule === "max-clock"
                ? m.at >= st.lastAt
                  ? m.outer
                  : st.last
                : {
                    t: "max",
                    a: m.outer,
                    b:
                      st.seen && (rule === "max-sub" || rule === "max-left")
                        ? at(st.last, [TOP])
                        : st.last,
                    tickOnly: rule === "max-tick",
                  };
            const sps = { ...st.sps, [m.n]: sp };
            return m.endLane
              ? { last: sp, seen: true, lastAt: clock(), sps, out: null }
              : { ...st, sps, out: null };
          }
          case "item": {
            const p = subst(`${pos}#${m.n}`, st.sps[m.n], m.x.p);
            return {
              ...st,
              last: p,
              seen: true,
              lastAt: clock(),
              out: m.x.end ? null : { ...m.x, p },
            };
          }
          case "fin":
            return { ...st, out: end(st.last) };
        }
      },
      { last: HOLE, seen: false, lastAt: -1, sps: {}, out: null },
    ),
    filter((st) => st.out !== null),
    rxMap((st) => st.out as Item),
  );
};

type M =
  | { k: "beat"; p: Pkt }
  | { k: "start"; n: number; outer: Pkt }
  | { k: "item"; n: number; x: Item }
  | { k: "fin" };
type FlatSt = { last: Pkt; sps: Record<number, Pkt>; out: Item | null };

const flatten = (
  rule: SubscribeRule,
  clock: () => number,
  how: "merge" | "switch" | "exhaust",
  limit: number | undefined,
  pos: string,
  outer: Observable<Item>,
  compileInner: (o: ObsVal) => Observable<Item>,
): Observable<Item> =>
  rule === "last-seen" || rule === "outer-packet" || rule === "lanes-only"
    ? flattenConnect(rule, how, limit, pos, outer, compileInner)
    : flattenFree(rule, how, limit, pos, outer, compileInner, clock);

const flattenConnect = (
  rule: "last-seen" | "outer-packet" | "lanes-only",
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
                  sps: {
                    ...st.sps,
                    [m.n]: rule === "outer-packet" ? m.outer : st.last,
                  },
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
          { last: HOLE, sps: {}, out: null },
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
  clock: () => number,
  exp: Closed,
  env: Val[],
  driver: PlainDriver,
  slots: Observable<Item>[],
  pos: string,
): Observable<Item> => {
  const recur = (e: Closed, sub: string) =>
    compile(rule, clock, e, env, driver, slots, `${pos}.${sub}`);
  const inner = (o: ObsVal) =>
    compile(rule, clock, o.exp, o.env, driver, slots, "");
  switch (exp.type) {
    case "input":
      return slots[exp.index];
    case "of":
      return rxOf(
        ...exp.items.map((it, k) => val(at(HOLE, [k]), evalWith(it, env))),
        end(at(HOLE, [exp.items.length])),
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
      return flatten(
        rule,
        clock,
        "merge",
        exp.limit,
        pos,
        recur(exp.src, "s"),
        inner,
      );
    case "switchAll":
      return flatten(
        rule,
        clock,
        "switch",
        undefined,
        pos,
        recur(exp.src, "s"),
        inner,
      );
    case "exhaustAll":
      return flatten(
        rule,
        clock,
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
      const hop: Pkt = {
        t: "rel",
        kind: `D${pos}`,
        path: [],
        off: 1,
        base: HOLE,
      };
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
          clock,
          exp.body,
          [Symbol("uniq"), ...env],
          driver,
          slots,
          `${pos}.m`,
        ),
      );
    case "batchSync":
      // the plain leg's, with the group in the subscribe instant and an
      // END seen inside the burst held until the group has left. The
      // held END is the completion, AFTER the group's cascade, so it
      // takes the subscribe instant too, not its own place in the burst.
      return rxDefer(() => {
        let sync = true;
        const burst: Val[] = [];
        let endP: Pkt | undefined;
        return merge(
          recur(exp.src, "s").pipe(
            mergeMap((x): Observable<Item> => {
              if (sync) {
                if (x.end) endP = at(HOLE, [TOP]);
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
                : [val(at(HOLE, [BURST]), [burst[0], burst.slice(1)] as Val)]),
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
// the packet's name, closed at the root. `key` is its computed
// position in the driver's order, and `tie` says a `max` had to guess.
export type TimedEmit = {
  value: string;
  instant: string;
  arrival: number;
  key: Key;
  tie: boolean;
};

export const runTimed = (
  testCase: TestCase,
  rule: SubscribeRule = "last-seen",
): TimedEmit[] => {
  const driver = createPlainDriver(testCase.slots.length);
  // the harness's own count, read only by `max-clock`
  let arrival = 0;
  const clock = () => arrival;
  const slots = testCase.slots.reduce<Observable<Item>[]>(
    (prefix, slot, j) => [
      ...prefix,
      slot.type === "scripted"
        ? timedInput(driver, slot.input, j)
        : compile(rule, clock, slot.def, [], driver, prefix, "").pipe(
            rxMap(onPkt((p) => closeShare(j, p))),
            rxShare({
              resetOnRefCountZero: false,
              resetOnComplete: false,
              resetOnError: false,
            }),
            // a fan-out, one item at a time
            rxMap(onPkt((p) => at(p, [RANK]))),
          ),
    ],
    [],
  );
  const out: TimedEmit[] = [];
  const sub = compile(
    rule,
    clock,
    testCase.exp,
    [],
    driver,
    slots,
    "",
  ).subscribe((x) => {
    if (!x.end) {
      const r = resolve(
        x.p,
        rule === "max-sub" ? "sub" : rule === "max-left" ? "left" : "key",
      );
      out.push({
        value: showVal(x.v),
        instant: r.name,
        arrival,
        key: r.key,
        tie: r.tie,
      });
    }
  });
  for (let spent = 0; spent < testCase.fuel; spent++) {
    arrival++;
    if (!driver.deliverNextArrival()) break;
  }
  sub.unsubscribe();
  return out;
};
