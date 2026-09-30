import {
  EMPTY,
  Observable,
  Subject,
  concat,
  connect,
  defer as rxDefer,
  endWith,
  exhaustAll,
  filter,
  ignoreElements,
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
// every subscriber rather than on the one that connected it. `max-dup`
// closes the first by subscribing the outer twice, except where the
// outer both schedules and reaches a share.
//
// `echo` needs none of that, and no key: a flattener that ECHOES each
// outer element as it arrives, before handling it, gives `last-seen` its
// beats from ordinary rxjs, and both gaps close, since the outer's END is
// echoed like any element and nothing is compared. `markers` -- a Start
// and Done per lane and an OuterDone -- is not enough: a queued lane and
// one whose outer value came later both follow a Done, and the OuterDone
// carries no instant.

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

// append the END marker, carrying the last instant seen, unless the
// stream already ended with one. A stream that completes with no item at
// all ends in its subscription's own instant: the hole.
const endAfter = (src: Observable<Item>): Observable<Item> =>
  concat(src.pipe(rxMap((x): Item | null => x)), rxOf<Item | null>(null)).pipe(
    rxScan(
      (st: { last: Pkt; ended: boolean; out: Item | null }, x: Item | null) =>
        x === null
          ? { ...st, out: st.ended ? null : end(st.last) }
          : { last: x.p, ended: x.end === true, out: x },
      { last: HOLE, ended: false, out: null },
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
    // a fan-out: every subscriber gets the value, then every one the END;
    // one subscribed after the last tick finds the subject completed, and
    // ends in its own subscription
    return endAfter(
      subject.pipe(
        rxMap((x): Item => ({ ...x, p: at(x.p, [x.end ? 1 : 0, RANK]) })),
      ),
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
//
// `max-dup` is `max-sub` with `switchAll`'s own END repaired by READING
// THE OUTER TWICE: a second copy, compiled at the same position so its
// packets carry the same names, read only for its END. Where a
// subscription to the outer schedules nothing of its own -- no `defer`
// hop, no cold slot with an async tail, anywhere the outer reaches --
// both copies hear the same deliveries in the same call stacks, and the
// copy, subscribed AFTER the real one, ends in the outer's own END.
// Where it does schedule, the copy is subscribed FIRST: each source it
// registers takes the ordinal just below its real twin's, so fires just
// before it at the same tick, and its END comes one arrival early under
// the name the real END will have. A shared slot forbids FIRST -- the
// copy would connect it and take its burst -- so an outer that both
// schedules and reaches a share is left to the lanes, as under `max-sub`.
//
// A FIRST copy is not free: the arrivals its sources fire in carry no
// plain emit, so the timed run has more arrivals than the plain one, and
// copies NEST -- an outer holding a `switchAll` copies that one's copy
// too, so k stacked `switchAll`s over a scheduling outer run 2^k copies.
export type SubscribeRule =
  | "last-seen"
  | "outer-packet"
  | "lanes-only"
  | "max-clock"
  | "max-key"
  | "max-tick"
  | "max-sub"
  | "max-left"
  | "max-dup"
  | "echo"
  | "markers";
type FreeRule =
  "max-clock" | "max-key" | "max-tick" | "max-sub" | "max-left" | "max-dup";

type N =
  | { k: "start"; n: number; outer: Pkt; at: number; endLane: boolean }
  | { k: "item"; n: number; x: Item }
  | { k: "outerEnd"; p: Pkt }
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
  // the outer's END, read off a second copy, and where it subscribes
  outerEnd: { copy: Observable<Item>; first: boolean } | undefined,
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
        ? ((ends: Observable<N>) =>
            outerEnd?.first
              ? merge(ends, lanes.pipe(switchAll()))
              : merge(lanes.pipe(switchAll()), ends))(
            (outerEnd?.copy ?? EMPTY).pipe(
              filter((x) => x.end === true),
              rxMap((x): N => ({ k: "outerEnd", p: x.p })),
            ),
          )
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
                      st.seen &&
                      (rule === "max-sub" ||
                        rule === "max-left" ||
                        rule === "max-dup")
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
          case "outerEnd":
            // no lane subscribes on it, so it only moves the last instant
            return { ...st, last: m.p, seen: true, lastAt: clock(), out: null };
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
  outerEnd?: { copy: Observable<Item>; first: boolean },
): Observable<Item> =>
  rule === "last-seen" || rule === "outer-packet" || rule === "lanes-only"
    ? flattenConnect(rule, how, limit, pos, outer, compileInner)
    : rule === "echo"
      ? flattenEcho(how, limit, pos, outer, compileInner)
      : rule === "markers"
        ? flattenMarked(how, limit, pos, outer, compileInner)
        : flattenFree(
            rule,
            how,
            limit,
            pos,
            outer,
            compileInner,
            clock,
            outerEnd,
          );

// ---------------------------------------------------------------
// Reporting flatteners: what a flattener former would have to emit for
// the translation to need no `connect` of its own.
// ---------------------------------------------------------------

const flattener =
  <T>(how: "merge" | "switch" | "exhaust", limit: number | undefined) =>
  (o: Observable<Observable<T>>): Observable<T> =>
    how === "merge"
      ? o.pipe(mergeAll(limit ?? Infinity))
      : how === "switch"
        ? o.pipe(switchAll())
        : o.pipe(exhaustAll());

// AN ECHOING FLATTENER: every outer element's `s` leaves AS IT ARRIVES,
// before its lane (if it has one) is handled. An element with no lane is
// only echoed, which is how the outer's END reaches the output without
// being subscribed. Generic, and ordinary rxjs.
type Echoed<S, T> = { k: "echo"; s: S } | { k: "value"; t: T };
const echoFlatten =
  <S, T>(how: "merge" | "switch" | "exhaust", limit: number | undefined) =>
  (outer: Observable<{ s: S; lane: Observable<T> | null }>) =>
    outer.pipe(
      connect((sh) =>
        merge(
          sh.pipe(rxMap((x): Echoed<S, T> => ({ k: "echo", s: x.s }))),
          sh.pipe(
            filter((x): x is { s: S; lane: Observable<T> } => x.lane !== null),
            rxMap((x) => x.lane),
            flattener<T>(how, limit),
            rxMap((t): Echoed<S, T> => ({ k: "value", t })),
          ),
        ),
      ),
    );

// A MARKING FLATTENER: a Start as each lane is actually subscribed, a
// Done as it completes, an OuterDone as the outer does.
type Marked<T> =
  { m: "start" } | { m: "value"; t: T } | { m: "done" } | { m: "outerDone" };
const markFlatten =
  <T>(how: "merge" | "switch" | "exhaust", limit: number | undefined) =>
  (outer: Observable<Observable<T>>): Observable<Marked<T>> =>
    outer.pipe(
      connect((sh) =>
        merge(
          sh.pipe(
            rxMap((lane) =>
              concat(
                rxDefer(() => rxOf<Marked<T>>({ m: "start" })),
                lane.pipe(rxMap((t): Marked<T> => ({ m: "value", t }))),
                rxOf<Marked<T>>({ m: "done" }),
              ),
            ),
            flattener<Marked<T>>(how, limit),
          ),
          sh.pipe(ignoreElements(), endWith<Marked<T>>({ m: "outerDone" })),
        ),
      ),
    );

// the outer's values as numbered lanes, each opening with its outer
// packet
const numbered = (
  outer: Observable<Item>,
  compileInner: (o: ObsVal) => Observable<Item>,
) =>
  outer.pipe(
    rxScan(
      (acc: { n: number; x: Item }, x: Item) => ({
        n: x.end ? acc.n : acc.n + 1,
        x,
      }),
      { n: -1, x: end(HOLE) },
    ),
    rxMap(({ n, x }) => ({
      p: x.p,
      lane: x.end
        ? null
        : concat(
            rxOf<M>({ k: "start", n, outer: x.p }),
            compileInner(x.v as ObsVal).pipe(
              rxMap((y): M => ({ k: "item", n, x: y })),
            ),
          ),
    })),
  );

// `echo`: the outer's packets echoed as beats, read by `last-seen`
const flattenEcho = (
  how: "merge" | "switch" | "exhaust",
  limit: number | undefined,
  pos: string,
  outer: Observable<Item>,
  compileInner: (o: ObsVal) => Observable<Item>,
): Observable<Item> =>
  readLastSeen(
    pos,
    false,
    numbered(outer, compileInner).pipe(
      rxMap(({ p, lane }) => ({ s: p, lane })),
      echoFlatten<Pkt, M>(how, limit),
      rxMap((e): M => (e.k === "echo" ? { k: "beat", p: e.s } : e.t)),
    ),
  );

// `markers`: a queued lane is read as subscribed in the END of the lane
// whose Done it follows, any other lane in its outer packet; the
// OuterDone names nothing, so the flattener's END is the last lane
// instant
type MarkSt = {
  last: Pkt;
  afterDone: boolean;
  sps: Record<number, Pkt>;
  out: Item | null;
};
const flattenMarked = (
  how: "merge" | "switch" | "exhaust",
  limit: number | undefined,
  pos: string,
  outer: Observable<Item>,
  compileInner: (o: ObsVal) => Observable<Item>,
): Observable<Item> =>
  concat(
    numbered(outer, compileInner).pipe(
      filter((x): x is { p: Pkt; lane: Observable<M> } => x.lane !== null),
      rxMap((x) => x.lane),
      markFlatten<M>(how, limit),
    ),
    rxOf<Marked<M> | { m: "fin" }>({ m: "fin" }),
  ).pipe(
    rxScan(
      (st: MarkSt, e: Marked<M> | { m: "fin" }): MarkSt => {
        switch (e.m) {
          case "start":
          case "outerDone":
            return { ...st, out: null };
          case "done":
            return { ...st, afterDone: true, out: null };
          case "fin":
            return { ...st, out: end(st.last) };
          case "value": {
            const m = e.t;
            if (m.k === "start") {
              const queued = how === "merge" && limit !== undefined;
              const sp = queued && st.afterDone ? st.last : m.outer;
              return {
                ...st,
                afterDone: false,
                sps: { ...st.sps, [m.n]: sp },
                out: null,
              };
            }
            if (m.k !== "item") return { ...st, out: null };
            const p = subst(`${pos}#${m.n}`, st.sps[m.n], m.x.p);
            return {
              ...st,
              last: p,
              afterDone: false,
              out: m.x.end ? null : { ...m.x, p },
            };
          }
        }
      },
      { last: HOLE, afterDone: false, sps: {}, out: null },
    ),
    filter((st) => st.out !== null),
    rxMap((st) => st.out as Item),
  );

// the slots a second copy has to reckon with: a cold with an async tail
// registers a source every time it is subscribed, and a share connects
// on its first subscriber
type SlotKinds = {
  scheduling: ReadonlySet<number>;
  shared: ReadonlySet<number>;
};
export const slotKinds = (testCase: TestCase): SlotKinds => ({
  scheduling: new Set(
    testCase.slots.flatMap((sl, j) =>
      sl.type === "scripted" &&
      sl.input.type === "cold" &&
      sl.input.async.length > 0
        ? [j]
        : [],
    ),
  ),
  shared: new Set(
    testCase.slots.flatMap((sl, j) => (sl.type === "scripted" ? [] : [j])),
  ),
});

// WHERE A SECOND COPY OF A TERM GOES, read off what subscribing it
// reaches. A subscription schedules on a `defer` hop or a scheduling
// slot; a shared slot never does, since it connects once. A stream
// VALUE is subscribed only by a flattener whose output is that stream's
// element type, so a stream the term carries -- written in it, or closed
// over in its environment -- counts only once the term holds such a
// flattener, and then what its body reaches counts too, to a fixpoint.
// The lanes a `switchAll` subscribes are not its outer's business.
type Copy = "after" | "first" | "none";
const copyOf = (exp: Closed, env: Val[], kinds: SlotKinds): Copy => {
  const found = { schedules: false, shares: false };
  const flattened = new Set<string>();
  const carried: { elem: string; body: unknown }[] = [];
  const seen = new Set<object>();
  // what subscribing `x` reaches, streams it carries set aside
  const subscribe = (x: unknown): void => {
    if (typeof x !== "object" || x === null || seen.has(x)) return;
    seen.add(x);
    const o = x as { type?: unknown; index?: unknown; ty?: unknown };
    if (o.type === "strmT") {
      const e = (x as { exp: Closed }).exp;
      carried.push({ elem: JSON.stringify(e.ty), body: e });
      return;
    }
    if (
      o.type === "mergeAll" ||
      o.type === "switchAll" ||
      o.type === "exhaustAll"
    )
      flattened.add(JSON.stringify(o.ty));
    if (o.type === "defer") found.schedules = true;
    if (o.type === "input" && typeof o.index === "number") {
      if (kinds.scheduling.has(o.index)) found.schedules = true;
      if (kinds.shared.has(o.index)) found.shares = true;
    }
    Object.values(x).forEach(subscribe);
  };
  // the streams a value closes over, set aside the same way
  const carry = (v: unknown): void => {
    if (typeof v !== "object" || v === null || seen.has(v)) return;
    seen.add(v);
    if ("exp" in v && "env" in v) {
      const o = v as ObsVal;
      carried.push({ elem: JSON.stringify(o.exp.ty), body: o.exp });
      carry(o.env);
      return;
    }
    Object.values(v).forEach(carry);
  };
  subscribe(exp);
  carry(env);
  const drain = (): void => {
    const next = carried.findIndex((c) => flattened.has(c.elem));
    if (next < 0) return;
    const [c] = carried.splice(next, 1);
    subscribe(c.body);
    drain();
  };
  drain();
  return !found.schedules ? "after" : !found.shares ? "first" : "none";
};

// the `switchAll` nodes the program text holds, by where their outer's
// second copy goes
export const switchOuters = (testCase: TestCase): Record<Copy, number> => {
  const kinds = slotKinds(testCase);
  const found: Record<Copy, number> = { after: 0, first: 0, none: 0 };
  const seen = new Set<object>();
  const go = (y: unknown): void => {
    if (typeof y !== "object" || y === null || seen.has(y)) return;
    seen.add(y);
    const o = y as { type?: unknown; src?: unknown };
    if (o.type === "switchAll")
      found[copyOf((o as { src: Closed }).src, [], kinds)]++;
    Object.values(y).forEach(go);
  };
  go(testCase.exp);
  testCase.slots.forEach((sl) => {
    if (sl.type !== "scripted") go(sl.def);
  });
  return found;
};

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
      return readLastSeen(
        pos,
        rule === "outer-packet",
        merge(beats, lanes.pipe(flattener<M>(how, limit))),
      );
    }),
  );

// a lane is subscribed in the last instant seen before its START: a
// beat's, or a lane item's
const readLastSeen = (
  pos: string,
  outerPacket: boolean,
  ms: Observable<M>,
): Observable<Item> =>
  concat(ms, rxOf<M>({ k: "fin" })).pipe(
    rxScan(
      (st: FlatSt, m: M): FlatSt => {
        switch (m.k) {
          case "beat":
            return { ...st, last: m.p, out: null };
          case "start":
            return {
              ...st,
              sps: { ...st.sps, [m.n]: outerPacket ? m.outer : st.last },
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

// ---------------------------------------------------------------
// The translation.
// ---------------------------------------------------------------

// `pos` is the node's position within its frame: a flattener's segment
// and a defer's hop are named by it, so two in one frame never collide.
const compile = (
  rule: SubscribeRule,
  clock: () => number,
  kinds: SlotKinds,
  exp: Closed,
  env: Val[],
  driver: PlainDriver,
  slots: Observable<Item>[],
  pos: string,
): Observable<Item> => {
  const recur = (e: Closed, sub: string) =>
    compile(rule, clock, kinds, e, env, driver, slots, `${pos}.${sub}`);
  const inner = (o: ObsVal) =>
    compile(rule, clock, kinds, o.exp, o.env, driver, slots, "");
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
      // fills the quota is cut at its nth value, before any END, and
      // completes in that value's instant, so the END is appended there;
      // one that does not passes its END as an item within the quota.
      const count = evalWith(exp.count, env);
      if (typeof count !== "bigint")
        throw new Error("take count did not evaluate to a nat");
      return count === 0n
        ? rxOf(end(HOLE))
        : endAfter(recur(exp.src, "s").pipe(rxTake(Number(count))));
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
        ((copy: Copy) =>
          rule === "max-dup" && copy !== "none"
            ? { copy: recur(exp.src, "s"), first: copy === "first" }
            : undefined)(copyOf(exp.src, env, kinds)),
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
          kinds,
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
  // arrivals to deliver: a translation that registers sources of its
  // own spends more than the plain run does
  fuel: number = testCase.fuel,
  // stop once this many values are out
  enough: number = Infinity,
): TimedEmit[] => {
  const driver = createPlainDriver(testCase.slots.length);
  // the harness's own count, read only by `max-clock`
  let arrival = 0;
  const clock = () => arrival;
  const kinds = slotKinds(testCase);
  const slots = testCase.slots.reduce<Observable<Item>[]>(
    (prefix, slot, j) => [
      ...prefix,
      slot.type === "scripted"
        ? timedInput(driver, slot.input, j)
        : // one subscribed after the share completed ends in its own
          // subscription
          endAfter(
            compile(rule, clock, kinds, slot.def, [], driver, prefix, "").pipe(
              rxMap(onPkt((p) => closeShare(j, p))),
              rxShare({
                resetOnRefCountZero: false,
                resetOnComplete: false,
                resetOnError: false,
              }),
              // a fan-out, one item at a time
              rxMap(onPkt((p) => at(p, [RANK]))),
            ),
          ),
    ],
    [],
  );
  const out: TimedEmit[] = [];
  const sub = compile(
    rule,
    clock,
    kinds,
    testCase.exp,
    [],
    driver,
    slots,
    "",
  ).subscribe((x) => {
    if (!x.end) {
      const r = resolve(
        x.p,
        rule === "max-sub" || rule === "max-dup"
          ? "sub"
          : rule === "max-left"
            ? "left"
            : "key",
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
  for (let spent = 0; spent < fuel && out.length < enough; spent++) {
    arrival++;
    if (!driver.deliverNextArrival()) break;
  }
  sub.unsubscribe();
  return out;
};
