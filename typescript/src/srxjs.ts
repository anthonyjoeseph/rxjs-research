import {
  EMPTY,
  NEVER,
  Observable,
  SchedulerLike,
  connect,
  defer,
  from,
  map,
  merge,
  mergeMap,
  of,
  scan,
  takeWhile,
} from "rxjs";

import { Code, FlatOp, Value, cold, evalTm, flatMapOf } from "./obs.js";

// SRXJS IN RXJS: `simultaneous.SObs.Elaborate`, former for former.  Every
// node is the rxjs operator the Agda names; the logic is plain functions
// over plain data, threaded by `scan`.  The Agda's renamings are its
// bookkeeping for de Bruijn handles; here a handle is a closure.

// A name is an object compared by identity, minted per subscription.
type Name = object;

type Mark =
  | "begin"
  | "over"
  | "stop"
  | "outerOpen"
  | "outerClose"
  | "laneStart"
  | "laneDone"
  | "burstEnd"
  | "outerDone"
  | "subscribed"
  | "completed";

type InstEvent<A> = { value: A } | { mark: Mark };

export type IE<A> = { event: InstEvent<A>; instant: Name };

type Obs<A> = Observable<A>;

// The subscribe burst's name, as the Agda's `root`.
const ROOT: Name = {};

const mint: Obs<Name> = defer(() => of({}));

const valueIE = <A>(a: A, n: Name): IE<A> => ({
  event: { value: a },
  instant: n,
});
const markIE = <A>(m: Mark, n: Name): IE<A> => ({
  event: { mark: m },
  instant: n,
});
const marked = <A>(m: Mark): IE<A> => markIE(m, ROOT);

const isMark = <A>(x: IE<A>, m: Mark): boolean =>
  "mark" in x.event && x.event.mark === m;

const valuesOf = <A>(x: IE<A>): A[] =>
  "value" in x.event ? [x.event.value] : [];

const concatS = <X>(s: Obs<X>, t: Obs<X>): Obs<X> =>
  of(true, false).pipe(mergeMap((b) => (b ? s : t), 1));

const each =
  <X, Y>(f: (x: X) => Y[]) =>
  (s: Obs<X>): Obs<Y> =>
    s.pipe(mergeMap((x) => from(f(x))));

const snd = <X, Y>([, y]: [X, Y]): Y => y;

// ---------------------------------------------------------------------
// The leaves and the one-to-one formers

type Tag<A> = { val: A } | "cdone" | "tick";

const phase = <A>([late]: [boolean, Tag<A>], t: Tag<A>): [boolean, Tag<A>] => [
  late || t === "tick",
  t,
];

const render = <A>([late, t]: [boolean, Tag<A>]): Obs<IE<A>> => {
  if (typeof t === "object") {
    const a = t.val;
    return late
      ? mint.pipe(
          mergeMap((n) =>
            of(markIE<A>("begin", n), valueIE(a, n), markIE<A>("over", n)),
          ),
        )
      : of(valueIE(a, ROOT));
  }
  return late && t === "cdone"
    ? mint.pipe(map((n) => markIE<A>("begin", n)))
    : EMPTY;
};

const coldS = <A>(c: Obs<A>): Obs<IE<A>> =>
  merge(
    concatS<Tag<A>>(c.pipe(map((a) => ({ val: a }))), of<Tag<A>>("cdone")),
    of<Tag<A>>("tick"),
  ).pipe(
    scan(phase<A>, [false, "tick"] as [boolean, Tag<A>]),
    mergeMap(render<A>),
  );

const mapIE =
  <A, B>(f: (a: A) => B) =>
  (x: IE<A>): IE<B> =>
    "value" in x.event
      ? valueIE(f(x.event.value), x.instant)
      : markIE(x.event.mark, x.instant);

const scanIE =
  <A, B>(f: (b: B, a: A) => B) =>
  ([b]: [B, IE<B>], x: IE<A>): [B, IE<B>] => {
    if ("value" in x.event) {
      const b2 = f(b, x.event.value);
      return [b2, valueIE(b2, x.instant)];
    }
    return [b, markIE(x.event.mark, x.instant)];
  };

const passes =
  <A>(p: (a: A) => boolean) =>
  (x: IE<A>): boolean =>
    "value" in x.event ? p(x.event.value) : true;

// ---------------------------------------------------------------------
// flatMap

const opening = <A, B>(x: IE<A>): IE<B> =>
  "value" in x.event
    ? markIE("outerOpen", x.instant)
    : markIE(x.event.mark, x.instant);

const closing = <A, B>(x: IE<A>): IE<B>[] =>
  "value" in x.event ? [markIE("outerClose", x.instant)] : [];

const closer = <A, B>(o: Obs<IE<A>>): Obs<IE<B>> =>
  concatS(o.pipe(each(closing<A, B>)), of(marked<B>("outerDone")));

type Part = "lanePart" | "burstPart";

const piece = <B>(k: Part, i: number, h: Obs<IE<B>>): Obs<IE<B>> => {
  if (i === 0)
    return of(marked<B>(k === "lanePart" ? "laneStart" : "burstEnd"));
  if (i === 1) return h;
  if (i === 2 && k === "lanePart") return of(marked<B>("laneDone"));
  return EMPTY;
};

const framed = <B>(k: Part, h: Obs<IE<B>>): Obs<IE<B>> =>
  of(0, 1, 2).pipe(mergeMap((i) => piece(k, i, h), 1));

const laneS = <B>(x: Obs<IE<B>>): Obs<IE<B>> =>
  from<Part[]>(["lanePart", "burstPart"]).pipe(
    mergeMap((k) =>
      of(k).pipe(
        takeWhile((p) => p === "lanePart", false),
        mergeMap(() => x),
        connect((h) => framed(k, h)),
      ),
    ),
  );

type Flat = {
  active: number;
  queue: number;
  finished: boolean;
  bracket: boolean;
  handoff: boolean;
  popping: boolean;
  dead: boolean;
};

type Out<B> = [Flat, IE<B>[]];

const flat0: Flat = {
  active: 0,
  queue: 0,
  finished: false,
  bracket: false,
  handoff: false,
  popping: false,
  dead: false,
};

const arrive = (op: FlatOp, s: Flat): Flat => {
  if (op[0] === "merge" && op.length === 2)
    return s.active < op[1] ? s : { ...s, queue: s.queue + 1 };
  if (op[0] === "switch") return { ...s, active: 0 };
  return s;
};

const sub1 = (k: number): number => Math.max(k - 1, 0);

const stopUnless = <B>(ok: boolean, n: Name, s: Flat): Out<B> =>
  ok ? [s, []] : [s, [markIE("stop", n)]];

const verdict = <B>(n: Name, s: Flat): Out<B> =>
  s.queue !== 0
    ? [{ ...s, handoff: true }, []]
    : stopUnless(s.finished && s.active === 0, n, { ...s, handoff: false });

const settle = <B>(inBracket: boolean, n: Name, s: Flat): Out<B> =>
  inBracket ? [s, []] : verdict(n, s);

const burstOver = <B>(live: boolean, n: Name, s: Flat): Out<B> =>
  live ? [{ ...s, handoff: false }, [markIE("stop", n)]] : [s, []];

const onMark = <B>(op: FlatOp, s: Flat, m: Mark, n: Name): Out<B> => {
  switch (m) {
    case "outerOpen":
      return [arrive(op, { ...s, bracket: true }), []];
    case "outerClose":
      return [{ ...s, bracket: false }, []];
    case "laneStart":
      return [
        {
          ...s,
          active: s.active + 1,
          queue: s.popping ? sub1(s.queue) : s.queue,
          popping: false,
          dead: false,
        },
        [],
      ];
    case "laneDone":
      return settle(s.bracket, n, {
        ...s,
        active: sub1(s.active),
        popping: s.queue !== 0,
        dead: true,
      });
    case "burstEnd":
      return burstOver(s.handoff && !s.dead, n, s);
    case "outerDone":
      return stopUnless(
        s.bracket || s.handoff || (s.queue === 0 && s.active === 0),
        n,
        { ...s, finished: true },
      );
    case "stop":
      return stopUnless(s.bracket || s.handoff, n, s);
    default:
      return [s, [markIE(m, n)]];
  }
};

const react =
  <B>(op: FlatOp) =>
  ([s]: Out<B>, x: IE<B>): Out<B> =>
    "value" in x.event ? [s, [x]] : onMark(op, s, x.event.mark, x.instant);

type Branch = "outerB" | "laneB" | "closeB";

const combined = <A, B>(
  op: FlatOp,
  o: Obs<IE<A>>,
  r: Obs<IE<B>>,
  c: Obs<IE<B>>,
): Obs<IE<B>> =>
  from<Branch[]>(["outerB", "laneB", "closeB"]).pipe(
    mergeMap((b) =>
      b === "outerB" ? o.pipe(map(opening<A, B>)) : b === "laneB" ? r : c,
    ),
    scan(react<B>(op), [flat0, []] as Out<B>),
    each(snd<Flat, IE<B>[]>),
  );

// The outer is read first by the scan, then by the real flatMap, then by
// `closer`: the order the nested connects subscribe them in.
const flatMapS = <A, B>(
  op: FlatOp,
  g: (a: A) => Obs<IE<B>>,
  s: Obs<IE<A>>,
): Obs<IE<B>> =>
  s.pipe(
    connect((o) =>
      closer<A, B>(o).pipe(
        connect((c) =>
          o.pipe(
            each(valuesOf<A>),
            flatMapOf(op, (a: A) => laneS(g(a))),
            connect((r) => combined(op, o, r, c)),
          ),
        ),
      ),
    ),
  );

// ---------------------------------------------------------------------
// The elaboration, over `obs.Code`

type Rec = () => Obs<IE<Value>>;

type Scope = {
  sch: SchedulerLike;
  n: number;
  g: Rec[];
  d: Rec[];
  th: Value[];
  gamma: Obs<IE<Value>>[];
};

const knot =
  (s: Scope, c: Code): Rec =>
  () =>
    s.n === 0
      ? NEVER
      : elab(
          { ...s, n: s.n - 1, g: [knot({ ...s, n: s.n - 1 }, c), ...s.g] },
          c,
        );

const elab = (s: Scope, code: Code): Obs<IE<Value>> => {
  switch (code[0]) {
    case "cold":
      return coldS(cold(s.sch, code[1], code[2], code[3]));
    case "fresh":
      return coldS(defer(() => of<Value>({ name: {} })));
    case "empty":
      return EMPTY;
    case "of":
      return of(...code[1].map((t) => valueIE(evalTm(t, s.th), ROOT)));
    case "map": {
      const f = code[1];
      return elab(s, code[2]).pipe(
        map(mapIE((a: Value) => evalTm(f, [a, ...s.th]))),
      );
    }
    case "scan": {
      const f = code[1];
      return elab(s, code[3]).pipe(
        scan(
          scanIE((acc: Value, a: Value) => evalTm(f, [a, acc, ...s.th])),
          [evalTm(code[2], s.th), marked<Value>("begin")] as [Value, IE<Value>],
        ),
        map(snd<Value, IE<Value>>),
      );
    }
    case "takeWhile": {
      const [, inclusive, p, src] = code;
      return elab(s, src).pipe(
        takeWhile(
          passes((a: Value) => evalTm(p, [a, ...s.th]) === true),
          inclusive,
        ),
      );
    }
    case "flatMap": {
      const [, op, l, src] = code;
      return flatMapS(
        op,
        (a: Value) => elab({ ...s, th: [a, ...s.th] }, l),
        elab(s, src),
      );
    }
    case "connect": {
      const b = code[2];
      return elab(s, code[1]).pipe(
        connect((sh) => elab({ ...s, gamma: [sh, ...s.gamma] }, b)),
      );
    }
    case "connected":
      return s.gamma[code[1]];
    case "mu":
      return elab({ ...s, g: [knot(s, code[1]), ...s.g] }, code[1]);
    case "var":
      return s.d[code[1]]();
    case "defer": {
      const c = code[1];
      return defer(() => elab({ ...s, g: [], d: [...s.g, ...s.d] }, c));
    }
  }
};

// Every emit under the name of the last `begin` before it.
const restamp = <A>([n]: [Name, IE<A>], x: IE<A>): [Name, IE<A>] =>
  isMark(x, "begin") ? [x.instant, x] : [n, { ...x, instant: n }];

// The run, then the end of its subscribe burst, then its completion.
export const elaborate = (
  sch: SchedulerLike,
  n: number,
  code: Code,
): Obs<IE<Value>> =>
  concatS(
    merge(
      elab({ sch, n, g: [], d: [], th: [], gamma: [] }, code),
      of(marked<Value>("subscribed")),
    ),
    of(marked<Value>("completed")),
  ).pipe(
    scan(restamp<Value>, [ROOT, marked<Value>("begin")] as [Name, IE<Value>]),
    map(snd<Name, IE<Value>>),
  );

// ---------------------------------------------------------------------
// The batcher

type Batching<A> = { late: boolean; at: Name; held: A[]; routes: number };

type Step<A> = [Batching<A>, IE<A[]>[]];

const release = <A>(b: Batching<A>): IE<A[]>[] =>
  b.held.length === 0 ? [] : [valueIE(b.held, b.at)];

const now = <A>(b: Batching<A>): Step<A> => [
  { ...b, held: [], routes: 0 },
  release(b),
];

const onBegin = <A>(n: Name, b: Batching<A>): Step<A> =>
  n === b.at
    ? [{ ...b, routes: b.routes + 1 }, []]
    : [{ ...b, at: n, held: [], routes: 1 }, release(b)];

const onStop = <A>(b: Batching<A>): Step<A> =>
  sub1(b.routes) === 0 ? now(b) : [{ ...b, routes: b.routes - 1 }, []];

const marking = <A>(
  late: boolean,
  m: Mark,
  n: Name,
  b: Batching<A>,
): Step<A> => {
  if (m === "subscribed") return now({ ...b, late: true });
  if (m === "completed") return now(b);
  if (!late) return [b, []];
  if (m === "begin") return onBegin(n, b);
  if (m === "over") return now(b);
  if (m === "stop") return onStop(b);
  return [b, []];
};

const bstep = <A>([b]: Step<A>, x: IE<A>): Step<A> =>
  "value" in x.event
    ? [{ ...b, held: [...b.held, x.event.value] }, []]
    : marking(b.late, x.event.mark, x.instant, b);

// The subscribe burst is one batch, released when it is over; after it,
// an instant's batch is released when its routes are.
export const batchSimultaneous = <A>(s: Obs<IE<A>>): Obs<IE<A[]>> =>
  s.pipe(
    scan(bstep<A>, [
      { late: false, at: ROOT, held: [], routes: 0 },
      [],
    ] as Step<A>),
    each(snd<Batching<A>, IE<A[]>[]>),
  );
