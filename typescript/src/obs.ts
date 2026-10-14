import {
  EMPTY,
  NEVER,
  Observable,
  SchedulerLike,
  concat,
  connect,
  defer,
  exhaustMap,
  from,
  map,
  mergeMap,
  of,
  repeat,
  scan,
  switchMap,
  takeWhile,
  timer,
} from "rxjs";

// THE TREE, AS AGDA PRINTS IT (`quickcheck.Code.showCode`), compiled onto
// real rxjs.  Every node is the rxjs operator of the same name; nothing
// here is an implementation of an operator.  Variables are positions
// counted from the innermost binder.

// `quickcheck.Ty`'s values: unit is null, a pair an array, a sum a
// one-key object.
export type Value =
  null | boolean | number | Value[] | { l: Value } | { r: Value };

export type Tm =
  | ["var", number]
  | ["unit"]
  | ["bool", boolean]
  | ["if", Tm, Tm, Tm]
  | ["nat", number]
  | ["plus", Tm, Tm]
  | ["less", Tm, Tm]
  | ["pair", Tm, Tm]
  | ["fst", Tm]
  | ["snd", Tm]
  | ["inl", Tm]
  | ["inr", Tm]
  | ["case", Tm, Tm, Tm]
  | ["nil"]
  | ["cons", Tm, Tm];

export type FlatOp = ["merge"] | ["merge", number] | ["switch"] | ["exhaust"];

export type Code =
  | ["cold", [number, Value[]][], boolean, boolean]
  | ["empty"]
  | ["of", Tm[]]
  | ["map", Tm, Code]
  | ["scan", Tm, Tm, Code]
  | ["takeWhile", boolean, Tm, Code]
  | ["flatMap", FlatOp, Code, Code]
  | ["connect", Code, Code]
  | ["connected", number]
  | ["mu", Code]
  | ["var", number]
  | ["defer", Code];

const nat = (v: Value): number => v as number;
const pair = (v: Value): Value[] => v as Value[];

export const evalTm = (tm: Tm, th: Value[]): Value => {
  switch (tm[0]) {
    case "var":
      return th[tm[1]];
    case "unit":
      return null;
    case "bool":
      return tm[1];
    case "if":
      return evalTm(tm[1], th) === true ? evalTm(tm[2], th) : evalTm(tm[3], th);
    case "nat":
      return tm[1];
    case "plus":
      return nat(evalTm(tm[1], th)) + nat(evalTm(tm[2], th));
    case "less":
      return nat(evalTm(tm[1], th)) < nat(evalTm(tm[2], th));
    case "pair":
      return [evalTm(tm[1], th), evalTm(tm[2], th)];
    case "fst":
      return pair(evalTm(tm[1], th))[0];
    case "snd":
      return pair(evalTm(tm[1], th))[1];
    case "inl":
      return { l: evalTm(tm[1], th) };
    case "inr":
      return { r: evalTm(tm[1], th) };
    case "case": {
      const e = evalTm(tm[1], th) as { l: Value } | { r: Value };
      return "l" in e
        ? evalTm(tm[2], [e.l, ...th])
        : evalTm(tm[3], [e.r, ...th]);
    }
    case "nil":
      return [];
    case "cons":
      return [evalTm(tm[1], th), ...pair(evalTm(tm[2], th))];
  }
};

// A scripted cold: frames at offsets from subscription.  Frame 0 is
// synchronous; each later one is a timer set where the frame before it
// ends, as `operation.Observable.fromTimeline` plays it.
// One play of the frames. A replay starts a tick after the last frame,
// as `quickcheck.Code.scriptML` restarts, so it is never synchronous.
const play = (
  sch: SchedulerLike,
  frames: [number, Value[]][],
  replay: boolean,
): Observable<Value> =>
  concat(
    ...frames.map(([t, xs], i) => {
      const gap = i === 0 ? (replay ? t + 1 : t) : t - frames[i - 1][0];
      return i === 0 && !replay && t === 0
        ? from(xs)
        : timer(Math.max(gap, 0), sch).pipe(mergeMap(() => from(xs)));
    }),
  );

const cold = (
  sch: SchedulerLike,
  frames: [number, Value[]][],
  completes: boolean,
  loops: boolean,
): Observable<Value> =>
  loops
    ? frames.length === 0
      ? NEVER
      : concat(play(sch, frames, false), play(sch, frames, true).pipe(repeat()))
    : concat(play(sch, frames, false), completes ? EMPTY : NEVER);

const flatMapOf = (
  op: FlatOp,
  lane: (a: Value) => Observable<Value>,
): ((s: Observable<Value>) => Observable<Value>) => {
  switch (op[0]) {
    case "merge":
      return op.length === 2 ? mergeMap(lane, op[1]) : mergeMap(lane);
    case "switch":
      return switchMap(lane);
    case "exhaust":
      return exhaustMap(lane);
  }
};

// The recursion variables, unfolded at most `n` more times; the last
// unfolding is a cold that never emits, as `quickcheck.Code.knot` cuts it.
type Rec = () => Observable<Value>;

type Scope = {
  sch: SchedulerLike;
  n: number;
  g: Rec[]; // bound by a `mu`, not yet past a `defer`
  d: Rec[]; // usable
  th: Value[]; // the elements of the enclosing lanes
  gamma: Observable<Value>[]; // the `connect` handles
};

const knot =
  (s: Scope, c: Code): Rec =>
  () =>
    s.n === 0
      ? NEVER
      : compile(
          { ...s, n: s.n - 1, g: [knot({ ...s, n: s.n - 1 }, c), ...s.g] },
          c,
        );

export const compile = (s: Scope, code: Code): Observable<Value> => {
  switch (code[0]) {
    case "cold":
      return cold(s.sch, code[1], code[2], code[3]);
    case "empty":
      return EMPTY;
    case "of":
      return of(...code[1].map((t) => evalTm(t, s.th)));
    case "map": {
      const f = code[1];
      return compile(s, code[2]).pipe(map((a) => evalTm(f, [a, ...s.th])));
    }
    case "scan": {
      const f = code[1];
      return compile(s, code[3]).pipe(
        scan(
          (acc: Value, a: Value) => evalTm(f, [a, acc, ...s.th]),
          evalTm(code[2], s.th),
        ),
      );
    }
    case "takeWhile": {
      const [, inclusive, p, src] = code;
      return compile(s, src).pipe(
        takeWhile((a) => evalTm(p, [a, ...s.th]) === true, inclusive),
      );
    }
    case "flatMap": {
      const [, op, l, src] = code;
      return compile(s, src).pipe(
        flatMapOf(op, (a) => compile({ ...s, th: [a, ...s.th] }, l)),
      );
    }
    case "connect": {
      const b = code[2];
      return compile(s, code[1]).pipe(
        connect((sh) => compile({ ...s, gamma: [sh, ...s.gamma] }, b)),
      );
    }
    case "connected":
      return s.gamma[code[1]];
    case "mu":
      return compile({ ...s, g: [knot(s, code[1]), ...s.g] }, code[1]);
    case "var":
      return s.d[code[1]]();
    case "defer": {
      const c = code[1];
      return defer(() => compile({ ...s, g: [], d: [...s.g, ...s.d] }, c));
    }
  }
};

export const compileProg = (
  sch: SchedulerLike,
  n: number,
  code: Code,
): Observable<Value> =>
  compile({ sch, n, g: [], d: [], th: [], gamma: [] }, code);
