import { Observable, Subject, of, toArray } from "rxjs";
import { Elem, FlatOp, Opt, flatten } from "./flatten.js";
import { genTestCases } from "./generator.js";
import { evaluatePlainArrivals } from "./plain-eval.js";
import { showVal } from "./exp.js";

// THE OLD FLATTENERS AGAINST THEIR ENCODING OVER `flatten`. Every
// generated program is run plain twice -- `mergeAll`/`switchAll`/
// `exhaustAll` as rxjs's own operators, then as `flatten` over echo-less
// elements -- and the two must agree on every value AND the driver
// arrival it left in, which is the call stack it was emitted in. The
// multicast `flatten` adds is the thing under test: it moves when the
// outer is subscribed, and so what a source registers first.
//
//   node flatten-diff.js [seeds] [--operator op]   the sweep (default 500)
//   node flatten-diff.js --selftest                 what an echo does

const show = (xs: { value: unknown; arrival: number }[]) =>
  xs.map((x) => `${showVal(x.value as never)}@${x.arrival}`).join(" ");

const sweep = (seeds: number, operator?: string) =>
  Array.from({ length: seeds }, (_, i) => genTestCases(`s${i}`, operator))
    .flatMap((cases, i) =>
      cases.map((testCase, c) => ({ testCase, name: `s${i} case ${c}` })),
    )
    .reduce(
      (t, { testCase, name }) => {
        const native = evaluatePlainArrivals(testCase, "native");
        const echo = evaluatePlainArrivals(testCase, "echo");
        const same = show(native) === show(echo);
        if (!same)
          console.log(
            `DIFFER ${name}\n  native ${show(native)}\n  echo   ${show(echo)}`,
          );
        return {
          cases: t.cases + 1,
          differ: t.differ + (same ? 0 : 1),
          loadBearing:
            t.loadBearing +
            (new Set(native.map((x) => x.arrival)).size > 1 ? 1 : 0),
        };
      },
      { cases: 0, differ: 0, loadBearing: 0 },
    );

// ---------------------------------------------------------------
// What an echo does, on hand-driven Subjects.
// ---------------------------------------------------------------

const el = <T>(echo: Opt<T>, lane: Opt<Observable<T>>): Elem<T> => ({
  echo,
  lane,
});

// drive `outer` by `script` and collect what `flatten(op)` emits
const drive = (
  op: FlatOp,
  script: (outer: Subject<Elem<string>>) => void,
): string[] => {
  const outer = new Subject<Elem<string>>();
  const out: string[] = [];
  const sub = flatten<string>(op)(outer)
    .pipe(toArray())
    .subscribe((xs) => {
      out.push(...xs, "|");
    });
  script(outer);
  sub.unsubscribe();
  return out;
};

const expect = (name: string, got: string[], want: string[]) => {
  const ok = JSON.stringify(got) === JSON.stringify(want);
  console.log(`${ok ? "ok      " : "WRONG   "} ${name}: ${got.join(" ")}`);
  return ok;
};

const selftest = (): boolean => {
  const results = [
    // the echo leaves before its own lane's synchronous values
    expect(
      "echo before its lane",
      drive({ how: "merge" }, (o) => {
        o.next(el(["e"], [of("a", "b")]));
        o.complete();
      }),
      ["e", "a", "b", "|"],
    ),
    // an echo-only element is a filter: it cancels nothing under switch
    ((live) =>
      expect(
        "switch: echo-only cancels nothing",
        drive({ how: "switch" }, (o) => {
          o.next(el([], [live]));
          live.next("a");
          o.next(el(["e"], []));
          live.next("b");
          o.complete();
          live.complete();
        }),
        ["a", "e", "b", "|"],
      ))(new Subject<string>()),
    // ...is not dropped under exhaust, however busy it is
    ((live) =>
      expect(
        "exhaust: echo-only is not dropped",
        drive({ how: "exhaust" }, (o) => {
          o.next(el([], [live]));
          o.next(el(["e"], [of("dropped")]));
          live.next("a");
          o.complete();
          live.complete();
        }),
        ["e", "a", "|"],
      ))(new Subject<string>()),
    // ...and takes no slot under a limit: it leaves while the lane waits
    ((live) =>
      expect(
        "merge(1): echo-only is not queued",
        drive({ how: "merge", limit: 1 }, (o) => {
          o.next(el([], [live]));
          o.next(el(["e1"], [of("queued")]));
          o.next(el(["e2"], []));
          live.next("a");
          o.complete();
          live.complete();
        }),
        ["e1", "e2", "a", "queued", "|"],
      ))(new Subject<string>()),
    // the flattener completes only when the outer and every lane have
    ((live) =>
      expect(
        "completion waits for the lanes",
        drive({ how: "merge" }, (o) => {
          o.next(el(["e"], [live]));
          o.complete();
          live.next("a");
          live.complete();
        }),
        ["e", "a", "|"],
      ))(new Subject<string>()),
  ];
  return results.every((b) => b);
};

const main = () => {
  const argv = process.argv.slice(2);
  if (argv[0] === "--selftest") {
    if (!selftest()) {
      console.log("SELFTEST FAILED");
      process.exit(1);
    }
    console.log("selftest ok: an echo leads its lane and no policy sees it");
    return;
  }
  const t = sweep(
    Number(argv[0] ?? 500),
    argv.includes("--operator")
      ? argv[argv.indexOf("--operator") + 1]
      : undefined,
  );
  console.log(JSON.stringify(t));
  if (t.differ > 0) process.exit(1);
};

main();
