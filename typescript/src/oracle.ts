import { spawnSync } from "node:child_process";
import {
  VirtualTimeScheduler,
  lastValueFrom,
  map,
  materialize,
  takeUntil,
  timer,
  toArray,
} from "rxjs";
import { Code, Value, compileProg } from "./obs.js";

// THE ORACLE: every generated program, run in real rxjs and compared with
// what the three Agda engines make of it.  Agda generates and prints
// (`quickcheck.Oracle-CLI`); this side only replays.  Same unfolding
// budget as the CLI, so both sides run the same finite tree.
//
//   oracle [COUNT] [FROM]

const UNFOLD = 3;

type Event = { tick: number } | { val: Value };
type End = "completed" | "silent" | "cut";
type Trace = { events: Event[]; end: End };
type Row = {
  seed: number;
  prog: Code;
  denote: Trace;
  pure: Trace;
  machine: Trace;
};

const bin = process.env.AGDA_CLI_BIN ?? "../agda-impl/_cli/Oracle-CLI";
const timeoutMs = Number(process.env.ORACLE_CASE_TIMEOUT_MS ?? 10000);

// Time is the virtual scheduler's frame; a tick opens each run of values
// at one time, as the Agda traces print it.
const rxjsTrace = async (prog: Code): Promise<Trace> => {
  const sch = new VirtualTimeScheduler();
  const done = lastValueFrom(
    compileProg(sch, UNFOLD, prog).pipe(
      materialize(),
      map((n) => ({ t: sch.now(), n })),
      takeUntil(timer(Number.MAX_SAFE_INTEGER, sch)),
      toArray(),
    ),
  );
  sch.flush();
  const log = await done;
  const vals = log.flatMap(({ t, n }) =>
    n.kind === "N" ? [{ t, v: n.value as Value }] : [],
  );
  const events = vals.flatMap(({ t, v }, i): Event[] =>
    i === 0 || vals[i - 1].t !== t ? [{ tick: t }, { val: v }] : [{ val: v }],
  );
  return {
    events,
    end: log.some(({ n }) => n.kind === "C") ? "completed" : "silent",
  };
};

const same = (a: Event, b: Event): boolean =>
  JSON.stringify(a) === JSON.stringify(b);
const prefix = (xs: Event[], ys: Event[]): boolean =>
  xs.length <= ys.length && xs.every((x, i) => same(x, ys[i]));

// `quickcheck.Quickcheck.agrees`: a trace the step budget cut only has to
// be a prefix of the other.
const agrees = (a: Trace, b: Trace): boolean =>
  a.end === "cut"
    ? prefix(a.events, b.events)
    : b.end === "cut"
      ? prefix(b.events, a.events)
      : a.end === b.end &&
        prefix(a.events, b.events) &&
        prefix(b.events, a.events);

const cli = (args: string[]): { out: string; failed?: string } => {
  const r = spawnSync(bin, args, {
    encoding: "utf8",
    timeout: timeoutMs,
    maxBuffer: 1 << 28,
  });
  return r.error !== undefined
    ? { out: r.stdout ?? "", failed: String(r.error) }
    : r.status !== 0
      ? {
          out: r.stdout ?? "",
          failed: `exit ${r.status}: ${r.stderr.trim().split("\n")[0]}`,
        }
      : { out: r.stdout };
};

const show = (t: Trace): string => JSON.stringify(t);

const check = async (row: Row): Promise<string[]> => {
  const rx = await rxjsTrace(row.prog);
  const io = cli(["io", String(row.seed)]);
  const ioTrace: Trace | undefined =
    io.failed === undefined ? (JSON.parse(io.out) as Trace) : undefined;
  const bad = [
    ...(agrees(row.denote, rx) ? [] : [`denotation ${show(row.denote)}`]),
    ...(agrees(row.pure, rx) ? [] : [`pure       ${show(row.pure)}`]),
    ...(agrees(row.machine, rx) ? [] : [`machine    ${show(row.machine)}`]),
    ...(ioTrace === undefined
      ? [`io         ${io.failed}`]
      : agrees(ioTrace, rx)
        ? []
        : [`io         ${show(ioTrace)}`]),
    // the QUICKCHECK leg: the two pure engines, against each other
    ...(agrees(row.denote, row.pure) ? [] : ["(denotation and pure disagree)"]),
  ];
  return bad.length === 0
    ? []
    : [...bad, `rxjs       ${show(rx)}`].map((l) => `  ${l}`);
};

const main = async (): Promise<void> => {
  const count = Number(process.argv[2] ?? 1000);
  const start = Number(process.argv[3] ?? 0);
  const listing = cli(["prog", String(start), String(count)]);
  if (listing.failed !== undefined)
    throw new Error(`Oracle-CLI prog: ${listing.failed}`);
  const rows = listing.out
    .split("\n")
    .filter((l) => l.trim().length > 0)
    .map((l) => JSON.parse(l) as Row);
  const verdicts = await Promise.all(
    rows.map(async (row) => ({ row, bad: await check(row) })),
  );
  const failures = verdicts.filter(({ bad }) => bad.length > 0);
  failures.forEach(({ row, bad }) =>
    console.log(
      `oracle: FAIL seed ${row.seed}\n  prog       ${JSON.stringify(row.prog)}\n${bad.join("\n")}`,
    ),
  );
  console.log(
    `oracle: ${rows.length - failures.length}/${rows.length} seeds agree`,
  );
  process.exitCode = failures.length === 0 && rows.length === count ? 0 : 1;
};

await main();
