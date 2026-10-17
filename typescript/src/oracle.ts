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

// A natural past 2^53 is exact only as text: an Agda trace is read with
// its integers quoted, and every event compared as that same text.
const exactly = (json: string): unknown =>
  JSON.parse(json.replace(/([:,[]\s*)(\d+)(?=\s*[,\]}])/g, '$1"$2"'));
const canon = (v: unknown): unknown =>
  typeof v === "number" || typeof v === "bigint"
    ? String(v)
    : Array.isArray(v)
      ? v.map(canon)
      : v !== null && typeof v === "object"
        ? Object.fromEntries(Object.entries(v).map(([k, x]) => [k, canon(x)]))
        : v;
type End = "completed" | "silent" | "cut";
type Trace = { events: Event[]; end: End };
type Row = {
  seed: number;
  prog: Code;
  denote: Trace;
  pure: Trace;
};

const bin = process.env.AGDA_CLI_BIN ?? "../agda-impl/_cli/Oracle-CLI";
const timeoutMs = Number(process.env.ORACLE_CASE_TIMEOUT_MS ?? 10000);

// Whether the program holds a cold that plays its frames forever: its run
// never drains, so it is read up to `HORIZON` and reported cut.
const HORIZON = 2000;
const loops = (c: unknown): boolean =>
  Array.isArray(c) &&
  (c[0] === "cold"
    ? c[3] === true && (c[1] as unknown[]).length > 0
    : c.some(loops));

// Time is the virtual scheduler's frame; a tick opens each run of values
// at one time, as the Agda traces print it.
const rxjsTrace = async (prog: Code): Promise<Trace> => {
  const sch = new VirtualTimeScheduler();
  const done = lastValueFrom(
    compileProg(sch, UNFOLD, prog).pipe(
      materialize(),
      map((n) => ({ t: sch.now(), n })),
      takeUntil(timer(loops(prog) ? HORIZON : Number.MAX_SAFE_INTEGER, sch)),
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
    end: log.some(({ n }) => n.kind === "C")
      ? "completed"
      : loops(prog)
        ? "cut"
        : "silent",
  };
};

const same = (a: Event, b: Event): boolean =>
  JSON.stringify(canon(a)) === JSON.stringify(canon(b));
const prefix = (xs: Event[], ys: Event[]): boolean =>
  xs.length <= ys.length && xs.every((x, i) => same(x, ys[i]));

// `quickcheck.Quickcheck.agrees`: a trace the budget cut only has to
// be a prefix of the other, and of two cut traces either may be shorter.
const agrees = (a: Trace, b: Trace): boolean =>
  a.end === "cut" && b.end === "cut"
    ? prefix(a.events, b.events) || prefix(b.events, a.events)
    : a.end === "cut"
      ? prefix(a.events, b.events)
      : b.end === "cut"
        ? prefix(b.events, a.events)
        : a.end === b.end &&
          prefix(a.events, b.events) &&
          prefix(b.events, a.events);

const cli = (
  args: string[],
  timeout = timeoutMs,
): { out: string; failed?: string } => {
  const r = spawnSync(bin, args, {
    encoding: "utf8",
    timeout,
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

const show = (t: Trace): string => JSON.stringify(canon(t));

const check = async (row: Row): Promise<string[]> => {
  const rx = await rxjsTrace(row.prog);
  // The IO engine returns only once nothing is left to wait for, which a
  // looping program never reaches: its leg is skipped there.
  const io = loops(row.prog) ? undefined : cli(["io", String(row.seed)]);
  const ioTrace: Trace | undefined =
    io?.failed === undefined && io !== undefined
      ? (exactly(io.out) as Trace)
      : undefined;
  const bad = [
    ...(agrees(row.denote, rx) ? [] : [`denotation ${show(row.denote)}`]),
    ...(agrees(row.pure, rx) ? [] : [`pure       ${show(row.pure)}`]),
    ...(io === undefined
      ? []
      : ioTrace === undefined
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
  // The listing runs every seed's two Agda engines: one case's time each.
  const listing = cli(
    ["prog", String(start), String(count)],
    timeoutMs * Math.max(1, Math.ceil(count / 50)),
  );
  // A listing cut short is listed again a seed at a time, so a seed whose
  // engines never finish is named, and the others still checked.
  // Five stuck seeds end the search: a slowdown everywhere is one finding.
  const seeds = Array.from({ length: count }, (_, i) => start + i);
  const single = seeds.reduce<
    { seed: number; listed?: { out: string; failed?: string } }[]
  >(
    (acc, s) =>
      listing.failed === undefined ||
      acc.filter(({ listed }) => listed?.failed !== undefined).length >= 5
        ? acc
        : [...acc, { seed: s, listed: cli(["prog", String(s), "1"]) }],
    [],
  );
  const stuck = single.filter(({ listed }) => listed?.failed !== undefined);
  stuck.forEach(({ seed, listed }) =>
    console.log(
      `oracle: FAIL seed ${seed}\n  prog       ${cli(["code", String(seed)]).out.trim()}\n  listing    ${listed?.failed}\n  denote     ${cli(["denote", String(seed)]).failed ?? "finishes"}\n  pure       ${cli(["pure", String(seed)]).failed ?? "finishes"}`,
    ),
  );
  const rows = (
    listing.failed === undefined
      ? listing.out
      : single
          .filter(({ listed }) => listed?.failed === undefined)
          .map(({ listed }) => listed?.out ?? "")
          .join("\n")
  )
    .split("\n")
    .filter((l) => l.trim().length > 0)
    .map((l) => {
      const exact = exactly(l) as Row;
      return {
        ...(JSON.parse(l) as Row),
        denote: exact.denote,
        pure: exact.pure,
      };
    });
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
