import { spawn } from "node:child_process";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";
import type { EvalResult } from "./prop-test.js";

// The Agda bridge. One long-lived process per batch (not a spawn per
// case): the compiled CLI reads NDJSON cases on stdin — one serialized
// TestCase per line, in order — decodes, re-checks, evaluates each, and
// writes one JSON line per case on stdout, in the SAME order. A case the
// CLI cannot handle emits `null`, which surfaces here as a null entry
// (kept positional so results still align with the input).
//
// A CASE THAT KILLS THE CLI IS A RESULT, NOT THE END OF THE BATCH. A
// postulate on the extracted path dies at `postulate evaluated` the first
// time a run reaches it, and that is a finding about ONE program. So the
// lines finished before the death are that many results, the case being
// evaluated is a crash carrying the reason, and the CLI is restarted at
// the next case. A line is finished only once its newline is written: the
// runtime flushes stdout on the way out, so a result half-rendered when
// the crash hit is a fragment, never a row.

// the compiled binary: override with AGDA_CLI_BIN, else the default build
// output (agda --compile of CLI.Main lands at agda/_cli/Main)
const defaultBin = resolve(
  dirname(fileURLToPath(import.meta.url)),
  "../../agda/_cli/Main",
);
const binPath = (): string => process.env.AGDA_CLI_BIN ?? defaultBin;

type Run = { lines: string[]; crash?: string };

// the postulate a run died at, else the first thing it said, else its code
const crashReason = (code: number | null, err: string): string =>
  /postulate evaluated: (\S+)/.exec(err)?.[1] ??
  err.trim().split("\n")[0] ??
  `exit ${code}`;

// AND A CASE THAT NEVER ANSWERS IS A RESULT TOO. The evaluator is total,
// but total is not fast: one program took minutes on a single arrival
// that its neighbours clear in milliseconds, and a batch waiting on it
// waits forever. So a CLI that writes nothing for this long is killed,
// and the case it was on is a crash whose reason says it timed out.
const CASE_TIMEOUT_MS = Number(process.env.ORACLE_CASE_TIMEOUT_MS ?? 10000);

const runOnce = (bin: string, serialized: string[]): Promise<Run> =>
  new Promise((resolvePromise, reject) => {
    const child = spawn(bin, [], { stdio: ["pipe", "pipe", "pipe"] });
    let out = "";
    let err = "";
    let timedOut = false;
    const watch = () =>
      setTimeout(() => {
        timedOut = true;
        child.kill("SIGKILL");
      }, CASE_TIMEOUT_MS);
    let timer = watch();
    child.stdout.setEncoding("utf8");
    child.stderr.setEncoding("utf8");
    child.stdout.on("data", (chunk: string) => {
      out += chunk;
      clearTimeout(timer);
      timer = watch();
    });
    child.stderr.on("data", (chunk: string) => (err += chunk));
    child.on("error", reject); // e.g. spawn failure
    // a child that died early closes its stdin under us; the death is
    // what `close` reports, so the write error carries nothing more
    child.stdin.on("error", () => undefined);
    child.on("close", (code) => {
      clearTimeout(timer);
      // the fragment after the last newline is a line the crash cut off
      const lines = out
        .split("\n")
        .slice(0, -1)
        .filter((l) => l.trim().length > 0);
      resolvePromise(
        timedOut
          ? { lines, crash: `timeout (${CASE_TIMEOUT_MS} ms)` }
          : code === 0
            ? { lines }
            : { lines, crash: crashReason(code, err) },
      );
    });
    child.stdin.write(serialized.join("\n") + "\n");
    child.stdin.end();
  });

// each line is either `null` (declined case) or {"values":[...]} —
// normalize null to an empty value list
const parseLine = (line: string): EvalResult => {
  try {
    return (JSON.parse(line) as EvalResult | null) ?? { values: [] };
  } catch (e) {
    throw new Error(`Agda CLI produced non-JSON output: ${String(e)}`);
  }
};

export const execAgda = async (serialized: string[]): Promise<EvalResult[]> => {
  const bin = binPath();
  if (serialized.length > 0 && !existsSync(bin))
    throw new Error(
      `Agda CLI not built at ${bin} — run \`npm run agda:cli\` (or set AGDA_CLI_BIN).`,
    );
  const go = async (rest: string[]): Promise<EvalResult[]> => {
    if (rest.length === 0) return [];
    const { lines, crash } = await runOnce(bin, rest);
    const done = lines.map(parseLine);
    if (crash === undefined) {
      if (lines.length !== rest.length)
        throw new Error(
          `Agda CLI returned ${lines.length} results for ${rest.length} cases`,
        );
      return done;
    }
    // a death after the last row belongs to no case, so it is the run's
    if (lines.length >= rest.length)
      throw new Error(`Agda CLI died after its last result: ${crash}`);
    return [
      ...done,
      { values: [], crash },
      ...(await go(rest.slice(lines.length + 1))),
    ];
  };
  return go(serialized);
};
