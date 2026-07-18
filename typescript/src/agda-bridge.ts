import { spawn } from "node:child_process";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";
import type { Stream } from "./prop-test.js";

// The Agda bridge. One long-lived process for the whole batch (not a
// spawn per case): the compiled CLI reads NDJSON cases on stdin — one
// serialized TestCase per line, in order — decodes, re-checks, evaluates
// each, and writes one JSON line per case on stdout, in the SAME order.
// A case the CLI cannot handle emits `null`, which surfaces here as a
// null entry (kept positional so results still align with the input).

// the compiled binary: override with AGDA_CLI_BIN, else the default build
// output (agda --compile of CLI.Main lands at agda/_cli/Main)
const defaultBin = resolve(
  dirname(fileURLToPath(import.meta.url)),
  "../../agda/_cli/Main",
);
const binPath = (): string => process.env.AGDA_CLI_BIN ?? defaultBin;

export const execAgda = (serialized: string[]): Promise<Stream[]> =>
  new Promise((resolvePromise, reject) => {
    if (serialized.length === 0) return resolvePromise([]);
    const bin = binPath();
    if (!existsSync(bin))
      return reject(
        new Error(
          `Agda CLI not built at ${bin} — run \`npm run agda:cli\` (or set AGDA_CLI_BIN).`,
        ),
      );

    const child = spawn(bin, [], { stdio: ["pipe", "pipe", "pipe"] });
    let out = "";
    let err = "";
    child.stdout.setEncoding("utf8");
    child.stderr.setEncoding("utf8");
    child.stdout.on("data", (chunk: string) => (out += chunk));
    child.stderr.on("data", (chunk: string) => (err += chunk));
    child.on("error", reject); // e.g. spawn failure
    child.on("close", (code) => {
      if (code !== 0)
        return reject(
          new Error(`Agda CLI exited with code ${code}\n${err.trim()}`),
        );
      // one result line per input line, order-aligned; a `null` line is a
      // case the CLI declined (unsupported / decode failure)
      const lines = out.split("\n").filter((l) => l.trim().length > 0);
      if (lines.length !== serialized.length)
        return reject(
          new Error(
            `Agda CLI returned ${lines.length} results for ${serialized.length} cases`,
          ),
        );
      try {
        resolvePromise(lines.map((line) => JSON.parse(line) as Stream));
      } catch (e) {
        reject(new Error(`Agda CLI produced non-JSON output: ${String(e)}`));
      }
    });

    child.stdin.write(serialized.join("\n") + "\n");
    child.stdin.end();
  });
