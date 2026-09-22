// A DEEP SWEEP OF THE SAME TWO MACHINES THE ORACLE COMPARES, AND
// NOTHING ELSE.  `npm run oracle` draws a bounded corpus so CI stays
// seconds; this walks seeds without a bound so a rare shape gets found
// at all.  It narrows nothing: the comparison, the generator and both
// legs are the oracle's own.
//
// The agda leg is one process per CHUNK rather than one per case --
// spawning the binary dominates otherwise -- and a divergence prints
// the program in the same spelling `--cases` replays, so pinning it is
// a copy.
import { genTestCases } from "./generator.js";
import { serialize } from "./serialize.js";
import { execAgda } from "./agda-bridge.js";
import { evaluatePlain } from "./plain-eval.js";
import type { TestCase } from "./prop-test.js";
import { appendFileSync } from "node:fs";

const flag = (name: string, fallback: number): number => {
  const argv = process.argv.slice(2);
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === `--${name}`) return Number(argv[i + 1]);
    if (argv[i].startsWith(`--${name}=`))
      return Number(argv[i].slice(name.length + 3));
  }
  return fallback;
};

const from = flag("from", 0);
const to = flag("to", 5000);
const chunk = flag("chunk", 2000);
const out = process.argv.includes("--out")
  ? process.argv[process.argv.indexOf("--out") + 1]
  : "corpus/.deep-failures.ndjson";

let seen = 0;
let emitting = 0;
let bad = 0;
const started = Date.now();

const check = async (batch: TestCase[]): Promise<void> => {
  const agda = await execAgda(batch.map(serialize));
  batch.forEach((testCase, i) => {
    const rx = evaluatePlain(testCase);
    emitting += rx.length > 0 ? 1 : 0;
    const a = JSON.stringify(agda[i].values);
    const r = JSON.stringify(rx);
    if (a === r) return;
    bad++;
    appendFileSync(out, serialize(testCase) + "\n");
    console.log(`DIVERGENCE agda=${a} rx=${r}\n  ${serialize(testCase)}`);
  });
};

const main = async (): Promise<void> => {
  let batch: TestCase[] = [];
  for (let s = from; s < to; s++) {
    batch = [...batch, ...genTestCases(`d${s}`)];
    if (batch.length < chunk) continue;
    await check(batch);
    seen += batch.length;
    batch = [];
    const secs = (Date.now() - started) / 1000;
    console.log(
      `seed ${s + 1}/${to}  cases ${seen}  emitting ${emitting}  ` +
        `divergent ${bad}  ${Math.round(seen / secs)}/s`,
    );
  }
  if (batch.length > 0) {
    await check(batch);
    seen += batch.length;
  }
  console.log(
    `deep sweep: ${seen} cases (${emitting} emitting), ${bad} divergent, ` +
      `${Math.round((Date.now() - started) / 1000)}s`,
  );
  if (bad > 0) process.exitCode = 1;
};

main();
