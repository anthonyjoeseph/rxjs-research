import { Closed, Ty, Val } from "./exp.js";
import { evaluatePlain } from "./plain-eval.js";
import { genSeeds, genTestCases } from "./generator.js";
import { serialize } from "./serialize.js";
import { execAgda } from "./agda-bridge.js";
import { readFileSync } from "node:fs";

// THE ORACLE, AND WHAT IT IS AN ORACLE FOR (Anthony: "the sole purpose
// of the fastcheck run is to ensure that the 'plain' agda Exp tree and
// evaluator's behavior matches the behavior of 'plain' rxjs. Nothing
// involving InstEmit at all"). Both sides produce a LIST OF VALUES and
// the lists are compared exactly. The envelope — instants, source ids,
// chain emits, the fin bit — is a construct of the simultaneity layer
// and is not under test here on either side: the TS leg is built from
// ordinary rxjs operators in `plain-eval.ts`, and the Agda leg is
// `Rx.Depth`, a plain evaluator whose result type carries no envelope
// at all — so there is nothing to project away, which is what makes
// this a comparison of two plain machines rather than of one plain one
// against a projection.
//
// The srxjs modules (`join.ts`, `primitive-operators.ts`,
// `inst-emit.ts`, `compile.ts`, `driver.ts`, `input-source.ts`) stay in
// the tree and are reached by nothing this file runs.

// Virtual time. fuel = ARRIVALS DELIVERED by the driver — async input
// values and defer-body wakeups, popped in (tick, ordinal) order. Sync
// bursts ride inside the triggering cascade and cost no fuel; the root
// subscription's burst is free (fuel 0 still yields it).
export type Fuel = number;

export type Timed<A> = {
  wait: number; // gap = wait + 1, so per-source ticks are strictly increasing by construction
  val: A;
};

export type ObservableInputCold<A> = {
  type: "cold";
  sync: A[]; // fired immediately on subscription, inside the subscriber's frame
  async: Timed<A>[]; // re-anchored at each subscription tick
};

export type ObservableInputHot<A> = {
  type: "hot";
  async: Timed<A>[]; // anchored at tick 0
};

export type ObservableInput<A> = ObservableInputCold<A> | ObservableInputHot<A>;

// Agda: Rx.Evaluator.Slot. Slot i of Γ is either an external scripted
// input or a SHARED observable — an exp tree with an implicit
// all-resets-false share() at its root. Share identity is the de
// Bruijn index: the binding, not the expression, exactly as a JS
// `const`. Shared defs may reference only strictly earlier slots (a
// const telescope) — generator invariant, re-checked by the Agda
// decoder alongside well-typedness and μ-guardedness.
export type Slot =
  | { type: "scripted"; input: ObservableInput<Val> }
  | { type: "shared"; def: Closed };

export type Slots = Slot[]; // one per Γ slot, index-aligned

// one program's output: the values the exp tree emitted, in order. Both
// sides (TS-here and Agda-via-CLI) return this per case.
export type EvalResult = { values: Val[] };

// The serializable unit of differential testing: a whole program.
// ctx is Γ — the types of the slots, index-aligned with slots.
export type TestCase = {
  ctx: Ty[];
  exp: Closed;
  slots: Slots;
  fuel: Fuel;
};

// CLI flags biasing the run: `--operator <op>` features that operator at
// the root of every generated program (the generator ignores an unknown
// name); `--seed <s>` pins a single seed, else the full genSeeds() sweep.
// Both accept `--flag value` and `--flag=value`; absent ⇒ undefined.
const readFlag = (name: string): string | undefined => {
  const argv = process.argv.slice(2);
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === `--${name}`) {
      const next = argv[i + 1];
      return next !== undefined && !next.startsWith("--") ? next : undefined;
    }
    if (arg.startsWith(`--${name}=`)) return arg.slice(name.length + 3);
  }
  return undefined;
};
const readOperatorFromCli = (): string | undefined => readFlag("operator");
const readSeedFromCli = (): string | undefined => readFlag("seed");
// `--cases <file>` REPLAYS programs instead of generating them: one
// serialized TestCase per line, which is exactly what a failing case
// prints.  Without it a divergence is reproducible only by re-running
// the sweep that found it, and a generator edit moves every offset.
const readCasesFromCli = (): string | undefined => readFlag("cases");

// A TOKEN IN A VALUE POSITION IS REFUSED, WHICH IS THE ONE PLACE A
// SYMBOL WOULD LIE.  `JSON.stringify` drops a symbol silently, so a
// minted token reaching the output would compare equal to a side that
// emitted nothing there — a false green, and the only kind this
// comparison can produce. The two sides carry a token differently (TS a
// `symbol`, Agda a ℕ), and nothing in a value list says which position
// is a token, so there is no renaming available either. The generator
// keeps uniq out of every element type precisely so the case cannot
// arise; this says so if it ever does.
const noToken = (v: unknown): void => {
  if (typeof v === "symbol")
    throw new Error(
      "a uniq token reached the output — the comparison has no renaming " +
        "for one, and JSON.stringify would drop it silently",
    );
  if (Array.isArray(v)) v.forEach(noToken);
  else if (v !== null && typeof v === "object")
    Object.values(v).forEach(noToken);
};

const render = (values: Val[]): string => (
  values.forEach(noToken),
  JSON.stringify(values)
);

// Compare the Agda (oracle) and rxjs value lists case by case, and
// render a compact report.
//
// THE VERDICT IS RETURNED BESIDE THE REPORT, AND THAT IS NOT A
// REFINEMENT.  This printed its findings and exited 0 whatever they
// were, so `make oracle` was green on a run whose rx output was EMPTY
// in a fifth of its cases -- a check that cannot fail, standing where
// the change workflow puts its second gate.  The report was always
// right; nothing read it.
//
// AND A FAILING CASE PRINTS ITS PROGRAM, because the two lists alone
// say WHAT diverged and nothing about what was run -- and the case
// index is an offset into a seed sweep, so it cannot be fed back to
// `--seed` to recover the input.  A divergence nobody can reproduce is
// a report rather than a finding.
const interpretResults = (
  agdaResults: EvalResult[],
  rxResults: EvalResult[],
  testCases: TestCase[],
): { report: string; ok: boolean } => {
  const n = Math.min(agdaResults.length, rxResults.length);
  const lines: string[] = [];
  let valuesOk = 0;
  for (let i = 0; i < n; i++) {
    const a = render(agdaResults[i].values);
    const r = render(rxResults[i].values);
    if (a === r) {
      valuesOk++;
      continue;
    }
    lines.push(`case ${i}: values ✗`);
    lines.push(`  program     = ${serialize(testCases[i])}`);
    lines.push(`  agda.values = ${a}`);
    lines.push(`  rx.values   = ${r}`);
  }
  const header =
    `${n} cases: values ${valuesOk}/${n} match` +
    (agdaResults.length !== rxResults.length
      ? ` (LENGTH MISMATCH: agda ${agdaResults.length}, rx ${rxResults.length})`
      : "");
  return {
    report: [header, ...lines].join("\n"),
    ok: valuesOk === n && n > 0 && agdaResults.length === rxResults.length,
  };
};

async function main() {
  const operator = readOperatorFromCli();
  const cliSeed = readSeedFromCli();
  const casesFile = readCasesFromCli();
  const seeds = cliSeed ? [cliSeed] : genSeeds();
  const testCases =
    casesFile !== undefined
      ? readFileSync(casesFile, "utf8")
          .split("\n")
          .filter((line) => line.trim().length > 0)
          .map((line) => JSON.parse(line) as TestCase)
      : seeds.flatMap((seed) => genTestCases(seed, operator));
  const agdaResults = await execAgda(testCases.map(serialize));
  const rxResults = testCases.map((testCase): EvalResult => ({
    values: evaluatePlain(testCase),
  }));
  const { report, ok } = interpretResults(agdaResults, rxResults, testCases);
  console.log(report);
  // a zero-case run is a failure too: it means the generator produced
  // nothing, which reads as a clean sweep of an empty corpus
  if (!ok) process.exitCode = 1;
}

main();
