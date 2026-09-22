import { Closed, Ty, Val } from "./exp.js";
import { evaluatePlain } from "./plain-eval.js";
import { genTestCases } from "./generator.js";
import { serialize } from "./serialize.js";
import { execAgda } from "./agda-bridge.js";
import { reachesRegion } from "./region.js";
import { readFileSync } from "node:fs";

// THE ORACLE, AND WHAT IT IS AN ORACLE FOR (Anthony: "the sole purpose
// of the fastcheck run is to ensure that the 'plain' agda Exp tree and
// evaluator's behavior matches the behavior of 'plain' rxjs. Nothing
// involving InstEmit at all"). Both sides produce a LIST OF VALUES and
// the lists are compared exactly. The envelope — instants, source ids,
// chain emits, the fin bit — is a construct of the simultaneity layer
// and is not under test here on either side: the TS leg is built from
// ordinary rxjs operators in `plain-eval.ts`, and the Agda leg is the
// evaluator reached through `CLI.Decode` — `evaluate↓`, whose result is
// a list of BURSTS of plain events, flattened and projected to values
// at the decode seam. Neither side carries an envelope, which is what
// makes this a comparison of two plain machines rather than of one
// plain one against a projection.
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
// name); `--seed <s>` pins a single seed, else the rejection draw below.
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
// THE TWO SIDES ARE THE COMPILED AGDA AND PLAIN RXJS, AND NOTHING ELSE
// MAY STAND ON EITHER.  A third machine here would be a semantics this
// repo wrote to check its own semantics against, and a green between
// two things we authored says nothing about rxjs -- which is the only
// authority the evaluator answers to.  `--machine` picks what is under
// test, `--baseline` what it is compared against; the defaults are the
// only pairing that measures anything.
const readMachineFromCli = (): string | undefined => readFlag("machine");
const readBaselineFromCli = (): string | undefined => readFlag("baseline");

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
// AND THE COUNT IS DENOMINATED IN ROWS THAT COULD HAVE DIVERGED, not in
// cases drawn. A program where NEITHER side emits agrees for a reason
// that has nothing to do with the machines under test, so counting it
// toward a coverage claim is the vacuous-row failure this file's own
// EMPTY-output incident already records, one notch weaker: there the
// check could not fail, here most of it does not.
//
// AND THE SIDES ARE NAMED BY THE CALLER, because the oracle side is not
// always the Agda: a reference run puts a transcription there, and a
// report calling it `agda` would be a lying label on the one output a
// reader takes a verdict from.
const interpretResults = (
  agdaResults: EvalResult[],
  rxResults: EvalResult[],
  testCases: TestCase[],
  lhs: string = "agda",
  rhs: string = "rx",
): { report: string; ok: boolean; live: number } => {
  const n = Math.min(agdaResults.length, rxResults.length);
  const lines: string[] = [];
  let valuesOk = 0;
  let live = 0;
  for (let i = 0; i < n; i++) {
    const a = render(agdaResults[i].values);
    const r = render(rxResults[i].values);
    if (agdaResults[i].values.length > 0 || rxResults[i].values.length > 0)
      live++;
    if (a === r) {
      valuesOk++;
      continue;
    }
    lines.push(`case ${i}: values ✗`);
    lines.push(`  program     = ${serialize(testCases[i])}`);
    lines.push(`  ${lhs}.values = ${a}`);
    lines.push(`  ${rhs}.values = ${r}`);
  }
  const region = testCases.slice(0, n).filter(reachesRegion).length;
  const header =
    `${n} cases (${live} emitting, ${region} in region):` +
    ` values ${valuesOk}/${n} match` +
    (agdaResults.length !== rxResults.length
      ? ` (LENGTH MISMATCH: ${lhs} ${agdaResults.length}, ${rhs} ${rxResults.length})`
      : "");
  return {
    report: [header, ...lines].join("\n"),
    ok: valuesOk === n && n > 0 && agdaResults.length === rxResults.length,
    live,
  };
};

// THE CORPUS IS DRAWN BY REJECTION, AND THE THING REJECTED IS A SILENT
// PROGRAM. A flat sweep of the seed list runs 500 programs of which 357
// emit NOTHING, so a reported 500/500 is 143 rows that could have
// diverged. Emptiness is a property of the PROGRAM and it is decidable
// here for free -- the rx leg has to be evaluated anyway -- so the draw
// keeps drawing past a silent program instead of spending an Agda row
// on it. Yield is what this buys; the Agda side still sees CORPUS cases,
// so it costs nothing.
//
// AND BIASING THE FUEL WAS THE OTHER CANDIDATE AND IT IS DEAD: re-run at
// fuel 60, 348 of the 357 stay empty. They are silent structurally --
// rooted at `empty`, at a flattener whose source never fires, at a
// spent `take` -- not starved of arrivals. Nine rows was the whole prize.
//
// A SILENT QUOTA IS KEPT DELIBERATELY, AND DROPPING IT WOULD DROP THE
// ONE CLASS THAT HAS ALREADY CAUGHT A REAL BUG. The rejection predicate
// reads ONE leg (rx), so a program where rx is silent and Agda is not is
// exactly a divergence -- and that is the shape of the depth-first
// witness this branch pinned, where the two machines disagreed by one
// side emitting and the other not. Filtering on rx-empty would have
// filtered that finding away. So the silent rows are thinned, never
// excluded.
const CORPUS = 500;
const SILENT_QUOTA = 100;
const LIVE_TARGET = CORPUS - SILENT_QUOTA;
const MAX_SEEDS = 400; // a bound, so an `--operator` that can only draw
// silent programs reports a short corpus instead of looping

const drawCorpus = (operator?: string): TestCase[] => {
  const live: TestCase[] = [];
  const silent: TestCase[] = [];
  for (
    let i = 0;
    i < MAX_SEEDS &&
    (live.length < LIVE_TARGET || silent.length < SILENT_QUOTA);
    i++
  ) {
    for (const testCase of genTestCases(`s${i}`, operator)) {
      const bucket = evaluatePlain(testCase).length > 0 ? live : silent;
      const cap = bucket === live ? LIVE_TARGET : SILENT_QUOTA;
      if (bucket.length < cap) bucket.push(testCase);
    }
  }
  return [...live, ...silent];
};

async function main() {
  const operator = readOperatorFromCli();
  const cliSeed = readSeedFromCli();
  const casesFile = readCasesFromCli();
  const machine = readMachineFromCli() ?? "agda";
  const baseline = readBaselineFromCli() ?? "rx";
  const known = ["agda", "rx"];
  for (const [flag, v] of [
    ["machine", machine],
    ["baseline", baseline],
  ])
    if (!known.includes(v))
      throw new Error(`--${flag} takes ${known.join(" | ")}, not '${v}'`);
  const testCases =
    casesFile !== undefined
      ? readFileSync(casesFile, "utf8")
          .split("\n")
          .filter((line) => line.trim().length > 0)
          .map((line) => JSON.parse(line) as TestCase)
      : cliSeed !== undefined
        ? genTestCases(cliSeed, operator)
        : drawCorpus(operator);
  const run = async (which: string): Promise<EvalResult[]> =>
    which === "rx"
      ? testCases.map((testCase): EvalResult => ({
          values: evaluatePlain(testCase),
        }))
      : await execAgda(testCases.map(serialize));
  if (machine !== "agda" || baseline !== "rx")
    console.log(`comparing ${machine} against ${baseline}`);
  const agdaResults = await run(machine);
  const rxResults = await run(baseline);
  const { report, ok, live } = interpretResults(
    agdaResults,
    rxResults,
    testCases,
    machine,
    baseline,
  );
  console.log(report);
  // a zero-case run is a failure too: it means the generator produced
  // nothing, which reads as a clean sweep of an empty corpus
  if (!ok) process.exitCode = 1;
  // AND A SWEPT CORPUS THAT CAME UP SHORT ON EMITTING ROWS IS A FAILURE,
  // because the yield is the thing the draw exists to hold. Only the
  // full sweep is held to it -- a pinned `--seed` or a `--cases` replay
  // is whatever the user asked for.
  if (casesFile === undefined && cliSeed === undefined && live < LIVE_TARGET) {
    console.log(
      `YIELD SHORT: ${live} emitting rows, target ${LIVE_TARGET} -- the ` +
        `draw could not find enough programs that emit within ${MAX_SEEDS} seeds`,
    );
    process.exitCode = 1;
  }
}

main();
