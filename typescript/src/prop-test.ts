import { Closed, ScriptVal, Ty, Val, showValues } from "./exp.js";
import { evaluatePlain } from "./plain-eval.js";
import { genTestCases } from "./generator.js";
import { serialize } from "./serialize.js";
import { execAgda } from "./agda-bridge.js";
import { reachesRegion } from "./region.js";
import { appendFileSync, readFileSync, writeFileSync } from "node:fs";

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
  | { type: "scripted"; input: ObservableInput<ScriptVal> }
  | { type: "shared"; def: Closed };

export type Slots = Slot[]; // one per Γ slot, index-aligned

// one program's output: the values the exp tree emitted, in order. Both
// sides (TS-here and Agda-via-CLI) return this per case. A `crash` names
// what the run died at, and its values are then no output at all.
export type EvalResult = { values: Val[]; crash?: string };

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
// `--crashes <file>` KEEPS EVERY CRASHING PROGRAM, one `{why, case}` per
// line, where the report keeps only the smallest few per reason. The
// smallest are the ones worth pinning; the whole set is what says
// whether a reason has ONE shape or several, which a sample of three
// cannot. The file is truncated at the start of the run and appended a
// chunk at a time, so a killed sweep still leaves what it found.
const readCrashesFromCli = (): string | undefined => readFlag("crashes");

// KEY ORDER IS NOT CONTENT, so two spellings of one row compare equal.
// A hand-written row and the compact line a failing case prints carry
// the same program in different orders, which is exactly the pair a
// textual comparison would miss.
const canonical = (v: unknown): string =>
  JSON.stringify(v, (_k, x: unknown) =>
    x !== null && typeof x === "object" && !Array.isArray(x)
      ? Object.fromEntries(
          Object.entries(x as Record<string, unknown>).sort(([a], [b]) =>
            a < b ? -1 : 1,
          ),
        )
      : x,
  );

// A PINNED FILE'S ROW COUNT IS A COVERAGE CLAIM, AND A REPEATED ROW
// MAKES IT A FALSE ONE.  Two rows naming one program cannot fail
// independently, so the count reads as reach the file does not have --
// the same shape of lie as a green sweep that never entered the region,
// and just as invisible while the number is only ever read.
//
// It is not a hypothetical: a row is pinned by COPYING the line a
// failing case prints, so a program already pinned by hand gets pinned
// again in the other spelling, and the file then reports a bigger
// denominator every summary of the run quotes.
const refuseDuplicates = (file: string, cases: TestCase[]): void => {
  const keys = cases.map(canonical);
  const dup = keys
    .map((k, i) => ({ i, first: keys.indexOf(k) }))
    .find(({ i, first }) => first !== i);
  if (dup !== undefined)
    throw new Error(
      `${file}: row ${dup.i} names the same program as row ${dup.first} — ` +
        `a row that cannot fail independently of another inflates the count ` +
        `this file is read for`,
    );
};

const replayCases = (file: string): TestCase[] => {
  const cases = readFileSync(file, "utf8")
    .split("\n")
    .filter((line) => line.trim().length > 0)
    .map((line) => JSON.parse(line) as TestCase);
  return (refuseDuplicates(file, cases), cases);
};
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
// SYMBOL WOULD LIE.  A JSON rendering drops a symbol silently, so a
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
        "for one, and a JSON rendering would drop it silently",
    );
  if (Array.isArray(v)) v.forEach(noToken);
  else if (v !== null && typeof v === "object")
    Object.values(v).forEach(noToken);
};

const render = (values: Val[]): string => (
  values.forEach(noToken),
  showValues(values)
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
//
// AND A CRASH IS ITS OWN VERDICT, COUNTED BY WHAT IT DIED AT. A run that
// reached a postulate has no output to compare, so it is neither a match
// nor a divergence; it fails the sweep all the same. At volume the same
// postulate is reached by thousands of programs, so what is printed is
// the count per reason and the SMALLEST few programs for each -- the
// ones worth pinning -- and the divergences past the first few are
// counted rather than listed. Only the printing is capped, never the
// verdict.
const SHOWN_DIVERGENCES = 20;
const SHOWN_CRASHES = 3;

type Tally = {
  n: number;
  live: number;
  region: number;
  valuesOk: number;
  lengthMismatch?: string;
  divergences: string[];
  diverged: number;
  crashes: Map<string, { count: number; smallest: string[] }>;
};

const emptyTally = (): Tally => ({
  n: 0,
  live: 0,
  region: 0,
  valuesOk: 0,
  divergences: [],
  diverged: 0,
  crashes: new Map(),
});

// the shortest programs first, ties broken by text so the pick is stable
const keepSmallest = (xs: string[], x: string): string[] =>
  [...xs, x]
    .sort((p, q) => p.length - q.length || (p < q ? -1 : p > q ? 1 : 0))
    .slice(0, SHOWN_CRASHES);

const tallyChunk = (
  t: Tally,
  agdaResults: EvalResult[],
  rxResults: EvalResult[],
  testCases: TestCase[],
  lhs: string,
  rhs: string,
): void => {
  const n = Math.min(agdaResults.length, rxResults.length);
  if (agdaResults.length !== rxResults.length && t.lengthMismatch === undefined)
    t.lengthMismatch = `${lhs} ${agdaResults.length}, ${rhs} ${rxResults.length}`;
  for (let i = 0; i < n; i++) {
    const at = t.n + i;
    if (agdaResults[i].values.length > 0 || rxResults[i].values.length > 0)
      t.live++;
    const crash = agdaResults[i].crash ?? rxResults[i].crash;
    if (crash !== undefined) {
      const seen = t.crashes.get(crash) ?? { count: 0, smallest: [] };
      t.crashes.set(crash, {
        count: seen.count + 1,
        smallest: keepSmallest(seen.smallest, serialize(testCases[i])),
      });
      continue;
    }
    const a = render(agdaResults[i].values);
    const r = render(rxResults[i].values);
    if (a === r) {
      t.valuesOk++;
      continue;
    }
    t.diverged++;
    if (t.divergences.length < SHOWN_DIVERGENCES * 4)
      t.divergences.push(
        `case ${at}: values ✗`,
        `  program     = ${serialize(testCases[i])}`,
        `  ${lhs}.values = ${a}`,
        `  ${rhs}.values = ${r}`,
      );
  }
  t.region += testCases.slice(0, n).filter(reachesRegion).length;
  t.n += n;
};

// the `--crashes` rows of one chunk: a case is a row iff either side
// died on it, and the row says what it died at
const crashRows = (
  agdaResults: EvalResult[],
  rxResults: EvalResult[],
  testCases: TestCase[],
): string[] =>
  testCases.flatMap((testCase, i) => {
    const why = agdaResults[i]?.crash ?? rxResults[i]?.crash;
    return why === undefined
      ? []
      : [`{"why":${JSON.stringify(why)},"case":${serialize(testCase)}}`];
  });

const crashedCount = (t: Tally): number =>
  [...t.crashes.values()].reduce((k, c) => k + c.count, 0);

const reportTally = (t: Tally): { report: string; ok: boolean } => {
  const crashed = crashedCount(t);
  const header =
    `${t.n} cases (${t.live} emitting, ${t.region} in region):` +
    ` values ${t.valuesOk}/${t.n} match` +
    (crashed > 0
      ? `, ${crashed} crashed (${[...t.crashes]
          .map(([why, c]) => `${why} ${c.count}`)
          .join(", ")})`
      : "") +
    (t.lengthMismatch !== undefined
      ? ` (LENGTH MISMATCH: ${t.lengthMismatch})`
      : "");
  const crashLines = [...t.crashes].flatMap(([why, c]) => [
    `crash ${why}: ${c.count} case(s), smallest ${c.smallest.length}:`,
    ...c.smallest.map((p) => `  program     = ${p}`),
  ]);
  const hidden =
    t.diverged > SHOWN_DIVERGENCES
      ? [`(${t.diverged - SHOWN_DIVERGENCES} more divergences not shown)`]
      : [];
  return {
    report: [...t.divergences, ...hidden, ...crashLines, header].join("\n"),
    ok: t.valuesOk === t.n && t.n > 0 && t.lengthMismatch === undefined,
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
//
// `--corpus <n>` SETS THE SIZE, and the proportions hold at any size: a
// fifth silent, the rest emitting, and a seed bound scaled with it. The
// draw is handed over in CHUNKS, each run and tallied before the next is
// drawn, so a sweep of millions holds one chunk in memory rather than
// the corpus -- and a chunk is one CLI batch, whose crashes restart it
// rather than end it.
const CORPUS = 500;
const CHUNK = 2000;
const quotas = (corpus: number) => {
  const silentQuota = Math.floor(corpus / 5);
  return {
    silentQuota,
    liveTarget: corpus - silentQuota,
    // a bound, so an `--operator` that can only draw silent programs
    // reports a short corpus instead of looping
    maxSeeds: Math.ceil((corpus * 4) / 5),
  };
};

function* drawChunks(corpus: number, operator?: string): Generator<TestCase[]> {
  const { silentQuota, liveTarget, maxSeeds } = quotas(corpus);
  let live = 0;
  let silent = 0;
  let chunk: TestCase[] = [];
  for (
    let i = 0;
    i < maxSeeds && (live < liveTarget || silent < silentQuota);
    i++
  ) {
    for (const testCase of genTestCases(`s${i}`, operator)) {
      const emits = evaluatePlain(testCase).length > 0;
      if (emits ? live >= liveTarget : silent >= silentQuota) continue;
      if (emits) live++;
      else silent++;
      chunk.push(testCase);
      if (chunk.length === CHUNK) {
        yield chunk;
        chunk = [];
      }
    }
  }
  if (chunk.length > 0) yield chunk;
}

const readCorpusFromCli = (): number | undefined => {
  const v = readFlag("corpus");
  if (v === undefined) return undefined;
  const n = Number(v);
  if (!Number.isInteger(n) || n <= 0)
    throw new Error(`--corpus takes a positive integer, not '${v}'`);
  return n;
};

async function main() {
  const operator = readOperatorFromCli();
  const cliSeed = readSeedFromCli();
  const casesFile = readCasesFromCli();
  const corpus = readCorpusFromCli() ?? CORPUS;
  const machine = readMachineFromCli() ?? "agda";
  const baseline = readBaselineFromCli() ?? "rx";
  const known = ["agda", "rx"];
  for (const [flag, v] of [
    ["machine", machine],
    ["baseline", baseline],
  ])
    if (!known.includes(v))
      throw new Error(`--${flag} takes ${known.join(" | ")}, not '${v}'`);
  const swept = casesFile === undefined && cliSeed === undefined;
  const chunks: Iterable<TestCase[]> =
    casesFile !== undefined
      ? [replayCases(casesFile)]
      : cliSeed !== undefined
        ? [genTestCases(cliSeed, operator)]
        : drawChunks(corpus, operator);
  const run = async (
    which: string,
    testCases: TestCase[],
  ): Promise<EvalResult[]> =>
    which === "rx"
      ? testCases.map((testCase): EvalResult => ({
          values: evaluatePlain(testCase),
        }))
      : await execAgda(testCases.map(serialize));
  if (machine !== "agda" || baseline !== "rx")
    console.log(`comparing ${machine} against ${baseline}`);
  const crashesFile = readCrashesFromCli();
  if (crashesFile !== undefined) writeFileSync(crashesFile, "");
  const tally = emptyTally();
  for (const testCases of chunks) {
    const machineResults = await run(machine, testCases);
    const baselineResults = await run(baseline, testCases);
    tallyChunk(
      tally,
      machineResults,
      baselineResults,
      testCases,
      machine,
      baseline,
    );
    if (crashesFile !== undefined) {
      const rows = crashRows(machineResults, baselineResults, testCases);
      if (rows.length > 0) appendFileSync(crashesFile, rows.join("\n") + "\n");
    }
    // progress on stderr, so the report on stdout stays the report
    if (swept && corpus > CHUNK)
      console.error(
        `${tally.n}/${corpus}: ${tally.valuesOk} match, ` +
          `${tally.diverged} diverged, ${crashedCount(tally)} crashed`,
      );
  }
  const { report, ok } = reportTally(tally);
  console.log(report);
  // a zero-case run is a failure too: it means the generator produced
  // nothing, which reads as a clean sweep of an empty corpus
  if (!ok) process.exitCode = 1;
  // AND A SWEPT CORPUS THAT CAME UP SHORT ON EMITTING ROWS IS A FAILURE,
  // because the yield is the thing the draw exists to hold. Only the
  // full sweep is held to it -- a pinned `--seed` or a `--cases` replay
  // is whatever the user asked for.
  const { liveTarget, maxSeeds } = quotas(corpus);
  if (swept && tally.live < liveTarget) {
    console.log(
      `YIELD SHORT: ${tally.live} emitting rows, target ${liveTarget} -- the ` +
        `draw could not find enough programs that emit within ${maxSeeds} seeds`,
    );
    process.exitCode = 1;
  }
}

main();
