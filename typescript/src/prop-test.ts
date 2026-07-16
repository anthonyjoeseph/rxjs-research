import { Closed, Ty } from "./exp.js";
import { Fuel, Inputs, Stream, evaluate } from "./evaluate.js";

// The serializable unit of differential testing: a whole program.
// ctx is Γ — the types of the input slots, index-aligned with inputs.
export type TestCase = {
  ctx: Ty[];
  exp: Closed;
  inputs: Inputs;
  fuel: Fuel;
};

declare const readOperatorFromCli: () => string | undefined; // generator bias: which operator to feature at/near the root
declare const readSeedFromCli: () => string | undefined;
declare const genSeeds: () => string[];
declare const genTestCases: (seed: string, operator?: string) => TestCase[];

// JSON — also the regression-corpus format. Agda decodes it, re-checks
// well-typedness and μ-guardedness, then evaluates.
declare const serialize: (testCase: TestCase) => string;

declare const execAgda: (
  serialized: string[],
) => Promise<Stream[]>; // one long-lived process, JSON over stdio — not a spawn per case

// The real-rxjs leg: compile the tree onto the primitive-operators and
// drive each arrival's cascade synchronously within one turn.
declare const evaluateRx: (testCase: TestCase) => Promise<Stream>;

// Streams are compared up to id renaming (≈): partition structure is
// the only meaning the ids have.
declare const interpretResults: (
  agdaResults: Stream[],
  mirrorResults: Stream[],
  rxResults: Stream[],
) => string;

async function main() {
  const operator = readOperatorFromCli();
  const cliSeed = readSeedFromCli();
  const seeds = cliSeed ? [cliSeed] : genSeeds();
  const testCases = seeds.flatMap((seed) => genTestCases(seed, operator));
  const [agdaResults, rxResults] = await Promise.all([
    execAgda(testCases.map(serialize)),
    Promise.all(testCases.map(evaluateRx)),
  ]);
  const mirrorResults = testCases.map((testCase) =>
    evaluate(testCase.fuel, testCase.exp, testCase.inputs),
  );
  console.log(interpretResults(agdaResults, mirrorResults, rxResults));
}

main();
