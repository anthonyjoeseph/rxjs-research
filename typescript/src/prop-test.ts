import { TestCase, evaluate } from "./evaluate.js";

declare const readOperatorFromCli: () => string;
declare const readSeedFromCli: () => string | undefined;
declare const genSeeds: () => string[];

declare const getFuel: (seed: string) => number;
declare const genTestCases: (seed: string, operator: string) => TestCase[];

const evalTs = (seeds: string[], operator: string): Promise<unknown[][]> => {
  return Promise.all(
    seeds.map((seed) => {
      const fuel = getFuel(seed);
      const testCases = genTestCases(seed, operator);
      return Promise.all(testCases.map((testCase) => evaluate(testCase, fuel)));
    }),
  );
};

declare const execAgda: (
  seed: string[],
  operator: string,
) => Promise<unknown[][]>;

declare const interpretResults: (
  tsResults: unknown[][],
  agdaResults: unknown[][],
) => string;

async function main() {
  const operator = readOperatorFromCli();
  const cliSeed = readSeedFromCli();
  const seeds = cliSeed ? [cliSeed] : genSeeds();
  const [agdaResults, tsResults] = await Promise.all([
    execAgda(seeds, operator),
    Promise.resolve(evalTs(seeds, operator)),
  ]);
  console.log(interpretResults(tsResults, agdaResults));
}

main();
