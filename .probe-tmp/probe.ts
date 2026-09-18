import { genSeeds, genTestCases } from "../src/generator.js";
import { evaluatePlain } from "../src/plain-eval.js";
import type { TestCase } from "../src/prop-test.js";

const cases: TestCase[] = genSeeds().flatMap((s) => genTestCases(s));
let empty = 0, starved = 0, silent = 0;
const silentRoots = new Map<string, number>();
for (const tc of cases) {
  if (evaluatePlain(tc).values.length > 0) continue;
  empty++;
  const fat = { ...tc, fuel: 60 };
  if (evaluatePlain(fat).values.length > 0) starved++;
  else {
    silent++;
    const r = (tc.exp as any).type ?? "?";
    silentRoots.set(r, (silentRoots.get(r) ?? 0) + 1);
  }
}
console.log(`cases ${cases.length}  empty ${empty}  fuel-starved ${starved}  structurally silent ${silent}`);
console.log([...silentRoots.entries()].sort((a,b)=>b[1]-a[1]));
