#!/usr/bin/env node
// Run the oracle property suite repeatedly (fresh random seeds each run)
// and stop at the first failure, printing the recorded counterexample.
//
//   npm run oracle:sweep -- [iterations]     (default 30; ~500 programs/run)
//
// Exit code 0 = all iterations clean, 1 = a counterexample was found.
import { spawnSync } from "node:child_process";

const iterations = parseInt(process.argv[2] ?? "30", 10);
for (let i = 1; i <= iterations; i++) {
  const res = spawnSync(
    "npx",
    ["jest", "src/v5/__tests__/oracle.property.test.ts"],
    { encoding: "utf8" },
  );
  if (res.status !== 0) {
    const out = `${res.stdout ?? ""}${res.stderr ?? ""}`;
    const failure = out.match(/Property failed[\s\S]*?(?=\n\s*Hint|$)/);
    console.log(`FAILED iter ${i}`);
    console.log(failure ? failure[0] : out.slice(-2000));
    process.exit(1);
  }
  console.log(`iter ${i} ok`);
}
console.log(`sweep clean (${iterations} iterations)`);
