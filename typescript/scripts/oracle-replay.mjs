#!/usr/bin/env node
// Replay a recorded fast-check counterexample against the oracle suite.
//
//   npm run oracle:replay -- <seed> <path> [extra jest args...]
//
// e.g. npm run oracle:replay -- -1593651650 "175:3:5:4:3"
//
// Wraps the FC_SEED/FC_PATH env convention (see oracle.property.test.ts)
// so replays are plain `npm run` invocations.
import { spawnSync } from "node:child_process";

const [seed, fcPath, ...rest] = process.argv.slice(2);
if (seed === undefined || fcPath === undefined) {
  console.error('usage: npm run oracle:replay -- <seed> "<path>"');
  process.exit(2);
}
const res = spawnSync(
  "npx",
  ["jest", "src/v5/__tests__/oracle.property.test.ts", ...rest],
  {
    stdio: "inherit",
    env: { ...process.env, FC_SEED: seed, FC_PATH: fcPath },
  },
);
process.exit(res.status ?? 1);
