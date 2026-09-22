// HOW OFTEN THE DRAW REACHES THE STORE RE-ENTRY.  A `scan` whose OUTPUT
// element type is itself an observable stores a stream value, and
// re-establishing the candidate at it is the one edge that leaves the
// expression the walk came in on.  A sweep's green says nothing about a
// region it never entered, so the rate is the coverage claim.
import { genTestCases } from "./generator.js";
import type { TestCase } from "./prop-test.js";

type Node = Record<string, unknown>;
const isObs = (t: unknown): boolean =>
  typeof t === "object" && t !== null && (t as Node).type === "obs";

const walk = (
  e: unknown,
  under: boolean,
  hit: { scanObs: number; scanObsUnderFlat: number },
): void => {
  if (typeof e !== "object" || e === null) return;
  const n = e as Node;
  if (n.type === "scan" && isObs(n.ty)) {
    hit.scanObs++;
    if (under) hit.scanObsUnderFlat++;
  }
  const flat =
    n.type === "mergeAll" || n.type === "switchAll" || n.type === "exhaustAll";
  for (const k of Object.keys(n))
    if (k !== "ty") walk(n[k], under || flat, hit);
};

const seeds = Number(process.argv[2] ?? 2000);
let progs = 0;
let withScanObs = 0;
let withUnderFlat = 0;
for (let s = 0; s < seeds; s++)
  for (const c of genTestCases(`d${s}`) as TestCase[]) {
    progs++;
    const hit = { scanObs: 0, scanObsUnderFlat: 0 };
    walk((c as unknown as Node).exp, false, hit);
    for (const sl of (c as unknown as { slots: Node[] }).slots)
      if (sl.type === "shared") walk(sl.def, false, hit);
    if (hit.scanObs > 0) withScanObs++;
    if (hit.scanObsUnderFlat > 0) withUnderFlat++;
  }
console.log(
  `${progs} programs: ${withScanObs} carry a scan at OBSERVABLE element type ` +
    `(${((100 * withScanObs) / progs).toFixed(2)}%), of which ` +
    `${withUnderFlat} sit under a flattener (${((100 * withUnderFlat) / progs).toFixed(2)}%)`,
);
