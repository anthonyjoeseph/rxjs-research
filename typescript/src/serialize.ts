import type { TestCase } from "./prop-test.js";

// The corpus / bridge format. A TestCase is already plain tagged-union
// data — Ty/Exp/Tm/Val all carry a `type` discriminant and JSON-safe
// fields (pairs are arrays, obs values are Exp objects), and every node
// carries its result Ty — so a faithful, complete encoding is just JSON.
// One line per case (NDJSON-friendly); the Agda decoder re-checks
// well-typedness and μ-guardedness against these tags, then evaluates.
export const serialize = (testCase: TestCase): string =>
  JSON.stringify(testCase);
