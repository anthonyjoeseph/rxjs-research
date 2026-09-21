// RUNNING AN AUTHOR'S PROGRAM, the way the Agda development does it.
//
// THE WHOLE POINT IS THAT THERE IS NO SIMUL EVALUATOR. `evaluateSExp`
// does not interpret an `SExp`; it ELABORATES one and hands the result
// to the plain evaluator that already exists. That is exactly the Agda
// shape --
//
//   formal-verification-batchSimultaneous  runs  evaluate (elaborate e)
//
// -- and it is why the proof's obligations land where they do. The
// evaluator is never asked to be correct about the protocol, because it
// has never heard of the protocol; what must be correct is the
// TRANSLATION, and that is one function with one clause per author
// former.
//
// THE SLOTS ARE ORDINARY PLAIN SLOTS, and this is the part worth
// staring at. `evaluatePlain` builds each slot source itself: a
// scripted slot becomes a bare rxjs stream, and a shared slot compiles
// its PLAIN definition under a never-resetting `share`. Nothing in the
// table is elaborated, and nothing in it carries an envelope. Every
// envelope in the run is put there by `inputP` at the REFERENCE site.
//
// AND THAT IS WHERE THE AGDA DIFFICULTY LIVES. Because the table holds
// plain trees, a shared slot at an observable type can hold a stream of
// observables that the elaboration never built -- and a `mergeAll` on
// the reference will subscribe them directly, so whatever they emit
// reaches the wire having never passed through `inputP`. Nothing about
// the AUTHOR'S program can see that; the forgery is in the table. On
// the Agda side that is what the palette parameter is for.

import type { Val } from "../exp.js";
import { evaluatePlain } from "../plain-eval.js";
import type { Slots, TestCase } from "../prop-test.js";
import type { Fuel } from "../prop-test.js";
import type { Ty } from "../exp.js";
import type { ClosedSExp } from "./s-exp.js";
import { elaborate } from "./to-plain.js";

// the same unit as `TestCase`, with the author's tree at the root. The
// slots are UNCHANGED -- plain, non-simul, index-aligned with `ctx`.
export type SExpTestCase = {
  ctx: Ty[];
  exp: ClosedSExp;
  slots: Slots;
  fuel: Fuel;
};

// ELABORATE, THEN RUN. The whole simul layer is the first argument to
// `evaluatePlain`, and there is nothing else to it.
export const evaluateSExp = (testCase: SExpTestCase): Val[] => {
  const elaborated: TestCase = {
    ctx: testCase.ctx,
    exp: elaborate(testCase.exp),
    slots: testCase.slots,
    fuel: testCase.fuel,
  };
  return evaluatePlain(elaborated);
};
