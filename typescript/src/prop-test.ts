import { Observable } from "rxjs";
import { Closed, Ty, Val } from "./exp.js";
import { InstEmit } from "./inst-emit.js";
import { share } from "./primitive-operators.js";
import { createDriver } from "./driver.js";
import { makeInputSource } from "./input-source.js";
import { compile } from "./compile.js";

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
  sync: A[]; // fired immediately on subscription, inside the subscriber's instant (id-inheritance)
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

export type Stream = InstEmit<Val>[]; // the flat canonical stream
export type Grouped = InstEmit<Val[]>[]; // batchSimultaneous's output: one emit per instant, still a protocol citizen (re-batchable)

// The serializable unit of differential testing: a whole program.
// ctx is Γ — the types of the slots, index-aligned with slots.
export type TestCase = {
  ctx: Ty[];
  exp: Closed;
  slots: Slots;
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

// createDriver (virtual time, the one impure edge), makeInputSource
// (scripted slots → protocol streams), and compile (the per-node
// switch onto the primitive-operators) live in their own modules.

const evaluateRx = async (testCase: TestCase): Promise<Stream> => {
  const driver = createDriver();
  // the const telescope, literally: each shared slot compiles against
  // the prefix of already-built slots and connects through the
  // protocol share (all resets false; source id = slot index)
  const slotSources = testCase.slots.reduce<Observable<InstEmit<Val>>[]>(
    (prefix, slot, index) => [
      ...prefix,
      slot.type === "scripted"
        ? makeInputSource(driver, slot.input)
        : share(compile(slot.def, driver, prefix), index),
    ],
    [],
  );
  const out: Stream = [];
  const sub = compile(testCase.exp, driver, slotSources).subscribe((emit) => out.push(emit));
  // subscribing already ran the root sync burst — fuel pays only for arrivals
  for (let spent = 0; spent < testCase.fuel; spent++) {
    if (!driver.deliverNextArrival()) break;
  }
  sub.unsubscribe();
  return out;
};

// Streams are compared up to id renaming (≈): partition structure is
// the only meaning the ids have.
declare const interpretResults: (
  agdaResults: Stream[],
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
  console.log(interpretResults(agdaResults, rxResults));
}

main();
