import { Observable } from "rxjs";
import { Closed, Ty, Val } from "./exp.js";
import { InstEmit } from "./inst-emit.js";

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

export type Inputs = ObservableInput<Val>[]; // one per Γ slot, index-aligned
export type Stream = InstEmit<Val>[]; // the flat canonical stream
export type Grouped = InstEmit<Val[]>[]; // batchSimultaneous's output: one record per instant — its prov + the values in emission order

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

// The Driver owns virtual time on the rx leg: one queue of pending
// deliveries keyed (tick, ordinal) — async input values AND defer-node
// hops — plus the current cascade id, which cold sync bursts inherit.
export type Driver = {
  // pop the min (tick, ordinal) delivery, mint its fresh id, run its
  // cascade synchronously to quiescence; false when the queue is empty
  deliverNextArrival: () => boolean;
};

declare const createDriver: () => Driver;

// hot: one Subject, async values registered at absolute ticks up
// front; cold: a defer factory — sync burst fires in the subscriber's
// instant, async values register relative to each subscription's tick
declare const makeInputSource: (
  driver: Driver,
  input: ObservableInput<Val>,
) => Observable<InstEmit<Val>>;

// the per-node switch delegating to the primitive-operators:
// evalTm/applyFn for of/map/scan/take, unfoldMu + a driver hop for
// mu/defer
declare const compile: (
  exp: Closed,
  driver: Driver,
  inputs: Observable<InstEmit<Val>>[],
) => Observable<InstEmit<Val>>;

const evaluateRx = async (testCase: TestCase): Promise<Stream> => {
  const driver = createDriver();
  const inputs = testCase.inputs.map((input) => makeInputSource(driver, input));
  const out: Stream = [];
  const sub = compile(testCase.exp, driver, inputs).subscribe((emit) => out.push(emit));
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
