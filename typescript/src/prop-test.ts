import { Observable, firstValueFrom, merge, of, toArray } from "rxjs";
import { Closed, Ty, Val } from "./exp.js";
import { InstEmit, Provenance, SourceId } from "./inst-emit.js";
import { materializeCompletion, share } from "./primitive-operators.js";
import { batchSimultaneous } from "./batch-simultaneous.js";
import { createDriver } from "./driver.js";
import { makeInputSource } from "./input-source.js";
import { compile } from "./compile.js";
import { genSeeds, genTestCases } from "./generator.js";
import { serialize } from "./serialize.js";
import { execAgda } from "./agda-bridge.js";

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

// one program's two outputs: the raw InstEmit stream the exp tree
// produced, and that same stream folded through batchSimultaneous. Both
// sides (TS-here and Agda-via-CLI) return this pair per case.
export type EvalResult = { stream: Stream; batches: Grouped };

// The serializable unit of differential testing: a whole program.
// ctx is Γ — the types of the slots, index-aligned with slots.
export type TestCase = {
  ctx: Ty[];
  exp: Closed;
  slots: Slots;
  fuel: Fuel;
};

// CLI flags biasing the run: `--operator <op>` features that operator at
// the root of every generated program (the generator ignores an unknown
// name); `--seed <s>` pins a single seed, else the full genSeeds() sweep.
// Both accept `--flag value` and `--flag=value`; absent ⇒ undefined.
const readFlag = (name: string): string | undefined => {
  const argv = process.argv.slice(2);
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === `--${name}`) {
      const next = argv[i + 1];
      return next !== undefined && !next.startsWith("--") ? next : undefined;
    }
    if (arg.startsWith(`--${name}=`)) return arg.slice(name.length + 3);
  }
  return undefined;
};
const readOperatorFromCli = (): string | undefined => readFlag("operator");
const readSeedFromCli = (): string | undefined => readFlag("seed");


// createDriver (virtual time, the one impure edge), makeInputSource
// (scripted slots → protocol streams), and compile (the per-node
// switch onto the primitive-operators) live in their own modules.

const evaluateRx = async (testCase: TestCase): Promise<EvalResult> => {
  const driver = createDriver();
  // the const telescope, literally: each shared slot compiles against
  // the prefix of already-built slots and connects through the
  // protocol share (all resets false; source id = slot index)
  const slotSources = testCase.slots.reduce<Observable<InstEmit<Val>>[]>(
    (prefix, slot, index) => [
      ...prefix,
      slot.type === "scripted"
        ? makeInputSource(driver, slot.input)
        : share(driver, compile(slot.def, driver, prefix), index),
    ],
    [],
  );
  const out: Stream = [];
  // the canonical root stream: the pipeline's emits interleaved (in
  // push order) with the shares' chain emits, the fin bit materialized
  // once over the merged ledger — the mirror of Agda's cascade output
  const sub = materializeCompletion<Val>(
    merge(driver.chainEmits, compile(testCase.exp, driver, slotSources)),
  ).subscribe((emit) => out.push(emit));
  // subscribing already ran the root sync burst — fuel pays only for arrivals
  for (let spent = 0; spent < testCase.fuel; spent++) {
    if (!driver.deliverNextArrival()) break;
  }
  sub.unsubscribe();
  // the batched twin: hand the finite raw stream to plain rxjs `of`, run
  // it through the same batchSimultaneous operator the Agda side folds
  // with, and toArray it back — so we hold both the raw emits and the
  // fully batched result for the same program.
  const batches = await firstValueFrom(
    of(...out).pipe(batchSimultaneous<Val>(), toArray()),
  );
  return { stream: out, batches };
};

// Streams are compared up to id renaming (≈): the ids' only meaning is
// the partition structure, so canonicalize both sides before comparing.
// Instants and sources are separate namespaces (an arrival's cascade vs
// an observable), each renamed to 0,1,2,… in first-appearance order over
// the flat stream. This also erases the representation gap — TS mints ids
// as `symbol` (dropped by JSON.stringify), Agda as ℕ — since each side is
// renamed independently to the same integers. Values/kinds/event
// types/order still compare exactly.
const canonical = <A>(stream: InstEmit<A>[]): unknown => {
  const inst = new Map<Provenance, number>();
  const src = new Map<SourceId, number>();
  const ri = (id: Provenance): number =>
    inst.has(id) ? inst.get(id)! : (inst.set(id, inst.size), inst.size - 1);
  const rs = (id: SourceId): number =>
    src.has(id) ? src.get(id)! : (src.set(id, src.size), src.size - 1);
  return stream.map((emit) => ({
    kind: emit.kind,
    instant: ri(emit.instant),
    source: rs(emit.source),
    events: emit.events.map((ev) =>
      ev.type === "value" || ev.type === "complete"
        ? ev
        : { ...ev, source: rs(ev.source) },
    ),
  }));
};

// Structural equality up to id renaming.
const sameStream = <A>(a: InstEmit<A>[], b: InstEmit<A>[]): boolean =>
  JSON.stringify(canonical(a)) === JSON.stringify(canonical(b));

// Compare the Agda (oracle) and rxjs results case by case, on BOTH the
// raw stream and the batched output, and render a compact report.
const interpretResults = (
  agdaResults: EvalResult[],
  rxResults: EvalResult[],
): string => {
  const n = Math.min(agdaResults.length, rxResults.length);
  const lines: string[] = [];
  let streamOk = 0;
  let batchOk = 0;
  for (let i = 0; i < n; i++) {
    const a = agdaResults[i];
    const r = rxResults[i];
    const sEq = sameStream(a.stream, r.stream);
    const bEq = sameStream(a.batches, r.batches);
    if (sEq) streamOk++;
    if (bEq) batchOk++;
    if (!sEq || !bEq) {
      lines.push(`case ${i}: ${sEq ? "stream ✓" : "stream ✗"} ${bEq ? "batches ✓" : "batches ✗"}`);
      if (!sEq) {
        lines.push(`  agda.stream  = ${JSON.stringify(canonical(a.stream))}`);
        lines.push(`  rx.stream    = ${JSON.stringify(canonical(r.stream))}`);
      }
      if (!bEq) {
        lines.push(`  agda.batches = ${JSON.stringify(canonical(a.batches))}`);
        lines.push(`  rx.batches   = ${JSON.stringify(canonical(r.batches))}`);
      }
    }
  }
  const header =
    `${n} cases: stream ${streamOk}/${n} match, batches ${batchOk}/${n} match` +
    (agdaResults.length !== rxResults.length
      ? ` (LENGTH MISMATCH: agda ${agdaResults.length}, rx ${rxResults.length})`
      : "");
  return [header, ...lines].join("\n");
};

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
