import { Closed, Val } from "./exp.js";
import { InstEmit, Provenance } from "./inst-emit.js";

// The mirror evaluator — structural twin of Agda's Rx.Evaluator.
// Everything below this file's signatures runs SYNCHRONOUSLY in
// virtual time: no promises, no queueMicrotask, no real-JS time.

export type Tick = number;
export type Fuel = number;
export type Ordinal = number;

export type Timed<A> = {
  wait: number; // gap = wait + 1, so per-source ticks are strictly increasing by construction
  val: A;
};

export type ObservableInputCold<A> = {
  type: "cold";
  sync: A[]; // fired immediately on subscription, inside the subscriber's instant (id-inheritance)
  async: Timed<A>[]; // anchored at the subscription tick
};

export type ObservableInputHot<A> = {
  type: "hot";
  async: Timed<A>[]; // anchored at tick 0
};

export type ObservableInput<A> = ObservableInputCold<A> | ObservableInputHot<A>;

export type Inputs = ObservableInput<Val>[]; // one per Γ slot, index-aligned
export type Stream = InstEmit<Val>[]; // the flat canonical stream
export type Grouped = InstEmit<Val>[][]; // batchSimultaneous's output

// Agda: freshId — deterministic minting from arrival identity. Mint
// from arbitration-order position (ordinal rank), not the raw tick, so
// timing-invariance holds with ≡; on this leg ids are numbers.
export declare const freshId: (tick: Tick, ordinal: Ordinal) => Provenance;

// Opaque twins of Agda's postulated state types. Whatever shapes they
// take must be serializable: step-level differential tests feed
// identical (state, event) pairs to both languages, and subscription-
// timing bugs hide unless node states are exposed to the serializer.
declare const schedBrand: unique symbol;
declare const arrivalBrand: unique symbol;
declare const evalStBrand: unique symbol;

// Live sources with pending arrivals keyed (tick, ordinal): hots at
// anchor 0, colds at their subscription tick, defer bodies at tick+1;
// ordinals minted in subscription order. Intended per-source shape:
// { ordinal: Ordinal; pending: [Tick, Val][] }.
export type Sched = { readonly [schedBrand]: never };
export type Arrival = { readonly [arrivalBrand]: never };
export type EvalSt = { readonly [evalStBrand]: never }; // all node states, incl. dynamically subscribed inners

export declare const schedInit: (root: Closed, inputs: Inputs) => Sched;
export declare const schedNext: (
  sched: Sched,
) => [Arrival, Sched] | null; // pure min by (tick, ordinal) — this ordering IS the semantics
export declare const arrTick: (arrival: Arrival) => Tick;
export declare const arrOrd: (arrival: Arrival) => Ordinal;

// Agda: subscribeE — called by evaluator clauses that subscribe things
// (*All operators on inner arrival, defer bodies, μ-unfolding). Fires
// the target's sync burst NOW, inside cascade `id` (id-inheritance is
// literally this argument being reused); resolves cold deltas to
// absolute ticks; registers the async future under a fresh ordinal.
export declare const subscribeE: (
  target: Closed,
  id: Provenance,
  now: Tick,
  sched: Sched,
  st: EvalSt,
) => [Stream, Sched, EvalSt];

// fuel = ARRIVALS PROCESSED. Each arrival's cascade runs to
// quiescence, never truncated mid-batch; work within an instant
// terminates structurally. Keep the driver literally
// `for (let i = 0; i < fuel; i++) processNextArrival()` so the unit
// cannot drift from the Agda side.
export declare const evaluate: (
  fuel: Fuel,
  root: Closed,
  inputs: Inputs,
) => Stream;
