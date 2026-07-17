import { Provenance, SourceId } from "./inst-emit.js";

// One scheduled delivery popped by the driver. Mirrors Agda's Arrival,
// minus the fields the fire-closure already captures (source, payload).
export type Arrival = {
  instant: Provenance; // freshly minted for this arrival's cascade
  isLast: boolean; // final pending entry of its source ⇒ the source completes with this delivery
};

// The Driver owns virtual time on the rx leg — the mirror of Agda's
// Sched, and the ONE sanctioned mutable/impure edge of the TS side
// (everything else delegates statefulness to rxjs operators). It holds
// the pending deliveries keyed (tick, ordinal) — async input values
// AND defer-node hops — plus the current cascade id, which sync
// subscription work (cold bursts, init emits) inherits.
export type Driver = {
  // ---- rx-leg internals (used by makeInputSource / compile) ----
  // fresh SourceId; Symbols compare only by identity, matching the
  // harness's comparison up to renaming (Agda mints ℕs — same order,
  // different carrier)
  mintSourceId: () => SourceId;
  // the instant sync work belongs to: the running arrival's cascade
  // id, or the root subscribe-frame id before any arrival
  // (id-inheritance is literally reading this)
  currentInstant: () => Provenance;
  // anchor for per-subscription scheduling (cold async tails, deferᵉ
  // hops at tick + 1)
  currentTick: () => number;
  // register one source's scripted deliveries (absolute ticks,
  // strictly increasing). The source's ordinal is minted in
  // registration order — Agda's subscription-order convention; the
  // total (tick, ordinal) arbitration order is what must match, not
  // the ordinal values. Returns a cancel: rx teardown drops the
  // remaining deliveries (Agda's sweepLive).
  registerSource: (
    pending: { tick: number; fire: (arrival: Arrival) => void }[],
  ) => () => void;
  // ---- harness surface ----
  // pop the min (tick, ordinal) delivery, mint its fresh instant, run
  // its cascade synchronously to quiescence; false when the queue is
  // empty. Mirrors Agda's sched-next + cascade step.
  deliverNextArrival: () => boolean;
};

type RegisteredSource = {
  ordinal: number;
  pending: { tick: number; fire: (arrival: Arrival) => void }[];
};

export const createDriver = (): Driver => {
  const sources: RegisteredSource[] = [];
  let nextOrdinal = 0;
  let nextSourceId = 0;
  // the root subscription's frame: tick 0, its own instant (Agda:
  // subscribeE e root (freshId 0 0) 0 …)
  let instant: Provenance = Symbol("subscribe-frame");
  let tick = 0;

  return {
    mintSourceId: () => Symbol(`source:${nextSourceId++}`),
    currentInstant: () => instant,
    currentTick: () => tick,
    registerSource: (pending) => {
      const entry: RegisteredSource = {
        ordinal: nextOrdinal++,
        pending: [...pending],
      };
      sources.push(entry);
      return () => {
        entry.pending = [];
      };
    },
    deliverNextArrival: () => {
      // min by (tick, ordinal); ordinals are unique, so no tie survives
      const next = sources.reduce<RegisteredSource | undefined>(
        (best, s) =>
          s.pending.length > 0 &&
          (best === undefined ||
            s.pending[0].tick < best.pending[0].tick ||
            (s.pending[0].tick === best.pending[0].tick &&
              s.ordinal < best.ordinal))
            ? s
            : best,
        undefined,
      );
      if (next === undefined) return false;
      const head = next.pending[0];
      next.pending = next.pending.slice(1);
      tick = head.tick;
      instant = Symbol(`arrival:${head.tick}:${next.ordinal}`);
      head.fire({ instant, isLast: next.pending.length === 0 });
      return true;
    },
  };
};
