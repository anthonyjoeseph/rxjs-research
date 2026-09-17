import { Observable } from "rxjs";
import { InstEmit, Provenance } from "./inst-emit.js";
import { channel, producer } from "./constructors.js";

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
  mintSourceId: () => number;
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
  // a share's chain emits (the emptied pass-through carrying the
  // handoff — Agda foldPath's share-sink clause) reach the root
  // stream directly, not through any subscriber's pipeline: shares
  // push here, the harness merges this channel into the collected
  // stream. Valueless by construction, hence InstEmit<never>.
  pushChainEmit: (emit: InstEmit<never>) => void;
  chainEmits: Observable<InstEmit<never>>;
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

// `slotCount` RESERVES the first that many source ids for the slots,
// which is not a convention this file is free to pick: a hot's source
// IS its slot index and a shared slot connects under its own, so the
// counter has to start above them or a minted source collides with a
// slot's. Agda says the same thing in one line (`mint-init n`, at both
// the source and ordinal keys) and the two must agree, since the oracle
// compares the streams up to renaming and a COLLAPSE is not a renaming
// -- two sources that became one cannot be renamed back apart.
export const createDriver = (slotCount = 0): Driver => {
  const sources: RegisteredSource[] = [];
  let nextOrdinal = 0;
  let nextSourceId = slotCount;
  // the root subscription's frame: tick 0, its own instant (Agda:
  // subscribeE e root (freshId 0 0) 0 …)
  let instant: Provenance = Symbol("subscribe-frame");
  let tick = 0;
  const [chainEmits, chainSink] = channel<InstEmit<never>>();

  return {
    // a NUMBER, because Agda's uniqᵗ reads as ℕ and `mint` is the first
    // thing that hands a token to a program rather than to the protocol.
    // Nothing else produces a SourceId, so this counter is the whole
    // namespace and a numeric one cannot collide.
    mintSourceId: () => nextSourceId++,
    pushChainEmit: (emit) => chainSink.next(emit),
    chainEmits,
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

// a one-shot driver delivery at a given tick, read per subscription —
// the async boundary under deferᵉ/μᵉ. Teardown cancels the pending hop
// (unsubscribing a not-yet-fired defer is free — Agda's sweepLive).
// It carries no source lifecycle and mints nothing, which is why it is
// a bare producer rather than either source constructor: what an
// operator wants from it is the ARRIVAL, and the emit that arrival
// causes is the operator's own to mint.
export const oneShotArrival = (
  driver: Driver,
  tick: number,
): Observable<Arrival> =>
  producer<Arrival>((sink) =>
    driver.registerSource([
      {
        tick,
        fire: (arrival) => {
          sink.next(arrival);
          sink.complete();
        },
      },
    ]),
  );
