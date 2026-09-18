import { Observable } from "rxjs";

// VIRTUAL TIME FOR THE PLAIN LEG, AND NOTHING ELSE. This is the
// envelope-free twin of `driver.ts`: the same (tick, ordinal)
// arbitration, none of the protocol. A source id, a cascade instant and
// a chain-emit channel are all things the ENVELOPE needs; a plain rxjs
// pipeline has no notion of any of them, so the oracle's plain leg must
// be able to run without one, and this is what "run without one" means
// concretely.
//
// WHY A SCHEDULER AT ALL, when the point is to be plain rxjs. Because
// the scripted inputs are written in ticks and the run is bounded by a
// count of ARRIVALS rather than by a frame number, which is not what
// rxjs's own VirtualTimeScheduler is bounded by (`maxFrames` counts
// time, and a run that must stop after exactly n deliveries cannot say
// so in frames). Virtual time is the harness's, not the library's: an
// rxjs program under test is unchanged by being driven this way, which
// is the whole difference between a scheduler and a protocol.
export type PlainDriver = {
  // anchor for per-subscription scheduling: a cold's async tail
  // re-anchors here, and a defer hop is this plus one
  currentTick: () => number;
  // register one source's deliveries at ABSOLUTE ticks, strictly
  // increasing. The ordinal breaks ties between sources due at the same
  // tick, and it is minted in registration order except where the
  // caller owns one already — a hot slot does, because Agda gives slot
  // i the ordinal `toℕ i` and starts the dynamic counter above the
  // slots. Minted here instead, a hot's ordinal would count the HOTS,
  // so a shared slot ahead of a hot one shifts every later ordinal down
  // and the arbitration order diverges from Agda's.
  // Returns a cancel: rx teardown drops what is still pending.
  registerSource: (
    pending: { tick: number; fire: (isLast: boolean) => void }[],
    ordinal?: number,
  ) => () => void;
  // pop the min (tick, ordinal) delivery and run its cascade
  // synchronously to quiescence; false when nothing is pending
  deliverNextArrival: () => boolean;
};

type RegisteredSource = {
  ordinal: number;
  pending: { tick: number; fire: (isLast: boolean) => void }[];
};

export const createPlainDriver = (slotCount = 0): PlainDriver => {
  const sources: RegisteredSource[] = [];
  let nextOrdinal = slotCount;
  // the root subscription's frame is tick 0
  let tick = 0;

  return {
    currentTick: () => tick,
    registerSource: (pending, ordinal) => {
      const entry: RegisteredSource = {
        ordinal: ordinal ?? nextOrdinal++,
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
      head.fire(next.pending.length === 0);
      return true;
    },
  };
};

// a one-shot delivery at a given tick: the async boundary under
// `defer`. Teardown cancels a hop that has not fired.
export const plainHop = (driver: PlainDriver, tick: number): Observable<void> =>
  new Observable<void>((sink) =>
    driver.registerSource([
      {
        tick,
        fire: () => {
          sink.next();
          sink.complete();
        },
      },
    ]),
  );
