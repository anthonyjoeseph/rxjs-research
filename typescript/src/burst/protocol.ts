import * as r from "rxjs";

/**
 * THE PROTOCOL (ratified in agda/src/Protocol.agda): what flows between
 * operators. No timestamps anywhere — that is the point. Batching is
 * decided downstream by counting registrations, never by comparing clocks.
 *
 *   reg p   a subscription chain of ROOT provenance p came alive
 *   val v   a value
 *   clo p   a registration of root p ended (take cuts, switches away)
 *   fin     this stream completes as part of THIS delivery — the carrier
 *           of completion cascades (concat advances by grafting the next
 *           leg's synchronous flush into the fin-carrying delivery)
 *
 * A Delivery is what one downstream .next() carries: the root provenance
 * of the registration it travels through, plus its events.
 *
 * Invariants every operator maintains (the truthfulness invariant, OkTrace
 * in the Agda):
 *  - registrations are counted per ROOT-CAUSE provenance; share is
 *    counting-transparent (each subscriber registers the roots feeding it);
 *  - for each async root event, each live registration chain of that root
 *    forwards EXACTLY ONE delivery (possibly valueless — deliveries are
 *    emptied, never swallowed), with the root's provenance as head prov;
 *  - everything caused by one incoming delivery is COALESCED into the one
 *    outgoing delivery (spawned inners' synchronous flushes ride their
 *    trigger's delivery; a queued concat leg's flush rides the closing
 *    delivery).
 */
export type Ev<A> =
  | { t: "reg"; p: number }
  | { t: "val"; v: A }
  | { t: "clo"; p: number }
  | { t: "fin" };

export type Delivery<A> = { prov: number; events: Ev<A>[] };

/** An Instantaneous observable: an rxjs Observable of protocol deliveries. */
export type Inst<A> = r.Observable<Delivery<A>>;

let provCounter = 0;
export const freshProv = (): number => ++provCounter;

/** provenance of deliveries that never key an async window (cold flushes,
 * late-ref registrations — they always ride inside a frame or a trigger's
 * window) */
export const COLD = -1;

export const reg = (p: number): Ev<never> => ({ t: "reg", p });
export const val = <A>(v: A): Ev<A> => ({ t: "val", v });
export const clo = (p: number): Ev<never> => ({ t: "clo", p });
export const fin: Ev<never> = { t: "fin" };

export const hasFin = <A>(d: Delivery<A>): boolean =>
  d.events.some((ev) => ev.t === "fin");

export const stripFin = <A>(d: Delivery<A>): Delivery<A> => ({
  prov: d.prov,
  events: d.events.filter((ev) => ev.t !== "fin"),
});

export const valsOf = <A>(events: Ev<A>[]): A[] => {
  const out: A[] = [];
  for (const ev of events) if (ev.t === "val") out.push(ev.v);
  return out;
};

export const bump = (m: Map<number, number>, p: number, delta: number): void => {
  const next = (m.get(p) ?? 0) + delta;
  if (next <= 0) m.delete(p);
  else m.set(p, next);
};
