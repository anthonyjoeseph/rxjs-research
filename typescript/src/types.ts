import * as r from "rxjs";

/**
 * THE PROTOCOL (ratified in agda/src/Protocol.agda): what flows between
 * operators. No timestamps anywhere — that is the point. Batching is
 * decided downstream by counting registrations, never by comparing clocks.
 *
 *   init p    a subscription chain of ROOT provenance p came alive
 *   value v   a value
 *   close p   a registration of root p ended (take cuts, switches away)
 *   fin       this stream completes as part of THIS emit — the carrier of
 *             completion cascades (concatAll advances by grafting the next
 *             inner's synchronous flush into the fin-carrying emit)
 *
 * An InstEmit is what one downstream .next() carries: the root provenance
 * of the registration it travels through, plus its events.
 *
 * Invariants every operator maintains (the truthfulness invariant, OkTrace
 * in the Agda):
 *  - registrations are counted per ROOT-CAUSE provenance; share is
 *    counting-transparent (each subscriber registers the roots feeding it);
 *  - for each async root event, each live registration chain of that root
 *    forwards EXACTLY ONE emit (possibly valueless — emits are emptied,
 *    never swallowed), with the root's provenance at the head;
 *  - everything caused by one incoming emit is COALESCED into the one
 *    outgoing emit (spawned inners' synchronous flushes ride their
 *    trigger's emit; a queued concatAll inner's flush rides the closing
 *    emit).
 */
export type InstInit = { type: "init"; provenance: number };
export type InstVal<A> = { type: "value"; value: A };
export type InstClose = { type: "close"; provenance: number };
export type InstFin = { type: "fin" };

export type InstEv<A> = InstInit | InstVal<A> | InstClose | InstFin;

export type InstEmit<A> = { provenance: number; events: InstEv<A>[] };

/** An Instantaneous observable: an rxjs Observable of protocol emits. */
export type Instantaneous<A> = r.Observable<InstEmit<A>>;

let provCounter = 0;
export const freshProvenance = (): number => ++provCounter;

/** provenance of emits that never key an async window (cold flushes,
 * late-ref registrations — they always ride inside a frame or a trigger's
 * window) */
export const COLD = -1;

export const init = (provenance: number): InstEv<never> => ({
  type: "init",
  provenance,
});
export const val = <A>(value: A): InstEv<A> => ({ type: "value", value });
export const close = (provenance: number): InstEv<never> => ({
  type: "close",
  provenance,
});
export const fin: InstEv<never> = { type: "fin" };

export const hasFin = <A>(e: InstEmit<A>): boolean =>
  e.events.some((ev) => ev.type === "fin");

export const stripFin = <A>(e: InstEmit<A>): InstEmit<A> => ({
  provenance: e.provenance,
  events: e.events.filter((ev) => ev.type !== "fin"),
});

export const values = <A>(events: readonly InstEv<A>[]): A[] =>
  events.flatMap((ev) => (ev.type === "value" ? [ev.value] : []));

export const bumpCount = (
  m: Map<number, number>,
  p: number,
  delta: number,
): void => {
  const next = (m.get(p) ?? 0) + delta;
  if (next <= 0) m.delete(p);
  else m.set(p, next);
};
