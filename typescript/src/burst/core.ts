import * as r from "rxjs";
import {
  bump,
  clo,
  COLD,
  Delivery,
  Ev,
  fin,
  freshProv,
  hasFin,
  Inst,
  reg,
  stripFin,
  val,
} from "./protocol";

/**
 * The burst-batching primitives, implementing the semantics ratified in
 * agda/src/Burst.agda over the protocol ratified in agda/src/Protocol.agda.
 * See protocol.ts for the invariants each operator maintains.
 */

/** A root subject: one .next() call = one instant. Subscribing registers
 * the root; rxjs Subject fan-out order IS registration order (the ranked
 * delivery model). */
export class BurstSubject<A> {
  readonly prov = freshProv();
  private ended = false;
  private subj = new r.Subject<Delivery<A>>();
  readonly inst: Inst<A> = new r.Observable((sub) => {
    if (this.ended) {
      // a completed subject completes late subscribers immediately — the
      // fin is part of its history (concat legs behind it must advance)
      sub.next({ prov: COLD, events: [fin] });
      sub.complete();
      return;
    }
    sub.next({ prov: this.prov, events: [reg(this.prov)] });
    const s = this.subj.subscribe(sub);
    return () => s.unsubscribe();
  });
  next(v: A): void {
    this.subj.next({ prov: this.prov, events: [val(v)] });
  }
  /** drive end: the subject completes — its own instant, carried by a fin
   * delivery so completion cascades (concat advancement) coalesce into it */
  end(): void {
    this.ended = true;
    this.subj.next({ prov: this.prov, events: [fin] });
    this.subj.complete();
  }
}

/** cold source: emits everything inside its subscription frame, then is
 * done — no async roots, so no registration */
export const of = <A>(vs: A[]): Inst<A> =>
  new r.Observable((sub) => {
    sub.next({ prov: COLD, events: [...vs.map(val), fin] });
    sub.complete();
  });

export const empty = <A>(): Inst<A> => of<A>([]);

export const map =
  <A, B>(f: (a: A) => B) =>
  (src: Inst<A>): Inst<B> =>
    src.pipe(
      r.map((d) => ({
        prov: d.prov,
        events: d.events.map((ev): Ev<B> => (ev.t === "val" ? val(f(ev.v)) : ev)),
      })),
    );

export const scan =
  <A, B>(f: (acc: B, a: A) => B, z: B) =>
  (src: Inst<A>): Inst<B> => {
    return new r.Observable((sub) => {
      let acc = z;
      const s = src.subscribe({
        next(d) {
          sub.next({
            prov: d.prov,
            events: d.events.map((ev): Ev<B> => {
              if (ev.t !== "val") return ev;
              acc = f(acc, ev.v);
              return val(acc);
            }),
          });
        },
        error: (e) => sub.error(e),
        complete: () => sub.complete(),
      });
      return () => s.unsubscribe();
    });
  };

/** take counts VALUES, exactly like rxjs — even mid-batch. At the cut it
 * synthesizes closes for every registration it passed downstream and
 * finishes as part of the same delivery (the completion cascade carrier). */
export const take =
  (n: number) =>
  <A>(src: Inst<A>): Inst<A> =>
    new r.Observable((sub) => {
      if (n === 0) {
        // completes at subscription — still a fin, so a concat behind it
        // advances in the frame
        sub.next({ prov: COLD, events: [fin] });
        sub.complete();
        return;
      }
      let budget = n;
      let done = false;
      const liveRegs = new Map<number, number>();
      const s = src.subscribe({
        next(d) {
          if (done) return;
          const out: Ev<A>[] = [];
          for (const ev of d.events) {
            if (ev.t === "reg") {
              liveRegs.set(ev.p, (liveRegs.get(ev.p) ?? 0) + 1);
              out.push(ev);
            } else if (ev.t === "clo") {
              liveRegs.set(ev.p, Math.max(0, (liveRegs.get(ev.p) ?? 0) - 1));
              out.push(ev);
            } else if (ev.t === "fin") {
              out.push(ev);
              done = true;
            } else {
              if (budget > 0) {
                out.push(ev);
                budget--;
                if (budget === 0) {
                  for (const [p, c] of liveRegs)
                    for (let i = 0; i < c; i++) out.push(clo(p));
                  out.push(fin);
                  done = true;
                  break;
                }
              }
            }
          }
          sub.next({ prov: d.prov, events: out });
          if (done) sub.complete();
        },
        error: (e) => sub.error(e),
        complete() {
          if (!done) sub.complete();
        },
      });
      if (done) s.unsubscribe();
      return () => s.unsubscribe();
    });

/** merge: arms subscribe in argument order (expression order =
 * registration order); deliveries pass through; the merge finishes with
 * its LAST arm's fin (earlier fins are stripped — those arms are done but
 * the merge is not). */
export const merge = <A>(...srcs: Inst<A>[]): Inst<A> =>
  new r.Observable((sub) => {
    if (srcs.length === 0) {
      sub.next({ prov: COLD, events: [fin] });
      sub.complete();
      return;
    }
    let live = srcs.length;
    // count FINS, not completes: rxjs completes arrive only after every
    // .next() of the dispatch, so two arms finning in one instant would
    // both look non-final by live-count
    let finned = 0;
    const subs: r.Subscription[] = [];
    for (const src of srcs) {
      subs.push(
        src.subscribe({
          next(d) {
            if (!hasFin(d)) {
              sub.next(d);
              return;
            }
            finned++;
            sub.next(finned === srcs.length ? d : stripFin(d));
          },
          error: (e) => sub.error(e),
          complete() {
            live--;
            if (live === 0) sub.complete();
          },
        }),
      );
    }
    return () => subs.forEach((s) => s.unsubscribe());
  });

/** mergeMap (the mergeAll ∘ mapS join): each trigger VALUE spawns an
 * inner subscription; the inner's synchronous flush is COALESCED into the
 * trigger's delivery (its cause), so cascades batch with their trigger;
 * the inner's later deliveries pass through under their own roots. */
export const mergeMap =
  <A, B>(f: (a: A) => Inst<B>) =>
  (trigger: Inst<A>): Inst<B> =>
    new r.Observable((sub) => {
      let outerDone = false;
      // inners that have not FINNED yet (fin deliveries, not rxjs
      // completes — completes lag the deliveries within a dispatch)
      let pending = 0;
      let closed = false;
      const innerSubs = new Set<r.Subscription>();

      const spawn = (inner: Inst<B>, collect: Ev<B>[]): void => {
        pending++;
        let finned = false;
        const noteFin = (): void => {
          if (!finned) {
            finned = true;
            pending--;
          }
        };
        let inFlush = true;
        let sRef: r.Subscription | null = null;
        const s = inner.subscribe({
          next(d) {
            if (inFlush) {
              // the flush rides the trigger delivery, its cause
              if (hasFin(d)) noteFin();
              collect.push(...d.events.filter((ev) => ev.t !== "fin"));
              return;
            }
            if (!hasFin(d)) {
              sub.next(d);
              return;
            }
            noteFin();
            const events = d.events.filter((ev) => ev.t !== "fin");
            if (outerDone && pending === 0 && !closed) {
              // the last live inner finishes: the whole join finishes here
              closed = true;
              sub.next({ prov: d.prov, events: [...events, fin] });
              sub.complete();
            } else {
              sub.next({ prov: d.prov, events });
            }
          },
          error: (e) => sub.error(e),
          complete() {
            noteFin();
            if (sRef !== null) innerSubs.delete(sRef);
            if (!inFlush && outerDone && pending === 0 && !closed) {
              closed = true;
              sub.complete();
            }
          },
        });
        sRef = s;
        inFlush = false;
        if (!finned) innerSubs.add(s);
      };

      const outer = trigger.subscribe({
        next(d) {
          const out: Ev<B>[] = [];
          for (const ev of d.events) {
            if (ev.t === "val") spawn(f(ev.v), out);
            else if (ev.t === "fin") outerDone = true;
            else out.push(ev);
          }
          let finishes = false;
          if (outerDone && pending === 0 && !closed) {
            closed = true;
            finishes = true;
            out.push(fin);
          }
          sub.next({ prov: d.prov, events: out });
          if (finishes) sub.complete();
        },
        error: (e) => sub.error(e),
        complete() {
          outerDone = true;
          if (pending === 0 && !closed) {
            closed = true;
            sub.complete();
          }
        },
      });

      return () => {
        outer.unsubscribe();
        innerSubs.forEach((s) => s.unsubscribe());
      };
    });

/** concat: subscribe the next leg when the previous FINISHES — and graft
 * its synchronous flush into the fin-carrying delivery, so the final
 * value, the closes, and the queued leg's flush are ONE instant (the
 * completion cascade, Agda's concatAllT). */
export const concat2 = <A>(a: Inst<A>, b: Inst<A>): Inst<A> =>
  new r.Observable((sub) => {
    let bSub: r.Subscription | null = null;
    const aSub = a.subscribe({
      next(d) {
        if (!hasFin(d)) {
          sub.next(d);
          return;
        }
        // a finishes here: graft b's flush into this delivery
        const out = d.events.filter((ev) => ev.t !== "fin");
        const collected: Ev<A>[] = [];
        let inFlush = true;
        let bDoneInFlush = false;
        bSub = b.subscribe({
          next(db) {
            if (inFlush) collected.push(...db.events);
            else sub.next(db);
          },
          error: (e) => sub.error(e),
          complete() {
            if (inFlush) bDoneInFlush = true;
            else sub.complete();
          },
        });
        inFlush = false;
        sub.next({ prov: d.prov, events: [...out, ...collected] });
        if (bDoneInFlush) sub.complete();
      },
      error: (e) => sub.error(e),
      complete() {
        // complete without fin: a never finishes mid-delivery (subjects
        // don't complete); nothing to advance to
      },
    });
    return () => {
      aSub.unsubscribe();
      bSub?.unsubscribe();
    };
  });

export const concat = <A>(...srcs: Inst<A>[]): Inst<A> =>
  srcs.length === 0
    ? empty<A>()
    : srcs.reduce((acc, s) => concat2(acc, s));

/** switchAll over a synchronous burst of inners: each inner is subscribed
 * in turn — every inner's sync values pass — and switching away from a
 * live inner CUTS it, synthesizing closes for the registrations it passed
 * downstream (batch accounting must know its slots died). Only the last
 * inner stays live; the switch finishes with it. */
export const switchStatic = <A>(insts: Inst<A>[]): Inst<A> =>
  new r.Observable((sub) => {
    if (insts.length === 0) {
      sub.next({ prov: COLD, events: [fin] });
      sub.complete();
      return;
    }
    const subs: r.Subscription[] = [];
    for (let i = 0; i < insts.length; i++) {
      const isLast = i === insts.length - 1;
      const liveRegs = new Map<number, number>();
      const state = { cut: false };
      const s = insts[i].subscribe({
        next(d) {
          if (state.cut) return;
          for (const ev of d.events) {
            if (ev.t === "reg") bump(liveRegs, ev.p, 1);
            else if (ev.t === "clo") bump(liveRegs, ev.p, -1);
          }
          // a non-last inner's fin is not the switch's fin
          sub.next(isLast || !hasFin(d) ? d : stripFin(d));
        },
        error: (e) => sub.error(e),
        complete() {
          if (isLast) sub.complete();
        },
      });
      if (!isLast) {
        // switch away NOW: the inner had its subscription frame, its async
        // tail is cut
        state.cut = true;
        s.unsubscribe();
        const clos: Ev<A>[] = [];
        for (const [p, c] of liveRegs)
          for (let k = 0; k < c; k++) clos.push(clo(p));
        if (clos.length > 0) sub.next({ prov: COLD, events: clos });
      } else {
        subs.push(s);
      }
    }
    return () => subs.forEach((s) => s.unsubscribe());
  });

/** exhaustAll over a synchronous burst of inners: an arrival is dropped
 * only while the previously accepted inner is STILL OPEN — a synchronous
 * inner completes immediately and frees the slot, so of-then-of runs both.
 * Once an accepted inner stays open, every remaining arrival is dropped
 * for good (they arrived during it). */
export const exhaustStatic = <A>(insts: Inst<A>[]): Inst<A> =>
  new r.Observable((sub) => {
    if (insts.length === 0) {
      sub.next({ prov: COLD, events: [fin] });
      sub.complete();
      return;
    }
    let liveSub: r.Subscription | null = null;
    let idx = 0;
    while (idx < insts.length) {
      const hasMoreArrivals = idx < insts.length - 1;
      let inFlush = true;
      let finnedInFlush = false;
      let completedInFlush = false;
      const s = insts[idx].subscribe({
        next(d) {
          if (!hasFin(d)) {
            sub.next(d);
            return;
          }
          if (inFlush) {
            finnedInFlush = true;
            // strip iff another arrival will be accepted after this one
            sub.next(hasMoreArrivals ? stripFin(d) : d);
          } else {
            // an async fin: no arrivals remain by construction — the
            // exhaust finishes here
            sub.next(d);
          }
        },
        error: (e) => sub.error(e),
        complete() {
          if (inFlush) completedInFlush = true;
          else sub.complete();
        },
      });
      inFlush = false;
      if (finnedInFlush) {
        if (!hasMoreArrivals && completedInFlush) sub.complete();
        idx++;
      } else {
        // stays open: the remaining arrivals came during it — dropped
        liveSub = s;
        break;
      }
    }
    return () => liveSub?.unsubscribe();
  });

/** share, with rxjs LIVES (ratified 2026-07-07): connect on first
 * subscriber, reset when the source completes or the refcount drains to
 * zero, reconnect-and-replay for a subscriber arriving after a reset.
 * rxjs share() provides the lives natively; the wrapper adds
 * counting-transparency — a late subscriber registers the ROOTS feeding
 * the share (the connecting subscriber's registrations flow through the
 * connection frame itself). */
export const share = <A>(src: Inst<A>): Inst<A> => {
  // live root registrations seen through the current connection
  let roots = new Map<number, number>();
  let connected = false;
  const reset = (): void => {
    connected = false;
    roots = new Map();
  };
  const shared = src.pipe(
    r.tap({
      next: (d) => {
        for (const ev of d.events) {
          if (ev.t === "reg") roots.set(ev.p, (roots.get(ev.p) ?? 0) + 1);
          else if (ev.t === "clo")
            roots.set(ev.p, Math.max(0, (roots.get(ev.p) ?? 0) - 1));
        }
      },
      complete: reset,
    }),
    r.share(),
  );
  let refCount = 0;
  return new r.Observable((sub) => {
    const late = connected;
    connected = true;
    refCount++;
    if (late) {
      // registration-only replay: a late subscriber taps the same roots
      const events: Ev<A>[] = [];
      for (const [p, c] of roots)
        for (let i = 0; i < c; i++) events.push(reg(p));
      if (events.length > 0) sub.next({ prov: COLD, events });
    }
    const s = shared.subscribe(sub);
    return () => {
      s.unsubscribe();
      refCount--;
      if (refCount === 0) reset();
    };
  });
};
