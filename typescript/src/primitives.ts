import * as r from "rxjs";
import {
  bumpCount,
  close,
  COLD,
  fin,
  freshProvenance,
  hasFin,
  init,
  InstEmit,
  InstEv,
  Instantaneous,
  val,
} from "./types";

/**
 * The canonical primitives, implementing the semantics ratified in
 * agda/src/Burst.agda over the protocol ratified in agda/src/Protocol.agda:
 *
 *   of, empty, map, take, scan, share,
 *   mergeAll, concatAll, switchAll, exhaustAll
 *
 * The *All joins consume streams OF streams (`Instantaneous<Instantaneous>`),
 * exactly like the Agda's two-sorted grammar — and `merge`, `concat` and
 * `mergeMap` are DERIVED one-liners at the bottom of this file, never
 * primitives. See types.ts for the protocol invariants each operator
 * maintains.
 */

/** A root subject: one .next() call = one instant. Subscribing registers
 * the root; rxjs Subject fan-out order IS registration order (the ranked
 * delivery model). */
export class InstantSubject<A> {
  readonly provenance = freshProvenance();
  private ended = false;
  private subj = new r.Subject<InstEmit<A>>();
  readonly inst: Instantaneous<A> = new r.Observable((sub) => {
    if (this.ended) {
      // a completed subject completes late subscribers immediately — the
      // fin is part of its history (concat legs behind it must advance)
      sub.next({ provenance: COLD, events: [fin] });
      sub.complete();
      return;
    }
    sub.next({ provenance: this.provenance, events: [init(this.provenance)] });
    const s = this.subj.subscribe(sub);
    return () => s.unsubscribe();
  });
  next(v: A): void {
    this.subj.next({ provenance: this.provenance, events: [val(v)] });
  }
  /** drive end: the subject completes — its own instant, carried by a fin
   * emit so completion cascades (concatAll advancement) coalesce into it */
  end(): void {
    this.ended = true;
    this.subj.next({ provenance: this.provenance, events: [fin] });
    this.subj.complete();
  }
}

/** cold source: emits everything inside its subscription frame, then is
 * done — no async roots, so no registration */
export const of = <A>(vs: A[]): Instantaneous<A> =>
  new r.Observable((sub) => {
    sub.next({ provenance: COLD, events: [...vs.map(val), fin] });
    sub.complete();
  });

export const empty = <A>(): Instantaneous<A> => of<A>([]);

export const map =
  <A, B>(f: (a: A) => B) =>
  (src: Instantaneous<A>): Instantaneous<B> =>
    src.pipe(
      r.map((e) => ({
        provenance: e.provenance,
        events: e.events.map(
          (ev): InstEv<B> => (ev.type === "value" ? val(f(ev.value)) : ev),
        ),
      })),
    );

export const scan =
  <A, B>(f: (acc: B, a: A) => B, z: B) =>
  (src: Instantaneous<A>): Instantaneous<B> =>
    new r.Observable((sub) => {
      let acc = z;
      const s = src.subscribe({
        next(e) {
          sub.next({
            provenance: e.provenance,
            events: e.events.map((ev): InstEv<B> => {
              if (ev.type !== "value") return ev;
              acc = f(acc, ev.value);
              return val(acc);
            }),
          });
        },
        error: (err) => sub.error(err),
        complete: () => sub.complete(),
      });
      return () => s.unsubscribe();
    });

/** take counts VALUES, exactly like rxjs — even mid-batch. At the cut it
 * synthesizes closes for every registration it passed downstream and
 * finishes as part of the same emit (the completion cascade carrier). */
export const take =
  (n: number) =>
  <A>(src: Instantaneous<A>): Instantaneous<A> =>
    new r.Observable((sub) => {
      if (n === 0) {
        // completes at subscription — still a fin, so a concatAll behind
        // it advances in the frame
        sub.next({ provenance: COLD, events: [fin] });
        sub.complete();
        return;
      }
      let budget = n;
      let done = false;
      const liveRegs = new Map<number, number>();
      const s = src.subscribe({
        next(e) {
          if (done) return;
          const out: InstEv<A>[] = [];
          for (const ev of e.events) {
            if (ev.type === "init") {
              bumpCount(liveRegs, ev.provenance, 1);
              out.push(ev);
            } else if (ev.type === "close") {
              bumpCount(liveRegs, ev.provenance, -1);
              out.push(ev);
            } else if (ev.type === "fin") {
              out.push(ev);
              done = true;
            } else {
              if (budget > 0) {
                out.push(ev);
                budget--;
                if (budget === 0) {
                  for (const [p, c] of liveRegs)
                    for (let i = 0; i < c; i++) out.push(close(p));
                  out.push(fin);
                  done = true;
                  break;
                }
              }
            }
          }
          sub.next({ provenance: e.provenance, events: out });
          if (done) sub.complete();
        },
        error: (err) => sub.error(err),
        complete() {
          if (!done) sub.complete();
        },
      });
      if (done) s.unsubscribe();
      return () => s.unsubscribe();
    });

// the joins — THE primitives, over streams of streams -------------------------

/** mergeAll: every arriving inner is subscribed at its arrival; its
 * synchronous flush is COALESCED into the arrival's emit (its cause), so
 * cascades batch with their trigger; its later emits pass through under
 * their own roots. The join finishes when the outer and every inner have
 * finished. */
export const mergeAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  new r.Observable((sub) => {
    let outerDone = false;
    // inners that have not FINNED yet (fin emits, not rxjs completes —
    // completes lag the emits within a dispatch)
    let pending = 0;
    let closed = false;
    const innerSubs = new Set<r.Subscription>();

    const spawn = (inner: Instantaneous<A>, out: InstEv<A>[]): void => {
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
        next(e) {
          if (inFlush) {
            if (hasFin(e)) noteFin();
            out.push(...e.events.filter((ev) => ev.type !== "fin"));
            return;
          }
          if (!hasFin(e)) {
            sub.next(e);
            return;
          }
          noteFin();
          const events = e.events.filter((ev) => ev.type !== "fin");
          if (outerDone && pending === 0 && !closed) {
            // the last live inner finishes: the whole join finishes here
            closed = true;
            sub.next({ provenance: e.provenance, events: [...events, fin] });
            sub.complete();
          } else {
            sub.next({ provenance: e.provenance, events });
          }
        },
        error: (err) => sub.error(err),
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

    const o = outer.subscribe({
      next(e) {
        const out: InstEv<A>[] = [];
        for (const ev of e.events) {
          if (ev.type === "value") spawn(ev.value, out);
          else if (ev.type === "fin") outerDone = true;
          else out.push(ev);
        }
        let finishes = false;
        if (outerDone && pending === 0 && !closed) {
          closed = true;
          finishes = true;
          out.push(fin);
        }
        sub.next({ provenance: e.provenance, events: out });
        if (finishes) sub.complete();
      },
      error: (err) => sub.error(err),
      complete() {
        outerDone = true;
        if (pending === 0 && !closed) {
          closed = true;
          sub.complete();
        }
      },
    });

    return () => {
      o.unsubscribe();
      innerSubs.forEach((s) => s.unsubscribe());
    };
  });

/** concatAll: one inner live at a time; arrivals during a live inner
 * QUEUE; when the live inner FINISHES, the next queued inner subscribes at
 * the closing instant — its flush grafted into the fin-carrying emit, so
 * the final value, the closes, and the queued inner's flush are ONE
 * instant (Agda's concatAllT). */
export const concatAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  new r.Observable((sub) => {
    let outerDone = false;
    let closed = false;
    let currentOpen = false;
    let currentSub: r.Subscription | null = null;
    const queue: Instantaneous<A>[] = [];

    const maybeFinish = (out: InstEv<A>[] | null): boolean => {
      if (outerDone && !currentOpen && queue.length === 0 && !closed) {
        closed = true;
        if (out !== null) out.push(fin);
        return true;
      }
      return false;
    };

    const runInner = (inner: Instantaneous<A>, out: InstEv<A>[]): void => {
      currentOpen = true;
      let finnedInFlush = false;
      let inFlush = true;
      const s = inner.subscribe({
        next(e) {
          if (inFlush) {
            if (hasFin(e)) finnedInFlush = true;
            out.push(...e.events.filter((ev) => ev.type !== "fin"));
            return;
          }
          if (!hasFin(e)) {
            sub.next(e);
            return;
          }
          // the live inner finishes asynchronously: advance INTO this emit
          const events = e.events.filter((ev) => ev.type !== "fin");
          currentOpen = false;
          advance(events);
          const finishes = maybeFinish(events);
          sub.next({ provenance: e.provenance, events });
          if (finishes) sub.complete();
        },
        error: (err) => sub.error(err),
        complete() {
          /* completion is bookkept via the fin emit */
        },
      });
      inFlush = false;
      if (finnedInFlush) currentOpen = false;
      else currentSub = s;
    };

    const advance = (out: InstEv<A>[]): void => {
      while (!currentOpen && queue.length > 0) {
        runInner(queue.shift() as Instantaneous<A>, out);
      }
    };

    const o = outer.subscribe({
      next(e) {
        const out: InstEv<A>[] = [];
        for (const ev of e.events) {
          if (ev.type === "value") {
            if (currentOpen) queue.push(ev.value);
            else {
              runInner(ev.value, out);
              advance(out);
            }
          } else if (ev.type === "fin") outerDone = true;
          else out.push(ev);
        }
        const finishes = maybeFinish(out);
        sub.next({ provenance: e.provenance, events: out });
        if (finishes) sub.complete();
      },
      error: (err) => sub.error(err),
      complete() {
        outerDone = true;
        if (maybeFinish(null)) sub.complete();
      },
    });

    return () => {
      o.unsubscribe();
      currentSub?.unsubscribe();
    };
  });

/** switchAll: a new arrival CUTS the live inner — its async tail dies, and
 * closes are synthesized for the registrations it passed downstream (batch
 * accounting must know its slots died). Every inner still gets its
 * subscription frame (sync values pass before the next burst arrival cuts
 * it). The outer completing does NOT kill the live inner. */
export const switchAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  new r.Observable((sub) => {
    let outerDone = false;
    let closed = false;
    type Cur = {
      s: r.Subscription | null;
      regs: Map<number, number>;
      cut: boolean;
      finned: boolean;
    };
    let cur: Cur | null = null;

    const cutCurrent = (out: InstEv<A>[]): void => {
      if (cur !== null && !cur.finned) {
        cur.cut = true;
        cur.s?.unsubscribe();
        for (const [p, c] of cur.regs)
          for (let k = 0; k < c; k++) out.push(close(p));
      }
      cur = null;
    };

    const spawn = (inner: Instantaneous<A>, out: InstEv<A>[]): void => {
      const state: Cur = { s: null, regs: new Map(), cut: false, finned: false };
      cur = state;
      let inFlush = true;
      const s = inner.subscribe({
        next(e) {
          if (state.cut) return;
          for (const ev of e.events) {
            if (ev.type === "init") bumpCount(state.regs, ev.provenance, 1);
            else if (ev.type === "close")
              bumpCount(state.regs, ev.provenance, -1);
          }
          if (inFlush) {
            if (hasFin(e)) state.finned = true;
            out.push(...e.events.filter((ev) => ev.type !== "fin"));
            return;
          }
          if (!hasFin(e)) {
            sub.next(e);
            return;
          }
          state.finned = true;
          const events = e.events.filter((ev) => ev.type !== "fin");
          if (outerDone && !closed) {
            closed = true;
            sub.next({ provenance: e.provenance, events: [...events, fin] });
            sub.complete();
          } else {
            sub.next({ provenance: e.provenance, events });
          }
        },
        error: (err) => sub.error(err),
        complete() {
          /* bookkept via fin */
        },
      });
      state.s = s;
      inFlush = false;
    };

    const o = outer.subscribe({
      next(e) {
        const out: InstEv<A>[] = [];
        for (const ev of e.events) {
          if (ev.type === "value") {
            cutCurrent(out);
            spawn(ev.value, out);
          } else if (ev.type === "fin") outerDone = true;
          else out.push(ev);
        }
        let finishes = false;
        if (outerDone && (cur === null || cur.finned) && !closed) {
          closed = true;
          finishes = true;
          out.push(fin);
        }
        sub.next({ provenance: e.provenance, events: out });
        if (finishes) sub.complete();
      },
      error: (err) => sub.error(err),
      complete() {
        outerDone = true;
        if ((cur === null || cur.finned) && !closed) {
          closed = true;
          sub.complete();
        }
      },
    });

    return () => {
      o.unsubscribe();
      cur?.s?.unsubscribe();
    };
  });

/** exhaustAll: an arrival is dropped only while the previously accepted
 * inner is STILL OPEN — a synchronous inner finishes immediately and frees
 * the slot, so of-then-of runs both. A dropped arrival is emptied, never
 * swallowed (its emit still forwards, valueless). */
export const exhaustAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  new r.Observable((sub) => {
    let outerDone = false;
    let closed = false;
    let curOpen = false;
    let curSub: r.Subscription | null = null;

    const spawn = (inner: Instantaneous<A>, out: InstEv<A>[]): void => {
      let finned = false;
      let inFlush = true;
      const s = inner.subscribe({
        next(e) {
          if (inFlush) {
            if (hasFin(e)) finned = true;
            out.push(...e.events.filter((ev) => ev.type !== "fin"));
            return;
          }
          if (!hasFin(e)) {
            sub.next(e);
            return;
          }
          finned = true;
          curOpen = false;
          const events = e.events.filter((ev) => ev.type !== "fin");
          if (outerDone && !closed) {
            closed = true;
            sub.next({ provenance: e.provenance, events: [...events, fin] });
            sub.complete();
          } else {
            sub.next({ provenance: e.provenance, events });
          }
        },
        error: (err) => sub.error(err),
        complete() {
          /* bookkept via fin */
        },
      });
      inFlush = false;
      if (!finned) {
        curOpen = true;
        curSub = s;
      }
    };

    const o = outer.subscribe({
      next(e) {
        const out: InstEv<A>[] = [];
        for (const ev of e.events) {
          if (ev.type === "value") {
            if (!curOpen) spawn(ev.value, out);
            // else: dropped — the emit still forwards, emptied
          } else if (ev.type === "fin") outerDone = true;
          else out.push(ev);
        }
        let finishes = false;
        if (outerDone && !curOpen && !closed) {
          closed = true;
          finishes = true;
          out.push(fin);
        }
        sub.next({ provenance: e.provenance, events: out });
        if (finishes) sub.complete();
      },
      error: (err) => sub.error(err),
      complete() {
        outerDone = true;
        if (!curOpen && !closed) {
          closed = true;
          sub.complete();
        }
      },
    });

    return () => {
      o.unsubscribe();
      curSub?.unsubscribe();
    };
  });

/** share, with rxjs LIVES (ratified 2026-07-07): connect on first
 * subscriber, reset when the source completes or the refcount drains to
 * zero, reconnect-and-replay for a subscriber arriving after a reset.
 * rxjs share() provides the lives natively; the wrapper adds
 * counting-transparency — a late subscriber registers the ROOTS feeding
 * the share (the connecting subscriber's registrations flow through the
 * connection frame itself). */
export const share = <A>(src: Instantaneous<A>): Instantaneous<A> => {
  // live root registrations seen through the current connection
  let roots = new Map<number, number>();
  let connected = false;
  const reset = (): void => {
    connected = false;
    roots = new Map();
  };
  const shared = src.pipe(
    r.tap({
      next: (e) => {
        for (const ev of e.events) {
          if (ev.type === "init") bumpCount(roots, ev.provenance, 1);
          else if (ev.type === "close") bumpCount(roots, ev.provenance, -1);
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
      const events: InstEv<A>[] = [];
      for (const [p, c] of roots)
        for (let i = 0; i < c; i++) events.push(init(p));
      if (events.length > 0) sub.next({ provenance: COLD, events });
    }
    const s = shared.subscribe(sub);
    return () => {
      s.unsubscribe();
      refCount--;
      if (refCount === 0) reset();
    };
  });
};

// the derived forms — NEVER primitives ------------------------------------------

export const merge = <A>(...srcs: Instantaneous<A>[]): Instantaneous<A> =>
  mergeAll(of(srcs));

export const concat = <A>(...srcs: Instantaneous<A>[]): Instantaneous<A> =>
  concatAll(of(srcs));

export const mergeMap =
  <A, B>(f: (a: A) => Instantaneous<B>) =>
  (e: Instantaneous<A>): Instantaneous<B> =>
    mergeAll(map(f)(e));

export const concatMap =
  <A, B>(f: (a: A) => Instantaneous<B>) =>
  (e: Instantaneous<A>): Instantaneous<B> =>
    concatAll(map(f)(e));

export const switchMap =
  <A, B>(f: (a: A) => Instantaneous<B>) =>
  (e: Instantaneous<A>): Instantaneous<B> =>
    switchAll(map(f)(e));

export const exhaustMap =
  <A, B>(f: (a: A) => Instantaneous<B>) =>
  (e: Instantaneous<A>): Instantaneous<B> =>
    exhaustAll(map(f)(e));
