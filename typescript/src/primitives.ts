import * as r from "rxjs";
import { batchSync } from "./batch-sync";
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
  values,
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
  readonly inst: Instantaneous<A> = r.defer(() =>
    this.ended
      ? // a completed subject completes late subscribers immediately — the
        // fin is part of its history (concat legs behind it must advance)
        r.of({ provenance: COLD, events: [fin] as InstEv<A>[] })
      : this.subj.pipe(
          r.startWith({
            provenance: this.provenance,
            events: [init(this.provenance)] as InstEv<A>[],
          }),
        ),
  );
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
 * done — no async roots, so no registration (Agda: ofP) */
export const of = <A>(vs: A[]): Instantaneous<A> =>
  r.of({ provenance: COLD, events: [...vs.map(val), fin] });

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

/** the accumulator threads through the value events in delivery order —
 * a pure fold (Agda: scanP/scanEvs) */
export const scan =
  <A, B>(f: (acc: B, a: A) => B, z: B) =>
  (src: Instantaneous<A>): Instantaneous<B> =>
    src.pipe(
      r.scan(
        (
          s: { acc: B; out: InstEmit<B> },
          e: InstEmit<A>,
        ): { acc: B; out: InstEmit<B> } => {
          const folded = e.events.reduce(
            (st: { acc: B; events: InstEv<B>[] }, ev) =>
              ev.type === "value"
                ? {
                    acc: f(st.acc, ev.value),
                    events: [...st.events, val(f(st.acc, ev.value))],
                  }
                : { acc: st.acc, events: [...st.events, ev] },
            { acc: s.acc, events: [] as InstEv<B>[] },
          );
          return {
            acc: folded.acc,
            out: { provenance: e.provenance, events: folded.events },
          };
        },
        { acc: z, out: { provenance: COLD, events: [] } },
      ),
      r.map((s) => s.out),
    );

/** take counts VALUES, exactly like rxjs — even mid-batch. At the cut it
 * synthesizes closes for every registration it passed downstream and
 * finishes as part of the same emit (the completion cascade carrier). */
/** take counts VALUES, exactly like rxjs — even mid-batch. At the cut it
 * closes every registration it passed downstream and finishes inside the
 * same emit (Agda: takeP/takeEvs — a pure fold over the events). */
type TakeState<A> = {
  readonly budget: number;
  readonly liveRegs: Readonly<Record<number, number>>;
  readonly done: boolean;
  readonly out: InstEmit<A> | null;
};

const takeEvs = <A>(
  st: { budget: number; liveRegs: Readonly<Record<number, number>>; done: boolean },
  events: readonly InstEv<A>[],
): { budget: number; liveRegs: Readonly<Record<number, number>>; done: boolean; out: InstEv<A>[] } =>
  events.reduce(
    (acc, ev) => {
      if (acc.done) return acc;
      if (ev.type === "init")
        return {
          ...acc,
          liveRegs: {
            ...acc.liveRegs,
            [ev.provenance]: (acc.liveRegs[ev.provenance] ?? 0) + 1,
          },
          out: [...acc.out, ev],
        };
      if (ev.type === "close")
        return {
          ...acc,
          liveRegs: {
            ...acc.liveRegs,
            [ev.provenance]: Math.max(0, (acc.liveRegs[ev.provenance] ?? 0) - 1),
          },
          out: [...acc.out, ev],
        };
      if (ev.type === "fin") return { ...acc, done: true, out: [...acc.out, ev] };
      // a value
      if (acc.budget <= 0) return acc;
      if (acc.budget === 1) {
        const closes = Object.entries(acc.liveRegs).flatMap(([p, c]) =>
          Array.from({ length: c }, () => close(Number(p))),
        );
        return {
          budget: 0,
          liveRegs: {},
          done: true,
          out: [...acc.out, ev, ...closes, fin],
        };
      }
      return { ...acc, budget: acc.budget - 1, out: [...acc.out, ev] };
    },
    { ...st, out: [] as InstEv<A>[] },
  );

export const take =
  (n: number) =>
  <A>(src: Instantaneous<A>): Instantaneous<A> =>
    n === 0
      ? // completes at subscription — still a fin, so a concat behind it
        // advances in the frame
        r.of({ provenance: COLD, events: [fin] as InstEv<A>[] })
      : src.pipe(
          r.scan(
            (st: TakeState<A>, e: InstEmit<A>): TakeState<A> => {
              const res = takeEvs(st, e.events);
              return {
                budget: res.budget,
                liveRegs: res.liveRegs,
                done: res.done,
                out: { provenance: e.provenance, events: res.out },
              };
            },
            { budget: n, liveRegs: {}, done: false, out: null },
          ),
          r.takeWhile((st) => !st.done, true),
          r.mergeMap((st) => (st.out === null ? r.EMPTY : r.of(st.out))),
        );

// the joins — THE primitives, over streams of streams -------------------------

/** the tagged item stream a join's scan consumes: the outer's emit (its
 * trigger chains' events + how many inners it spawns), each spawned
 * inner's synchronous flush (captured by batchSync — the coalescing), and
 * inners' later emits. r.merge subscribes in order, so a trigger item is
 * always followed synchronously by exactly its own flushes. */
type JoinItem<A> =
  | {
      t: "trigger";
      provenance: number;
      others: InstEv<A>[];
      spawns: number;
      outerFin: boolean;
    }
  | { t: "flush"; events: InstEv<A>[]; finned: boolean }
  | { t: "emit"; e: InstEmit<A> };

const innerItems = <A>(inner: Instantaneous<A>): r.Observable<JoinItem<A>> =>
  inner.pipe(
    batchSync<InstEmit<A>>(),
    r.map(
      (g): JoinItem<A> =>
        g.type === "sync"
          ? {
              t: "flush",
              events: g.value.flatMap((em) =>
                em.events.filter((ev) => ev.type !== "fin"),
              ),
              finned: g.value.some(hasFin),
            }
          : { t: "emit", e: g.value },
    ),
  );

const triggerItem = <A>(
  e: InstEmit<Instantaneous<A>>,
  spawns: number,
): JoinItem<A> => ({
  t: "trigger",
  provenance: e.provenance,
  others: e.events.filter(
    (ev): ev is InstEv<A> & { type: "init" | "close" } =>
      ev.type === "init" || ev.type === "close",
  ),
  spawns,
  outerFin: hasFin(e),
});

type MergeState<A> = {
  readonly expecting: number;
  readonly buf: readonly InstEv<A>[];
  readonly prov: number;
  readonly pending: number;
  readonly outerDone: boolean;
  readonly closed: boolean;
  readonly out: InstEmit<A> | null;
};

/** mergeAll (Agda: mergeAllP): every arriving inner is subscribed at its
 * arrival; its synchronous flush is COALESCED into the arrival's emit
 * (its cause), so cascades batch with their trigger; its later emits pass
 * through under their own roots. The join finishes when the outer and
 * every inner have finished (fin emits, not rxjs completes — completes
 * lag the emits within a dispatch). A pure scan over the item stream. */
export const mergeAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  outer.pipe(
    r.mergeMap((e): r.Observable<JoinItem<A>> => {
      const inners = values(e.events);
      return r.merge<JoinItem<A>[]>(
        r.of(triggerItem(e, inners.length)),
        ...inners.map(innerItems),
      );
    }),
    r.scan(
      (s: MergeState<A>, item: JoinItem<A>): MergeState<A> => {
        if (item.t === "trigger") {
          const pending = s.pending + item.spawns;
          const outerDone = s.outerDone || item.outerFin;
          if (item.spawns > 0)
            return {
              ...s,
              pending,
              outerDone,
              expecting: item.spawns,
              buf: item.others,
              prov: item.provenance,
              out: null,
            };
          const closes = outerDone && pending === 0 && !s.closed;
          return {
            ...s,
            pending,
            outerDone,
            closed: s.closed || closes,
            out: {
              provenance: item.provenance,
              events: closes ? [...item.others, fin] : item.others,
            },
          };
        }
        if (item.t === "flush") {
          const pending = item.finned ? s.pending - 1 : s.pending;
          const expecting = s.expecting - 1;
          const buf = [...s.buf, ...item.events];
          if (expecting > 0)
            return { ...s, pending, expecting, buf, out: null };
          const closes = s.outerDone && pending === 0 && !s.closed;
          return {
            ...s,
            pending,
            expecting: 0,
            buf: [],
            closed: s.closed || closes,
            out: {
              provenance: s.prov,
              events: closes ? [...buf, fin] : [...buf],
            },
          };
        }
        // an inner's later emit
        if (!hasFin(item.e)) return { ...s, out: item.e };
        const pending = s.pending - 1;
        const events = item.e.events.filter((ev) => ev.type !== "fin");
        const closes = s.outerDone && pending === 0 && !s.closed;
        return {
          ...s,
          pending,
          closed: s.closed || closes,
          out: {
            provenance: item.e.provenance,
            events: closes ? [...events, fin] : events,
          },
        };
      },
      {
        expecting: 0,
        buf: [],
        prov: COLD,
        pending: 0,
        outerDone: false,
        closed: false,
        out: null,
      } as MergeState<A>,
    ),
    r.takeWhile((s) => !s.closed, true),
    r.mergeMap((s) => (s.out === null ? r.EMPTY : r.of(s.out))),
  );

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
