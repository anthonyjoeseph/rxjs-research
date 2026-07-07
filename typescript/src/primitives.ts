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
    (this.ended
      ? // a completed subject completes late subscribers immediately — the
        // fin is part of its history (concat legs behind it must advance)
        r.of({ provenance: COLD, events: [fin] as InstEv<A>[] })
      : this.subj.pipe(
          r.startWith({
            provenance: this.provenance,
            events: [init(this.provenance)] as InstEv<A>[],
          }),
        )
    ).pipe(
      // COMPLETE on the in-band fin, not on the separate rxjs complete().
      // The fin is the single completion channel the whole protocol uses
      // (a join completes on its inner's fin emit); if the bare subject
      // instead only completed via rxjs complete(), a `merge(s)`-wrapped
      // leg would advance on the fin — one dispatch pass EARLIER than a
      // bare-s leg advancing on complete() — reordering sibling arms
      // (merge(s) ≠ s). Completing on the fin makes every leg advance in
      // the same pass, in subscription order, matching the Agda model.
      r.takeWhile((e) => !hasFin(e), true),
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

/** the serial joins share one architecture: r.connect multicasts the
 * single outer subscription into a trigger branch and an inner branch —
 * the inner branch routed through the NATIVE rxjs flattening operator
 * whose subscription policy IS the semantics (concatMap queues, switchMap
 * cuts, exhaustMap drops) — and a pure scan reassembles emits, HOLDING an
 * open group exactly while more synchronous flushes are guaranteed to
 * follow (advancement flushes ride the fin-carrying emit; spawn flushes
 * ride their trigger). */
const serialItems =
  <A>(
    flatten: (
      project: (inner: Instantaneous<A>) => r.Observable<JoinItem<A>>,
    ) => r.OperatorFunction<Instantaneous<A>, JoinItem<A>>,
  ) =>
  (outer: Instantaneous<Instantaneous<A>>): r.Observable<JoinItem<A>> =>
    outer.pipe(
      r.connect((sh) =>
        r.merge(
          sh.pipe(r.map((e) => triggerItem<A>(e, values(e.events).length))),
          sh.pipe(
            r.mergeMap((e) => r.from(values(e.events))),
            flatten(innerItems),
          ),
        ),
      ),
    );

type SerialState<A> = {
  /** an emit being assembled, awaiting guaranteed-synchronous flushes */
  readonly holding: { readonly prov: number; readonly buf: readonly InstEv<A>[] } | null;
  /** arrivals not yet started (concat: queued; switch/exhaust: burst countdown) */
  readonly queued: number;
  /** the live inner's fin status and (for switch) its registration balance */
  readonly currentOpen: boolean;
  readonly curRegs: Readonly<Record<number, number>>;
  readonly outerDone: boolean;
  readonly closed: boolean;
  readonly out: InstEmit<A> | null;
};

const serialSeed = <A>(): SerialState<A> => ({
  holding: null,
  queued: 0,
  currentOpen: false,
  curRegs: {},
  outerDone: false,
  closed: false,
  out: null,
});

const trackRegs = <A>(
  regs: Readonly<Record<number, number>>,
  events: readonly InstEv<A>[],
): Readonly<Record<number, number>> =>
  events.reduce(
    (rs, ev) =>
      ev.type === "init"
        ? { ...rs, [ev.provenance]: (rs[ev.provenance] ?? 0) + 1 }
        : ev.type === "close"
          ? { ...rs, [ev.provenance]: Math.max(0, (rs[ev.provenance] ?? 0) - 1) }
          : rs,
    regs,
  );

const closesFor = <A>(
  regs: Readonly<Record<number, number>>,
): InstEv<A>[] =>
  Object.entries(regs).flatMap(([p, c]) =>
    Array.from({ length: c }, () => close(Number(p))),
  );

/** finalize the held emit; the join fins when the outer is done and
 * nothing is live or queued */
const finalize = <A>(
  s: SerialState<A>,
  extra: { currentOpen: boolean; queued: number; outerDone: boolean },
): SerialState<A> => {
  const h = s.holding;
  if (h === null) return { ...s, ...extra, out: null };
  const fins =
    extra.outerDone && !extra.currentOpen && extra.queued === 0 && !s.closed;
  return {
    ...s,
    ...extra,
    holding: null,
    closed: s.closed || fins,
    out: { provenance: h.prov, events: fins ? [...h.buf, fin] : [...h.buf] },
  };
};

const runSerial =
  <A>(step: (s: SerialState<A>, item: JoinItem<A>) => SerialState<A>) =>
  (items: r.Observable<JoinItem<A>>): Instantaneous<A> =>
    items.pipe(
      r.scan(step, serialSeed<A>()),
      r.takeWhile((s) => !s.closed, true),
      r.mergeMap((s) => (s.out === null ? r.EMPTY : r.of(s.out))),
    );

/** concatAll (Agda: the concatAllP hole): one inner live at a time;
 * arrivals during a live inner QUEUE (concatMap, natively); when the live
 * inner FINISHES, the queued inner's flush is grafted into the
 * fin-carrying emit — one instant. */
export const concatAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  runSerial<A>((s, item) => {
    if (item.t === "trigger") {
      const queued = s.queued + item.spawns;
      const outerDone = s.outerDone || item.outerFin;
      const held = { prov: item.provenance, buf: item.others };
      if (s.currentOpen || item.spawns === 0)
        // nothing advances now: the arrivals just queue (or none came)
        return finalize(
          { ...s, holding: held },
          { currentOpen: s.currentOpen, queued, outerDone },
        );
      // idle: the first inner's flush follows synchronously — hold
      return { ...s, holding: held, queued, outerDone, out: null };
    }
    if (item.t === "flush") {
      const queued = s.queued - 1;
      const buf = [...(s.holding?.buf ?? []), ...item.events];
      const held = { prov: s.holding?.prov ?? COLD, buf };
      if (item.finned && queued > 0)
        // this inner finished synchronously and another is queued: its
        // flush follows synchronously — keep holding
        return { ...s, holding: held, queued, out: null };
      return finalize(
        { ...s, holding: held },
        { currentOpen: !item.finned, queued, outerDone: s.outerDone },
      );
    }
    // the live inner's later emit
    if (!hasFin(item.e)) return { ...s, out: item.e };
    const events = item.e.events.filter((ev) => ev.type !== "fin");
    const held = { prov: item.e.provenance, buf: events };
    if (s.queued > 0)
      // advancement: the next queued inner's flush follows synchronously
      return { ...s, holding: held, currentOpen: false, out: null };
    return finalize(
      { ...s, holding: held },
      { currentOpen: false, queued: 0, outerDone: s.outerDone },
    );
  })(serialItems<A>((project) => r.concatMap(project))(outer));

/** switchAll (Agda: the switchAllP hole): a new arrival CUTS the live
 * inner (switchMap, natively) — closes are synthesized for the cut
 * inner's registrations, riding the switching trigger's emit; every inner
 * still gets its subscription frame; the outer completing does not kill
 * the live inner. */
export const switchAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  runSerial<A>((s, item) => {
    if (item.t === "trigger") {
      const outerDone = s.outerDone || item.outerFin;
      const cuts =
        item.spawns > 0 && s.currentOpen ? closesFor<A>(s.curRegs) : [];
      const held = { prov: item.provenance, buf: [...item.others, ...cuts] };
      if (item.spawns === 0)
        return finalize(
          { ...s, holding: held },
          { currentOpen: s.currentOpen, queued: 0, outerDone },
        );
      // the new inner's flush follows synchronously — hold; queued counts
      // the burst down (each spawn's flush cuts its predecessor)
      return {
        ...s,
        holding: held,
        queued: item.spawns,
        currentOpen: false,
        curRegs: {},
        outerDone,
        out: null,
      };
    }
    if (item.t === "flush") {
      const queued = s.queued - 1;
      const regs = trackRegs<A>({}, item.events);
      if (queued > 0) {
        // a later burst sibling follows synchronously and cuts THIS one
        const cuts = item.finned ? [] : closesFor<A>(regs);
        const held = {
          prov: s.holding?.prov ?? COLD,
          buf: [...(s.holding?.buf ?? []), ...item.events, ...cuts],
        };
        return { ...s, holding: held, queued, curRegs: {}, out: null };
      }
      const held = {
        prov: s.holding?.prov ?? COLD,
        buf: [...(s.holding?.buf ?? []), ...item.events],
      };
      return finalize(
        { ...s, holding: held, curRegs: item.finned ? {} : regs },
        { currentOpen: !item.finned, queued: 0, outerDone: s.outerDone },
      );
    }
    // the live inner's later emit
    const curRegs = trackRegs(s.curRegs, item.e.events);
    if (!hasFin(item.e)) return { ...s, curRegs, out: item.e };
    const events = item.e.events.filter((ev) => ev.type !== "fin");
    const held = { prov: item.e.provenance, buf: events };
    return finalize(
      { ...s, holding: held, curRegs: {} },
      { currentOpen: false, queued: 0, outerDone: s.outerDone },
    );
  })(serialItems<A>((project) => r.switchMap(project))(outer));

/** exhaustAll (Agda: the exhaustAllP hole): an arrival is dropped only
 * while the previously accepted inner is STILL OPEN (exhaustMap,
 * natively — fin makes our completion match rxjs's); a synchronous inner
 * frees the slot, so of-then-of runs both. Dropped arrivals are emptied,
 * never swallowed. */
export const exhaustAll = <A>(
  outer: Instantaneous<Instantaneous<A>>,
): Instantaneous<A> =>
  runSerial<A>((s, item) => {
    if (item.t === "trigger") {
      const outerDone = s.outerDone || item.outerFin;
      const held = { prov: item.provenance, buf: item.others };
      if (s.currentOpen || item.spawns === 0)
        // all arrivals dropped (or none): the emit forwards, emptied
        return finalize(
          { ...s, holding: held },
          { currentOpen: s.currentOpen, queued: 0, outerDone },
        );
      // the first arrival is accepted: its flush follows synchronously
      return { ...s, holding: held, queued: item.spawns, outerDone, out: null };
    }
    if (item.t === "flush") {
      const queued = s.queued - 1;
      const buf = [...(s.holding?.buf ?? []), ...item.events];
      const held = { prov: s.holding?.prov ?? COLD, buf };
      if (item.finned && queued > 0)
        // it finished synchronously, so the next burst arrival is
        // accepted: its flush follows synchronously — keep holding
        return { ...s, holding: held, queued, out: null };
      return finalize(
        { ...s, holding: held },
        { currentOpen: !item.finned, queued: 0, outerDone: s.outerDone },
      );
    }
    // the live inner's later emit
    if (!hasFin(item.e)) return { ...s, out: item.e };
    const events = item.e.events.filter((ev) => ev.type !== "fin");
    const held = { prov: item.e.provenance, buf: events };
    return finalize(
      { ...s, holding: held },
      { currentOpen: false, queued: 0, outerDone: s.outerDone },
    );
  })(serialItems<A>((project) => r.exhaustMap(project))(outer));

/** share, with rxjs LIVES (ratified 2026-07-07): connect on first
 * subscriber, reset when the source completes or the refcount drains to
 * zero, reconnect-and-replay for a subscriber arriving after a reset.
 * rxjs share() provides the lives natively; the wrapper adds
 * counting-transparency — a late subscriber registers the ROOTS feeding
 * the share (the connecting subscriber's registrations flow through the
 * connection frame itself). */
export const share = <A>(src: Instantaneous<A>): Instantaneous<A> => {
  // the share is the inherently stateful primitive (multicast + lives),
  // like the subject — everything else in this file is a pure fold; its
  // wiring is still combinator-only (defer/merge/finalize, no subscribe)
  let roots: Readonly<Record<number, number>> = {};
  let connected = false;
  let refCount = 0;
  const reset = (): void => {
    connected = false;
    roots = {};
  };
  const shared = src.pipe(
    r.tap({
      next: (e) => {
        roots = trackRegs(roots, e.events);
      },
      complete: reset,
    }),
    r.share(),
  );
  return r.defer(() => {
    const late = connected;
    connected = true;
    refCount++;
    // registration-only replay: a late subscriber taps the same roots
    const regs: InstEv<A>[] = late
      ? Object.entries(roots).flatMap(([p, c]) =>
          Array.from({ length: c }, () => init(Number(p))),
        )
      : [];
    return r
      .merge(
        regs.length > 0
          ? r.of({ provenance: COLD, events: regs })
          : (r.EMPTY as r.Observable<InstEmit<A>>),
        shared,
      )
      .pipe(
        r.finalize(() => {
          refCount--;
          if (refCount === 0) reset();
        }),
      );
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
