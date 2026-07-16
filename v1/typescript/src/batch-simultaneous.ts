import * as r from "rxjs";
import { batchSync } from "./batch-sync";
import { InstEmit, InstEv, Instantaneous, values } from "./types";

/**
 * batchSimultaneous: the counting machine, transcribed from
 * agda/src/Protocol.agda (Mem / stepD / runMem / machine) — a PURE fold
 * (rxjs scan) over the emits; no mutable state anywhere.
 *
 * The subscription frame is one instant — its boundary is the subscribe
 * call itself, made observable by `batchSync` (exactly as in the earlier
 * drafts), so everything delivered synchronously during subscribe is one
 * batch. After the frame, batching is decided by COUNTING ALONE: totalNum
 * tracks live registrations per root provenance (maintained from
 * init/close events); an emit arriving with no window open opens the
 * instant of its provenance, owing totalNum[provenance] emits in total;
 * the window drains one per emit and flushes at zero. Valueless instants
 * (pure protocol traffic) batch nothing.
 */

type TotalNum = Readonly<Record<number, number>>;

type Mem<A> = {
  readonly totalNum: TotalNum;
  readonly win: { readonly owed: number; readonly acc: readonly A[] } | null;
  /** the batch this step flushes, if any */
  readonly flush: readonly A[] | null;
};

const applyEv = <A>(tn: TotalNum, ev: InstEv<A>): TotalNum =>
  ev.type === "init"
    ? { ...tn, [ev.provenance]: (tn[ev.provenance] ?? 0) + 1 }
    : ev.type === "close"
      ? { ...tn, [ev.provenance]: Math.max(0, (tn[ev.provenance] ?? 0) - 1) }
      : tn;

const applyEvs = <A>(tn: TotalNum, events: readonly InstEv<A>[]): TotalNum =>
  events.reduce(applyEv, tn);

/** the frame: one instant, no windows needed — its boundary was the
 * subscribe call */
const frameStep = <A>(emits: readonly InstEmit<A>[]): Mem<A> => {
  const events = emits.flatMap((e) => e.events);
  const vals = values(events);
  return {
    totalNum: applyEvs({}, events),
    win: null,
    flush: vals.length > 0 ? vals : null,
  };
};

/** one async emit (Agda: stepD) — owed is computed from totalNum as of
 * the instant's start, BEFORE this emit's init/close events apply */
const step = <A>(m: Mem<A>, e: InstEmit<A>): Mem<A> => {
  const owedStart =
    m.win === null ? (m.totalNum[e.provenance] ?? 1) : m.win.owed;
  const acc = [...(m.win?.acc ?? []), ...values(e.events)];
  const totalNum = applyEvs(m.totalNum, e.events);
  const owed = owedStart - 1;
  return owed <= 0
    ? { totalNum, win: null, flush: acc.length > 0 ? acc : null }
    : { totalNum, win: { owed, acc }, flush: null };
};

export const batchSimultaneous = <A>(
  src: Instantaneous<A>,
): r.Observable<A[]> =>
  src.pipe(
    batchSync<InstEmit<A>>(),
    // the stream ending drains a still-open window (Agda: runMem's end
    // flush — reached when an instant's later slots died mid-window, the
    // corner the postulated runMemCut refines)
    r.endWith({ type: "end" } as const),
    r.scan(
      (m: Mem<A>, e): Mem<A> =>
        e.type === "end"
          ? { totalNum: m.totalNum, win: null, flush: m.win?.acc ?? null }
          : e.type === "sync"
            ? frameStep(e.value)
            : step({ ...m, flush: null }, e.value),
      { totalNum: {}, win: null, flush: null },
    ),
    r.mergeMap((m) =>
      m.flush === null || m.flush.length === 0 ? r.EMPTY : r.of([...m.flush]),
    ),
  );
