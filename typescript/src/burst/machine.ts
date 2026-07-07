import * as r from "rxjs";
import { Delivery, Inst } from "./protocol";

/**
 * batchSimultaneous: the counting machine, transcribed from
 * agda/src/Protocol.agda (Mem / stepD / runMem / machine).
 *
 * The subscription frame is one instant — its boundary is the subscribe
 * call itself (the batchSync trick), so everything delivered synchronously
 * during subscribe is one batch. After the frame, batching is decided by
 * COUNTING ALONE: totalNum tracks live registrations per root provenance
 * (maintained from reg/clo events); a delivery arriving with no window
 * open opens the instant of its provenance, owing totalNum[prov]
 * deliveries in total; the window drains one per delivery and flushes at
 * zero. Valueless instants (pure protocol traffic) batch nothing.
 */
export const batchSimultaneous = <A>(src: Inst<A>): r.Observable<A[]> =>
  new r.Observable<A[]>((sub) => {
    let inFrame = true;
    const totalNum = new Map<number, number>();
    const frameVals: A[] = [];
    let win: { owed: number; acc: A[] } | null = null;
    let pendingComplete = false;

    const flush = (acc: A[]): void => {
      if (acc.length > 0) sub.next(acc);
    };

    const step = (d: Delivery<A>): void => {
      // owed is computed from totalNum as of the instant's start — BEFORE
      // this delivery's reg/clo events apply (Agda: stepD reads tn p, then
      // applyEvs)
      const owedStart = win === null ? (totalNum.get(d.prov) ?? 1) : win.owed;
      const acc = win === null ? [] : win.acc;
      for (const ev of d.events) {
        if (ev.t === "val") acc.push(ev.v);
        else if (ev.t === "reg")
          totalNum.set(ev.p, (totalNum.get(ev.p) ?? 0) + 1);
        else if (ev.t === "clo")
          totalNum.set(ev.p, Math.max(0, (totalNum.get(ev.p) ?? 0) - 1));
      }
      const owed = owedStart - 1;
      if (owed <= 0) {
        win = null;
        flush(acc);
      } else {
        win = { owed, acc };
      }
    };

    const upstream = src.subscribe({
      next(d) {
        if (inFrame) {
          for (const ev of d.events) {
            if (ev.t === "val") frameVals.push(ev.v);
            else if (ev.t === "reg")
              totalNum.set(ev.p, (totalNum.get(ev.p) ?? 0) + 1);
            else if (ev.t === "clo")
              totalNum.set(ev.p, Math.max(0, (totalNum.get(ev.p) ?? 0) - 1));
          }
          return;
        }
        step(d);
      },
      error(e) {
        sub.error(e);
      },
      complete() {
        if (inFrame) {
          // sources completing inside the frame (all-cold programs): the
          // frame batch still needs to go out first
          pendingComplete = true;
          return;
        }
        if (win !== null) {
          // unreachable on truthful traces; mirror runMem's end flush
          flush(win.acc);
          win = null;
        }
        sub.complete();
      },
    });

    // the frame boundary: the subscribe call has returned
    inFrame = false;
    flush(frameVals);
    if (pendingComplete) sub.complete();

    return () => upstream.unsubscribe();
  });
