import { Observable } from "rxjs";
import {
  InstEmit,
  InstEvent,
  SourceId,
  flattenBurst,
  openAfter,
  reassemble,
  splitEmit,
} from "./inst-emit.js";
import { captureSync, cold } from "./constructors.js";

// ---- the one join engine: mergeAll/concatAll/switchAll/exhaustAll ----
// (the TS mirror of Agda's subscribeAll + stepFrame thru-outer/from-inner)
//
// The four ops differ ONLY in two decisions — what to do with a newly
// arrived inner (subscribe / queue behind the active one / cut the
// current one / drop), and how to react when an inner finishes (concat
// advances its queue; the others just bookkeep) — plus the completion
// condition. Everything else is shared:
//
// - a subscribed inner's SYNC burst is captured and flattened into the
//   emit that carried it (Agda's splitBurst): all bookkeeping in walk
//   order, then all values — the id-inheritance that makes the diamond
//   batch. Inner complete events are absorbed into the done bit; the
//   join completes on its own terms.
// - an inner's completion is detected ON the emit that closes its last
//   registration (the open-source multiset — TS's reading of Agda's
//   threaded fin bit), so concat can graft the next inner's burst into
//   that very emit (completion cascades inherit). Plumbing emits are
//   excluded: a share's connect traffic opens nothing the join owns.
// - a cut inner (switch) contributes close…cut events for exactly the
//   registrations it still holds (Agda's cutThrough), and its rx
//   teardown cancels whatever it had scheduled (sweepLive).

type JoinOp = "merge" | "concat" | "switch" | "exhaust";

type InnerHandle = {
  open: SourceId[]; // this inner's live registrations — its fin bit
  unsubscribe: () => void;
};

type Grafts<A> = { bookkeeping: InstEvent<never>[]; values: A[] };

const joinAll =
  (op: JoinOp) =>
  <A>(
    outer: Observable<InstEmit<Observable<InstEmit<A>>>>,
  ): Observable<InstEmit<A>> =>
    cold<InstEmit<A>>((sink) => {
      let outerDone = false;
      let finished = false;
      const active: InnerHandle[] = []; // merge: all; the rest keep at most one
      const queue: Observable<InstEmit<A>>[] = []; // concat only

      const joinDone = () =>
        outerDone && active.length === 0 && queue.length === 0;

      const finishIfDone = () => {
        if (!finished && joinDone()) {
          finished = true;
          sink.complete();
        }
      };

      const removeHandle = (handle: InnerHandle) => {
        const at = active.indexOf(handle);
        if (at !== -1) active.splice(at, 1);
      };

      // an inner's LATER (async) emits pass through under their own
      // envelopes; when one closes the inner's last registration, the
      // reaction (concat: advance the queue) grafts into that same emit
      const forwardInnerEmit = (handle: InnerHandle, emit: InstEmit<A>) => {
        const parts = splitEmit(emit);
        handle.open = openAfter(emit, handle.open, false);
        const innerDone = parts.fin || handle.open.length === 0;
        let grafts: Grafts<A> = { bookkeeping: [], values: [] };
        if (innerDone) {
          removeHandle(handle);
          if (op === "concat") grafts = drainQueue();
        }
        sink.next(
          reassemble(
            emit,
            parts.bookkeeping,
            grafts.bookkeeping,
            [...parts.values, ...grafts.values],
            false,
          ),
        );
        if (innerDone) finishIfDone();
      };

      // subscribe an inner NOW, flattening its sync burst into grafts
      // for the carrying emit; register it as live unless it died
      // inside its own burst
      const subscribeInner = (
        innerObs: Observable<InstEmit<A>>,
      ): Grafts<A> & { done: boolean } => {
        const handle: InnerHandle = { open: [], unsubscribe: () => {} };
        const capture = captureSync(innerObs, {
          next: (emit) => forwardInnerEmit(handle, emit),
          complete: () => {
            // fin already observed on the closing emit via the
            // multiset; the rx completion itself is absorbed
          },
        });
        handle.unsubscribe = capture.unsubscribe;
        for (const emit of capture.burst)
          handle.open = openAfter(emit, handle.open, false);
        const flat = flattenBurst(capture.burst);
        const done =
          capture.completedSync || flat.done || handle.open.length === 0;
        if (!done) active.push(handle);
        return { bookkeeping: flat.bookkeeping, values: flat.values, done };
      };

      // concat: subscribe queued inners until one survives its burst
      const drainQueue = (): Grafts<A> => {
        let grafts: Grafts<A> = { bookkeeping: [], values: [] };
        while (queue.length > 0) {
          const nextInner = queue.shift();
          if (nextInner === undefined) break;
          const result = subscribeInner(nextInner);
          grafts = {
            bookkeeping: [...grafts.bookkeeping, ...result.bookkeeping],
            values: [...grafts.values, ...result.values],
          };
          if (!result.done) break;
        }
        return grafts;
      };

      // switch: end the current inner — close…cut for exactly the
      // registrations it still holds, teardown cancelling its schedule
      const cutCurrent = (): InstEvent<never>[] => {
        const current = active.shift();
        if (current === undefined) return [];
        current.unsubscribe();
        return current.open.map(
          (source) => ({ type: "close", source, reason: "cut" }) as const,
        );
      };

      // the per-op decision for one arriving inner observable
      const acceptInner = (innerObs: Observable<InstEmit<A>>): Grafts<A> => {
        switch (op) {
          case "merge":
            return subscribeInner(innerObs);
          case "concat": {
            if (active.length > 0) {
              queue.push(innerObs);
              return { bookkeeping: [], values: [] };
            }
            return subscribeInner(innerObs);
          }
          case "switch": {
            const closes = cutCurrent();
            const result = subscribeInner(innerObs);
            return {
              bookkeeping: [...closes, ...result.bookkeeping],
              values: result.values,
            };
          }
          case "exhaust": {
            if (active.length > 0) return { bookkeeping: [], values: [] }; // dropped: never subscribed
            return subscribeInner(innerObs);
          }
        }
      };

      const onOuterEmit = (emit: InstEmit<Observable<InstEmit<A>>>) => {
        const parts = splitEmit(emit);
        let grafts: Grafts<A> = { bookkeeping: [], values: [] };
        for (const innerObs of parts.values) {
          const result = acceptInner(innerObs);
          grafts = {
            bookkeeping: [...grafts.bookkeeping, ...result.bookkeeping],
            values: [...grafts.values, ...result.values],
          };
        }
        if (parts.fin) outerDone = true;
        const done = joinDone();
        // the carrying emit under the outer's envelope; a spent-at-
        // subscribe join materializes its complete here (pushBurst),
        // a spent delivery leaves that to the root
        sink.next(
          reassemble(
            emit,
            parts.bookkeeping,
            grafts.bookkeeping,
            grafts.values,
            done && emit.kind === "subscribe",
          ),
        );
        if (parts.fin || done) finishIfDone();
      };

      const outerCapture = captureSync(outer, {
        next: onOuterEmit,
        complete: () => {
          outerDone = true;
          finishIfDone();
        },
      });
      // the outer's own subscribe burst, replayed through the same
      // path — still inside this subscription's synchronous frame
      for (const emit of outerCapture.burst) onOuterEmit(emit);
      if (outerCapture.completedSync) {
        outerDone = true;
        finishIfDone();
      }

      return () => {
        outerCapture.unsubscribe();
        for (const inner of active) inner.unsubscribe();
      };
    });

export const mergeAll = joinAll("merge");
export const concatAll = joinAll("concat");
export const switchAll = joinAll("switch");
export const exhaustAll = joinAll("exhaust");
