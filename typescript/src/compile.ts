import { Observable, defer as rxDefer, merge, mergeMap, of as rxOf } from "rxjs";
import { InstEmit, SourceId } from "./inst-emit.js";
import { Closed, Val, applyFn, evalTm, unfoldMu } from "./exp.js";
import { Arrival, Driver } from "./driver.js";
import * as P from "./primitive-operators.js";

// a one-shot driver delivery at the NEXT tick, read per subscription —
// the async boundary under deferᵉ/μᵉ. Teardown cancels the pending
// hop (unsubscribing a not-yet-fired defer is free — Agda's sweepLive).
const oneShotArrival = (driver: Driver, tick: number): Observable<Arrival> =>
  new Observable<Arrival>((subscriber) =>
    driver.registerSource([
      {
        tick,
        fire: (arrival) => {
          subscriber.next(arrival);
          subscriber.complete();
        },
      },
    ]),
  );

// deferᵉ (NOT rxjs defer): lazy PLUS a one-tick hop, the body's
// emissions minting fresh ids (an async boundary). Mirrors Agda's
// deferᵉ clause: a one-shot source — init in the subscriber's
// instant, the body subscribed when the hop fires at tick + 1, close
// riding that arrival, the whole completing when the body does.
// The body thunk compiles AT FIRE TIME, which is what breaks μ's
// unfolding regress: each unfolding costs a schedule hop.
// ⚠ Known coalescing gap vs Agda until the primitives land: the close
// bookkeeping and the body's sync burst arrive as separate emits here,
// where Agda grafts them into ONE arrival emit (batchSync territory).
const deferHop = (
  driver: Driver,
  compileBody: () => Observable<InstEmit<Val>>,
): Observable<InstEmit<Val>> =>
  rxDefer(() => {
    const source: SourceId = driver.mintSourceId();
    return merge(
      rxOf<InstEmit<Val>>({
        events: [{ type: "init", source }],
        instant: driver.currentInstant(),
        source,
      }),
      oneShotArrival(driver, driver.currentTick() + 1).pipe(
        mergeMap(({ instant }) =>
          merge(
            rxOf<InstEmit<Val>>({
              events: [{ type: "close", source }],
              instant,
              source,
            }),
            rxDefer(compileBody),
          ),
        ),
      ),
    );
  });

// the per-node switch delegating to the primitive-operators:
// evalTm/applyFn for of/map/scan/take, unfoldMu + a driver hop for
// mu/defer. Inner observables are CLOSED EXPS carried as values
// (strmT), so the *All cases compile each inner as its emission
// passes — laziness for free, defers inside stay thunked.
export const compile = (
  exp: Closed,
  driver: Driver,
  slotSources: Observable<InstEmit<Val>>[],
): Observable<InstEmit<Val>> => {
  const recur = (e: Closed) => compile(e, driver, slotSources);
  const inner = (src: Closed) =>
    P.map(recur(src), (v: Val) => recur(v as Closed));
  switch (exp.type) {
    case "input": {
      const source = slotSources[exp.index];
      if (source === undefined)
        throw new Error(`input ${exp.index} out of slot range`);
      return source;
    }
    case "of":
      return P.of(exp.items.map((item) => evalTm(item)));
    case "empty":
      return P.empty;
    case "map":
      return P.map(recur(exp.src), (v: Val) => applyFn(exp.fn, v));
    case "take": {
      // Agda evaluates the count at subscription time; a closed Tm is
      // deterministic, so evaluating once here cannot differ
      const count = evalTm(exp.count);
      if (typeof count !== "number")
        throw new Error("take count did not evaluate to a nat");
      return P.take(recur(exp.src), count);
    }
    case "scan":
      return P.scan(recur(exp.src), evalTm(exp.init), (acc: Val, cur: Val) =>
        applyFn(exp.fn, [acc, cur]),
      );
    case "mergeAll":
      return P.mergeAll(inner(exp.src));
    case "concatAll":
      return P.concatAll(inner(exp.src));
    case "switchAll":
      return P.switchAll(inner(exp.src));
    case "exhaustAll":
      return P.exhaustAll(inner(exp.src));
    case "mu":
      // one unfolding now; the recursive occurrences inside sit behind
      // defer thunks, so each further unfolding costs a hop
      return recur(unfoldMu(exp.body));
    case "defer":
      return deferHop(driver, () => recur(exp.body));
    case "varE":
      throw new Error(
        "varE in a closed expression — generator/decoder invariant violated",
      );
  }
};
