import {
  EMPTY,
  Observable,
  Subject,
  defer as rxDefer,
  exhaustAll,
  map as rxMap,
  merge,
  mergeAll,
  mergeMap,
  of as rxOf,
  scan as rxScan,
  share as rxShare,
  switchAll,
  take as rxTake,
} from "rxjs";
import { Closed, ObsVal, Val, evalWith, unfoldMu } from "./exp.js";
import { PlainDriver, createPlainDriver, plainHop } from "./plain-driver.js";
import type { ObservableInput, TestCase, Timed } from "./prop-test.js";

// THE PLAIN LEG OF THE ORACLE: an Exp tree run as ORDINARY rxjs, with
// no envelope anywhere in it (Anthony: "nothing involving InstEmit at
// all"). Every case below is one rxjs operator, which is the property
// being tested — if a former cannot be written as one, the Agda
// implementation has claimed a capability plain rxjs does not have, and
// that is the finding this module exists to make unmissable.
//
// The srxjs primitives and the join engine are NOT imported here and
// must never be: they are the layer under test everywhere else, and
// reaching for one would put the thing being compared on both sides of
// the comparison.

// delta-encoded waits → absolute ticks (gap = wait + 1, so a source's
// ticks are strictly increasing by construction)
const resolveTicks = (
  anchor: number,
  timed: Timed<Val>[],
): { tick: number; val: Val }[] =>
  timed.reduce<{ tick: number; val: Val }[]>((acc, { wait, val }) => {
    const prev = acc.length > 0 ? acc[acc.length - 1].tick : anchor;
    return [...acc, { tick: prev + wait + 1, val }];
  }, []);

// a scripted tail as an observable: the driver fires each entry, the
// last one completing the stream
const tail = (
  driver: PlainDriver,
  entries: { tick: number; val: Val }[],
  ordinal?: number,
): Observable<Val> =>
  new Observable<Val>((sink) =>
    driver.registerSource(
      entries.map(({ tick, val }) => ({
        tick,
        fire: (isLast: boolean) => {
          sink.next(val);
          if (isLast) sink.complete();
        },
      })),
      ordinal,
    ),
  );

// THE TWO SOURCE SHAPES, AND THE DIFFERENCE IS WHEN THE SCRIPT IS
// ANCHORED. A cold re-anchors at the subscribing tick and replays its
// sync prefix into the subscribe frame, so each subscriber gets its
// own run; a hot is anchored at tick 0 once, so a later subscriber
// misses whatever already fired. A Subject is what "already running,
// subscriber-independent" IS in rxjs, and it is the harness's own edge
// rather than anything the tree can reach.
const plainInput = (
  driver: PlainDriver,
  input: ObservableInput<Val>,
  index: number,
): Observable<Val> => {
  if (input.type === "hot") {
    const subject = new Subject<Val>();
    const entries = resolveTicks(0, input.async);
    driver.registerSource(
      entries.map(({ tick, val }) => ({
        tick,
        fire: (isLast: boolean) => {
          subject.next(val);
          if (isLast) subject.complete();
        },
      })),
      index,
    );
    return subject;
  }
  // A COLD REGISTERS ITS TAIL BEFORE REPLAYING ITS PREFIX, AND THE
  // ORDER IS OBSERVABLE RATHER THAN COSMETIC. Both orderings are
  // ordinary rxjs -- a source may schedule and then emit, or emit and
  // then schedule -- and with real timers the choice decides which of
  // two same-instant deliveries is armed first. Here it decides the
  // ORDINAL, since the driver mints those in registration order, so a
  // cold whose prefix cascade subscribes another source either outranks
  // that source or is outranked by it.
  //
  // `merge` AND NOT `concat`, WHICH IS THE WHOLE EDIT. `concat`
  // subscribes the tail only once the prefix has completed, so every
  // source the prefix's own cascade subscribes registers first; the
  // Agda evaluator registers at the point of subscription, before
  // handing the prefix back as a burst for its caller to cascade, and
  // that is forced there rather than chosen -- a subscribe returns its
  // burst upward, so it cannot run the cascade and then register. The
  // two must agree for the same reason the hot slot above takes its
  // ordinal from the slot index instead of minting one, and a flattener
  // is where a disagreement surfaces: `exhaustAll` refuses an arrival
  // while an inner is live, so whether the inner's completion or the
  // outer's next value is delivered first decides whether a whole inner
  // run is admitted or dropped.
  //
  // The cut is handled either way and is not what decides this:
  // `concat` never subscribes a tail the prefix cut, while a tail
  // registered first is severed by rx teardown through
  // `registerSource`'s cancel.
  return rxDefer(() =>
    merge(
      input.async.length === 0
        ? EMPTY
        : tail(driver, resolveTicks(driver.currentTick(), input.async)),
      rxOf(...input.sync),
    ),
  );
};

export const compilePlain = (
  exp: Closed,
  env: Val[],
  driver: PlainDriver,
  slotSources: Observable<Val>[],
): Observable<Val> => {
  const recur = (e: Closed) => compilePlain(e, env, driver, slotSources);
  // an inner observable is a CLOSURE carried as a value, so it compiles
  // against the environment it was written under as its emission passes
  const inner = (src: Closed): Observable<Observable<Val>> =>
    recur(src).pipe(
      rxMap((v) => {
        const o = v as ObsVal;
        return compilePlain(o.exp, o.env, driver, slotSources);
      }),
    );
  switch (exp.type) {
    case "input": {
      const source = slotSources[exp.index];
      if (source === undefined)
        throw new Error(`input ${exp.index} out of slot range`);
      return source;
    }
    case "of":
      return rxOf(...exp.items.map((item) => evalWith(item, env)));
    case "empty":
      return EMPTY;
    case "map":
      return recur(exp.src).pipe(
        rxMap((value) => evalWith(exp.fn, [value, ...env])),
      );
    case "scan":
      // the step binds the pair (carried state, one value) and its
      // result IS the next state, so nothing is projected out of it
      return recur(exp.src).pipe(
        rxScan(
          (state: Val, value: Val) =>
            evalWith(exp.fn, [[state, value], ...env]),
          evalWith(exp.init, env),
        ),
      );
    case "take": {
      const count = evalWith(exp.count, env);
      if (typeof count !== "number")
        throw new Error("take count did not evaluate to a nat");
      // take 0 never subscribes its source, as in rxjs
      return count === 0 ? EMPTY : recur(exp.src).pipe(rxTake(count));
    }
    case "mergeAll":
      return inner(exp.src).pipe(mergeAll(exp.limit ?? Infinity));
    case "switchAll":
      return inner(exp.src).pipe(switchAll());
    case "exhaustAll":
      return inner(exp.src).pipe(exhaustAll());
    case "mu":
      // one unfolding now; the recursive occurrences inside sit behind
      // defer hops, so each further unfolding costs a tick
      return recur(unfoldMu(exp.body));
    case "defer":
      // NOT rxjs's `defer` alone: lazy PLUS a one-tick hop, which is
      // what breaks mu's unfolding regress
      return rxDefer(() =>
        plainHop(driver, driver.currentTick() + 1).pipe(
          mergeMap(() => recur(exp.body)),
        ),
      );
    case "mint":
      // a fresh token per subscription, bound at index 0. `Symbol()`
      // admits exactly the one operation `eqU` is, and nothing else
      // produces one, so the token cannot be forged or ordered.
      return rxDefer(() =>
        compilePlain(exp.body, [Symbol("uniq"), ...env], driver, slotSources),
      );
    case "batchSync":
      // THE SYNC BIT IS rxjs's OWN SUBSCRIBE ORDERING AND NOTHING ELSE.
      // `merge` subscribes its inputs in order and synchronously, so the
      // source drains its whole subscribe burst before the second input's
      // `defer` runs — which is the boundary, arriving as a VALUE rather
      // than as a callback, with no hop and no timing change. That is the
      // one bit this operator sees, and it is why nothing here is
      // forward-looking: the group is emitted once the burst is known to
      // be over, never held back to see whether more is owed.
      //
      // STATE IS PER SUBSCRIPTION, NOT PER PIPE: a cold carrying one of
      // these can be subscribed many times — a reused inner delivered by
      // several triggers — and a burst shared across those subscriptions
      // would group one subscriber's values into another's frame.
      //
      // The pair is Agda's `groupSync`/`soloSync` exactly: the burst
      // leaves as ONE head-and-tail pair, every later value as its own
      // `(v , [])`, and an EMPTY burst yields no pair at all rather than
      // an empty group.
      return rxDefer(() => {
        let sync = true;
        const burst: Val[] = [];
        return merge(
          recur(exp.src).pipe(
            mergeMap((value) => {
              if (sync) {
                burst.push(value);
                return EMPTY;
              }
              return rxOf([value, []] as Val);
            }),
          ),
          rxDefer(() => {
            sync = false;
            return burst.length === 0
              ? EMPTY
              : rxOf([burst[0], burst.slice(1)] as Val);
          }),
        );
      });
    case "varE":
      throw new Error(
        "varE in a closed expression — generator/decoder invariant violated",
      );
  }
};

export const evaluatePlain = (testCase: TestCase): Val[] => {
  const driver = createPlainDriver(testCase.slots.length);
  // the const telescope, literally: each shared slot compiles against
  // the prefix of already-built slots, under a share that never resets
  const slotSources = testCase.slots.reduce<Observable<Val>[]>(
    (prefix, slot, index) => [
      ...prefix,
      slot.type === "scripted"
        ? plainInput(driver, slot.input, index)
        : compilePlain(slot.def, [], driver, prefix).pipe(
            rxShare({
              resetOnRefCountZero: false,
              resetOnComplete: false,
              resetOnError: false,
            }),
          ),
    ],
    [],
  );
  const out: Val[] = [];
  const sub = compilePlain(testCase.exp, [], driver, slotSources).subscribe(
    (value) => out.push(value),
  );
  // subscribing already ran the root sync burst — fuel pays only for
  // arrivals
  for (let spent = 0; spent < testCase.fuel; spent++)
    if (!driver.deliverNextArrival()) break;
  sub.unsubscribe();
  return out;
};
