import { Observable, Subject, defer, merge, of } from "rxjs";
import { InstEmit, SourceId } from "./inst-emit.js";
import { Val } from "./exp.js";
import { Arrival, Driver } from "./driver.js";
import type { ObservableInput, Timed } from "./prop-test.js";

// delta-encoded waits → absolute ticks (gap = wait + 1, so a source's
// ticks are strictly increasing by construction) — Agda's resolve
const resolveTicks = (
  anchor: number,
  timed: Timed<Val>[],
): { tick: number; val: Val }[] =>
  timed.reduce<{ tick: number; val: Val }[]>((acc, { wait, val }) => {
    const prev = acc.length > 0 ? acc[acc.length - 1].tick : anchor;
    return [...acc, { tick: prev + wait + 1, val }];
  }, []);

// one scripted source's driver deliveries: each is one InstEmit under
// the arrival's fresh instant; the final one carries the
// registration's close and then completes the stream (the fin bit
// travels as rx completion — it only becomes a `complete` EVENT where
// the protocol materializes it: subscribe bursts and the root)
const scriptedDeliveries = (
  source: SourceId,
  entries: { tick: number; val: Val }[],
  deliver: (emit: InstEmit<Val>, isLast: boolean) => void,
) =>
  entries.map(({ tick, val }) => ({
    tick,
    fire: ({ instant, isLast }: Arrival) =>
      deliver(
        {
          events: [
            ...(isLast
              ? [{ type: "close", source, reason: "exhausted" } as const]
              : []),
            { type: "value", value: val } as const,
          ],
          instant,
          source,
          kind: "delivery",
        },
        isLast,
      ),
  }));

// hot: one Subject, async values registered at absolute ticks up
// front (anchor 0, live whether or not anyone subscribes — a value
// with no subscribers is dropped, and still costs fuel); cold: a
// defer factory — a fresh source per subscription, sync burst firing
// in the subscriber's instant (id-inheritance), async values
// re-anchored at the subscription's tick. Every subscription leads
// with its own init emit; a cold with no async tail is spent inside
// its own burst (init, values, close, complete — Agda's oneShotBurst).
export const makeInputSource = (
  driver: Driver,
  input: ObservableInput<Val>,
): Observable<InstEmit<Val>> => {
  if (input.type === "hot") {
    const source = driver.mintSourceId();
    const subject = new Subject<InstEmit<Val>>();
    // the completion latch flips BEFORE the final value fans out —
    // matching the Agda cascade, which latches a spent source before
    // its last delivery — so a subscriber joining mid-final-cascade
    // (or any time later) gets the one-shot below, never a
    // registration that would be dropped without its close
    let completed = false;
    driver.registerSource(
      scriptedDeliveries(source, resolveTicks(0, input.async), (emit, isLast) => {
        if (isLast) completed = true;
        subject.next(emit);
        if (isLast) subject.complete();
      }),
    );
    return defer(() =>
      completed
        ? of<InstEmit<Val>>({
            events: [
              { type: "init", source },
              { type: "close", source, reason: "exhausted" },
              { type: "complete" },
            ],
            instant: driver.currentInstant(),
            source,
            kind: "subscribe",
          })
        : merge(
            of<InstEmit<Val>>({
              events: [{ type: "init", source }],
              instant: driver.currentInstant(),
              source,
              kind: "subscribe",
            }),
            subject,
          ),
    );
  }
  return defer(() => {
    const source = driver.mintSourceId();
    const spent = input.async.length === 0;
    const burst: InstEmit<Val> = {
      events: [
        { type: "init", source },
        ...input.sync.map((value) => ({ type: "value", value }) as const),
        ...(spent
          ? [
              { type: "close", source, reason: "exhausted" } as const,
              { type: "complete" } as const,
            ]
          : []),
      ],
      instant: driver.currentInstant(),
      source,
      kind: "subscribe",
    };
    return spent
      ? of(burst)
      : merge(
          of(burst),
          new Observable<InstEmit<Val>>((subscriber) =>
            driver.registerSource(
              scriptedDeliveries(
                source,
                resolveTicks(driver.currentTick(), input.async),
                (emit, isLast) => {
                  subscriber.next(emit);
                  if (isLast) subscriber.complete();
                },
              ),
            ),
          ),
        );
  });
};
