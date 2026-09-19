import { Observable } from "rxjs";
import { InstEmit, SourceId } from "./inst-emit.js";
import { Val } from "./exp.js";
import { Arrival, Driver } from "./driver.js";
import { LiveSink, cold, hot } from "./constructors.js";
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
// registration's close and then spends the source (the fin bit
// travels as rx completion — it only becomes a `complete` EVENT where
// the protocol materializes it: subscribe bursts and the root)
const scriptedDeliveries = (
  source: SourceId,
  entries: { tick: number; val: Val }[],
  sink: LiveSink<InstEmit<Val>>,
) =>
  entries.map(({ tick, val }) => ({
    tick,
    fire: ({ instant, isLast }: Arrival) =>
      sink.next(
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

// A scripted slot is one of the two source shapes with its deliveries
// read off the script: a hot registers at absolute ticks up front
// (anchor 0), a cold re-anchors at the subscription's own tick and
// fires its sync values inside the subscribing frame. Everything else
// — the id, the init, the one-shot burst when there is no async tail —
// belongs to the constructors and is not restated here.
export const makeInputSource = (
  driver: Driver,
  input: ObservableInput<Val>,
  index: number,
): Observable<InstEmit<Val>> =>
  input.type === "hot"
    ? hot<Val>(driver, index, (source, sink) => {
        driver.registerSource(
          scriptedDeliveries(source, resolveTicks(0, input.async), sink),
          index,
        );
      })
    : cold<Val>(driver, (source) => ({
        sync: input.sync.map((value) => ({ type: "value", value }) as const),
        async:
          input.async.length === 0
            ? undefined
            : (sink) =>
                driver.registerSource(
                  scriptedDeliveries(
                    source,
                    resolveTicks(driver.currentTick(), input.async),
                    {
                      next: (emit, isLast) => {
                        sink.next(emit);
                        if (isLast) sink.complete();
                      },
                    },
                  ),
                ),
      }));
