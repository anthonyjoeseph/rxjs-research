import { pipeWith } from "pipe-ts";
import { EMPTY, of, share } from "../basic-primitives";
import { cold, InstantSubject } from "../constructors";
import { mergeAll, switchAll } from "../joins";
import { Instantaneous, InstEmit } from "../types";
import {
  buffer,
  bufferCount,
  filter,
  merge,
  mergeMap,
  pairwise,
  scan,
  switchMap,
  takeUntil,
  expand,
} from "../util";
import { record } from "./helpers";

describe("switchAll", () => {
  it("switches to the latest inner observable", () => {
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(pipeWith(outer, switchAll));

    const s1 = new InstantSubject<number>();
    outer.next(s1);
    s1.next(1);
    expect(rec.batches).toEqual([[1]]);

    const s2 = new InstantSubject<number>();
    outer.next(s2);
    s1.next(99); // s1 was switched away from: ignored
    expect(rec.batches).toEqual([[1]]);
    s2.next(2);
    expect(rec.batches).toEqual([[1], [2]]);

    // rxjs semantics: outer completion doesn't kill the live inner — the
    // switch completes only once the inner does. (The outer's protocol
    // close is valueless traffic: it forwards without switching.)
    outer.complete();
    expect(rec.isCompleted()).toBe(false);
    s2.next(3);
    expect(rec.batches).toEqual([[1], [2], [3]]);
    s2.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("subscribes sync-burst inners in turn, keeping only the last live", () => {
    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    const rec = record(
      pipeWith(of(...([s1, s2] as Instantaneous<number>[])), switchAll),
    );
    s1.next(99); // switched away during the burst: dropped
    expect(rec.batches).toEqual([]);
    s2.next(2);
    expect(rec.batches).toEqual([[2]]);
  });

  it("sync values of every burst inner pass before the switch", () => {
    const rec = record(pipeWith(of(of(1, 2), of(3, 4)), switchAll));
    expect(rec.batches).toEqual([
      [1, 2],
      [3, 4],
    ]);
    expect(rec.isCompleted()).toBe(true);
  });

  // switching away a LIVE inner synthesizes closes for its registrations —
  // without them, a diamond across the switch strands the shared
  // provenance's window (totalNum overcounts a subscription that will
  // never deliver again)
  it("diamond across a sync-burst switch: switched-away registration closes", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(of(...([s, of(1)] as Instantaneous<number>[])), switchAll),
      ),
    );
    // the burst: s registered then switched away (closed), of(1) emits
    expect(rec.batches).toEqual([[1]]);
    s.next(5); // only the root subscription is live: a single delivery
    expect(rec.batches).toEqual([[1], [5]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("diamond across an async switch: the old inner's registration closes", () => {
    const s = new InstantSubject<number>();
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(merge<number>(s, pipeWith(outer, switchAll)));

    outer.next(s); // second subscription of s: a live diamond
    s.next(1);
    expect(rec.batches).toEqual([[1, 1]]);

    outer.next(of(9)); // s's inner subscription switched away and closed
    expect(rec.batches).toEqual([[1, 1], [9]]);
    s.next(2); // back to a single delivery
    expect(rec.batches).toEqual([[1, 1], [9], [2]]);

    s.complete();
    outer.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("switchMap", () => {
  it("flattens each value through the function", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      pipeWith(
        s,
        switchMap((n: number) => of(n, n + 1)),
      ),
    );
    s.next(1);
    expect(rec.batches).toEqual([[1, 2]]);
    s.next(5);
    expect(rec.batches).toEqual([
      [1, 2],
      [5, 6],
    ]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("keeps switchMapped values simultaneous with their source", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          switchMap((n: number) => of(n * 10)),
        ),
      ),
    );
    s.next(5);
    expect(rec.batches).toEqual([[5, 50]]);
    s.next(6);
    expect(rec.batches).toEqual([
      [5, 50],
      [6, 60],
    ]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("a switchMap branch that filters an instant still releases the batch", () => {
    const s = new InstantSubject<number>();
    // the `switched` example from scratch.ts: filter out 0
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          switchMap((n: number) => (n === 0 ? EMPTY : of(n))),
        ),
      ),
    );
    s.next(0);
    expect(rec.batches).toEqual([[0]]);
    s.next(3);
    expect(rec.batches).toEqual([[0], [3, 3]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("diamonds through mergeMap", () => {
  it("batches all inner values with their trigger", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          mergeMap((n: number) => of(n * 10, n * 100)),
        ),
      ),
    );
    s.next(5);
    expect(rec.batches).toEqual([[5, 50, 500]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("filter", () => {
  it("filter diamond: merge(a, filter(p)(a)) batches passing instants", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          filter((n: number): n is number => n % 2 === 0),
        ),
      ),
    );
    s.next(1);
    expect(rec.batches).toEqual([[1]]);
    s.next(2);
    expect(rec.batches).toEqual([[1], [2, 2]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("keeps only passing values", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      pipeWith(
        s,
        filter((n: number): n is number => n % 2 === 0),
      ),
    );
    s.next(1);
    expect(rec.batches).toEqual([]);
    s.next(2);
    expect(rec.batches).toEqual([[2]]);
    s.next(3);
    s.next(4);
    expect(rec.batches).toEqual([[2], [4]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("scan", () => {
  it("accumulates state across emissions", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      pipeWith(
        s,
        scan(0, (acc: number, cur: number) => acc + cur),
      ),
    );
    s.next(1);
    s.next(2);
    s.next(4);
    expect(rec.batches).toEqual([[1], [3], [7]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("pairwise", () => {
  it("pairs consecutive values, seeded with an initial value", () => {
    const s = new InstantSubject<number>();
    const rec = record(pipeWith(s, pairwise(0)));
    s.next(1);
    s.next(2);
    expect(rec.batches).toEqual([[[0, 1]], [[1, 2]]]);
  });
});

describe("bufferCount", () => {
  it("emits every n values", () => {
    const s = new InstantSubject<number>();
    const rec = record(pipeWith(s, bufferCount(2)));
    s.next(1);
    expect(rec.batches).toEqual([]);
    s.next(2);
    expect(rec.batches).toEqual([[[1, 2]]]);
    s.next(3);
    expect(rec.batches).toEqual([[[1, 2]]]);
    s.next(4);
    expect(rec.batches).toEqual([[[1, 2]], [[3, 4]]]);
  });
});

describe("buffer (as currently implemented)", () => {
  // NOTE: unlike rxjs `buffer`, this emits the growing batch on every source
  // value and resets when the notifier fires, rather than emitting on the
  // notifier itself
  it("accumulates values and resets on the notifier", () => {
    const src = new InstantSubject<number>();
    const notifier = new InstantSubject<number>();
    const rec = record(pipeWith(src, buffer(notifier)));
    src.next(1);
    expect(rec.batches).toEqual([[[1]]]);
    src.next(2);
    expect(rec.batches).toEqual([[[1]], [[1, 2]]]);
    notifier.next(0);
    expect(rec.batches).toEqual([[[1]], [[1, 2]]]);
    src.next(3);
    expect(rec.batches).toEqual([[[1]], [[1, 2]], [[3]]]);
  });
});

describe("EMPTY in combinations", () => {
  it("emits nothing on its own", () => {
    const rec = record(EMPTY);
    expect(rec.batches).toEqual([]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("merge with EMPTY passes the live source through", () => {
    const s = new InstantSubject<number>();
    const rec = record(merge<number>(s, EMPTY));
    s.next(1);
    expect(rec.batches).toEqual([[1]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("mergeMap to EMPTY drops all values", () => {
    const rec = record(
      pipeWith(
        of(1, 2, 3),
        mergeMap(() => EMPTY),
      ),
    );
    expect(rec.batches).toEqual([]);
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("mergeAll with concurrency", () => {
  it("mergeAll(1) subscribes inners one at a time", () => {
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(pipeWith(outer, mergeAll(1)));

    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    outer.next(s1);
    outer.next(s2); // queued behind s1
    s1.next(1);
    s2.next(99); // s2 not yet subscribed: dropped
    expect(rec.batches).toEqual([[1]]);

    s1.complete(); // s2's turn begins
    s2.next(2);
    expect(rec.batches).toEqual([[1], [2]]);

    s2.complete();
    outer.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("share", () => {
  it("subscribes the source once and replays the init to late subscribers", () => {
    let subscriptions = 0;
    const a = cold<number>(() => {
      subscriptions += 1;
    }).pipe(share);

    const first: InstEmit<number>[] = [];
    const second: InstEmit<number>[] = [];
    a.subscribe((e) => first.push(e));
    a.subscribe((e) => second.push(e));

    expect(subscriptions).toBe(1);
    expect(first).toHaveLength(1);
    expect(first[0].type).toBe("init");
    // the late subscriber shares the provenance and misses the past, but
    // is its OWN registration: a fresh sub id
    expect(second).toHaveLength(1);
    expect(second[0].type).toBe("init");
    expect(second[0].provenance).toBe(first[0].provenance);
    expect((second[0] as { children: unknown[] }).children).toEqual(
      (first[0] as { children: unknown[] }).children,
    );
    expect(second[0].sub).toBeDefined();
    expect(second[0].sub).not.toBe(first[0].sub);
  });
});

describe("takeUntil (derived: switchAll onto EMPTY at the notifier)", () => {
  it("emits until the notifier fires, then completes", () => {
    const src = new InstantSubject<number>();
    const stop = new InstantSubject<string>();
    const rec = record(pipeWith(src, takeUntil(stop)));

    src.next(1);
    src.next(2);
    expect(rec.batches).toEqual([[1], [2]]);

    stop.next("go");
    expect(rec.isCompleted()).toBe(true);

    src.next(3); // dropped: unsubscribed at the switch
    expect(rec.batches).toEqual([[1], [2]]);
  });

  it("completes without values when the notifier fires first", () => {
    const src = new InstantSubject<number>();
    const stop = new InstantSubject<string>();
    const rec = record(pipeWith(src, takeUntil(stop)));

    stop.next("go");
    expect(rec.batches).toEqual([]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("a taken-until branch still batches with its source (diamond)", () => {
    const src = new InstantSubject<number>();
    const stop = new InstantSubject<string>();
    const rec = record(merge<number>(src, pipeWith(src, takeUntil(stop))));

    src.next(5);
    expect(rec.batches).toEqual([[5, 5]]);

    stop.next("go");
    src.next(6); // only the direct branch remains — no stranded window
    expect(rec.batches).toEqual([[5, 5], [6]]);

    src.complete();
    stop.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("completes when the source completes before the notifier", () => {
    const src = new InstantSubject<number>();
    const stop = new InstantSubject<string>();
    const rec = record(pipeWith(src, takeUntil(stop)));

    src.next(1);
    src.complete();
    stop.complete();
    expect(rec.batches).toEqual([[1]]);
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("expand (derived: recursive mergeMap feedback)", () => {
  const doubleUntil8 = (n: number): Instantaneous<number> =>
    n < 8 ? of(n * 2) : EMPTY;

  it("a synchronous expansion chain is ONE instant (the causation rule)", () => {
    const s = new InstantSubject<number>();
    const rec = record(pipeWith(s, expand(doubleUntil8)));

    s.next(1);
    // 1 spawns 2 spawns 4 spawns 8 — all caused by the one event
    expect(rec.batches).toEqual([[1, 2, 4, 8]]);

    s.next(3);
    expect(rec.batches).toEqual([
      [1, 2, 4, 8],
      [3, 6, 12],
    ]);

    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("expansion of a cold source happens at its subscription instant", () => {
    const rec = record(pipeWith(of(1), expand(doubleUntil8)));
    expect(rec.batches).toEqual([[1, 2, 4, 8]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("the expanded diamond: cascade batches with its root event", () => {
    const s = new InstantSubject<number>();
    const rec = record(merge<number>(s, pipeWith(s, expand(doubleUntil8))));
    s.next(2);
    expect(rec.batches).toEqual([[2, 2, 4, 8]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("multi-value expansions walk depth-first, like rxjs", () => {
    // 1 → [10, 20], both terminal; mirrors rxjs expand's synchronous order
    const fanOut = (n: number): Instantaneous<number> =>
      n < 10 ? of(n * 10, n * 10 + 10) : EMPTY;
    const s = new InstantSubject<number>();
    const rec = record(pipeWith(s, expand(fanOut)));
    s.next(1);
    expect(rec.batches).toEqual([[1, 10, 20]]);
  });
});
