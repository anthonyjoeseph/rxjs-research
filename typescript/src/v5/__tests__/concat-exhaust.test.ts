import { pipeWith } from "pipe-ts";
import { of } from "../basic-primitives";
import { InstantSubject } from "../constructors";
import { concatAll, exhaustAll } from "../joins";
import { Instantaneous } from "../types";
import { concat, concatMap, exhaustMap, merge } from "../util";
import { record } from "./helpers";

describe("concatAll", () => {
  it("flattens synchronous inners in order", () => {
    const rec = record(pipeWith(of(of(1, 2), of(3)), concatAll));
    expect(rec.batches).toEqual([[1, 2], [3]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("concat(a, b) is the variadic derived form", () => {
    const rec = record(concat(of(1, 2), of(3)));
    expect(rec.batches).toEqual([[1, 2], [3]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("serializes synchronously delivered async inners", () => {
    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    const inners: Instantaneous<number>[] = [s1, s2];
    const rec = record(pipeWith(of(...inners), concatAll));

    s1.next(1);
    expect(rec.batches).toEqual([[1]]);
    s2.next(99); // s2 not yet subscribed: dropped
    expect(rec.batches).toEqual([[1]]);

    s1.complete(); // now s2 subscribes
    s2.next(2);
    expect(rec.batches).toEqual([[1], [2]]);
    s2.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("queues async-arriving inners behind the active one", () => {
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(pipeWith(outer, concatAll));

    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    outer.next(s1);
    outer.next(s2);
    s1.next(1);
    s2.next(99); // queued inner: not subscribed yet
    expect(rec.batches).toEqual([[1]]);

    s1.complete();
    s2.next(2);
    expect(rec.batches).toEqual([[1], [2]]);

    s2.complete();
    outer.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("concatMap flattens in order; inners inherit the trigger instant", () => {
    // both triggers share their of's instant, so the serially subscribed
    // inners inherit it too — one batch, in subscription order (the
    // causation rule: derivation creates simultaneity, sync or async)
    const rec = record(
      pipeWith(
        of(1, 2),
        concatMap((n: number) => of(n, n + 1)),
      ),
    );
    expect(rec.batches).toEqual([[1, 2, 2, 3]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("concatMapped values stay simultaneous with their source (diamond)", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          concatMap((n: number) => of(n * 10)),
        ),
      ),
    );
    s.next(5);
    expect(rec.batches).toEqual([[5, 50]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});

describe("exhaustAll", () => {
  it("a sync-completing inner frees the slot for the next in the burst", () => {
    const rec = record(pipeWith(of(of(1), of(2)), exhaustAll));
    expect(rec.batches).toEqual([[1], [2]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("a live first inner blocks the rest of the burst", () => {
    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    const inners: Instantaneous<number>[] = [s1, s2];
    const rec = record(pipeWith(of(...inners), exhaustAll));

    s1.next(1);
    s2.next(99); // dropped: never subscribed
    expect(rec.batches).toEqual([[1]]);

    s1.complete();
    expect(rec.isCompleted()).toBe(true);
    s2.next(2);
    expect(rec.batches).toEqual([[1]]);
  });

  it("drops inners that arrive while one is active", () => {
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(pipeWith(outer, exhaustAll));

    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    const s3 = new InstantSubject<number>();
    outer.next(s1);
    s1.next(1);
    outer.next(s2); // dropped: s1 still active
    s2.next(99);
    expect(rec.batches).toEqual([[1]]);

    s1.complete();
    outer.next(s3); // accepted: nothing active
    s3.next(3);
    expect(rec.batches).toEqual([[1], [3]]);

    s3.complete();
    outer.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("exhaustMap ignores triggers while the inner is active", () => {
    const s = new InstantSubject<number>();
    const inners = [new InstantSubject<number>(), new InstantSubject<number>()];
    let call = 0;
    const rec = record(
      pipeWith(
        s,
        exhaustMap(() => inners[call++]),
      ),
    );

    s.next(0); // subscribes inners[0]
    inners[0].next(10);
    s.next(1); // inners[0] active: this trigger's inner is dropped
    inners[1].next(99);
    expect(rec.batches).toEqual([[10]]);

    inners[0].complete();
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});
