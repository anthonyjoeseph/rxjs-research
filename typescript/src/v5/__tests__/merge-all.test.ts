import * as r from "rxjs";
import { pipeWith } from "pipe-ts";
import { fromInstantaneous, of } from "../basic-primitives";
import { InstantSubject } from "../constructors";
import { mergeAll } from "../joins";
import { mergeMap } from "../util";
import { Instantaneous } from "../types";
import { record } from "./helpers";

describe("mergeAll", () => {
  it("flattens nested synchronous of's, batching per inner source", () => {
    const rec = record(pipeWith(of(of(1, 2), of(3)), mergeAll()));
    expect(rec.batches).toEqual([[1, 2], [3]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("flattening without batching still yields every value", async () => {
    const result = await r.firstValueFrom(
      pipeWith(of(of(1, 2), of(3)), mergeAll(), fromInstantaneous, r.toArray()),
    );
    expect(result).toEqual([1, 2, 3]);
  });

  it("mergeMap inners inherit their trigger's instant (transitively)", () => {
    // 1, 2 and 3 share their of's instant, and each spawned inner inherits
    // its trigger value's instant — so ALL the inner values are one batch
    // (the causation rule, ratified 2026-07-06)
    const rec = record(
      pipeWith(
        of(1, 2, 3),
        mergeMap((n: number) => of(n, n * 100)),
      ),
    );
    expect(rec.batches).toEqual([[1, 100, 2, 200, 3, 300]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("handles inner observables arriving asynchronously", () => {
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(pipeWith(outer, mergeAll()));

    outer.next(of(1, 2));
    expect(rec.batches).toEqual([[1, 2]]);

    const s = new InstantSubject<number>();
    outer.next(s);
    s.next(5);
    expect(rec.batches).toEqual([[1, 2], [5]]);

    // inner subjects survive outer completion
    outer.complete();
    s.next(6);
    expect(rec.batches).toEqual([[1, 2], [5], [6]]);

    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("merges two async subjects delivered through an async outer", () => {
    const outer = new InstantSubject<Instantaneous<number>>();
    const rec = record(pipeWith(outer, mergeAll()));

    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    outer.next(s1);
    outer.next(s2);

    s1.next(1);
    expect(rec.batches).toEqual([[1]]);
    s2.next(10);
    expect(rec.batches).toEqual([[1], [10]]);
    s1.next(2);
    expect(rec.batches).toEqual([[1], [10], [2]]);

    s1.complete();
    s2.complete();
    outer.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});
