import * as r from "rxjs";
import { pipeWith } from "pipe-ts";
import { fromInstantaneous, map, of } from "../basic-primitives";
import { async, close, init, map as mapEmit, val } from "../types";
import { InstantSubject } from "../constructors";
import { merge } from "../util";
import { record } from "./helpers";

describe("map (emission primitive)", () => {
  const prov = Symbol("outer");
  const inner = Symbol("inner");

  it("maps values inside an init emission and preserves provenance", () => {
    const emit = init<number>({
      provenance: prov,
      children: [val(1), val(2), close],
    });
    expect(mapEmit(emit, (n) => n * 10)).toEqual(
      init<number>({
        provenance: prov,
        // mapped values are marked derived: a join subscribing them knows
        // the spawned inner inherits the trigger's instant
        children: [
          { ...val(10), derived: true },
          { ...val(20), derived: true },
          close,
        ],
      }),
    );
  });

  it("maps values nested inside async emissions", () => {
    const emit = async<number>({
      provenance: prov,
      child: async<number>({ provenance: inner, child: val(5) }),
    });
    expect(mapEmit(emit, (n) => n + 1)).toEqual(
      async<number>({
        provenance: prov,
        child: async<number>({
          provenance: inner,
          child: { ...val(6), derived: true },
        }),
      }),
    );
  });

  it("leaves close and null children untouched", () => {
    const closing = async<number>({ provenance: prov, child: close });
    expect(mapEmit(closing, (n) => n * 2)).toEqual(closing);
    const empty = async<number>({ provenance: prov, child: null });
    expect(mapEmit(empty, (n) => n * 2)).toEqual(empty);
  });
});

describe("map (operator)", () => {
  it("maps synchronous values", async () => {
    const result = await r.firstValueFrom(
      pipeWith(
        of(1, 2, 3),
        map((n) => n * 2),
        fromInstantaneous,
        r.toArray(),
      ),
    );
    expect(result).toEqual([2, 4, 6]);
  });

  it("composes: map(g) after map(f) behaves like map(g . f)", async () => {
    const result = await r.firstValueFrom(
      pipeWith(
        of(1, 2, 3),
        map((n) => n + 1),
        map((n) => n * 10),
        fromInstantaneous,
        r.toArray(),
      ),
    );
    expect(result).toEqual([20, 30, 40]);
  });

  it("maps async values from a subject", () => {
    const s = new InstantSubject<number>();
    const seen: number[] = [];
    pipeWith(
      s,
      map((n: number) => n * 3),
      fromInstantaneous,
    ).subscribe((n) => seen.push(n));
    s.next(1);
    s.next(2);
    expect(seen).toEqual([3, 6]);
  });

  it("a mapped observable stays simultaneous with its source (the diamond)", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          map((n: number) => n * 10),
        ),
      ),
    );
    s.next(5);
    expect(rec.batches).toEqual([[5, 50]]);
    s.next(7);
    expect(rec.batches).toEqual([
      [5, 50],
      [7, 70],
    ]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });
});
