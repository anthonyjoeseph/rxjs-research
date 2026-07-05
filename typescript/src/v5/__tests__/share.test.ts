import { pipeWith } from "pipe-ts";
import { fromInstantaneous, map, of, share } from "../basic-primitives";
import { cold, InstantSubject } from "../constructors";
import { InstEmit, InstInit, values } from "../types";
import { merge, scan } from "../util";
import { record } from "./helpers";

const flatValues = <A>(emits: InstEmit<A>[]): A[] =>
  emits.flatMap((e) => values(e));

describe("share", () => {
  it("late subscribers miss past values but share the provenance and see the future", () => {
    let emit: (n: number) => void = () => {};
    const a = cold<number>((sub) => {
      emit = (n) => sub.next(n);
    }).pipe(share);

    const first: InstEmit<number>[] = [];
    const second: InstEmit<number>[] = [];
    a.subscribe((e) => first.push(e));
    emit(1);
    a.subscribe((e) => second.push(e));
    emit(2);

    expect(flatValues(first)).toEqual([1, 2]);
    expect(flatValues(second)).toEqual([2]); // 1 happened before B existed
    expect((second[0] as InstInit<number>).type).toBe("init");
    expect((second[0] as InstInit<number>).provenance).toBe(
      (first[0] as InstInit<number>).provenance,
    );
  });

  it("unsubscribing one subscriber does not kill the others", () => {
    let emit: (n: number) => void = () => {};
    const a = cold<number>((sub) => {
      emit = (n) => sub.next(n);
    }).pipe(share);

    const first: number[] = [];
    pipeWith(a, fromInstantaneous).subscribe((n) => first.push(n));
    const subB = pipeWith(a, fromInstantaneous).subscribe();
    emit(1);
    subB.unsubscribe(); // the old implementation tore down upstream here
    emit(2);
    expect(first).toEqual([1, 2]);
  });

  it("disconnects upstream only when the last subscriber leaves", () => {
    let tornDown = false;
    const a = cold<number>(() => () => {
      tornDown = true;
    }).pipe(share);

    const s1 = a.subscribe();
    const s2 = a.subscribe();
    s1.unsubscribe();
    expect(tornDown).toBe(false);
    s2.unsubscribe();
    expect(tornDown).toBe(true);
  });

  it("a completed share resets: the next subscriber starts a fresh life", () => {
    const a = of(1, 2, 3).pipe(share);
    const rec1 = record(a);
    expect(rec1.batches).toEqual([[1, 2, 3]]);
    expect(rec1.isCompleted()).toBe(true);
    const rec2 = record(a);
    expect(rec2.batches).toEqual([[1, 2, 3]]);
    expect(rec2.isCompleted()).toBe(true);
  });

  it("fan-out delivery order: a share's refs receive consecutively", () => {
    const s = new InstantSubject<number>();
    const x = share(
      pipeWith(
        s,
        map((n: number) => n * 10),
      ),
    );
    // merge(x, s, map(+1)(x)): the share connects to s at x's (leftmost)
    // position, so both refs' values precede the raw branch's
    const rec = record(
      merge<number>(
        x,
        s,
        pipeWith(
          x,
          map((n: number) => n + 1),
        ),
      ),
    );
    s.next(5);
    expect(rec.batches).toEqual([[50, 51, 5]]);
  });

  it("the shared diamond still batches", () => {
    let emit: (n: number) => void = () => {};
    const a = cold<number>((sub) => {
      emit = (n) => sub.next(n);
    }).pipe(share);
    const rec = record(
      merge<number>(
        a,
        pipeWith(
          a,
          map((n: number) => n * 10),
        ),
      ),
    );
    emit(5);
    expect(rec.batches).toEqual([[5, 50]]);
  });
});

describe("accumulate", () => {
  it("keeps state per subscription", () => {
    const s = new InstantSubject<number>();
    const acc = pipeWith(
      s,
      scan(0, (a: number, b: number) => a + b),
    );
    const out1: number[] = [];
    const out2: number[] = [];
    pipeWith(acc, fromInstantaneous).subscribe((n) => out1.push(n));
    pipeWith(acc, fromInstantaneous).subscribe((n) => out2.push(n));
    s.next(1);
    s.next(2);
    // with the old shared-closure state, the two subscriptions interleaved
    // writes into one accumulator ([1, 4] / [2, 6])
    expect(out1).toEqual([1, 3]);
    expect(out2).toEqual([1, 3]);
  });
});
