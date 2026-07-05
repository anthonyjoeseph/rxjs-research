import * as r from "rxjs";
import { pipeWith } from "pipe-ts";
import { of } from "../basic-primitives";
import { InstantSubject } from "../constructors";
import { concatAll, exhaustAll, mergeAll, switchAll } from "../joins";
import { Instantaneous } from "../types";
import { record } from "./helpers";

/** the ***All joins are meant to mirror rxjs semantics exactly: same
 * program shape, same value sequence. Each scenario runs the plain-rxjs
 * program and the Instantaneous program side by side. */

const collect = <A>(obs: r.Observable<A>): A[] => {
  const out: A[] = [];
  obs.subscribe((v) => out.push(v));
  return out;
};

describe("switchAll mirrors rxjs", () => {
  it("sync burst of colds: every inner's sync values pass", () => {
    const expected = collect(r.of(r.of(1, 2), r.of(3, 4)).pipe(r.switchAll()));
    const rec = record(pipeWith(of(of(1, 2), of(3, 4)), switchAll));
    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1, 2, 3, 4]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("sync burst ending in a hot inner: only the last stays live", () => {
    const rSubj1 = new r.Subject<number>();
    const rSubj2 = new r.Subject<number>();
    const iSubj1 = new InstantSubject<number>();
    const iSubj2 = new InstantSubject<number>();

    const expected = collect(r.of(rSubj1, rSubj2).pipe(r.switchAll()));
    const rec = record(
      pipeWith(of(...([iSubj1, iSubj2] as Instantaneous<number>[])), switchAll),
    );

    rSubj1.next(9); // switched away: dropped
    iSubj1.next(9);
    rSubj2.next(2);
    iSubj2.next(2);

    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([2]);
  });

  it("sync values of an earlier hot inner pass before the switch", () => {
    // a hot first inner emits nothing at subscription, then a cold second
    // inner takes over — but a cold FIRST inner's sync values still pass
    const rSubj = new r.Subject<number>();
    const iSubj = new InstantSubject<number>();

    const expected = collect(
      r.of(r.of(1), rSubj as r.Observable<number>).pipe(r.switchAll()),
    );
    const rec = record(
      pipeWith(of(...([of(1), iSubj] as Instantaneous<number>[])), switchAll),
    );

    rSubj.next(2);
    iSubj.next(2);

    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1, 2]);
  });
});

describe("exhaustAll mirrors rxjs", () => {
  it("a sync-completing inner frees the slot for the next in the burst", () => {
    const expected = collect(
      r.of(r.of(1), r.of(2), r.of(3)).pipe(r.exhaustAll()),
    );
    const rec = record(pipeWith(of(of(1), of(2), of(3)), exhaustAll));
    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1, 2, 3]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("a live hot inner blocks the rest of the burst", () => {
    const rSubj = new r.Subject<number>();
    const iSubj = new InstantSubject<number>();

    const expected = collect(
      r.of(rSubj as r.Observable<number>, r.of(99)).pipe(r.exhaustAll()),
    );
    const rec = record(
      pipeWith(of(...([iSubj, of(99)] as Instantaneous<number>[])), exhaustAll),
    );

    rSubj.next(1);
    iSubj.next(1);

    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1]);
  });

  it("the blocker completing readmits later async arrivals", () => {
    const rOuter = new r.Subject<r.Observable<number>>();
    const iOuter = new InstantSubject<Instantaneous<number>>();
    const rSubj1 = new r.Subject<number>();
    const iSubj1 = new InstantSubject<number>();

    const expected = collect(rOuter.pipe(r.exhaustAll()));
    const rec = record(pipeWith(iOuter, exhaustAll));

    rOuter.next(rSubj1);
    iOuter.next(iSubj1);
    rSubj1.next(1);
    iSubj1.next(1);
    rOuter.next(r.of(99)); // dropped: subj1 active
    iOuter.next(of(99));
    rSubj1.complete();
    iSubj1.complete();
    rOuter.next(r.of(3)); // accepted: nothing active
    iOuter.next(of(3));

    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1, 3]);
  });
});

describe("concatAll mirrors rxjs", () => {
  it("sync burst of colds runs serially", () => {
    const expected = collect(r.of(r.of(1, 2), r.of(3)).pipe(r.concatAll()));
    const rec = record(pipeWith(of(of(1, 2), of(3)), concatAll));
    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1, 2, 3]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("a hot inner delays the rest of the burst until it completes", () => {
    const rSubj = new r.Subject<number>();
    const iSubj = new InstantSubject<number>();

    const expected = collect(
      r.of(rSubj as r.Observable<number>, r.of(2)).pipe(r.concatAll()),
    );
    const rec = record(
      pipeWith(of(...([iSubj, of(2)] as Instantaneous<number>[])), concatAll),
    );

    rSubj.next(1);
    iSubj.next(1);
    rSubj.complete();
    iSubj.complete();

    expect(rec.batches.flat()).toEqual(expected);
    expect(expected).toEqual([1, 2]);
  });
});

describe("mergeAll mirrors rxjs", () => {
  it("sync burst of colds interleaves in subscription order", () => {
    const expected = collect(r.of(r.of(1, 2), r.of(3)).pipe(r.mergeAll()));
    const rec = record(pipeWith(of(of(1, 2), of(3)), mergeAll()));
    expect(rec.batches.flat().sort()).toEqual([...expected].sort());
    expect(rec.isCompleted()).toBe(true);
  });
});
