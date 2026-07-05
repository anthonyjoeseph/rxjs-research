import { pipeWith } from "pipe-ts";
import { EMPTY, map, of, share } from "../basic-primitives";
import { cold, InstantSubject } from "../constructors";
import { merge } from "../util";
import { record } from "./helpers";

describe("batchSimultaneous", () => {
  it("batches the synchronous values of `of` into a single emission", () => {
    const rec = record(of(1, 2, 3));
    expect(rec.batches).toEqual([[1, 2, 3]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("emits nothing for EMPTY and completes", () => {
    const rec = record(EMPTY);
    expect(rec.batches).toEqual([]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("emits singleton batches for a lone async source", () => {
    const s = new InstantSubject<number>();
    const rec = record(s);
    s.next(1);
    expect(rec.batches).toEqual([[1]]);
    s.next(2);
    expect(rec.batches).toEqual([[1], [2]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("keeps two independent sources in separate batches", () => {
    const s1 = new InstantSubject<number>();
    const s2 = new InstantSubject<number>();
    const rec = record(merge<number>(s1, s2));
    s1.next(1);
    expect(rec.batches).toEqual([[1]]);
    s2.next(10);
    expect(rec.batches).toEqual([[1], [10]]);
    s1.next(2);
    expect(rec.batches).toEqual([[1], [10], [2]]);
    s1.complete();
    s2.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("batches a three-way diamond", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      merge<number>(
        s,
        pipeWith(
          s,
          map((n: number) => n * 10),
        ),
        pipeWith(
          s,
          map((n: number) => n * 100),
        ),
      ),
    );
    s.next(1);
    expect(rec.batches).toEqual([[1, 10, 100]]);
    s.next(2);
    expect(rec.batches).toEqual([
      [1, 10, 100],
      [2, 20, 200],
    ]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("batches a diamond over a shared cold observable driven by timers", () => {
    jest.useFakeTimers();
    try {
      const a = cold<number>((subscriber) => {
        let count = 0;
        const id = setInterval(() => {
          subscriber.next(count++);
          if (count > 2) {
            subscriber.complete();
            clearInterval(id);
          }
        }, 1000);
        return () => clearInterval(id);
      }).pipe(share);

      const rec = record(
        merge<number>(
          a,
          pipeWith(
            a,
            map((n: number) => n * 2),
          ),
        ),
      );

      jest.advanceTimersByTime(1000);
      expect(rec.batches).toEqual([[0, 0]]);
      jest.advanceTimersByTime(1000);
      expect(rec.batches).toEqual([
        [0, 0],
        [1, 2],
      ]);
      jest.advanceTimersByTime(1000);
      expect(rec.batches).toEqual([
        [0, 0],
        [1, 2],
        [2, 4],
      ]);
      expect(rec.isCompleted()).toBe(true);
    } finally {
      jest.useRealTimers();
    }
  });
});
