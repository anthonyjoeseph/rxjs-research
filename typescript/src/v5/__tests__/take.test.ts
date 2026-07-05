import { pipeWith } from "pipe-ts";
import { map, of, take } from "../basic-primitives";
import { InstantSubject } from "../constructors";
import { merge } from "../util";
import { record } from "./helpers";

describe("take", () => {
  it("truncates the synchronous values of `of`", () => {
    const rec = record(pipeWith(of(1, 2, 3), take(2)));
    expect(rec.batches).toEqual([[1, 2]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("passes everything through when the source has fewer values", () => {
    const rec = record(pipeWith(of(1, 2), take(5)));
    expect(rec.batches).toEqual([[1, 2]]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("completes an async source after n values", () => {
    const s = new InstantSubject<number>();
    const rec = record(pipeWith(s, take(2)));
    s.next(1);
    s.next(2);
    expect(rec.batches).toEqual([[1], [2]]);
    expect(rec.isCompleted()).toBe(true);
    s.next(3);
    expect(rec.batches).toEqual([[1], [2]]);
  });

  it("take(0) completes immediately", () => {
    const s = new InstantSubject<number>();
    const rec = record(pipeWith(s, take(0)));
    expect(rec.batches).toEqual([]);
    expect(rec.isCompleted()).toBe(true);
  });

  it("a taken branch of a diamond leaves the rest of the diamond intact", () => {
    const s = new InstantSubject<number>();
    const rec = record(merge<number>(s, pipeWith(s, take(1))));
    s.next(1);
    expect(rec.batches).toEqual([[1, 1]]);
    // the taken branch has closed: later values are no longer waited on
    s.next(2);
    expect(rec.batches).toEqual([[1, 1], [2]]);
    s.complete();
    expect(rec.isCompleted()).toBe(true);
  });

  it("composes with map", () => {
    const s = new InstantSubject<number>();
    const rec = record(
      pipeWith(
        s,
        take(2),
        map((n: number) => n * 10),
      ),
    );
    s.next(1);
    s.next(2);
    s.next(3);
    expect(rec.batches).toEqual([[10], [20]]);
    expect(rec.isCompleted()).toBe(true);
  });
});
