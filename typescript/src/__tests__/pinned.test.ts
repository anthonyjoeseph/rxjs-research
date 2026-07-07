/**
 * Pinned cases: each one transcribes a proven Agda theorem (Burst.agda /
 * Protocol.agda) and checks the live machinery — and, where the program is
 * inside the model's validity domain, the model too.
 */
import * as r from "rxjs";
import { InstantSubject, merge, of, share, take, mergeMap, map, scan, concat } from "../primitives";
import { batchSimultaneous } from "../batch-simultaneous";
import { Exp, mergeE, mergeMapE, concatE, modelBatches } from "../model";
import { implBatches } from "../interp";
import { Instantaneous } from "../types";

const collect = (inst: Instantaneous<number>): { batches: number[][]; done: () => void } => {
  const batches: number[][] = [];
  const sub = batchSimultaneous(inst).subscribe((b) => batches.push(b));
  return { batches, done: () => sub.unsubscribe() };
};

const ref = (slot: number): Exp => ({ k: "shareRef", first: false, slot });

describe("burst pinned (Agda theorem transcriptions)", () => {
  test("frame-batch: one subscribe = one batch (merge of colds)", () => {
    const { batches, done } = collect(merge(of([1, 2]), of([3])));
    done();
    expect(batches).toEqual([[1, 2, 3]]);
  });

  test("frame-batch: concat of colds is still one frame batch", () => {
    const { batches, done } = collect(concat(of([1, 2]), of([3])));
    done();
    expect(batches).toEqual([[1, 2, 3]]);
  });

  test("protocol-diamond: each .next() batches both copies", () => {
    const s = new InstantSubject<number>();
    const { batches, done } = collect(
      merge(s.inst, map((n: number) => n * 2)(s.inst)),
    );
    s.next(5);
    s.next(6);
    done();
    expect(batches).toEqual([
      [5, 10],
      [6, 12],
    ]);
  });

  test("two subjects are two instants", () => {
    const a = new InstantSubject<number>();
    const b = new InstantSubject<number>();
    const { batches, done } = collect(merge(a.inst, b.inst));
    a.next(1);
    b.next(2);
    done();
    expect(batches).toEqual([[1], [2]]);
  });

  test("cascade: spawned inner batches with its trigger (multi-value unit)", () => {
    const s = new InstantSubject<number>();
    const { batches, done } = collect(
      merge(
        s.inst,
        mergeMap((n: number) => of([n * 10, n * 10 + 1]))(s.inst),
      ),
    );
    s.next(5);
    done();
    expect(batches).toEqual([[5, 50, 51]]);
  });

  test("completion cascade: take(1) close pulls the queued cold into the batch", () => {
    const s = new InstantSubject<number>();
    const { batches, done } = collect(
      merge(s.inst, concat(take(1)(s.inst), of([9]))),
    );
    s.next(5);
    s.next(6);
    done();
    expect(batches).toEqual([[5, 5, 9], [6]]);
  });

  test("cold-share-lives (Protocol.agda, rxjs-confirmed): shared of(5) twice = [5,5]", () => {
    const shared = share(of([5]));
    const { batches, done } = collect(merge(shared, shared));
    done();
    expect(batches).toEqual([[5, 5]]);
  });

  test("share-diamond: one connection, two refs, one batch", () => {
    const s = new InstantSubject<number>();
    const shared = share(s.inst);
    const { batches, done } = collect(
      merge(map((n: number) => n + 1)(shared), map((n: number) => n * 10)(shared)),
    );
    s.next(5);
    done();
    expect(batches).toEqual([[6, 50]]);
  });

  test("late-join growth (readme-late-subscriber): [7,7] then [8,8,8]", () => {
    const src = new InstantSubject<number>();
    const trigger = new InstantSubject<number>();
    const { batches, done } = collect(
      merge(src.inst, mergeMap(() => src.inst)(trigger.inst)),
    );
    trigger.next(0);
    src.next(7);
    trigger.next(0);
    src.next(8);
    done();
    expect(batches).toEqual([
      [7, 7],
      [8, 8, 8],
    ]);
  });

  test("ranked-delivery (Protocol.agda): spawn arm written first still delivers second", () => {
    const src = new InstantSubject<number>();
    const trigger = new InstantSubject<number>();
    const shared = share(src.inst);
    const f = (n: number): number => n * 100;
    const g = (n: number): number => n + 1;
    const { batches, done } = collect(
      merge(
        // spawn arm, syntactically LEFT
        mergeMap(() => map(f)(shared))(trigger.inst),
        // static arm, syntactically RIGHT — but registered FIRST
        map(g)(shared),
      ),
    );
    trigger.next(0);
    src.next(7);
    done();
    // registration order, not syntactic order
    expect(batches).toEqual([[8, 700]]);
  });

  test("transient ref: take-limited ref leaves, survivor keeps receiving", () => {
    const s = new InstantSubject<number>();
    const { batches, done } = collect(merge(take(1)(s.inst), s.inst));
    s.next(1);
    s.next(2);
    done();
    expect(batches).toEqual([[1, 1], [2]]);
  });

  test("scan folds in delivery order across the diamond", () => {
    const s = new InstantSubject<number>();
    const { batches, done } = collect(
      scan((acc: number, n: number) => acc + n, 0)(
        merge(s.inst, map((n: number) => n * 2)(s.inst)),
      ),
    );
    s.next(5);
    s.next(1);
    done();
    expect(batches).toEqual([
      [5, 15],
      [16, 18],
    ]);
  });

  test("take splits instants mid-batch", () => {
    const s = new InstantSubject<number>();
    const { batches, done } = collect(
      take(3)(merge(s.inst, map((n: number) => n * 2)(s.inst))),
    );
    s.next(5);
    s.next(6);
    done();
    expect(batches).toEqual([[5, 10], [6]]);
  });

  test("model agrees on a letShare diamond program (validity domain)", () => {
    const e: Exp = {
      k: "letShare",
      src: { k: "shareRef", first: false, slot: 0 },
      body: mergeE(
        { k: "map", f: { op: "add", k: 1 }, e: { k: "shareRef", first: true, slot: 0 } },
        { k: "map", f: { op: "mul", k: 10 }, e: { k: "shareRef", first: false, slot: 0 } },
      ),
    };
    // slots inside letShare body: 0 = the share, 1.. = roots (shifted)
    const d = [{ slot: 0, value: 5 }];
    expect(implBatches(e, 1, d)).toEqual(modelBatches(e, 1, d));
    expect(modelBatches(e, 1, d)).toEqual([[6, 50]]);
  });

  test("model agrees on the late-join program", () => {
    const e: Exp = mergeE(
      ref(0),
      mergeMapE({ k: "refI", slot: 0 }, ref(1)),
    );
    const d = [
      { slot: 1, value: 0 },
      { slot: 0, value: 7 },
      { slot: 1, value: 0 },
      { slot: 0, value: 8 },
    ];
    expect(implBatches(e, 2, d)).toEqual(modelBatches(e, 2, d));
    expect(modelBatches(e, 2, d)).toEqual([[7, 7], [8, 8, 8]]);
  });

  test("model agrees on the completion cascade program", () => {
    const e: Exp = mergeE(ref(0), concatE({ k: "take", n: 1, e: ref(0) }, { k: "of", vs: [9] }));
    const d = [
      { slot: 0, value: 5 },
      { slot: 0, value: 6 },
    ];
    expect(implBatches(e, 1, d)).toEqual(modelBatches(e, 1, d));
    expect(modelBatches(e, 1, d)).toEqual([[5, 5, 9], [6]]);
  });

  test("KNOWN DIVERGENCE (upstream race): trigger-first wiring leaks the in-flight value", () => {
    // A trigger derived from the share's SOURCE spawns a ref of the share,
    // and the trigger arm is wired BEFORE the share connects: the spawned
    // subscription joins the share's internal subject before the share's
    // own delivery of the same event arrives, so it RECEIVES the in-flight
    // value (plain rxjs wiring order). The ratified strictly-after spec
    // (Burst.agda refView, Protocol.agda shareLives) says it misses it —
    // the spec answer here is [[8], [10, 9]]. The stray value also derails
    // the counting windows (batches regroup across instants). Wiring the
    // static arm FIRST avoids it entirely (the share fans out before the
    // trigger chain spawns). Same frontier the old oracle fenced; excluded
    // from the generator (refIMin) — to resolve either way in the morning.
    const src = new InstantSubject<number>();
    const shared = share(src.inst);
    const { batches, done } = collect(
      merge(
        mergeMap(() => shared)(src.inst), // trigger arm first: races
        map((n: number) => n + 1)(shared), // static ref connects second
      ),
    );
    src.next(7);
    src.next(9);
    done();
    // (the second event's values are stranded in a miscounted open window)
    expect(batches).toEqual([[8], [7, 10]]);
  });

  test("upstream race, static-arm-first wiring: strictly-after holds and matches spec", () => {
    const src = new InstantSubject<number>();
    const shared = share(src.inst);
    const { batches, done } = collect(
      merge(
        map((n: number) => n + 1)(shared), // static ref connects FIRST
        mergeMap(() => shared)(src.inst), // spawns fire after the fan-out
      ),
    );
    src.next(7);
    src.next(9);
    done();
    expect(batches).toEqual([[8], [10, 9]]);
  });

  test("ranked delivery over plain subjects: impl follows registration order where the flat model cannot", () => {
    // Non-canonical tree: the spawn arm is written LEFT of the static arm
    // of the same subject. The impl delivers in REGISTRATION order (the
    // ratified rank rule, Protocol.agda ranked-delivery): the static arm's
    // value first. The flat model (left-biased merge) would answer [0, 1]
    // — this shape is outside its validity domain, excluded from the
    // oracle generator by the canonicity filter.
    const trig = new InstantSubject<number>();
    const src = new InstantSubject<number>();
    const { batches, done } = collect(
      merge(
        mergeMap(() => src.inst)(trig.inst), // spawn arm, written first
        map((n: number) => n + 1)(src.inst), // static arm, registered first
      ),
    );
    trig.next(0);
    src.next(0);
    done();
    expect(batches).toEqual([[1, 0]]);
  });

  test("plain rxjs sanity mirror: share replay matches real rxjs", () => {
    // the behavior Anthony confirmed on 2026-07-07
    const shared = r.of(5).pipe(r.share());
    const got: number[] = [];
    r.merge(shared, shared).subscribe((x) => got.push(x));
    expect(got).toEqual([5, 5]);
  });
});
