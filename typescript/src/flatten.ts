import {
  Observable,
  connect,
  exhaustAll,
  filter,
  map,
  merge,
  mergeAll,
  switchAll,
} from "rxjs";

// THE ONE FLATTENER, as ordinary rxjs: `flattenᵉ`'s semantics, and the
// reference both trees are held to. Each outer element carries an
// optional ECHO and an optional LANE -- `(unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)`,
// each option a zero- or one-element array, since `null` is a value (the
// unit) here. The echo leaves AS THE ELEMENT ARRIVES, before its lane is
// handled; the lane is flattened under the op. So an element with no lane
// only echoes -- a filter, which no flattener limit or cancel sees -- and
// one with no echo is the old flattener's element exactly.
//
// THE ECHO IS FIRST BECAUSE `merge` SUBSCRIBES IN ORDER. `connect`
// multicasts the outer to both branches, and a multicast delivers to its
// subscribers in the order they subscribed, so every element reaches the
// echo branch before the flattening one.
export type FlatOp =
  { how: "merge"; limit?: number } | { how: "switch" } | { how: "exhaust" };

export type Opt<A> = readonly [] | readonly [A];
export type Elem<T> = { echo: Opt<T>; lane: Opt<Observable<T>> };

// the three policies over lanes alone: what happens when a lane arrives
// while the flattener is busy -- queue, cancel, drop
export const flattener =
  <T>(op: FlatOp) =>
  (lanes: Observable<Observable<T>>): Observable<T> =>
    op.how === "merge"
      ? lanes.pipe(mergeAll(op.limit ?? Infinity))
      : op.how === "switch"
        ? lanes.pipe(switchAll())
        : lanes.pipe(exhaustAll());

export const flatten =
  <T>(op: FlatOp) =>
  (outer: Observable<Elem<T>>): Observable<T> =>
    outer.pipe(
      connect((sh) =>
        merge(
          sh.pipe(
            filter((x) => x.echo.length === 1),
            map((x) => x.echo[0] as T),
          ),
          sh.pipe(
            filter((x) => x.lane.length === 1),
            map((x) => x.lane[0] as Observable<T>),
            flattener<T>(op),
          ),
        ),
      ),
    );
