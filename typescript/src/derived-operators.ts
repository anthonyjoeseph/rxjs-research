// DERIVED OPERATORS: the srxjs palette a user composes, each written
// over the primitives and over nothing else.  A file of its own because
// the boundary is the point -- a primitive is a former the evaluator
// knows about and the object language has a constructor for, and
// everything here is a composition the language could not tell from a
// hand-written pipeline.  Adding one costs no former, no decoder clause
// and no theorem; adding a primitive costs all three.

import { Observable } from "rxjs";
import { InstEmit } from "./inst-emit.js";
import { Driver } from "./driver.js";
import { defer, map, of } from "./primitive-operators.js";
import { mergeAllAll } from "./join.js";

// expand: rxjs's recursive flattener — every value emitted (the source's own and every projected one) is
// re-projected and merged, which is `mergeAll` over an outer whose
// inner is one value's whole expansion.
//
// AND IT IS BREADTH-FIRST, WHICH PLAIN RXJS IS NOT, AND THAT IS NOT A
// BUG TO FIX HERE.  The recursion must be guarded — nothing else stops
// it running at construction — and the only lazy former this language
// has is `defer`, which costs a schedule hop by design, since that hop
// is what breaks mu's unfolding regress.  So each level of the
// expansion lands in its own instant.  Plain rxjs subscribes the
// projection inside the frame that produced the value, so the whole
// expansion is ONE frame.
//
// The values agree as a multiset and disagree in order and, more to the
// point, in BATCHING: a countdown from three is one batch in rxjs and
// four here, one per tick.  Closing that gap means either a former of
// its own or a mu that unfolds without a hop, and both decide what
// every theorem above quantifies over — so neither is taken here.
export const expand = <A>(
  driver: Driver,
  project: (a: A) => Observable<InstEmit<A>>,
) => {
  // one value's expansion: the value, and the recursion on its
  // projection, as two inners of a single outer emit — so both are
  // subscribed inside the frame that carried the value and the join's
  // id-inheritance puts them in that emit's instant.
  function fromValue(a: A): Observable<InstEmit<A>> {
    return mergeAllAll(undefined)(
      of<Observable<InstEmit<A>>>(driver, [
        of<A>(driver, [a]),
        defer(driver, () => expandAll(project(a))),
      ]),
    );
  }
  function expandAll(src: Observable<InstEmit<A>>): Observable<InstEmit<A>> {
    return mergeAllAll(undefined)(map(src, fromValue));
  }
  return expandAll;
};
