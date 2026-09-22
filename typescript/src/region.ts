import { Exp, Tm } from "./exp.js";
import type { TestCase } from "./prop-test.js";

// THE REGION IS THE COVERAGE CLAIM, SO IT IS A PREDICATE AND NOT A
// MEMORY.  A carrier that hands a subscription's whole emission back as
// a LIST is sound exactly while a reaction to a value cannot change what
// the source still owes, and measurement has put the disagreement in one
// place: a SHARE, a SYNCHRONOUS burst of at least two values through it,
// and a subscription to THAT share caused by one of those values.  Drop
// any one of the three and the two carriers agree.
//
// WHY IT IS WORTH A FILE.  A green sweep beside a red pinned corpus is
// not two results, it is one finding -- the draw never reached the
// region -- and that finding is invisible as long as coverage is a thing
// somebody remembers checking.  Counted on every run, a draw that stops
// reaching it fails loudly instead of reading as a stronger green.
//
// The three tests are all UNDER-approximations: an unknown answers NO.
// That is the safe direction for a coverage count, which would otherwise
// report its own optimism as reach.
//
// AND THE UNDER-READING IS MEASURED, NOT ASSUMED: the burst carrier loses
// two cases of the draw that this predicate places outside the region, and
// the pushing carrier wins both.  So the misses are the predicate being
// conservative, not a second mechanism -- which is the reading available
// only because the two carriers are counted separately.  A case outside
// the region that the pushing carrier ALSO loses would be the other
// finding, and there is none.

// Every input index reachable by SUBSCRIBING this expression.  A `strmT`
// is a VALUE, not a subscription -- whatever it names is reached only
// when some flattener spawns it -- so this walk does not enter terms at
// all.
const subscribed = (e: Exp, acc: Set<number>): void => {
  switch (e.type) {
    case "input":
      acc.add(e.index);
      return;
    case "of":
    case "empty":
    case "varE":
      return;
    case "map":
    case "scan":
    case "take":
    case "mergeAll":
    case "switchAll":
    case "exhaustAll":
    case "batchSync":
      subscribed(e.src, acc);
      return;
    case "mu":
    case "defer":
    case "mint":
      subscribed(e.body, acc);
      return;
  }
};

// Every input index anywhere under an expression, terms included: once a
// spawned observable is itself subscribed, what IT spawns is in reach
// too.
const anywhere = (e: Exp, acc: Set<number>): void => {
  switch (e.type) {
    case "input":
      acc.add(e.index);
      return;
    case "empty":
    case "varE":
      return;
    case "of":
      e.items.forEach((t) => anywhereTm(t, acc));
      return;
    case "map":
      anywhereTm(e.fn, acc);
      anywhere(e.src, acc);
      return;
    case "scan":
      anywhereTm(e.fn, acc);
      anywhereTm(e.init, acc);
      anywhere(e.src, acc);
      return;
    case "take":
      anywhereTm(e.count, acc);
      anywhere(e.src, acc);
      return;
    case "mergeAll":
    case "switchAll":
    case "exhaustAll":
    case "batchSync":
      anywhere(e.src, acc);
      return;
    case "mu":
    case "defer":
    case "mint":
      anywhere(e.body, acc);
      return;
  }
};

const anywhereTm = (t: Tm, acc: Set<number>): void => {
  switch (t.type) {
    case "varT":
    case "unitT":
    case "boolT":
    case "natT":
    case "nilT":
      return;
    case "strmT":
      anywhere(t.exp, acc);
      return;
    case "fstT":
    case "sndT":
      anywhereTm(t.pair, acc);
      return;
    case "inlT":
    case "inrT":
      anywhereTm(t.val, acc);
      return;
    case "pairT":
      anywhereTm(t.fst, acc);
      anywhereTm(t.snd, acc);
      return;
    case "consT":
      anywhereTm(t.head, acc);
      anywhereTm(t.tail, acc);
      return;
    case "caseT":
      anywhereTm(t.scrut, acc);
      anywhereTm(t.onInl, acc);
      anywhereTm(t.onInr, acc);
      return;
    case "ifT":
      anywhereTm(t.cond, acc);
      anywhereTm(t.then, acc);
      anywhereTm(t.else, acc);
      return;
    case "primT":
      anywhereTm(t.arg, acc);
      return;
    case "foldT":
      anywhereTm(t.list, acc);
      anywhereTm(t.init, acc);
      anywhereTm(t.step, acc);
      return;
  }
};

// Input indices this expression SPAWNS: those named inside a `strmT`,
// which is the only way an observable becomes a value and so the only
// way a subscription can be caused by a value.
const spawned = (e: Exp, acc: Set<number>): void => {
  switch (e.type) {
    case "input":
    case "empty":
    case "varE":
      return;
    case "of":
      e.items.forEach((t) => anywhereTm(t, acc));
      return;
    case "map":
      anywhereTm(e.fn, acc);
      spawned(e.src, acc);
      return;
    case "scan":
      anywhereTm(e.fn, acc);
      anywhereTm(e.init, acc);
      spawned(e.src, acc);
      return;
    case "take":
      anywhereTm(e.count, acc);
      spawned(e.src, acc);
      return;
    case "mergeAll":
    case "switchAll":
    case "exhaustAll":
    case "batchSync":
      spawned(e.src, acc);
      return;
    case "mu":
    case "defer":
    case "mint":
      spawned(e.body, acc);
      return;
  }
};

// A LOWER BOUND on how many values leave this expression inside its own
// subscribe call.  An unknown is 0, so a share whose burst cannot be
// read off the tree is not counted as one.  `defer` contributes nothing
// on purpose: here it is an async hop, so nothing under it is
// synchronous with the subscribe that crossed it.
export const syncBurst = (e: Exp): number => {
  switch (e.type) {
    case "of":
      return e.items.length;
    case "map":
    case "scan":
      return syncBurst(e.src);
    case "mint":
      return syncBurst(e.body);
    case "take":
      return e.count.type === "natT"
        ? Math.min(e.count.val, syncBurst(e.src))
        : 0;
    // the bracket's whole point: a subscribe burst leaves as ONE group
    case "batchSync":
      return Math.min(1, syncBurst(e.src));
    default:
      return 0;
  }
};

const setOf = (f: (e: Exp, acc: Set<number>) => void, e: Exp): Set<number> => {
  const acc = new Set<number>();
  f(e, acc);
  return acc;
};

// every flattener node in a tree, itself included
const flattenerSrcs = (e: Exp, acc: Exp[]): Exp[] => {
  switch (e.type) {
    case "input":
    case "empty":
    case "varE":
      return acc;
    case "of":
      return acc;
    case "mergeAll":
    case "switchAll":
    case "exhaustAll":
      acc.push(e.src);
      return flattenerSrcs(e.src, acc);
    case "map":
    case "scan":
    case "take":
    case "batchSync":
      return flattenerSrcs(e.src, acc);
    case "mu":
    case "defer":
    case "mint":
      return flattenerSrcs(e.body, acc);
  }
};

// CONDITION (iii), AND IT IS WHAT THE GUARD ROWS FAIL.  A flattener whose
// outer both SUBSCRIBES share `i` and SPAWNS an observable naming it is
// one whose inner subscriptions are caused by that share's own values.
// Two inners written into an `of` name the share just as plainly, and
// are not in the region, because the `of` caused them.
const causedBy = (e: Exp, i: number): boolean =>
  flattenerSrcs(e, []).some(
    (src) => setOf(subscribed, src).has(i) && setOf(spawned, src).has(i),
  );

export const reachesRegion = (tc: TestCase): boolean => {
  // a flattener anywhere in the program: the root tree, or any shared
  // slot's own definition
  const trees = [
    tc.exp,
    ...tc.slots.flatMap((s) => (s.type === "shared" ? [s.def] : [])),
  ];
  return tc.slots.some(
    (s, i) =>
      s.type === "shared" &&
      syncBurst(s.def) >= 2 &&
      trees.some((t) => causedBy(t, i)),
  );
};
