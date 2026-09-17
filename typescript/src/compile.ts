import { Observable } from "rxjs";
import { InstEmit } from "./inst-emit.js";
import { Closed, Val, applyFn, bindMinted, evalTm, unfoldMu } from "./exp.js";
import { Driver } from "./driver.js";
import * as P from "./primitive-operators.js";

// the per-node switch delegating to the primitive-operators:
// evalTm/applyFn for of/map/scan/take, unfoldMu + a driver hop for
// mu/defer. Inner observables are CLOSED EXPS carried as values
// (strmT), so the *All cases compile each inner as its emission
// passes — laziness for free, defers inside stay thunked.
export const compile = (
  exp: Closed,
  driver: Driver,
  slotSources: Observable<InstEmit<Val>>[],
): Observable<InstEmit<Val>> => {
  const recur = (e: Closed) => compile(e, driver, slotSources);
  const inner = (src: Closed) =>
    P.map(recur(src), (v: Val) => recur(v as Closed));
  switch (exp.type) {
    case "input": {
      const source = slotSources[exp.index];
      if (source === undefined)
        throw new Error(`input ${exp.index} out of slot range`);
      return source;
    }
    case "of":
      return P.of(
        driver,
        exp.items.map((item) => evalTm(item)),
      );
    case "empty":
      return P.empty(driver);
    case "map":
      // the step is a Tm on ONE value; the primitive is pointwise too,
      // so applying the Fn is the whole clause
      return P.map(recur(exp.src), (value: Val) => applyFn(exp.fn, value));
    case "scan":
      // a scan's step takes the pair (carried state, one value) and its
      // result IS the next state, so nothing is projected out of it
      return P.scan(recur(exp.src), evalTm(exp.init), (state, value) =>
        applyFn(exp.fn, [state, value]),
      );
    case "take": {
      // Agda evaluates the count at subscription time; a closed Tm is
      // deterministic, so evaluating once here cannot differ
      const count = evalTm(exp.count);
      if (typeof count !== "number")
        throw new Error("take count did not evaluate to a nat");
      // take 0 never subscribes its source (as in rxjs): a spent
      // one-shot, exactly emptyᵉ
      return count === 0 ? P.empty(driver) : P.take(recur(exp.src), count);
    }
    case "mergeAll":
      return P.mergeAllAll(exp.limit)(inner(exp.src));
    case "switchAll":
      return P.switchAll(inner(exp.src));
    case "exhaustAll":
      return P.exhaustAll(inner(exp.src));
    case "mu":
      // one unfolding now; the recursive occurrences inside sit behind
      // defer thunks, so each further unfolding costs a hop
      return recur(unfoldMu(exp.body));
    case "defer":
      return P.defer(driver, () => recur(exp.body));
    case "mint":
      // the token is substituted INTO the body, mirroring Agda's
      // subs-mint: the binder is discharged before the body compiles
      return P.mint(driver, (token) => recur(bindMinted(exp.body, token)));
    case "batchSync":
      // the node's sync bit is rxjs's own subscribe ordering, read
      // through `bracketSync` — see the primitive
      return P.batchSync(recur(exp.src)) as Observable<InstEmit<Val>>;
    case "varE":
      throw new Error(
        "varE in a closed expression — generator/decoder invariant violated",
      );
  }
};
