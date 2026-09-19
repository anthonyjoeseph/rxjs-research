import { Observable } from "rxjs";
import { InstEmit } from "./inst-emit.js";
import { Closed, ObsVal, Val, evalWith, unfoldMu } from "./exp.js";
import { Driver } from "./driver.js";
import * as P from "./primitive-operators.js";

// the per-node switch delegating to the primitive-operators:
// evalWith for of/map/scan/take, unfoldMu + a driver hop for
// mu/defer. Inner observables are CLOSURES carried as values
// (strmT), so the *All cases compile each inner against the
// environment it was written under as its emission passes —
// laziness for free, defers inside stay thunked.
//
// THE ENVIRONMENT IS THE ARGUMENT SUBSTITUTION USED TO BE.  A binder
// used to be discharged by rewriting the body, which demanded a term
// denoting every value that could be bound — a uniq token included,
// hence the numeral-carrying literal.  Extending this list instead
// asks for no such term: index 0 is the innermost binder, and mint
// puts a plain host number there.
export const compile = (
  exp: Closed,
  env: Val[],
  driver: Driver,
  slotSources: Observable<InstEmit<Val>>[],
): Observable<InstEmit<Val>> => {
  const recur = (e: Closed) => compile(e, env, driver, slotSources);
  const inner = (src: Closed) =>
    P.map(recur(src), (v: Val) => {
      const o = v as ObsVal;
      return compile(o.exp, o.env, driver, slotSources);
    });
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
        exp.items.map((item) => evalWith(item, env)),
      );
    case "empty":
      return P.empty(driver);
    case "map":
      // the step is a Tm binding ONE value at index 0; the primitive is
      // pointwise too, so extending the environment is the whole clause
      return P.map(recur(exp.src), (value: Val) =>
        evalWith(exp.fn, [value, ...env]),
      );
    case "scan":
      // a scan's step binds the pair (carried state, one value) and its
      // result IS the next state, so nothing is projected out of it
      return P.scan(recur(exp.src), evalWith(exp.init, env), (state, value) =>
        evalWith(exp.fn, [[state, value], ...env]),
      );
    case "take": {
      // Agda evaluates the count at subscription time; a Tm is
      // deterministic in its environment, so evaluating once here
      // cannot differ
      const count = evalWith(exp.count, env);
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
      // defer thunks, so each further unfolding costs a hop. μ-vars are
      // a separate binder stack from Θ, so the environment rides along
      return recur(unfoldMu(exp.body));
    case "defer":
      return P.defer(driver, () => recur(exp.body));
    case "mint":
      // the token is BOUND, not substituted: the body sees it as Θ-var
      // 0, mirroring Agda's `reducible body (src ∷ᵉ ρ)`
      return P.mint(driver, (token) =>
        compile(exp.body, [token, ...env], driver, slotSources),
      );
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
