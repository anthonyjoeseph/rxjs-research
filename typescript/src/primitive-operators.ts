import { Observable } from "rxjs";
import { InstEmit, SourceId } from "./inst-emit.js";

export declare const of: <A>(input: A[]) => Observable<InstEmit<A>>;
export declare const empty: Observable<InstEmit<never>>;
// The slot-telescope share (NOT default rxjs share()): all reset
// options are false by definition. Connects the underlying once, at
// the first subscription; never disconnects (an unobserved share keeps
// running); latches completion forever — a post-completion subscriber
// sees only an immediate close/complete, because completion is
// re-observable and values are not. Emits init/close per subscriber,
// and one upstream arrival fans out to every subscriber within the
// same instant. `source` stamps the fan-out emits — by convention the
// shared slot's index.
export declare const share: <A>(
  obs: Observable<InstEmit<A>>,
  source: SourceId,
) => Observable<InstEmit<A>>;
export declare const defer: <A>(
  fn: () => Observable<InstEmit<A>>,
) => Observable<InstEmit<A>>;
export declare const map: <A, B>(
  obs: Observable<InstEmit<A>>,
  fn: (a: A) => B,
) => Observable<InstEmit<B>>;
export declare const take: <A>(
  obs: Observable<InstEmit<A>>,
  emissions: number,
) => Observable<InstEmit<A>>;
export declare const scan: <A, B>(
  obs: Observable<InstEmit<A>>,
  initial: B,
  fn: (acc: B, cur: A) => B,
) => Observable<InstEmit<B>>;
export declare const mergeAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
export declare const switchAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
export declare const concatAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
export declare const exhaustAll: <A>(
  obs: Observable<InstEmit<Observable<InstEmit<A>>>>,
) => Observable<InstEmit<A>>;
