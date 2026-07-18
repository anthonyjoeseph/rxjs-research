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
// shared slot's index. The latch must flip BEFORE the final delivery
// fans out (as a Subject closes before delivering its completion, and
// as the Agda dispatchShare latches before its fan-out): a subscriber
// joining mid-final-cascade already gets the one-shot
// init/close/complete, never a registration dropped without its close.
// Protocol duties (mirror of Agda foldPath's share-sink clause): the
// upstream emit that triggers a fan-out passes through FIRST, emptied
// of values, with a `handoff` event for this share appended — the
// writer-asserted announcement that the fan-out follows in the same
// instant.  Fan-out emits are kind "delivery"; per-subscriber
// init/one-shot emits are kind "subscribe"; closes minted here (the
// def completing) carry reason "exhausted".
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
