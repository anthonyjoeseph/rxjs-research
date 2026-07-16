import { Observable } from "rxjs";
import { InstEmit } from "./inst-emit.js";

export declare const of: <A>(input: A[]) => Observable<InstEmit<A>>;
export declare const empty: Observable<InstEmit<never>>;
export declare const share: <A>(
  obs: Observable<InstEmit<A>>,
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
