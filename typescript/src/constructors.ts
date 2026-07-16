import { Observable } from "rxjs";

export declare const cold: <A>(subscribe: {
  next: (val: A) => void;
  complete: () => void;
}) => Observable<A>;

export declare const hot: <A>() => [
  Observable<A>,
  {
    next: (val: A) => void;
    complete: () => void;
  },
];
