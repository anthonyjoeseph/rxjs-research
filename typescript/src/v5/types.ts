import * as r from "rxjs";
import Observable = r.Observable;

export type InstInit<A> = {
  type: "init";
  provenance: symbol;
  /** REGISTRATION id: minted at each actual subscription of a source
   * (of/cold/InstantSubject subscriber, share ref) and preserved verbatim
   * by every re-statement and rewrap. Two inits with the same provenance
   * but different subs are different subscriptions of the same source;
   * the same sub seen twice is one registration re-stated along two
   * downstream paths (a diamond). Closes are attributed to the enclosing
   * node's sub. */
  sub?: symbol;
  children: (InstEmit<A> | InstVal<A> | InstClose)[];
  /** closes of THIS provenance that were structurally CANCELLED against a
   * continuing re-subscription (a concat advancing back onto the source
   * whose close advanced it — see graftInner's cancel rules). The
   * registration arithmetic already nets out, but window slot accounting
   * must still see them: a cancelled close may have belonged to a
   * swallowed diamond branch whose delivery slot needs consuming. */
  cancelled?: number;
};
export type InstAsync<A> = {
  type: "async";
  provenance: symbol;
  /** the registration this delivery travels through — see InstInit.sub */
  sub?: symbol;
  child: InstEmit<A> | InstVal<A> | InstClose | null;
};
export type InstVal<A> = {
  type: "value";
  value: A;
  /** set by map/accumulate: this value was computed from an upstream value,
   * so a stream spawned from it (a join subscribing it) belongs to the
   * upstream value's instant. Values `of` emits directly are underived —
   * a join subscribing THOSE is static wiring, each inner its own cause. */
  derived?: true;
};
export type InstClose = {
  type: "close";
};

export type InstEmit<A> = InstInit<A> | InstAsync<A>;
export type Instantaneous<A> = Observable<InstEmit<A>>;

export const init = <A>(input: {
  provenance: symbol;
  sub?: symbol;
  children: (InstEmit<A> | InstVal<A> | InstClose)[];
  cancelled?: number;
}): InstInit<A> => ({
  type: "init",
  ...input,
});
export const async = <A>(input: {
  provenance: symbol;
  sub?: symbol;
  child: InstInit<A> | InstAsync<A> | InstVal<A> | InstClose | null;
}): InstAsync<A> => ({
  type: "async",
  ...input,
});
export const val = <A>(value: A): InstVal<A> => ({ type: "value", value });
export const close: InstClose = { type: "close" };

export const isInit = <A>(a: InstEmit<A>): a is InstInit<A> => {
  return a.type === "init";
};

export const isAsync = <A>(a: InstEmit<A>): a is InstAsync<A> => {
  return a.type === "async";
};

export const map = <A, B>(
  a: InstInit<A> | InstAsync<A> | InstVal<A> | InstClose,
  fn: (a: A) => B,
): InstInit<B> | InstAsync<B> | InstVal<B> | InstClose => {
  switch (a.type) {
    case "init":
      return {
        type: "init",
        provenance: a.provenance,
        ...(a.sub !== undefined ? { sub: a.sub } : {}),
        children: a.children.map(
          (child) => map(child, fn) as InstClose | InstEmit<B>,
        ),
        ...(a.cancelled !== undefined ? { cancelled: a.cancelled } : {}),
      } satisfies InstInit<B>;
    case "async":
      return {
        type: "async",
        provenance: a.provenance,
        ...(a.sub !== undefined ? { sub: a.sub } : {}),
        child: a.child == null ? null : map(a.child, fn),
      } satisfies InstAsync<B>;
    case "value":
      return {
        type: "value",
        value: fn(a.value),
        derived: true,
      } satisfies InstVal<B>;
    case "close":
      return a;
  }
};

export const values = <A>(emit: InstEmit<A>): A[] => {
  if (emit.type === "init") {
    return emit.children.flatMap((child) =>
      child.type === "value"
        ? [child.value]
        : child.type === "close"
          ? []
          : values(child),
    );
  }
  return emit.child == null
    ? []
    : emit.child.type === "value"
      ? [emit.child.value]
      : emit.child.type === "close"
        ? []
        : values(emit.child);
};
