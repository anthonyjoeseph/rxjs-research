/**
 * The pure timed-list model: a LINE-BY-LINE transcription of the ratified
 * Agda spec (agda/src/Burst.agda). Agda is the design authority; this file
 * must not contain semantics of its own — every function mirrors its Agda
 * namesake, and any divergence is a transcription bug.
 *
 * Validity domain (per Burst.agda's header): programs whose shares never
 * RESET — a subject-backed letShare binding with a subscriber alive from
 * the frame onward. Resetting shares (cold sync-completing bindings,
 * refcount-zero gaps) are decided by the operational layer
 * (agda/src/Protocol.agda: shareLives) and are excluded from this model's
 * domain — the oracle generator must respect that.
 */

// Time ------------------------------------------------------------------------

export type Time = readonly [number, number]; // tick , origin

export const timeEq = (a: Time, b: Time): boolean =>
  a[0] === b[0] && a[1] === b[1];
export const timeLt = (a: Time, b: Time): boolean =>
  a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
export const timeLeq = (a: Time, b: Time): boolean =>
  a[0] < b[0] || (a[0] === b[0] && a[1] <= b[1]);
export const timeMin: Time = [0, 0];
export const timeMax = (a: Time, b: Time): Time => (timeLeq(a, b) ? b : a);

// TimedObs ---------------------------------------------------------------------

export type TimedObs<A> = [Time, A][];

/** stable sort-merge: on equal Times the LEFT argument wins (subscription
 * order) */
export const mergeT = <A>(xs: TimedObs<A>, ys: TimedObs<A>): TimedObs<A> => {
  const out: [Time, A][] = [];
  let i = 0;
  let j = 0;
  while (i < xs.length && j < ys.length) {
    if (timeLeq(xs[i][0], ys[j][0])) out.push(xs[i++]);
    else out.push(ys[j++]);
  }
  while (i < xs.length) out.push(xs[i++]);
  while (j < ys.length) out.push(ys[j++]);
  return out;
};

export const mapT = <A, B>(f: (a: A) => B, xs: TimedObs<A>): TimedObs<B> =>
  xs.map(([t, v]) => [t, f(v)]);

export const takeT = <A>(n: number, xs: TimedObs<A>): TimedObs<A> =>
  xs.slice(0, n);

/** group consecutive equal Times */
export const batchSpec = <A>(xs: TimedObs<A>): TimedObs<A[]> => {
  const out: [Time, A[]][] = [];
  for (const [t, v] of xs) {
    const last = out[out.length - 1];
    if (last !== undefined && timeEq(last[0], t)) last[1].push(v);
    else out.push([t, [v]]);
  }
  return out;
};

/** emissions strictly after a boundary */
export const filterAfter = <A>(c: Time, xs: TimedObs<A>): TimedObs<A> =>
  xs.filter(([t]) => timeLt(c, t));

export const scanT = <A, B>(
  f: (acc: B, a: A) => B,
  z: B,
  xs: TimedObs<A>,
): TimedObs<B> => {
  const out: [Time, B][] = [];
  let acc = z;
  for (const [t, v] of xs) {
    acc = f(acc, v);
    out.push([t, acc]);
  }
  return out;
};

/** the close of take n subscribed at t: the nth emission's time if it
 * exists, the source's close if it has fewer, t itself for take 0 */
export const takeCloseB = <A>(
  t: Time,
  n: number,
  xs: TimedObs<A>,
  c: Time,
): Time => {
  if (n === 0) return t;
  if (xs.length < n) return c;
  return xs[n - 1][0];
};

// Obs / Env ---------------------------------------------------------------------

export type Obs<A> = { emits: TimedObs<A>; close: Time };
export type Inner = (t: Time) => Obs<number>;
export type Slot = { connT: Time; obs: Obs<number> };
export type Env = (i: number) => Slot;

export const extendEnv =
  (s: Slot, env: Env): Env =>
  (i: number) =>
    i === 0 ? s : env(i - 1);

// the grammar (two-sorted, exactly Burst.agda's Exp/ExpS) -----------------------

export type Fn = { op: "add" | "mul"; k: number };
export const applyFn =
  (f: Fn) =>
  (v: number): number =>
    f.op === "add" ? v + f.k : v * f.k;

/** the one scan fold both sides use: acc folded by f, plus the value */
export const scanStep =
  (f: Fn) =>
  (acc: number, v: number): number =>
    applyFn(f)(acc) + v;

export type Exp =
  | { k: "empty" }
  | { k: "of"; vs: number[] }
  | { k: "shareRef"; first: boolean; slot: number }
  | { k: "letShare"; src: Exp; body: Exp }
  | { k: "map"; f: Fn; e: Exp }
  | { k: "take"; n: number; e: Exp }
  | { k: "scan"; f: Fn; e: Exp } // acc `op` v, z = 0-ish: f(acc, v) = applyFn2
  | { k: "mergeAll"; s: ExpS }
  | { k: "concatAll"; s: ExpS }
  | { k: "switchAll"; s: ExpS }
  | { k: "exhaustAll"; s: ExpS };

/** inner templates for mapS — a defunctionalized (v: number) => Exp, so the
 * generator can build and show them */
export type InnerTemplate =
  | { k: "ofv"; extra: number[] } // v => of([v, ...extra])
  | { k: "constOf"; vs: number[] } // v => of(vs)
  | { k: "refI"; slot: number } // v => shareRef(slot)  (late join!)
  | { k: "mapOfv"; f: Fn }; // v => map(f, of([v]))

export type ExpS =
  | { k: "ofS"; es: Exp[] }
  | { k: "mapS"; tmpl: InnerTemplate; e: Exp };

export const applyTemplate = (tmpl: InnerTemplate, v: number): Exp => {
  switch (tmpl.k) {
    case "ofv":
      return { k: "of", vs: [v, ...tmpl.extra] };
    case "constOf":
      return { k: "of", vs: tmpl.vs };
    case "refI":
      return { k: "shareRef", first: false, slot: tmpl.slot };
    case "mapOfv":
      return { k: "map", f: tmpl.f, e: { k: "of", vs: [v] } };
  }
};

export const mergeE = (a: Exp, b: Exp): Exp => ({
  k: "mergeAll",
  s: { k: "ofS", es: [a, b] },
});
export const concatE = (a: Exp, b: Exp): Exp => ({
  k: "concatAll",
  s: { k: "ofS", es: [a, b] },
});
export const mergeMapE = (tmpl: InnerTemplate, e: Exp): Exp => ({
  k: "mergeAll",
  s: { k: "mapS", tmpl, e },
});

// join list machinery (Burst.agda lines 128–206, verbatim) ----------------------

const mergeAllT = (os: TimedObs<Inner>): TimedObs<number> => {
  let out: TimedObs<number> = [];
  // Agda: mergeAllT ((a , d) ∷ os) = mergeT (emits (d a)) (mergeAllT os)
  for (let i = os.length - 1; i >= 0; i--) {
    const [a, d] = os[i];
    out = mergeT(d(a).emits, out);
  }
  return out;
};

const maxCloses = (c: Time, os: TimedObs<Inner>): Time => {
  let acc = c;
  for (const [a, d] of os) acc = timeMax(acc, d(a).close);
  return acc;
};

const concatAllT = (ready: Time, os: TimedObs<Inner>): TimedObs<number> => {
  const out: TimedObs<number> = [];
  let r = ready;
  for (const [a, d] of os) {
    const o = d(timeMax(r, a));
    out.push(...o.emits);
    r = o.close;
  }
  return out;
};

const concatAllClose = (ready: Time, os: TimedObs<Inner>): Time => {
  let r = ready;
  for (const [a, d] of os) r = d(timeMax(r, a)).close;
  return r;
};

/** switch: an inner keeps its own subscription frame, but its async tail
 * is cut when the next inner arrives */
const cutAt = <A>(a: Time, nxt: Time, xs: TimedObs<A>): TimedObs<A> =>
  xs.filter(([u]) => timeEq(u, a) || timeLt(u, nxt));

const switchAllT = (os: TimedObs<Inner>): TimedObs<number> => {
  const out: TimedObs<number> = [];
  for (let i = 0; i < os.length; i++) {
    const [a, d] = os[i];
    if (i === os.length - 1) out.push(...d(a).emits);
    else out.push(...cutAt(a, os[i + 1][0], d(a).emits));
  }
  return out;
};

const lastClose = (c: Time, os: TimedObs<Inner>): Time => {
  if (os.length === 0) return c;
  const [a, d] = os[os.length - 1];
  return d(a).close;
};

/** exhaust: an arrival is dropped only while the previous accepted inner
 * is still open */
const exhaustAllT = (b0: Time, os: TimedObs<Inner>): TimedObs<number> => {
  const out: TimedObs<number> = [];
  let b = b0;
  for (const [a, d] of os) {
    if (timeLt(a, b)) continue;
    const o = d(a);
    out.push(...o.emits);
    b = o.close;
  }
  return out;
};

const exhaustClose = (b0: Time, os: TimedObs<Inner>): Time => {
  let b = b0;
  for (const [a, d] of os) {
    if (timeLt(a, b)) continue;
    b = d(a).close;
  }
  return b;
};

/** what a ref subscribed at t sees of a share connected at tc */
const refView = (
  first: boolean,
  t: Time,
  tc: Time,
  xs: TimedObs<number>,
): TimedObs<number> => {
  if (first && timeEq(t, tc)) return xs;
  return filterAfter(t, xs);
};

// the denotation (Burst.agda lines 217–258, verbatim) ---------------------------

export const denote = (e: Exp, env: Env, t: Time): Obs<number> => {
  switch (e.k) {
    case "empty":
      return { emits: [], close: t };
    case "of":
      return { emits: e.vs.map((v): [Time, number] => [t, v]), close: t };
    case "shareRef": {
      const slot = env(e.slot);
      return {
        emits: refView(e.first, t, slot.connT, slot.obs.emits),
        close: timeMax(t, slot.obs.close),
      };
    }
    case "letShare":
      return denote(
        e.body,
        extendEnv({ connT: t, obs: denote(e.src, env, t) }, env),
        t,
      );
    case "map": {
      const o = denote(e.e, env, t);
      return { emits: mapT(applyFn(e.f), o.emits), close: o.close };
    }
    case "take": {
      const o = denote(e.e, env, t);
      return {
        emits: takeT(e.n, o.emits),
        close: takeCloseB(t, e.n, o.emits, o.close),
      };
    }
    case "scan": {
      const o = denote(e.e, env, t);
      return { emits: scanT(scanStep(e.f), 0, o.emits), close: o.close };
    }
    case "mergeAll": {
      const s = denoteS(e.s, env, t);
      return { emits: mergeAllT(s.emits), close: maxCloses(s.close, s.emits) };
    }
    case "concatAll": {
      const s = denoteS(e.s, env, t);
      return {
        emits: concatAllT(t, s.emits),
        close: timeMax(s.close, concatAllClose(t, s.emits)),
      };
    }
    case "switchAll": {
      const s = denoteS(e.s, env, t);
      return {
        emits: switchAllT(s.emits),
        close: timeMax(s.close, lastClose(s.close, s.emits)),
      };
    }
    case "exhaustAll": {
      const s = denoteS(e.s, env, t);
      return {
        emits: exhaustAllT(t, s.emits),
        close: timeMax(s.close, exhaustClose(t, s.emits)),
      };
    }
  }
};

const denoteS = (s: ExpS, env: Env, t: Time): Obs<Inner> => {
  switch (s.k) {
    case "ofS":
      return {
        emits: s.es.map((e): [Time, Inner] => [t, (u) => denote(e, env, u)]),
        close: t,
      };
    case "mapS": {
      const o = denote(s.e, env, t);
      return {
        emits: o.emits.map(([a, v]): [Time, Inner] => [
          a,
          (u) => denote(applyTemplate(s.tmpl, v), env, u),
        ]),
        close: o.close,
      };
    }
  }
};

// driving ------------------------------------------------------------------------

export type DriverEvent = { slot: number; value: number };

/** the env induced by a driver: slot j's history = its events at ticks
 * 1..K (origin 0); slot j closes at tick K+1+j (drive end completes the
 * subjects one at a time, in slot order — each completion is its own
 * instant) */
export const envOfDriver = (numSlots: number, d: DriverEvent[]): Env => {
  const emitsBySlot: TimedObs<number>[] = Array.from(
    { length: numSlots },
    () => [],
  );
  d.forEach((ev, k) => {
    emitsBySlot[ev.slot]?.push([[k + 1, 0], ev.value]);
  });
  return (i: number) => ({
    connT: timeMin,
    obs: { emits: emitsBySlot[i] ?? [], close: [d.length + 1 + i, 0] },
  });
};

/** the model's answer: batches of values, in order (times forgotten) */
export const modelBatches = (
  e: Exp,
  numSlots: number,
  d: DriverEvent[],
): number[][] =>
  batchSpec(denote(e, envOfDriver(numSlots, d), timeMin).emits).map(
    ([, vs]) => vs,
  );
