import { OperatorFunction, from, mergeMap, toArray } from "rxjs";
import { EmitKind, InstEmit, InstEvent, Provenance, SourceId } from "./inst-emit.js";

// The ONLINE batcher — the TS twin of Agda's impl-batchSimultaneous
// (Implementation.agda): one emission at a time, own state only, no
// lookahead. It is Rx.Protocol's automaton in producing mode — the same
// live/owed arithmetic — but where the automaton rejects a broken stream
// it clamps and carries on, and where the automaton demands "fully paid"
// it FLUSHES: the moment an instant's obligations hit zero its batch is
// emitted. Subscribe frames (owed never takes on obligations) flush
// lazily, at the next instant or the end of the stream.

// ---- Rx.Protocol's Owed arithmetic (source ⇒ remaining count) ----
type Owed = Array<[SourceId, number]>;

const countIn = (s: SourceId, xs: SourceId[]): number =>
  xs.reduce<number>((n, x) => (x === s ? n + 1 : n), 0);

// remove one occurrence; null on underflow (source absent)
const removeOne = (s: SourceId, xs: SourceId[]): SourceId[] | null => {
  const at = xs.indexOf(s);
  return at === -1 ? null : [...xs.slice(0, at), ...xs.slice(at + 1)];
};

const hasOwed = (s: SourceId, owed: Owed): boolean =>
  owed.some(([x]) => x === s);

// add k to s's owed, in place; append at the end if absent
const bumpOwed = (s: SourceId, k: number, owed: Owed): Owed =>
  hasOwed(s, owed)
    ? owed.map(([x, n]): [SourceId, number] => (x === s ? [x, k + n] : [x, n]))
    : [...owed, [s, k]];

// decrement s's owed by one; null on underflow (count 0, or s absent)
const payOwed = (s: SourceId, owed: Owed): Owed | null => {
  if (owed.length === 0) return null;
  const [[x, n], ...rest] = owed;
  if (x === s) return n === 0 ? null : [[x, n - 1], ...rest];
  const r = payOwed(s, rest);
  return r === null ? null : [[x, n], ...r];
};

const allZero = (owed: Owed): boolean => owed.every(([, n]) => n === 0);

// a cutPending victim's cancellation: one owed count forgiven (clamped)
const cancelOwed = (s: SourceId, owed: Owed): Owed =>
  owed.map(([x, n]): [SourceId, number] =>
    x === s ? [x, Math.max(0, n - 1)] : [x, n],
  );

// ---- the batcher state (Agda's OpenBatch / BatchSt) ----
type OpenBatch<A> = {
  instant: Provenance;
  source: SourceId;
  kind: EmitKind;
  values: A[];
  owed: Owed;
};
type BatchSt<A> = { live: SourceId[]; current: OpenBatch<A> | null };

const batchInit = <A>(): BatchSt<A> => ({ live: [], current: null });

// a finished batch: one value event under the instant's own envelope,
// dropped when valueless (the spec's batchOf, online)
const closeBatch = <A>(b: OpenBatch<A>): InstEmit<A[]>[] =>
  b.values.length === 0
    ? []
    : [
        {
          events: [{ type: "value", value: b.values }],
          instant: b.instant,
          source: b.source,
          kind: b.kind,
        },
      ];

// settle: a subscription's own burst and a share's forwarded connect
// burst are net zero; a delivery pays owed[s], seeded from live(s) — the
// multiset BEFORE this emit's events — at s's first delivery
const settleBatch = (
  k: EmitKind,
  s: SourceId,
  live: SourceId[],
  owed: Owed,
): Owed => {
  if (k === "subscribe" || k === "plumbing") return owed;
  const seeded = hasOwed(s, owed) ? owed : bumpOwed(s, countIn(s, live), owed);
  return payOwed(s, seeded) ?? seeded;
};

// applyEvents, clamped, also collecting values: inits enlist, closes
// retire, a handoff bumps the announced share's owed by its live count
// AT THE ANNOUNCEMENT, values accumulate in stream order
const applyBatch = <A>(
  events: InstEvent<A>[],
  live0: SourceId[],
  owed0: Owed,
  vs0: A[],
): [SourceId[], Owed, A[]] =>
  events.reduce<[SourceId[], Owed, A[]]>(
    ([live, owed, vs], ev) =>
      ev.type === "init"
        ? [[ev.source, ...live], owed, vs]
        : ev.type === "value"
          ? [live, owed, [...vs, ev.value]]
          : ev.type === "handoff"
            ? [live, bumpOwed(ev.source, countIn(ev.source, live), owed), vs]
            : ev.type === "close"
              ? [
                  removeOne(ev.source, live) ?? live,
                  // cutPending: the victim never pays — cancel one owed
                  ev.reason === "cutPending"
                    ? cancelOwed(ev.source, owed)
                    : owed,
                  vs,
                ]
              : [live, owed, vs], // complete: no traffic
    [live0, owed0, vs0],
  );

// obligations existed and are now discharged — an EMPTY owed table is
// not closure (a subscribe frame never takes on obligations)
const paidOff = (owed: Owed): boolean =>
  owed.length > 0 && allZero(owed);

const stepBatch = <A>(
  emit: InstEmit<A>,
  st: BatchSt<A>,
): [InstEmit<A[]>[], BatchSt<A>] => {
  const { events, instant: i, source: s, kind: k } = emit;
  const fresh: OpenBatch<A> = {
    instant: i,
    source: s,
    kind: k,
    values: [],
    owed: [],
  };
  // same instant continues the open batch; a new instant flushes it
  const [flushed, b]: [InstEmit<A[]>[], OpenBatch<A>] =
    st.current === null
      ? [[], fresh]
      : st.current.instant === i
        ? [[], st.current]
        : [closeBatch(st.current), fresh];

  const owed1 = settleBatch(k, s, st.live, b.owed);
  const [live2, owed2, vals2] = applyBatch(events, st.live, owed1, b.values);
  const b2: OpenBatch<A> = { ...b, owed: owed2, values: vals2 };
  return paidOff(owed2)
    ? [[...flushed, ...closeBatch(b2)], { live: live2, current: null }]
    : [flushed, { live: live2, current: b2 }];
};

const flushBatch = <A>(st: BatchSt<A>): InstEmit<A[]>[] =>
  st.current === null ? [] : closeBatch(st.current);

// the pure fold (Agda's foldBatch): step each emit, flush the tail
const foldBatch = <A>(emits: InstEmit<A>[]): InstEmit<A[]>[] => {
  const { out, st } = emits.reduce<{ out: InstEmit<A[]>[]; st: BatchSt<A> }>(
    (acc, emit) => {
      const [o, s] = stepBatch(emit, acc.st);
      return { out: [...acc.out, ...o], st: s };
    },
    { out: [], st: batchInit<A>() },
  );
  return [...out, ...flushBatch(st)];
};

// the rxjs operator form: collect the stream, fold it, re-emit the
// batches. The fold has no lookahead (it is online); toArray just hands
// it the finite stream in one piece, matching Agda's List → List shape.
export const batchSimultaneous = <A>(): OperatorFunction<
  InstEmit<A>,
  InstEmit<A[]>
> => (source) => source.pipe(toArray(), mergeMap((emits) => from(foldBatch(emits))));
