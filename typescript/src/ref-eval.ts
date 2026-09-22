import {
  Closed,
  Exp,
  Fn,
  Ty,
  Val,
  ObsVal,
  evalWith,
  tyEq,
  unfoldMu,
} from "./exp.js";
import type { Slot, Slots, TestCase, Timed } from "./prop-test.js";

// THE REFERENCE EVALUATOR: THE AGDA MACHINE, AS A PARTIAL FUNCTION.
//
// WHY IT EXISTS.  The Agda evaluator is `proj₁` of its own inhabitation
// proof, so a RUN is a corollary of the totality tower rather than
// something available beside it.  That is free for an ordinary clause
// and expensive for a change to the CARRIER, where the shape of every
// family's result moves and the differential verdict -- the only thing
// that says whether the new shape was worth proving -- arrives only once
// the whole tower is closed again.  Here a partial function costs
// nothing, so the design can be measured first and transcribed second.
//
// WHAT IT IS FAITHFUL TO.  Every family below is one constructor block
// of `Rx.Evaluator.Domain`, clause for clause and in the same order, and
// every helper is its namesake in `Rx.Evaluator`.  Where the Agda reads
// a stored element type out of an existential and pays a `_≟ᵗ_`, this
// pays a `tyEq`; where the Agda degrades a mistyped or missing read to
// forwarding NOTHING, so does this.  It is NOT a second semantics and
// nothing may be "improved" here on its own: a divergence from the Agda
// is a transcription bug until the two are changed together.
//
// WHAT IT IS NOT.  It is not on the proof path and nothing in `agda/`
// may be justified by it.  It is a place to run a design, and the run it
// gives is evidence of the same kind a probe is -- a receipt at concrete
// programs, never a theorem.

type Tick = number;
type NodeId = number;
type RegId = number;
type Source = number;
type Ordinal = number;

// ---------------------------------------------------------------
// The carrier
// ---------------------------------------------------------------

// A BURST IS EVERYTHING ONE INCOMING EMIT CAUSES, and a subscription
// hands its whole output back as a list of them.  This is the carrier
// under test: the group a bracket wants is already assembled by the
// time a frame sees it, which is what `batchVals` below reads.
type PlainEvent = { k: "value"; val: Val } | { k: "complete" };
type Burst = PlainEvent[];
type Stream = Burst[];

const valueP = (val: Val): PlainEvent => ({ k: "value", val });
const completeP: PlainEvent = { k: "complete" };

const oneShotBurst = (vals: Val[]): Stream => [
  [...vals.map(valueP), completeP],
];
const spentBurst: Stream = [[completeP]];

const splitEvents = (b: Burst): { vals: Val[]; complete: boolean } => ({
  vals: b.flatMap((e) => (e.k === "value" ? [e.val] : [])),
  complete: b.some((e) => e.k === "complete"),
});

const splitBurst = (s: Stream): { vals: Val[]; complete: boolean } =>
  s.reduce<{ vals: Val[]; complete: boolean }>(
    (acc, b) => {
      const { vals, complete } = splitEvents(b);
      return {
        vals: [...acc.vals, ...vals],
        complete: acc.complete || complete,
      };
    },
    { vals: [], complete: false },
  );

const burstCompleted = (s: Stream): boolean =>
  s.some((b) => b.some((e) => e.k === "complete"));

// ---------------------------------------------------------------
// The node store, the frames and the rootward paths
// ---------------------------------------------------------------

type AllOp = "mergeAll" | "switch" | "exhaust";

type NodeState =
  | { k: "cell"; ty: Ty; val: Val }
  | { k: "take"; remaining: number }
  | {
      k: "mergeAll";
      ty: Ty;
      limit: number | null; // null is rxjs's Infinity
      active: number;
      queued: Val[];
      outerDone: boolean;
    }
  | { k: "switch"; current: NodeId | null; outerDone: boolean }
  | { k: "exhaust"; innerActive: boolean; outerDone: boolean }
  | { k: "batchSync"; sync: boolean };

// A FRAME CARRIES THE ELEMENT TYPE IT WORKS AT, and that is not
// bookkeeping: in Agda the type is an INDEX on the frame, so the three
// clauses that pay a `_≟ᵗ_` against a stored node read it off the frame
// for free.  Recovering it here from the value flowing past instead
// would be a guess, and a wrong guess reads as a missing node rather
// than as a type error -- silently forwarding nothing.
type Frame =
  | { k: "map"; fn: Fn; env: Val[] }
  | { k: "scan"; fn: Fn; env: Val[]; nid: NodeId; ty: Ty }
  | { k: "take"; nid: NodeId }
  | { k: "batchSync"; nid: NodeId }
  | { k: "fromInner"; op: AllOp; allNode: NodeId; inst: NodeId; elemTy: Ty }
  | { k: "thruOuter"; op: AllOp; nid: NodeId; elemTy: Ty };

// THE FLOOR IS NOT CARRIED ON THE PATH HERE, and that is the one place
// the shape differs from the Agda without the meaning differing.  There
// the floor is a TYPE index, so `lowerFloor` exists to retype a path a
// registry row is about to store; here it is an ordinary argument to
// `subscribeE` and a field on the row, and lowering is the identity on
// structure -- which is exactly what `lowerFloor` computes.
type Path =
  | { k: "root" }
  | { k: "shareSink"; i: number }
  | { k: "step"; frame: Frame; rest: Path };

const frameNodes = (f: Frame): NodeId[] => {
  switch (f.k) {
    case "map":
      return [];
    case "scan":
    case "take":
    case "batchSync":
    case "thruOuter":
      return [f.nid];
    case "fromInner":
      return [f.allNode, f.inst];
  }
};

const pathHasNode = (nid: NodeId, p: Path): boolean =>
  p.k === "step" &&
  (frameNodes(p.frame).includes(nid) || pathHasNode(nid, p.rest));

// ---------------------------------------------------------------
// The registry, the schedule and the evaluator state
// ---------------------------------------------------------------

type RegSrc =
  { k: "slot"; i: number } | { k: "dyn"; source: Source; floor: number };

const regSource = (rs: RegSrc): Source => (rs.k === "slot" ? rs.i : rs.source);
const regFloor = (rs: RegSrc): number =>
  rs.k === "slot" ? rs.i + 1 : rs.floor;

type RegRow = { rid: RegId; src: RegSrc; elemTy: Ty; path: Path };

type LiveSource = {
  source: Source;
  ordinal: Ordinal;
  elemTy: Ty;
  pending: { tick: Tick; val: Val }[];
};

type MintKey = "ordinal" | "source" | "node" | "reg";
type Mint = Record<MintKey, number>;

type Sched = { mint: Mint; live: LiveSource[]; slots: Slots };

type EvalSt = {
  registry: RegRow[];
  nodes: { nid: NodeId; state: NodeState }[];
  connectedShares: Source[];
  completedSources: Source[];
  delivered: RegId[];
  cancelled: RegId[];
  dying: Source[];
};

type Arrival = {
  tick: Tick;
  ordinal: Ordinal;
  source: Source;
  elemTy: Ty;
  payload: Val;
  isLast: boolean;
};

const freshId = (k: MintKey, m: Mint): number => m[k];
const setAt = (k: MintKey, v: number, m: Mint): Mint => ({ ...m, [k]: v });
const bump = (k: MintKey, sched: Sched): Sched => ({
  ...sched,
  mint: setAt(k, freshId(k, sched.mint) + 1, sched.mint),
});

const lookupNode = (nid: NodeId, ns: EvalSt["nodes"]): NodeState | undefined =>
  ns.find((row) => row.nid === nid)?.state;

const setNode = (
  nid: NodeId,
  state: NodeState,
  ns: EvalSt["nodes"],
): EvalSt["nodes"] =>
  ns.some((row) => row.nid === nid)
    ? ns.map((row) => (row.nid === nid ? { nid, state } : row))
    : [...ns, { nid, state }];

const installNode = (nid: NodeId, state: NodeState, st: EvalSt): EvalSt => ({
  ...st,
  nodes: setNode(nid, state, st.nodes),
});

// append: the registry stays in subscription order, which is what a
// share's fan-out order IS
const register = (
  rid: RegId,
  src: RegSrc,
  elemTy: Ty,
  path: Path,
  st: EvalSt,
): EvalSt => ({
  ...st,
  registry: [...st.registry, { rid, src, elemTy, path }],
});

const stInit = (): EvalSt => ({
  registry: [],
  nodes: [],
  connectedShares: [],
  completedSources: [],
  delivered: [],
  cancelled: [],
  dying: [],
});

const cutThrough = (
  nid: NodeId,
  reg: RegRow[],
): { kept: RegRow[]; cut: RegId[] } => ({
  kept: reg.filter((row) => !pathHasNode(nid, row.path)),
  cut: reg.filter((row) => pathHasNode(nid, row.path)).map((row) => row.rid),
});

// drop dead dynamic sources; slot sources (< n) keep firing regardless,
// exactly like a hot Subject with no subscribers
const sweepLive = (
  n: number,
  reg: RegRow[],
  live: LiveSource[],
): LiveSource[] =>
  live.filter(
    (l) => l.source < n || reg.some((row) => regSource(row.src) === l.source),
  );

const dropSource = (src: Source, reg: RegRow[]): RegRow[] =>
  reg.filter((row) => regSource(row.src) !== src);

// ---------------------------------------------------------------
// The schedule
// ---------------------------------------------------------------

// delta-encoded waits → absolute ticks (gap = wait + 1, so a source's
// ticks are strictly increasing by construction)
const resolve = (
  anchor: Tick,
  timed: Timed<Val>[],
): { tick: Tick; val: Val }[] =>
  timed.reduce<{ tick: Tick; val: Val }[]>((acc, { wait, val }) => {
    const prev = acc.length > 0 ? acc[acc.length - 1].tick : anchor;
    return [...acc, { tick: prev + wait + 1, val }];
  }, []);

// hots go live at anchor 0, slot i minting source AND ordinal i -- the
// convention `subscribeE` relies on to register hot chains.  Shared
// slots own source i too but connect lazily, at their first subscription.
const mkHot = (ctx: Ty[], slot: Slot, i: number): LiveSource[] =>
  slot.type === "scripted" && slot.input.type === "hot"
    ? [
        {
          source: i,
          ordinal: i,
          elemTy: ctx[i],
          pending: resolve(0, slot.input.async),
        },
      ]
    : [];

const schedInit = (ctx: Ty[], slots: Slots): Sched => ({
  mint: { ordinal: ctx.length, source: ctx.length + 1, node: 0, reg: 0 },
  live: slots.flatMap((slot, i) => mkHot(ctx, slot, i)),
  slots,
});

// pop the pending arrival minimal by (tick, ordinal); ordinals are
// unique, so no tie survives
const schedNext = (sched: Sched): { arrival: Arrival; sched: Sched } | null => {
  const heads = sched.live.flatMap((l, index) =>
    l.pending.length === 0
      ? []
      : [
          {
            index,
            arrival: {
              tick: l.pending[0].tick,
              ordinal: l.ordinal,
              source: l.source,
              elemTy: l.elemTy,
              payload: l.pending[0].val,
              isLast: l.pending.length === 1,
            },
          },
        ],
  );
  if (heads.length === 0) return null;
  const best = heads.reduce((a, b) =>
    a.arrival.tick < b.arrival.tick ||
    (a.arrival.tick === b.arrival.tick && a.arrival.ordinal < b.arrival.ordinal)
      ? a
      : b,
  );
  return {
    arrival: best.arrival,
    sched: {
      ...sched,
      live: sched.live.map((l, index) =>
        index === best.index ? { ...l, pending: l.pending.slice(1) } : l,
      ),
    },
  };
};

// the arrival's source's live chains, in subscription order, at exactly
// the arrival's element type: a chain is admitted only past a type
// equality check, so no payload is read at the wrong type
const chainsOf = (
  a: Arrival,
  st: EvalSt,
): { rid: RegId; path: Path; lo: number }[] =>
  st.registry
    .filter(
      (row) => regSource(row.src) === a.source && tyEq(row.elemTy, a.elemTy),
    )
    .map((row) => ({ rid: row.rid, path: row.path, lo: regFloor(row.src) }));

// ---------------------------------------------------------------
// The per-frame semantics -- every one of them takes a BURST
// ---------------------------------------------------------------

// take's emission split: pass through up to the remaining budget,
// reporting the new count and whether this burst hit the limit.  Real
// `take` cuts MID-BURST rather than waiting for the burst to finish.
const takeVals = (
  k: number,
  vals: Val[],
): { out: Val[]; remaining: number; didCut: boolean } => {
  if (k === 0) return { out: [], remaining: 0, didCut: false };
  if (vals.length === 0) return { out: [], remaining: k, didCut: false };
  if (k === 1) return { out: [vals[0]], remaining: 0, didCut: true };
  const rest = takeVals(k - 1, vals.slice(1));
  return {
    out: [vals[0], ...rest.out],
    remaining: rest.remaining,
    didCut: rest.didCut,
  };
};

type StepOut = { vals: Val[]; fin: boolean; sched: Sched; st: EvalSt };

const takeDispatch = (
  n: number,
  nid: NodeId,
  vals: Val[],
  fin: boolean,
  sched: Sched,
  st: EvalSt,
  node: NodeState | undefined,
): StepOut => {
  if (node === undefined || node.k !== "take")
    return { vals: [], fin, sched, st };
  const { out, remaining, didCut } = takeVals(node.remaining, vals);
  if (!didCut)
    return {
      vals: out,
      fin,
      sched,
      st: installNode(nid, { k: "take", remaining }, st),
    };
  const { kept, cut } = cutThrough(nid, st.registry);
  return {
    vals: out,
    fin: true,
    sched: { ...sched, live: sweepLive(n, kept, sched.live) },
    st: installNode(
      nid,
      { k: "take", remaining: 0 },
      {
        ...st,
        registry: kept,
        cancelled: [...cut, ...st.cancelled],
      },
    ),
  };
};

// scan's per-value fold: one running output per input.  Its output IS
// its carried state, which is what rxjs's `scan` is.
const scanDispatch = (
  fn: Fn,
  env: Val[],
  nid: NodeId,
  ty: Ty,
  vals: Val[],
  fin: boolean,
  sched: Sched,
  st: EvalSt,
  node: NodeState | undefined,
): StepOut => {
  if (node === undefined || node.k !== "cell" || !tyEq(node.ty, ty))
    return { vals: [], fin, sched, st };
  const { outs, last } = vals.reduce<{ outs: Val[]; last: Val }>(
    (acc, v) => {
      const next = evalWith(fn, [[acc.last, v], ...env]);
      return { outs: [...acc.outs, next], last: next };
    },
    { outs: [], last: node.val },
  );
  return {
    vals: outs,
    fin,
    sched,
    st: installNode(nid, { k: "cell", ty, val: last }, st),
  };
};

// THE BRACKET, AND THE BURST IS THE BATCH.  While the bit is up --
// inside the subscribe call -- the whole burst leaves as ONE value
// carrying all of it, head and tail; once it is down every value leaves
// as its own group of one.  An empty burst produces no value at all.
const batchVals = (sync: boolean, vals: Val[]): Val[] =>
  vals.length === 0
    ? []
    : sync
      ? [[vals[0], vals.slice(1)] as Val]
      : vals.map((v) => [v, []] as Val);

const batchDispatch = (vals: Val[], node: NodeState | undefined): Val[] =>
  node !== undefined && node.k === "batchSync"
    ? batchVals(node.sync, vals)
    : [];

// a from-inner completion is absorbed iff some registration under this
// inner instance is still live
const aliveThrough = (inst: NodeId, st: EvalSt, row: RegRow): boolean =>
  pathHasNode(inst, row.path) &&
  !st.cancelled.includes(row.rid) &&
  (!st.dying.includes(regSource(row.src)) || !st.delivered.includes(row.rid));

const hasRoom = (limit: number | null, active: number): boolean =>
  limit === null || active < limit;

// bump the live count on whatever state the node holds NOW: the inner's
// own synchronous burst can route back through this node and finish
// there, and a captured count would discard that drain
const mergeAllBump = (nid: NodeId, done: boolean, ns: EvalSt["nodes"]) => {
  const node = lookupNode(nid, ns);
  return node !== undefined && node.k === "mergeAll"
    ? setNode(
        nid,
        { ...node, active: done ? node.active : node.active + 1 },
        ns,
      )
    : ns;
};

const switchKill = (
  n: number,
  victim: NodeId | null,
  sched: Sched,
  st: EvalSt,
): { sched: Sched; st: EvalSt } => {
  if (victim === null) return { sched, st };
  const { kept, cut } = cutThrough(victim, st.registry);
  return {
    sched: { ...sched, live: sweepLive(n, kept, sched.live) },
    st: { ...st, registry: kept, cancelled: [...cut, ...st.cancelled] },
  };
};

// THE OUTER HAS FINISHED, RECORDED AND READ BACK IN ONE BREATH.  A lane
// can be drained and refilled while the outer's own burst is still being
// walked, so the verdict is a READING of the store as it then stands.
const thruWrap = (
  op: AllOp,
  nid: NodeId,
  fin: boolean,
  vals: Val[],
  sched: Sched,
  st: EvalSt,
): StepOut => {
  if (!fin) return { vals, fin: false, sched, st };
  const node = lookupNode(nid, st.nodes);
  if (node === undefined) return { vals, fin: true, sched, st };
  if (op === "mergeAll" && node.k === "mergeAll")
    return {
      vals,
      fin: node.active === 0 && node.queued.length === 0,
      sched,
      st: installNode(nid, { ...node, outerDone: true }, st),
    };
  if (op === "switch" && node.k === "switch")
    return {
      vals,
      fin: node.current === null,
      sched,
      st: installNode(nid, { ...node, outerDone: true }, st),
    };
  if (op === "exhaust" && node.k === "exhaust")
    return {
      vals,
      fin: !node.innerActive,
      sched,
      st: installNode(nid, { ...node, outerDone: true }, st),
    };
  return { vals, fin: true, sched, st };
};

const consumeUsable = (
  op: AllOp,
  u: Ty,
  node: NodeState | undefined,
): boolean => {
  if (node === undefined) return false;
  if (op === "mergeAll") return node.k === "mergeAll" && tyEq(node.ty, u);
  if (op === "switch") return node.k === "switch";
  return node.k === "exhaust" && !node.innerActive;
};

const finishUsable = (
  op: AllOp,
  s: Ty,
  inst: NodeId,
  node: NodeState | undefined,
): boolean => {
  if (node === undefined) return false;
  if (op === "mergeAll") return node.k === "mergeAll" && tyEq(node.ty, s);
  if (op === "switch") return node.k === "switch" && node.current === inst;
  return node.k === "exhaust";
};

// ---------------------------------------------------------------
// The share cycle's own helpers
// ---------------------------------------------------------------

// Latch completion AND mark the share dying, so a cut landing
// mid-fan-out can tell a share that has already finished from one still
// running; the registry entries drop at `shareFinish`.
const shareLatch = (i: number, fin: boolean, st: EvalSt): EvalSt =>
  fin
    ? {
        ...st,
        completedSources: [i, ...st.completedSources],
        dying: [i, ...st.dying],
      }
    : st;

// the registrations this share owes an emit: the row is a SLOT row on
// this very slot and the chain's element type is the share's.  A dynamic
// row is refused even when its source number matches, which is the Agda
// reading its own list's type rather than a premise -- every row here
// sinks strictly above `i`, so the floor is `suc i` by construction.
const shareAdmit = (
  i: number,
  ctx: Ty[],
  reg: RegRow[],
): { rid: RegId; path: Path; lo: number }[] =>
  reg
    .filter(
      (row) =>
        row.src.k === "slot" && row.src.i === i && tyEq(row.elemTy, ctx[i]),
    )
    .map((row) => ({ rid: row.rid, path: row.path, lo: regFloor(row.src) }));

type Out = { stream: Stream; sched: Sched; st: EvalSt };

const shareFinish = (n: number, i: number, fin: boolean, out: Out): Out => {
  if (!fin) return out;
  const kept = dropSource(i, out.st.registry);
  return {
    stream: out.stream,
    sched: { ...out.sched, live: sweepLive(n, kept, out.sched.live) },
    st: { ...out.st, registry: kept },
  };
};

// one arrival, count(source) emits.  A spent source is latched completed
// BEFORE its last delivery fans out -- as a Subject closes before
// delivering its completion -- and marked dying, so a chain that already
// spent this source's final delivery is not asked for another.
const cascadeLatch = (a: Arrival, st: EvalSt): EvalSt => ({
  ...st,
  completedSources: a.isLast
    ? [a.source, ...st.completedSources]
    : st.completedSources,
  delivered: [],
  cancelled: [],
  dying: a.isLast ? [a.source] : [],
});

const cascadeFinish = (
  n: number,
  a: Arrival,
  sched: Sched,
  st: EvalSt,
): { sched: Sched; st: EvalSt } => {
  if (!a.isLast) return { sched, st };
  const kept = dropSource(a.source, st.registry);
  return {
    sched: { ...sched, live: sweepLive(n, kept, sched.live) },
    st: { ...st, registry: kept },
  };
};

// ---------------------------------------------------------------
// THE MACHINE.  One function per constructor block of
// `Rx.Evaluator.Domain`, in that module's own order.
// ---------------------------------------------------------------

// The context is fixed for a whole run, so it rides in a closure rather
// than through twenty signatures -- which is what Agda's module
// telescope does with `Γ`.
const machine = (ctx: Ty[]) => {
  const n = ctx.length;

  // `subscribeE⇓`.  `lo` is the floor: the subscription may only reach
  // slots strictly below it.
  const subscribeE = (
    exp: Exp,
    env: Val[],
    kappa: Path,
    lo: number,
    now: Tick,
    sched: Sched,
    st: EvalSt,
  ): Out => {
    switch (exp.type) {
      case "input": {
        const i = exp.index;
        // subs-floor: a slot at or above the floor is out of reach
        if (i >= lo) return { stream: spentBurst, sched, st };
        const slot = sched.slots[i];
        if (slot.type === "shared")
          return subscribeSharedSlot(i, slot.def, kappa, now, sched, st);
        if (slot.input.type === "hot") {
          // subs-hot-done / subs-hot-live
          if (st.completedSources.includes(i))
            return { stream: spentBurst, sched, st };
          const rid = freshId("reg", sched.mint);
          return {
            stream: [],
            sched: bump("reg", sched),
            st: register(rid, { k: "slot", i }, ctx[i], kappa, st),
          };
        }
        // subs-cold-sync: no tail, so the prefix and the end are ONE
        // burst and nothing is registered
        if (slot.input.async.length === 0)
          return { stream: oneShotBurst(slot.input.sync), sched, st };
        // subs-cold-async: the registration is made BEFORE the prefix is
        // replayed, because a synchronous value can cut this very chain
        // and a cut severs registrations
        const src = freshId("source", sched.mint);
        const ord = freshId("ordinal", sched.mint);
        const rid = freshId("reg", sched.mint);
        return {
          stream: [slot.input.sync.map(valueP)],
          sched: {
            ...bump("reg", bump("source", bump("ordinal", sched))),
            live: [
              {
                source: src,
                ordinal: ord,
                elemTy: ctx[i],
                pending: resolve(now, slot.input.async),
              },
              ...sched.live,
            ],
          },
          st: register(
            rid,
            { k: "dyn", source: src, floor: lo },
            ctx[i],
            kappa,
            st,
          ),
        };
      }
      case "of":
        return {
          stream: oneShotBurst(exp.items.map((item) => evalWith(item, env))),
          sched,
          st,
        };
      case "empty":
        return { stream: oneShotBurst([]), sched, st };
      case "take": {
        const count = evalWith(exp.count, env);
        if (typeof count !== "number")
          throw new Error("take count did not evaluate to a nat");
        // `take(0)` NEVER SUBSCRIBES ITS SOURCE
        if (count === 0) return { stream: oneShotBurst([]), sched, st };
        const nid = freshId("node", sched.mint);
        const frame: Frame = { k: "take", nid };
        const inner = subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          bump("node", sched),
          installNode(nid, { k: "take", remaining: count }, st),
        );
        return pushBurst(
          now,
          frame,
          kappa,
          lo,
          inner.stream,
          inner.sched,
          inner.st,
        );
      }
      case "batchSync": {
        // THE BRACKET IS OPENED BY THE INSTALL AND CLOSED WHEN THE
        // SUBSCRIBE CALL RETURNS, WHICH IS WHERE THE BIT GOES DOWN.
        const nid = freshId("node", sched.mint);
        const frame: Frame = { k: "batchSync", nid };
        const inner = subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          bump("node", sched),
          installNode(nid, { k: "batchSync", sync: true }, st),
        );
        const out = pushBurst(
          now,
          frame,
          kappa,
          lo,
          inner.stream,
          inner.sched,
          inner.st,
        );
        return {
          ...out,
          st: installNode(nid, { k: "batchSync", sync: false }, out.st),
        };
      }
      case "map": {
        // A MAP INSTALLS NOTHING, which is why this arm is shorter than
        // every other transformer arm here.
        const frame: Frame = { k: "map", fn: exp.fn, env };
        const inner = subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          sched,
          st,
        );
        return pushBurst(
          now,
          frame,
          kappa,
          lo,
          inner.stream,
          inner.sched,
          inner.st,
        );
      }
      case "scan": {
        const nid = freshId("node", sched.mint);
        const frame: Frame = { k: "scan", fn: exp.fn, env, nid, ty: exp.ty };
        const inner = subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          bump("node", sched),
          installNode(
            nid,
            { k: "cell", ty: exp.ty, val: evalWith(exp.init, env) },
            st,
          ),
        );
        return pushBurst(
          now,
          frame,
          kappa,
          lo,
          inner.stream,
          inner.sched,
          inner.st,
        );
      }
      case "mergeAll":
        return subscribeAll(
          "mergeAll",
          {
            k: "mergeAll",
            ty: exp.ty,
            limit: exp.limit ?? null,
            active: 0,
            queued: [],
            outerDone: false,
          },
          exp.ty,
          exp.src,
          env,
          kappa,
          lo,
          now,
          sched,
          st,
        );
      case "switchAll":
        return subscribeAll(
          "switch",
          { k: "switch", current: null, outerDone: false },
          exp.ty,
          exp.src,
          env,
          kappa,
          lo,
          now,
          sched,
          st,
        );
      case "exhaustAll":
        return subscribeAll(
          "exhaust",
          { k: "exhaust", innerActive: false, outerDone: false },
          exp.ty,
          exp.src,
          env,
          kappa,
          lo,
          now,
          sched,
          st,
        );
      case "mu":
        // THE UNFOLDING IS UNCONDITIONAL: the recursive occurrences sit
        // behind defer hops, so each further unfolding costs a tick.
        return subscribeE(unfoldMu(exp.body), env, kappa, lo, now, sched, st);
      case "defer": {
        // a one-tick hop: the body is scheduled as an OBSERVABLE value
        // arriving at a merge node, which is what breaks mu's regress
        const nid = freshId("node", sched.mint);
        const src = freshId("source", sched.mint);
        const ord = freshId("ordinal", sched.mint);
        const rid = freshId("reg", sched.mint);
        const elemTy: Ty = { type: "obs", elem: exp.ty };
        return {
          stream: [],
          sched: {
            ...bump(
              "reg",
              bump("node", bump("source", bump("ordinal", sched))),
            ),
            live: [
              {
                source: src,
                ordinal: ord,
                elemTy,
                pending: [{ tick: now + 1, val: { exp: exp.body, env } }],
              },
              ...sched.live,
            ],
          },
          st: register(
            rid,
            { k: "dyn", source: src, floor: lo },
            elemTy,
            {
              k: "step",
              frame: { k: "thruOuter", op: "mergeAll", nid, elemTy: exp.ty },
              rest: kappa,
            },
            installNode(
              nid,
              {
                k: "mergeAll",
                ty: exp.ty,
                limit: null,
                active: 0,
                queued: [],
                outerDone: false,
              },
              st,
            ),
          ),
        };
      }
      case "mint": {
        // MINTING IS THE RUN'S, AND THE BODY RECEIVES THE TOKEN AS A
        // VALUE -- the only thing in the tree that lengthens the
        // environment.
        const src = freshId("source", sched.mint);
        return subscribeE(
          exp.body,
          [src, ...env],
          kappa,
          lo,
          now,
          bump("source", sched),
          st,
        );
      }
      case "varE":
        throw new Error(
          "varE in a closed expression — generator/decoder invariant violated",
        );
    }
  };

  // `subscribeInner⇓`: one inner subscription, at a freshly counted
  // instance.
  const subscribeInner = (
    op: AllOp,
    allNid: NodeId,
    elemTy: Ty,
    kappa: Path,
    lo: number,
    now: Tick,
    o: Val,
    sched: Sched,
    st: EvalSt,
  ): { inst: NodeId; vals: Val[]; done: boolean; sched: Sched; st: EvalSt } => {
    const inst = freshId("node", sched.mint);
    const obs = o as ObsVal;
    const out = subscribeE(
      obs.exp,
      obs.env,
      {
        k: "step",
        frame: { k: "fromInner", op, allNode: allNid, inst, elemTy },
        rest: kappa,
      },
      lo,
      now,
      bump("node", sched),
      st,
    );
    const { vals, complete } = splitBurst(out.stream);
    return { inst, vals, done: complete, sched: out.sched, st: out.st };
  };

  // `thruConsume⇓`: one arriving inner observable, admitted or refused
  // by the operator's own node.
  const thruConsume = (
    op: AllOp,
    nid: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    o: Val,
    u: Ty,
    sched: Sched,
    st: EvalSt,
  ): { vals: Val[]; sched: Sched; st: EvalSt } => {
    const node = lookupNode(nid, st.nodes);
    if (!consumeUsable(op, u, node)) return { vals: [], sched, st };
    if (op === "mergeAll" && node !== undefined && node.k === "mergeAll") {
      if (!hasRoom(node.limit, node.active))
        return {
          vals: [],
          sched,
          st: installNode(nid, { ...node, queued: [...node.queued, o] }, st),
        };
      const sub = subscribeInner(op, nid, u, kappa, lo, now, o, sched, st);
      return {
        vals: sub.vals,
        sched: sub.sched,
        st: { ...sub.st, nodes: mergeAllBump(nid, sub.done, sub.st.nodes) },
      };
    }
    if (op === "switch" && node !== undefined && node.k === "switch") {
      const killed = switchKill(n, node.current, sched, st);
      const sub = subscribeInner(
        op,
        nid,
        u,
        kappa,
        lo,
        now,
        o,
        killed.sched,
        killed.st,
      );
      return {
        vals: sub.vals,
        sched: sub.sched,
        st: installNode(
          nid,
          {
            k: "switch",
            current: sub.done ? null : sub.inst,
            outerDone: node.outerDone,
          },
          sub.st,
        ),
      };
    }
    if (op === "exhaust" && node !== undefined && node.k === "exhaust") {
      const sub = subscribeInner(op, nid, u, kappa, lo, now, o, sched, st);
      return {
        vals: sub.vals,
        sched: sub.sched,
        st: installNode(
          nid,
          { k: "exhaust", innerActive: !sub.done, outerDone: node.outerDone },
          sub.st,
        ),
      };
    }
    return { vals: [], sched, st };
  };

  // `thruWalk⇓`
  const thruWalk = (
    op: AllOp,
    nid: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    os: Val[],
    u: Ty,
    sched: Sched,
    st: EvalSt,
  ): { vals: Val[]; sched: Sched; st: EvalSt } =>
    os.reduce(
      (acc, o) => {
        const step = thruConsume(
          op,
          nid,
          kappa,
          lo,
          now,
          o,
          u,
          acc.sched,
          acc.st,
        );
        return {
          vals: [...acc.vals, ...step.vals],
          sched: step.sched,
          st: step.st,
        };
      },
      { vals: [] as Val[], sched, st },
    );

  // `mergeAllDrain⇓`.  THE SHORTENED QUEUE IS WRITTEN BEFORE THE
  // SUBSCRIBE, NOT AFTER THE WHOLE DRAIN: rxjs takes the item out of the
  // buffer before it subscribes it, so a batch write-back diverges.
  const mergeAllDrain = (
    allNid: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    ty: Ty,
    limit: number | null,
    active: number,
    outerDone: boolean,
    queued: Val[],
    sched: Sched,
    st: EvalSt,
  ): {
    vals: Val[];
    active: number;
    queued: Val[];
    sched: Sched;
    st: EvalSt;
  } => {
    if (queued.length === 0) return { vals: [], active, queued: [], sched, st };
    if (!hasRoom(limit, active)) return { vals: [], active, queued, sched, st };
    const rest = queued.slice(1);
    const sub = subscribeInner(
      "mergeAll",
      allNid,
      ty,
      kappa,
      lo,
      now,
      queued[0],
      sched,
      installNode(
        allNid,
        { k: "mergeAll", ty, limit, active, queued: rest, outerDone },
        st,
      ),
    );
    const tail = mergeAllDrain(
      allNid,
      kappa,
      lo,
      now,
      ty,
      limit,
      sub.done ? active : active + 1,
      outerDone,
      rest,
      sub.sched,
      sub.st,
    );
    return { ...tail, vals: [...sub.vals, ...tail.vals] };
  };

  // `innerFinish⇓`: an inner has died and its operator has to finish it.
  const innerFinish = (
    op: AllOp,
    allNid: NodeId,
    inst: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    vals: Val[],
    s: Ty,
    sched: Sched,
    st: EvalSt,
  ): StepOut => {
    const node = lookupNode(allNid, st.nodes);
    if (!finishUsable(op, s, inst, node) || node === undefined)
      return { vals, fin: false, sched, st };
    if (node.k === "mergeAll") {
      const drained = mergeAllDrain(
        allNid,
        kappa,
        lo,
        now,
        node.ty,
        node.limit,
        Math.max(node.active - 1, 0),
        node.outerDone,
        node.queued,
        sched,
        st,
      );
      return {
        vals: [...vals, ...drained.vals],
        fin:
          node.outerDone && drained.active === 0 && drained.queued.length === 0,
        sched: drained.sched,
        st: installNode(
          allNid,
          { ...node, active: drained.active, queued: drained.queued },
          drained.st,
        ),
      };
    }
    if (node.k === "switch")
      return {
        vals,
        fin: node.outerDone,
        sched,
        st: installNode(allNid, { ...node, current: null }, st),
      };
    if (node.k === "exhaust")
      return {
        vals,
        fin: node.outerDone,
        sched,
        st: installNode(allNid, { ...node, innerActive: false }, st),
      };
    return { vals, fin: false, sched, st };
  };

  // `innerReact⇓`: a completion arriving out of an inner is absorbed
  // while anything under that instance is still live.
  const innerReact = (
    op: AllOp,
    allNid: NodeId,
    inst: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    vals: Val[],
    s: Ty,
    fin: boolean,
    sched: Sched,
    st: EvalSt,
  ): StepOut => {
    if (!fin) return { vals, fin: false, sched, st };
    if (st.registry.some((row) => aliveThrough(inst, st, row)))
      return { vals, fin: false, sched, st };
    return innerFinish(op, allNid, inst, kappa, lo, now, vals, s, sched, st);
  };

  // `stepFrame⇓`
  const stepFrame = (
    now: Tick,
    f: Frame,
    kappa: Path,
    lo: number,
    vals: Val[],
    fin: boolean,
    sched: Sched,
    st: EvalSt,
  ): StepOut => {
    switch (f.k) {
      case "map":
        return {
          vals: vals.map((v) => evalWith(f.fn, [v, ...f.env])),
          fin,
          sched,
          st,
        };
      case "scan":
        return scanDispatch(
          f.fn,
          f.env,
          f.nid,
          f.ty,
          vals,
          fin,
          sched,
          st,
          lookupNode(f.nid, st.nodes),
        );
      case "take":
        return takeDispatch(
          n,
          f.nid,
          vals,
          fin,
          sched,
          st,
          lookupNode(f.nid, st.nodes),
        );
      case "batchSync":
        return {
          vals: batchDispatch(vals, lookupNode(f.nid, st.nodes)),
          fin,
          sched,
          st,
        };
      case "fromInner":
        return innerReact(
          f.op,
          f.allNode,
          f.inst,
          kappa,
          lo,
          now,
          vals,
          f.elemTy,
          fin,
          sched,
          st,
        );
      case "thruOuter": {
        const walked = thruWalk(
          f.op,
          f.nid,
          kappa,
          lo,
          now,
          vals,
          f.elemTy,
          sched,
          st,
        );
        return thruWrap(f.op, f.nid, fin, walked.vals, walked.sched, walked.st);
      }
    }
  };

  // `pushBurst⇓`: a burst at a time, each one stepped and re-emitted.
  //
  // THE CONTINUATION IS NOT DECORATION HERE, which is easy to miss
  // because four of the six frames ignore it.  A FLATTENING frame
  // subscribes what it consumes, so it needs the path BELOW itself and
  // the floor it stands at -- and neither is recoverable from the burst,
  // which carries values and nothing else.  That is the burst carrier's
  // one structural cost, and it is why this takes them as arguments
  // rather than reconstructing them.
  const pushBurst = (
    now: Tick,
    f: Frame,
    kappa: Path,
    lo: number,
    stream: Stream,
    sched: Sched,
    st: EvalSt,
  ): Out =>
    stream.reduce<Out>(
      (acc, b) => {
        const { vals, complete } = splitEvents(b);
        const stepped = stepFrame(
          now,
          f,
          kappa,
          lo,
          vals,
          complete,
          acc.sched,
          acc.st,
        );
        return {
          stream: [
            ...acc.stream,
            [...stepped.vals.map(valueP), ...(stepped.fin ? [completeP] : [])],
          ],
          sched: stepped.sched,
          st: stepped.st,
        };
      },
      { stream: [], sched, st },
    );

  // `subscribeAll⇓`
  const subscribeAll = (
    op: AllOp,
    ns: NodeState,
    elemTy: Ty,
    src: Exp,
    env: Val[],
    kappa: Path,
    lo: number,
    now: Tick,
    sched: Sched,
    st: EvalSt,
  ): Out => {
    const nid = freshId("node", sched.mint);
    const frame: Frame = { k: "thruOuter", op, nid, elemTy };
    const inner = subscribeE(
      src,
      env,
      { k: "step", frame, rest: kappa },
      lo,
      now,
      bump("node", sched),
      installNode(nid, ns, st),
    );
    return pushBurst(
      now,
      frame,
      kappa,
      lo,
      inner.stream,
      inner.sched,
      inner.st,
    );
  };

  // `sharedConnect⇓`: the def is subscribed ONCE, at the floor its own
  // INDEX fixes rather than the subscriber's -- which is why no floor is
  // taken here.  A share's definition may only reach slots below the
  // share itself, whoever happens to be subscribing.
  const sharedConnect = (
    i: number,
    def: Closed,
    kappa: Path,
    now: Tick,
    sched: Sched,
    st: EvalSt,
  ): Out => {
    const rid = freshId("reg", sched.mint);
    const out = subscribeE(
      def,
      [],
      { k: "shareSink", i },
      i,
      now,
      bump("reg", sched),
      register(rid, { k: "slot", i }, ctx[i], kappa, {
        ...st,
        connectedShares: [i, ...st.connectedShares],
      }),
    );
    if (!burstCompleted(out.stream)) return out;
    return {
      ...out,
      st: {
        ...out.st,
        registry: dropSource(i, out.st.registry),
        completedSources: [i, ...out.st.completedSources],
      },
    };
  };

  // `subscribeSharedSlot⇓`
  const subscribeSharedSlot = (
    i: number,
    def: Closed,
    kappa: Path,
    now: Tick,
    sched: Sched,
    st: EvalSt,
  ): Out => {
    // a completed Subject re-delivers completion to late subscribers;
    // values are not re-observable, completion is
    if (st.completedSources.includes(i))
      return { stream: spentBurst, sched, st };
    if (st.connectedShares.includes(i)) {
      const rid = freshId("reg", sched.mint);
      return {
        stream: [],
        sched: bump("reg", sched),
        st: register(rid, { k: "slot", i }, ctx[i], kappa, st),
      };
    }
    return sharedConnect(i, def, kappa, now, sched, st);
  };

  // `dispatchShare⇓` / `shareGo⇓`
  const dispatchShare = (
    now: Tick,
    i: number,
    vals: Val[],
    fin: boolean,
    sched: Sched,
    st: EvalSt,
  ): Out => {
    const latched = shareLatch(i, fin, st);
    const rows = shareAdmit(i, ctx, st.registry);
    const gone = rows.reduce<Out>(
      (acc, row) => {
        if (acc.st.cancelled.includes(row.rid)) return acc;
        const folded = foldPath(
          now,
          row.path,
          vals,
          fin,
          acc.sched,
          { ...acc.st, delivered: [row.rid, ...acc.st.delivered] },
          row.lo,
        );
        return {
          stream: [...acc.stream, ...folded.stream],
          sched: folded.sched,
          st: folded.st,
        };
      },
      { stream: [], sched, st: latched },
    );
    return shareFinish(n, i, fin, gone);
  };

  // `foldPath⇓`: the path is walked sinkward and the burst is assembled
  // at the root, so the root clause is the only one that mints an emit
  // from nothing.
  //
  // THE FLOOR A STORED PATH STANDS AT IS THE ROW'S, not zero, and a
  // flattening frame reached this way subscribes at it.  That is what
  // `regFloor` is for: a slot row floors at `suc i`, a dynamic row at
  // whatever floor its registration was made under.
  const foldPath = (
    now: Tick,
    p: Path,
    vals: Val[],
    fin: boolean,
    sched: Sched,
    st: EvalSt,
    lo: number,
  ): Out => {
    if (p.k === "root")
      return {
        stream: [[...vals.map(valueP), ...(fin ? [completeP] : [])]],
        sched,
        st,
      };
    if (p.k === "shareSink")
      return dispatchShare(now, p.i, vals, fin, sched, st);
    const stepped = stepFrame(now, p.frame, p.rest, lo, vals, fin, sched, st);
    return foldPath(
      now,
      p.rest,
      stepped.vals,
      stepped.fin,
      stepped.sched,
      stepped.st,
      lo,
    );
  };

  // `cascade⇓`: one arrival, every live chain of its source, in
  // subscription order.
  const cascade = (a: Arrival, sched: Sched, st: EvalSt): Out => {
    const latched = cascadeLatch(a, st);
    const gone = chainsOf(a, latched).reduce<Out>(
      (acc, chain) => {
        if (acc.st.cancelled.includes(chain.rid)) return acc;
        const folded = foldPath(
          a.tick,
          chain.path,
          [a.payload],
          a.isLast,
          acc.sched,
          { ...acc.st, delivered: [chain.rid, ...acc.st.delivered] },
          chain.lo,
        );
        return {
          stream: [...acc.stream, ...folded.stream],
          sched: folded.sched,
          st: folded.st,
        };
      },
      { stream: [], sched, st: latched },
    );
    const finished = cascadeFinish(n, a, gone.sched, gone.st);
    return { stream: gone.stream, ...finished };
  };

  // `drain⇓`
  const drain = (fuel: number, sched: Sched, st: EvalSt): Stream => {
    if (fuel === 0) return [];
    const next = schedNext(sched);
    if (next === null) return [];
    const out = cascade(next.arrival, next.sched, st);
    return [...out.stream, ...drain(fuel - 1, out.sched, out.st)];
  };

  // `evaluate⇓`: the root subscription's burst, then the arrivals fuel
  // pays for.
  const evaluate = (fuel: number, e: Closed, slots: Slots): Stream => {
    const sched = schedInit(ctx, slots);
    const first = subscribeE(e, [], { k: "root" }, n, 0, sched, stInit());
    return [...first.stream, ...drain(fuel, first.sched, first.st)];
  };

  return { evaluate };
};

export const evaluateRef = (testCase: TestCase): Val[] => {
  const stream = machine(testCase.ctx).evaluate(
    testCase.fuel,
    testCase.exp,
    testCase.slots,
  );
  return stream.flatMap((b) =>
    b.flatMap((e) => (e.k === "value" ? [e.val] : [])),
  );
};
