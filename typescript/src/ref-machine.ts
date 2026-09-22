import { Fn, Ty, Val, evalWith, tyEq } from "./exp.js";
import type { Slot, Slots, Timed } from "./prop-test.js";

// THE SHARED VOCABULARY OF THE REFERENCE MACHINES.
//
// The carrier is the thing under test in this tier, so there are two
// machines here: `ref-eval.ts` transcribes the Agda as it stands, and
// `ref-push.ts` is the candidate.  What they may NOT differ on is
// everything a carrier change has no business touching -- the schedule,
// the registry, the mint, the node store, the share cycle -- because a
// divergence there would read as a carrier finding and be one of them
// having drifted.  So that vocabulary is defined once, here, and neither
// machine may keep a private copy.
//
// This module states no semantics of its own.  Every name below is its
// namesake in `Rx.Evaluator`, and the two machines are the two readings
// of `Rx.Evaluator.Domain` built on it.

export type Tick = number;
export type NodeId = number;
export type RegId = number;
export type Source = number;
export type Ordinal = number;

// ---------------------------------------------------------------
// The carrier
// ---------------------------------------------------------------

// A BURST IS EVERYTHING ONE INCOMING EMIT CAUSES, and a subscription
// hands its whole output back as a list of them.  This is the carrier
// under test: the group a bracket wants is already assembled by the
// time a frame sees it, which is what `batchVals` below reads.
export type PlainEvent = { k: "value"; val: Val } | { k: "complete" };
export type Burst = PlainEvent[];
export type Stream = Burst[];

export const valueP = (val: Val): PlainEvent => ({ k: "value", val });
export const completeP: PlainEvent = { k: "complete" };

export const oneShotBurst = (vals: Val[]): Stream => [
  [...vals.map(valueP), completeP],
];
export const spentBurst: Stream = [[completeP]];

export const splitEvents = (b: Burst): { vals: Val[]; complete: boolean } => ({
  vals: b.flatMap((e) => (e.k === "value" ? [e.val] : [])),
  complete: b.some((e) => e.k === "complete"),
});

export const splitBurst = (s: Stream): { vals: Val[]; complete: boolean } =>
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

export const burstCompleted = (s: Stream): boolean =>
  s.some((b) => b.some((e) => e.k === "complete"));

// ---------------------------------------------------------------
// The node store, the frames and the rootward paths
// ---------------------------------------------------------------

export type AllOp = "mergeAll" | "switch" | "exhaust";

// `batchSync`'s BUFFER IS EMPTY UNDER THE BURST CARRIER AND IS THE
// GROUP UNDER THE PUSH CARRIER, which is the one field here that is not
// common ground.  It is shared anyway because the node STORE is: a
// carrier decides when a value reaches a frame, never which frames
// exist, and giving the push machine its own node union would let the
// two drift on everything else in it to buy one field.
export type NodeState =
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
  | { k: "batchSync"; sync: boolean; buffer: Val[] };

// A FRAME CARRIES THE ELEMENT TYPE IT WORKS AT, and that is not
// bookkeeping: in Agda the type is an INDEX on the frame, so the three
// clauses that pay a `_≟ᵗ_` against a stored node read it off the frame
// for free.  Recovering it here from the value flowing past instead
// would be a guess, and a wrong guess reads as a missing node rather
// than as a type error -- silently forwarding nothing.
export type Frame =
  | { k: "map"; fn: Fn; env: Val[] }
  | { k: "scan"; fn: Fn; env: Val[]; nid: NodeId; ty: Ty }
  | { k: "take"; nid: NodeId }
  | { k: "batchSync"; nid: NodeId }
  | {
      k: "fromInner";
      op: AllOp;
      allNode: NodeId;
      inst: NodeId;
      elemTy: Ty;
      lo: number;
    }
  | { k: "thruOuter"; op: AllOp; nid: NodeId; elemTy: Ty; lo: number };

// AND A JOINING FRAME CARRIES ITS FLOOR FOR THE SAME REASON IT CARRIES
// ITS TYPE.  A flattener subscribes inners in reaction to values, and the
// floor those inners are subscribed at is the flattener's OWN -- where it
// was written -- never the floor of whatever delivered the value.  The
// two coincide until a SHARE is in between: a share's rows are stored at
// the share's floor, so a value arriving through one carries a floor that
// can see fewer slots than the program that reacts to it, and an inner
// subscribed at that floor silently ends instead of reading its input.
// A carrier that hands the burst back to the caller never exposed this,
// because there the caller supplied the floor.

// THE FLOOR IS NOT CARRIED ON THE PATH ITSELF, and that is the one place
// the shape differs from the Agda without the meaning differing.  There
// the floor is a TYPE index, so `lowerFloor` exists to retype a path a
// registry row is about to store; here it is an ordinary argument to
// `subscribeE` and a field on the row, and lowering is the identity on
// structure -- which is exactly what `lowerFloor` computes.
export type Path =
  | { k: "root" }
  | { k: "shareSink"; i: number }
  | { k: "step"; frame: Frame; rest: Path };

export const frameNodes = (f: Frame): NodeId[] => {
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

export const pathHasNode = (nid: NodeId, p: Path): boolean =>
  p.k === "step" &&
  (frameNodes(p.frame).includes(nid) || pathHasNode(nid, p.rest));

// ---------------------------------------------------------------
// The registry, the schedule and the evaluator state
// ---------------------------------------------------------------

export type RegSrc =
  { k: "slot"; i: number } | { k: "dyn"; source: Source; floor: number };

export const regSource = (rs: RegSrc): Source =>
  rs.k === "slot" ? rs.i : rs.source;
export const regFloor = (rs: RegSrc): number =>
  rs.k === "slot" ? rs.i + 1 : rs.floor;

export type RegRow = { rid: RegId; src: RegSrc; elemTy: Ty; path: Path };

export type LiveSource = {
  source: Source;
  ordinal: Ordinal;
  elemTy: Ty;
  pending: { tick: Tick; val: Val }[];
};

export type MintKey = "ordinal" | "source" | "node" | "reg";
export type Mint = Record<MintKey, number>;

export type Sched = { mint: Mint; live: LiveSource[]; slots: Slots };

export type EvalSt = {
  registry: RegRow[];
  nodes: { nid: NodeId; state: NodeState }[];
  connectedShares: Source[];
  completedSources: Source[];
  delivered: RegId[];
  cancelled: RegId[];
  dying: Source[];
};

export type Arrival = {
  tick: Tick;
  ordinal: Ordinal;
  source: Source;
  elemTy: Ty;
  payload: Val;
  isLast: boolean;
};

export const freshId = (k: MintKey, m: Mint): number => m[k];
export const setAt = (k: MintKey, v: number, m: Mint): Mint => ({
  ...m,
  [k]: v,
});
export const bump = (k: MintKey, sched: Sched): Sched => ({
  ...sched,
  mint: setAt(k, freshId(k, sched.mint) + 1, sched.mint),
});

export const lookupNode = (
  nid: NodeId,
  ns: EvalSt["nodes"],
): NodeState | undefined => ns.find((row) => row.nid === nid)?.state;

export const setNode = (
  nid: NodeId,
  state: NodeState,
  ns: EvalSt["nodes"],
): EvalSt["nodes"] =>
  ns.some((row) => row.nid === nid)
    ? ns.map((row) => (row.nid === nid ? { nid, state } : row))
    : [...ns, { nid, state }];

export const installNode = (
  nid: NodeId,
  state: NodeState,
  st: EvalSt,
): EvalSt => ({
  ...st,
  nodes: setNode(nid, state, st.nodes),
});

// append: the registry stays in subscription order, which is what a
// share's fan-out order IS
export const register = (
  rid: RegId,
  src: RegSrc,
  elemTy: Ty,
  path: Path,
  st: EvalSt,
): EvalSt => ({
  ...st,
  registry: [...st.registry, { rid, src, elemTy, path }],
});

export const stInit = (): EvalSt => ({
  registry: [],
  nodes: [],
  connectedShares: [],
  completedSources: [],
  delivered: [],
  cancelled: [],
  dying: [],
});

export const cutThrough = (
  nid: NodeId,
  reg: RegRow[],
): { kept: RegRow[]; cut: RegId[] } => ({
  kept: reg.filter((row) => !pathHasNode(nid, row.path)),
  cut: reg.filter((row) => pathHasNode(nid, row.path)).map((row) => row.rid),
});

// drop dead dynamic sources; slot sources (< n) keep firing regardless,
// exactly like a hot Subject with no subscribers
export const sweepLive = (
  n: number,
  reg: RegRow[],
  live: LiveSource[],
): LiveSource[] =>
  live.filter(
    (l) => l.source < n || reg.some((row) => regSource(row.src) === l.source),
  );

export const dropSource = (src: Source, reg: RegRow[]): RegRow[] =>
  reg.filter((row) => regSource(row.src) !== src);

// ---------------------------------------------------------------
// The schedule
// ---------------------------------------------------------------

// delta-encoded waits → absolute ticks (gap = wait + 1, so a source's
// ticks are strictly increasing by construction)
export const resolve = (
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
export const mkHot = (ctx: Ty[], slot: Slot, i: number): LiveSource[] =>
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

export const schedInit = (ctx: Ty[], slots: Slots): Sched => ({
  mint: { ordinal: ctx.length, source: ctx.length + 1, node: 0, reg: 0 },
  live: slots.flatMap((slot, i) => mkHot(ctx, slot, i)),
  slots,
});

// pop the pending arrival minimal by (tick, ordinal); ordinals are
// unique, so no tie survives
export const schedNext = (
  sched: Sched,
): { arrival: Arrival; sched: Sched } | null => {
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
export const chainsOf = (
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
export const takeVals = (
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

export type StepOut = { vals: Val[]; fin: boolean; sched: Sched; st: EvalSt };

export const takeDispatch = (
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
export const scanDispatch = (
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
export const batchVals = (sync: boolean, vals: Val[]): Val[] =>
  vals.length === 0
    ? []
    : sync
      ? [[vals[0], vals.slice(1)] as Val]
      : vals.map((v) => [v, []] as Val);

export const batchDispatch = (
  vals: Val[],
  node: NodeState | undefined,
): Val[] =>
  node !== undefined && node.k === "batchSync"
    ? batchVals(node.sync, vals)
    : [];

// a from-inner completion is absorbed iff some registration under this
// inner instance is still live
export const aliveThrough = (inst: NodeId, st: EvalSt, row: RegRow): boolean =>
  pathHasNode(inst, row.path) &&
  !st.cancelled.includes(row.rid) &&
  (!st.dying.includes(regSource(row.src)) || !st.delivered.includes(row.rid));

export const hasRoom = (limit: number | null, active: number): boolean =>
  limit === null || active < limit;

// bump the live count on whatever state the node holds NOW: the inner's
// own synchronous burst can route back through this node and finish
// there, and a captured count would discard that drain
export const mergeAllBump = (
  nid: NodeId,
  done: boolean,
  ns: EvalSt["nodes"],
) => {
  const node = lookupNode(nid, ns);
  return node !== undefined && node.k === "mergeAll"
    ? setNode(
        nid,
        { ...node, active: done ? node.active : node.active + 1 },
        ns,
      )
    : ns;
};

export const switchKill = (
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
export const thruWrap = (
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

export const consumeUsable = (
  op: AllOp,
  u: Ty,
  node: NodeState | undefined,
): boolean => {
  if (node === undefined) return false;
  if (op === "mergeAll") return node.k === "mergeAll" && tyEq(node.ty, u);
  if (op === "switch") return node.k === "switch";
  return node.k === "exhaust" && !node.innerActive;
};

export const finishUsable = (
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
export const shareLatch = (i: number, fin: boolean, st: EvalSt): EvalSt =>
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
export const shareAdmit = (
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

export type Out = { stream: Stream; sched: Sched; st: EvalSt };

export const shareFinish = (
  n: number,
  i: number,
  fin: boolean,
  out: Out,
): Out => {
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
export const cascadeLatch = (a: Arrival, st: EvalSt): EvalSt => ({
  ...st,
  completedSources: a.isLast
    ? [a.source, ...st.completedSources]
    : st.completedSources,
  delivered: [],
  cancelled: [],
  dying: a.isLast ? [a.source] : [],
});

export const cascadeFinish = (
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
