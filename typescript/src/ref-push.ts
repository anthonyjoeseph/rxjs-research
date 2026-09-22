import { Closed, Exp, Ty, Val, ObsVal, evalWith, unfoldMu } from "./exp.js";
import type { Slots, TestCase } from "./prop-test.js";
import {
  AllOp,
  Arrival,
  EvalSt,
  Frame,
  NodeId,
  NodeState,
  Path,
  Sched,
  Stream,
  Tick,
  aliveThrough,
  bump,
  cascadeFinish,
  cascadeLatch,
  chainsOf,
  completeP,
  consumeUsable,
  finishUsable,
  freshId,
  hasRoom,
  installNode,
  lookupNode,
  mergeAllBump,
  register,
  resolve,
  scanDispatch,
  schedInit,
  schedNext,
  shareAdmit,
  shareFinish,
  shareLatch,
  switchKill,
  takeDispatch,
  thruWrap,
  valueP,
} from "./ref-machine.js";

// THE PUSH CARRIER: THE CANDIDATE THE POSITION PAIR DECIDES.
//
// WHAT CHANGES.  A subscription hands back no burst.  It pushes each
// value through its own continuation AS THE VALUE IS PRODUCED, so a
// reaction to a value runs before the source is asked for the next one.
// Everything else is `ref-machine`, shared with the burst reading so the
// two cannot drift on anything a carrier has no business touching.
//
// WHY.  A subscription that returns a list is sound exactly while a
// reaction cannot change what the source still owes, and a SHARE is
// where it can: a burst hands the whole emission to the first subscriber,
// so the subscriptions that emission causes register after it is over
// and receive nothing.  The fix is not a rule about shares -- the share
// clause below is unchanged.  It is that the def now reaches
// `dispatchShare` one value at a time, so the fan-out reads the registry
// as it stands at each value rather than as it stood at the first.
//
// AND THE GROUP MOVES WITH THE CARRIER.  `batchSync` used to read its
// batch off the burst, which is the one thing here that cannot survive
// the change: with no burst there is nothing to read.  So the bracket
// keeps its own buffer in its node and flushes at the moment the
// subscribe call returns, which is what the bracket always meant.  That
// is the only place this rewrite can change an answer rather than
// re-thread one.
//
// This is NOT the Agda.  While the burst reading is what `agda/`
// implements, `--machine agda --baseline ref` is the check that says so,
// and this file is measured against rxjs instead.  When the transcription
// lands, the burst reading is a superseded predecessor and goes.

// The world every push threads: what has reached the ROOT so far, the
// schedule, and the evaluator state.
type W = { out: Stream; sched: Sched; st: EvalSt };

// ALIVE IS THE SOURCE'S QUESTION, and it is the burst carrier's one
// genuine loss: a caller that held the whole emission never had to ask
// whether the consumer was still there.  A `take` that cuts mid-emission
// unsubscribes its source, so a synchronous source pushing value by
// value has to stop -- which is exactly what rxjs does and what a list
// could not express.
type Pushed = { alive: boolean; w: W };

// DONE IS READ, NOT CARRIED.  The burst reading asked whether a
// `completeᵖ` appeared in the list it was handed; with nothing handed
// back, each clause reports whether a completion left it, and the
// flattening clauses read that off their own node -- the same reading
// `thruWrap` makes when it decides to emit one.
type Subbed = { done: boolean; w: W };

const machine = (ctx: Ty[]) => {
  const n = ctx.length;

  // `foldPath⇓`, walked sinkward-to-rootward as before -- but now once
  // per value rather than once per burst.
  const foldPath = (
    now: Tick,
    p: Path,
    vals: Val[],
    fin: boolean,
    lo: number,
    w: W,
  ): Pushed => {
    if (p.k === "root")
      return {
        alive: true,
        w:
          vals.length === 0 && !fin
            ? w
            : {
                ...w,
                out: [
                  ...w.out,
                  [...vals.map(valueP), ...(fin ? [completeP] : [])],
                ],
              },
      };
    if (p.k === "shareSink") return dispatchShare(now, p.i, vals, fin, w);
    const stepped = stepFrame(now, p.frame, p.rest, lo, vals, fin, w);
    const up = foldPath(now, p.rest, stepped.vals, stepped.fin, lo, stepped.w);
    return { alive: stepped.alive && up.alive, w: up.w };
  };

  // `stepFrame⇓`
  const stepFrame = (
    now: Tick,
    f: Frame,
    kappa: Path,
    lo: number,
    vals: Val[],
    fin: boolean,
    w: W,
  ): { vals: Val[]; fin: boolean; alive: boolean; w: W } => {
    switch (f.k) {
      case "map":
        return {
          vals: vals.map((v) => evalWith(f.fn, [v, ...f.env])),
          fin,
          alive: true,
          w,
        };
      case "scan": {
        const r = scanDispatch(
          f.fn,
          f.env,
          f.nid,
          f.ty,
          vals,
          fin,
          w.sched,
          w.st,
          lookupNode(f.nid, w.st.nodes),
        );
        return {
          vals: r.vals,
          fin: r.fin,
          alive: true,
          w: { ...w, sched: r.sched, st: r.st },
        };
      }
      case "take": {
        const r = takeDispatch(
          n,
          f.nid,
          vals,
          fin,
          w.sched,
          w.st,
          lookupNode(f.nid, w.st.nodes),
        );
        // a cut is `take` ending a subscription the source did not end,
        // which is the one thing that makes a live source stop
        return {
          vals: r.vals,
          fin: r.fin,
          alive: !(r.fin && !fin),
          w: { ...w, sched: r.sched, st: r.st },
        };
      }
      case "batchSync": {
        const node = lookupNode(f.nid, w.st.nodes);
        if (node === undefined || node.k !== "batchSync")
          return { vals: [], fin, alive: true, w };
        // INSIDE THE BRACKET NOTHING LEAVES, THE END INCLUDED.  A source
        // that finishes within the subscribe call has to leave with its
        // group rather than ahead of it, so the completion is swallowed
        // here and re-emitted by the clause that closes the bracket.
        if (node.sync)
          return {
            vals: [],
            fin: false,
            alive: true,
            w: {
              ...w,
              st: installNode(
                f.nid,
                { ...node, buffer: [...node.buffer, ...vals] },
                w.st,
              ),
            },
          };
        return {
          vals: vals.map((v) => [v, []] as Val),
          fin,
          alive: true,
          w,
        };
      }
      case "fromInner": {
        if (!fin) return { vals, fin: false, alive: true, w };
        const r = innerReact(
          f.op,
          f.allNode,
          f.inst,
          kappa,
          lo,
          now,
          f.elemTy,
          w,
        );
        return { vals, fin: r.fin, alive: true, w: r.w };
      }
      case "thruOuter": {
        // the inners' own values reach the root through their own
        // `fromInner` paths, so nothing passes through here
        const walked = thruWalk(f.op, f.nid, kappa, lo, now, vals, f.elemTy, w);
        const r = thruWrap(f.op, f.nid, fin, [], walked.sched, walked.st);
        return {
          vals: [],
          fin: r.fin,
          alive: true,
          w: { ...walked, sched: r.sched, st: r.st },
        };
      }
    }
  };

  // A VALUE AND AN END MAY NEVER SHARE A CALL, and this is the only
  // place that guarantees it -- so every emission goes through here, a
  // scheduled arrival carrying `isLast` as much as a synchronous burst.
  // The frames REACT to an end: `fromInner` drains its joiner's queue
  // there, and a queued inner subscribed inside that reaction emits
  // before the value it was handed alongside.  The burst carrier could
  // not see this, because under it the pair was the unit of delivery.
  // Value by value, stopping the moment the chain is cut.
  const pushAll = (
    now: Tick,
    kappa: Path,
    lo: number,
    vals: Val[],
    finish: boolean,
    w: W,
  ): Subbed => {
    const stepped = vals.reduce<Pushed>(
      (acc, v) =>
        acc.alive ? foldPath(now, kappa, [v], false, lo, acc.w) : acc,
      { alive: true, w },
    );
    // a cut ENDED this subscription, so it is done whether or not the
    // source got as far as saying so
    if (!stepped.alive) return { done: true, w: stepped.w };
    if (!finish) return { done: false, w: stepped.w };
    return { done: true, w: foldPath(now, kappa, [], true, lo, stepped.w).w };
  };

  const endNow = (now: Tick, kappa: Path, lo: number, w: W): Subbed => ({
    done: true,
    w: foldPath(now, kappa, [], true, lo, w).w,
  });

  // `subscribeE⇓`
  const subscribeE = (
    exp: Exp,
    env: Val[],
    kappa: Path,
    lo: number,
    now: Tick,
    w: W,
  ): Subbed => {
    switch (exp.type) {
      case "input": {
        const i = exp.index;
        if (i >= lo) return endNow(now, kappa, lo, w);
        const slot = w.sched.slots[i];
        if (slot.type === "shared")
          return subscribeSharedSlot(i, slot.def, kappa, now, w);
        if (slot.input.type === "hot") {
          if (w.st.completedSources.includes(i))
            return endNow(now, kappa, lo, w);
          const rid = freshId("reg", w.sched.mint);
          return {
            done: false,
            w: {
              ...w,
              sched: bump("reg", w.sched),
              st: register(rid, { k: "slot", i }, ctx[i], kappa, w.st),
            },
          };
        }
        if (slot.input.async.length === 0)
          return pushAll(now, kappa, lo, slot.input.sync, true, w);
        // the registration is made BEFORE the prefix is replayed, since
        // a synchronous value can cut this very chain
        const src = freshId("source", w.sched.mint);
        const ord = freshId("ordinal", w.sched.mint);
        const rid = freshId("reg", w.sched.mint);
        return pushAll(now, kappa, lo, slot.input.sync, false, {
          out: w.out,
          sched: {
            ...bump("reg", bump("source", bump("ordinal", w.sched))),
            live: [
              {
                source: src,
                ordinal: ord,
                elemTy: ctx[i],
                pending: resolve(now, slot.input.async),
              },
              ...w.sched.live,
            ],
          },
          st: register(
            rid,
            { k: "dyn", source: src, floor: lo },
            ctx[i],
            kappa,
            w.st,
          ),
        });
      }
      case "of":
        return pushAll(
          now,
          kappa,
          lo,
          exp.items.map((item) => evalWith(item, env)),
          true,
          w,
        );
      case "empty":
        return endNow(now, kappa, lo, w);
      case "take": {
        const count = evalWith(exp.count, env);
        if (typeof count !== "number")
          throw new Error("take count did not evaluate to a nat");
        // `take(0)` NEVER SUBSCRIBES ITS SOURCE
        if (count === 0) return endNow(now, kappa, lo, w);
        const nid = freshId("node", w.sched.mint);
        const frame: Frame = { k: "take", nid };
        // take forwards its source's end and manufactures one when it
        // cuts, and `pushAll` already reports a cut as done -- so the
        // source's own verdict is this subscription's
        return subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          {
            ...w,
            sched: bump("node", w.sched),
            st: installNode(nid, { k: "take", remaining: count }, w.st),
          },
        );
      }
      case "batchSync": {
        const nid = freshId("node", w.sched.mint);
        const frame: Frame = { k: "batchSync", nid };
        const inner = subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          {
            ...w,
            sched: bump("node", w.sched),
            st: installNode(
              nid,
              { k: "batchSync", sync: true, buffer: [] },
              w.st,
            ),
          },
        );
        // CLOSING THE BRACKET IS WHERE THE GROUP LEAVES, carrying the
        // end if the source finished inside it
        const node = lookupNode(nid, inner.w.st.nodes);
        const buffer =
          node !== undefined && node.k === "batchSync" ? node.buffer : [];
        const flushed = foldPath(
          now,
          kappa,
          buffer.length > 0 ? [[buffer[0], buffer.slice(1)] as Val] : [],
          inner.done,
          lo,
          {
            ...inner.w,
            st: installNode(
              nid,
              { k: "batchSync", sync: false, buffer: [] },
              inner.w.st,
            ),
          },
        );
        return { done: inner.done, w: flushed.w };
      }
      case "map": {
        const frame: Frame = { k: "map", fn: exp.fn, env };
        return subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          w,
        );
      }
      case "scan": {
        const nid = freshId("node", w.sched.mint);
        const frame: Frame = { k: "scan", fn: exp.fn, env, nid, ty: exp.ty };
        return subscribeE(
          exp.src,
          env,
          { k: "step", frame, rest: kappa },
          lo,
          now,
          {
            ...w,
            sched: bump("node", w.sched),
            st: installNode(
              nid,
              { k: "cell", ty: exp.ty, val: evalWith(exp.init, env) },
              w.st,
            ),
          },
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
          w,
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
          w,
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
          w,
        );
      case "mu":
        return subscribeE(unfoldMu(exp.body), env, kappa, lo, now, w);
      case "defer": {
        const nid = freshId("node", w.sched.mint);
        const src = freshId("source", w.sched.mint);
        const ord = freshId("ordinal", w.sched.mint);
        const rid = freshId("reg", w.sched.mint);
        const elemTy: Ty = { type: "obs", elem: exp.ty };
        return {
          done: false,
          w: {
            out: w.out,
            sched: {
              ...bump(
                "reg",
                bump("node", bump("source", bump("ordinal", w.sched))),
              ),
              live: [
                {
                  source: src,
                  ordinal: ord,
                  elemTy,
                  pending: [{ tick: now + 1, val: { exp: exp.body, env } }],
                },
                ...w.sched.live,
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
                w.st,
              ),
            ),
          },
        };
      }
      case "mint": {
        const src = freshId("source", w.sched.mint);
        return subscribeE(exp.body, [src, ...env], kappa, lo, now, {
          ...w,
          sched: bump("source", w.sched),
        });
      }
      case "varE":
        throw new Error(
          "varE in a closed expression — generator/decoder invariant violated",
        );
    }
  };

  // has the operator emitted its own end?  `thruWrap` is what emits one,
  // and this is the reading it makes -- taken after the fact, because a
  // lane can be drained and refilled while the outer's end is in flight.
  const allDone = (op: AllOp, nid: NodeId, st: EvalSt): boolean => {
    const node = lookupNode(nid, st.nodes);
    if (node === undefined) return false;
    if (op === "mergeAll" && node.k === "mergeAll")
      return node.outerDone && node.active === 0 && node.queued.length === 0;
    if (op === "switch" && node.k === "switch")
      return node.outerDone && node.current === null;
    if (op === "exhaust" && node.k === "exhaust")
      return node.outerDone && !node.innerActive;
    return false;
  };

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
    w: W,
  ): Subbed => {
    const nid = freshId("node", w.sched.mint);
    const frame: Frame = { k: "thruOuter", op, nid, elemTy };
    const inner = subscribeE(
      src,
      env,
      { k: "step", frame, rest: kappa },
      lo,
      now,
      {
        ...w,
        sched: bump("node", w.sched),
        st: installNode(nid, ns, w.st),
      },
    );
    return { done: allDone(op, nid, inner.w.st), w: inner.w };
  };

  // `subscribeInner⇓`
  const subscribeInner = (
    op: AllOp,
    allNid: NodeId,
    elemTy: Ty,
    kappa: Path,
    lo: number,
    now: Tick,
    o: Val,
    w: W,
  ): { inst: NodeId; done: boolean; w: W } => {
    const inst = freshId("node", w.sched.mint);
    const obs = o as ObsVal;
    const sub = subscribeE(
      obs.exp,
      obs.env,
      {
        k: "step",
        frame: { k: "fromInner", op, allNode: allNid, inst, elemTy },
        rest: kappa,
      },
      lo,
      now,
      { ...w, sched: bump("node", w.sched) },
    );
    return { inst, done: sub.done, w: sub.w };
  };

  // `thruConsume⇓`
  const thruConsume = (
    op: AllOp,
    nid: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    o: Val,
    u: Ty,
    w: W,
  ): W => {
    const node = lookupNode(nid, w.st.nodes);
    if (node === undefined || !consumeUsable(op, u, node)) return w;
    if (op === "mergeAll" && node.k === "mergeAll") {
      if (!hasRoom(node.limit, node.active))
        return {
          ...w,
          st: installNode(nid, { ...node, queued: [...node.queued, o] }, w.st),
        };
      const sub = subscribeInner(op, nid, u, kappa, lo, now, o, w);
      return {
        ...sub.w,
        st: { ...sub.w.st, nodes: mergeAllBump(nid, sub.done, sub.w.st.nodes) },
      };
    }
    if (op === "switch" && node.k === "switch") {
      const killed = switchKill(n, node.current, w.sched, w.st);
      const sub = subscribeInner(op, nid, u, kappa, lo, now, o, {
        ...w,
        sched: killed.sched,
        st: killed.st,
      });
      return {
        ...sub.w,
        st: installNode(
          nid,
          {
            k: "switch",
            current: sub.done ? null : sub.inst,
            outerDone: node.outerDone,
          },
          sub.w.st,
        ),
      };
    }
    if (op === "exhaust" && node.k === "exhaust") {
      const sub = subscribeInner(op, nid, u, kappa, lo, now, o, w);
      return {
        ...sub.w,
        st: installNode(
          nid,
          { k: "exhaust", innerActive: !sub.done, outerDone: node.outerDone },
          sub.w.st,
        ),
      };
    }
    return w;
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
    w: W,
  ): W =>
    os.reduce((acc, o) => thruConsume(op, nid, kappa, lo, now, o, u, acc), w);

  // `mergeAllDrain⇓`.  The shortened queue is written BEFORE the
  // subscribe, not after the whole drain: rxjs takes the item out of the
  // buffer before it subscribes it.
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
    w: W,
  ): { active: number; queued: Val[]; w: W } => {
    if (queued.length === 0) return { active, queued: [], w };
    if (!hasRoom(limit, active)) return { active, queued, w };
    const rest = queued.slice(1);
    const sub = subscribeInner(
      "mergeAll",
      allNid,
      ty,
      kappa,
      lo,
      now,
      queued[0],
      {
        ...w,
        st: installNode(
          allNid,
          { k: "mergeAll", ty, limit, active, queued: rest, outerDone },
          w.st,
        ),
      },
    );
    return mergeAllDrain(
      allNid,
      kappa,
      lo,
      now,
      ty,
      limit,
      sub.done ? active : active + 1,
      outerDone,
      rest,
      sub.w,
    );
  };

  // `innerFinish⇓`
  const innerFinish = (
    op: AllOp,
    allNid: NodeId,
    inst: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    s: Ty,
    w: W,
  ): { fin: boolean; w: W } => {
    const node = lookupNode(allNid, w.st.nodes);
    if (node === undefined || !finishUsable(op, s, inst, node))
      return { fin: false, w };
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
        w,
      );
      return {
        fin:
          node.outerDone && drained.active === 0 && drained.queued.length === 0,
        w: {
          ...drained.w,
          st: installNode(
            allNid,
            { ...node, active: drained.active, queued: drained.queued },
            drained.w.st,
          ),
        },
      };
    }
    if (node.k === "switch")
      return {
        fin: node.outerDone,
        w: { ...w, st: installNode(allNid, { ...node, current: null }, w.st) },
      };
    if (node.k === "exhaust")
      return {
        fin: node.outerDone,
        w: {
          ...w,
          st: installNode(allNid, { ...node, innerActive: false }, w.st),
        },
      };
    return { fin: false, w };
  };

  // `innerReact⇓`: a completion out of an inner is absorbed while
  // anything under that instance is still live.
  const innerReact = (
    op: AllOp,
    allNid: NodeId,
    inst: NodeId,
    kappa: Path,
    lo: number,
    now: Tick,
    s: Ty,
    w: W,
  ): { fin: boolean; w: W } =>
    w.st.registry.some((row) => aliveThrough(inst, w.st, row))
      ? { fin: false, w }
      : innerFinish(op, allNid, inst, kappa, lo, now, s, w);

  // `sharedConnect⇓`.  THE CONNECT BURST IS GONE, and with it the
  // bookkeeping it needed: the def's values and its end now travel the
  // `shareSink` like any other emission, so `dispatchShare` latches the
  // completion and drops the rows, and there is nothing left for this
  // clause to do afterwards.
  const sharedConnect = (
    i: number,
    def: Closed,
    kappa: Path,
    now: Tick,
    w: W,
  ): Subbed => {
    const rid = freshId("reg", w.sched.mint);
    return subscribeE(def, [], { k: "shareSink", i }, i, now, {
      ...w,
      sched: bump("reg", w.sched),
      st: register(rid, { k: "slot", i }, ctx[i], kappa, {
        ...w.st,
        connectedShares: [i, ...w.st.connectedShares],
      }),
    });
  };

  // `subscribeSharedSlot⇓`
  const subscribeSharedSlot = (
    i: number,
    def: Closed,
    kappa: Path,
    now: Tick,
    w: W,
  ): Subbed => {
    // a completed Subject re-delivers completion to late subscribers
    if (w.st.completedSources.includes(i)) return endNow(now, kappa, i + 1, w);
    if (w.st.connectedShares.includes(i)) {
      const rid = freshId("reg", w.sched.mint);
      return {
        done: false,
        w: {
          ...w,
          sched: bump("reg", w.sched),
          st: register(rid, { k: "slot", i }, ctx[i], kappa, w.st),
        },
      };
    }
    return sharedConnect(i, def, kappa, now, w);
  };

  // `dispatchShare⇓`.  THE REGISTRY IS READ HERE, AND THE CARRIER IS WHY
  // THAT IS NOW ENOUGH.  The snapshot is per CALL, and a call now carries
  // one value, so a subscription made in reaction to a value is present
  // for the next one.  Under a burst this same line saw the registry as
  // it stood before any of the emission had been delivered.
  const dispatchShare = (
    now: Tick,
    i: number,
    vals: Val[],
    fin: boolean,
    w: W,
  ): Pushed => {
    const latched = shareLatch(i, fin, w.st);
    const gone = shareAdmit(i, ctx, latched.registry).reduce<W>(
      (acc, row) =>
        acc.st.cancelled.includes(row.rid)
          ? acc
          : pushAll(now, row.path, row.lo, vals, fin, {
              ...acc,
              st: { ...acc.st, delivered: [row.rid, ...acc.st.delivered] },
            }).w,
      { ...w, st: latched },
    );
    const finished = shareFinish(n, i, fin, {
      stream: gone.out,
      sched: gone.sched,
      st: gone.st,
    });
    return {
      alive: true,
      w: { out: finished.stream, sched: finished.sched, st: finished.st },
    };
  };

  // `cascade⇓`: one arrival, every live chain of its source, in
  // subscription order.
  const cascade = (a: Arrival, w: W): W => {
    const latched = cascadeLatch(a, w.st);
    const gone = chainsOf(a, latched).reduce<W>(
      (acc, chain) =>
        acc.st.cancelled.includes(chain.rid)
          ? acc
          : pushAll(a.tick, chain.path, chain.lo, [a.payload], a.isLast, {
              ...acc,
              st: { ...acc.st, delivered: [chain.rid, ...acc.st.delivered] },
            }).w,
      { ...w, st: latched },
    );
    return { out: gone.out, ...cascadeFinish(n, a, gone.sched, gone.st) };
  };

  // `drain⇓`
  const drain = (fuel: number, w: W): W => {
    if (fuel === 0) return w;
    const next = schedNext(w.sched);
    if (next === null) return w;
    return drain(fuel - 1, cascade(next.arrival, { ...w, sched: next.sched }));
  };

  // `evaluate⇓`
  const evaluate = (fuel: number, e: Closed, slots: Slots): Stream => {
    const first = subscribeE(e, [], { k: "root" }, n, 0, {
      out: [],
      sched: schedInit(ctx, slots),
      st: {
        registry: [],
        nodes: [],
        connectedShares: [],
        completedSources: [],
        delivered: [],
        cancelled: [],
        dying: [],
      },
    });
    return drain(fuel, first.w).out;
  };

  return { evaluate };
};

export const evaluatePush = (testCase: TestCase): Val[] => {
  const stream = machine(testCase.ctx).evaluate(
    testCase.fuel,
    testCase.exp,
    testCase.slots,
  );
  return stream.flatMap((b) =>
    b.flatMap((e) => (e.k === "value" ? [e.val] : [])),
  );
};
