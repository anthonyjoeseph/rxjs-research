import { Closed, Exp, Ty, Val, ObsVal, evalWith, unfoldMu } from "./exp.js";
import type { Slots, TestCase } from "./prop-test.js";
import {
  AllOp,
  Arrival,
  aliveThrough,
  EvalSt,
  Frame,
  NodeId,
  NodeState,
  Out,
  Path,
  Sched,
  Stream,
  StepOut,
  Tick,
  batchDispatch,
  bump,
  burstCompleted,
  cascadeFinish,
  cascadeLatch,
  chainsOf,
  completeP,
  consumeUsable,
  dropSource,
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
  spentBurst,
  splitBurst,
  splitEvents,
  stInit,
  switchKill,
  takeDispatch,
  thruWrap,
  valueP,
  oneShotBurst,
} from "./ref-machine.js";

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
          installNode(nid, { k: "batchSync", sync: true, buffer: [] }, st),
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
          st: installNode(
            nid,
            { k: "batchSync", sync: false, buffer: [] },
            out.st,
          ),
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
