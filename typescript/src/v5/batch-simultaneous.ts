import * as r from "rxjs";
import {
  Instantaneous,
  InstEmit,
  InstAsync,
  async,
  close,
  init,
  val,
  values,
  InstInit,
  InstClose,
  InstVal,
} from "./types";

type ProvenanceState<A> = {
  awaitingValueCount: number | undefined;
  totalNum: number;
  /** the window's values in DELIVERY order — batches read exactly as the
   * emissions arrived (rxjs delivery order; ratified 2026-07-06, replacing
   * the Phase-B syntactic pre-order sorting) */
  batch: A[];
  /** slots CONSUMED by the current window so far, by the delivering
   * registration's sub — a cut's extra closes only eat slots of
   * registrations that have NOT yet delivered (a co-closed registration
   * that already delivered consumed its own). Sub identity lets multiple
   * live copies of the same source tell their slots apart; an undefined
   * key is a consumption whose registration id is unknown and matches
   * any close (the pre-identity counting rule). */
  delivered: ReadonlyMap<symbol | undefined, number>;
};

const deleteKey = <K extends string | number | symbol, A>(
  record: Record<K, A>,
  key: K,
): Record<K, A> => {
  const { [key]: _, ...rest } = record;
  return rest as Record<K, A>;
};

/** identity of a protocol node: provenance + registration id. Two nodes
 * are the SAME registration when provenances match and neither side's sub
 * contradicts the other (a missing sub matches anything — the structural
 * pre-identity rules). */
type NodeId = { prov: symbol; sub: symbol | undefined };
const sameId = (
  prov: symbol,
  sub: symbol | undefined,
  b: NodeId,
): boolean =>
  prov === b.prov &&
  (sub === undefined || b.sub === undefined || sub === b.sub);

/** mirror of the registration decision shared by registerSubtree,
 * registrationDeltas and unitProvenanceCloseSubs: EMPTY inits are
 * registration leaves; a non-empty init is a routing re-statement (does
 * NOT register) when its identity matches ANY enclosing wrapper on the
 * path from the delivery's routing chain down to it — same provenance
 * AND (where ids are known) the same sub. A registration delivers at
 * most once per identity, so a non-empty init under its own id's wrapper
 * is always a re-statement (e.g. a graft wrapping a deferred flush in
 * the TRIGGER's identity while the unit is anchored at the closing
 * chain's id — seed -1062187723). A same-source init with a DIFFERENT,
 * unenclosed sub is a genuine fresh lifecycle (e.g. take(0)(src)
 * spawned in-frame by a trigger derived from src): it registers, so its
 * close nets zero. */
const registersHere = <A>(
  c: InstInit<A>,
  ancestors: readonly NodeId[],
): boolean =>
  c.children.length === 0 ||
  ancestors.every((a) => !sameId(c.provenance, c.sub, a));

const addDelivered = (
  delivered: ReadonlyMap<symbol | undefined, number>,
  sub: symbol | undefined,
): ReadonlyMap<symbol | undefined, number> => {
  const next = new Map(delivered);
  next.set(sub, (next.get(sub) ?? 0) + 1);
  return next;
};

const updateMemory = <A>(
  memory: Record<symbol, ProvenanceState<A>>,
  provenance: symbol,
  {
    awaitingValueCount,
    totalNum,
    batchAppend,
    deliveredSub,
  }: {
    awaitingValueCount?: "--";
    totalNum?: "++" | "--";
    batchAppend?: A[];
    /** the registration whose slot this consumption spends (recorded
     * only when awaitingValueCount is decremented) */
    deliveredSub?: symbol;
  },
): Record<symbol, ProvenanceState<A>> => {
  const state = memory[provenance];
  if (state === undefined && totalNum === "--") {
    // decrementing a provenance we no longer track is a no-op
    // (e.g. a second 'close' arriving after the entry was deleted)
    return memory;
  }
  const currentCount = state?.awaitingValueCount;
  const currentTotal = state?.totalNum ?? 0;
  const currentBatch = state?.batch ?? [];
  const newTotal =
    totalNum === "++"
      ? currentTotal + 1
      : totalNum === "--"
        ? currentTotal - 1
        : currentTotal;
  if (newTotal === 0) {
    return deleteKey(memory, provenance);
  }
  // a batch window is complete when the value that just arrived was the last
  // one awaited: either the count ran down to 1, or the provenance only has a
  // single live subscriber so every value completes its own window
  const windowComplete =
    awaitingValueCount === "--" &&
    (currentCount === 1 || (currentCount === undefined && newTotal <= 1));
  const newAwaitingValueCount =
    awaitingValueCount === "--"
      ? currentCount === undefined
        ? windowComplete
          ? undefined
          : newTotal - 1
        : currentCount === 1
          ? undefined
          : currentCount - 1
      : currentCount;
  return {
    ...memory,
    [provenance]: {
      awaitingValueCount: newAwaitingValueCount,
      totalNum: newTotal,
      batch: windowComplete
        ? []
        : batchAppend !== undefined && batchAppend.length > 0
          ? [...currentBatch, ...batchAppend]
          : currentBatch,
      delivered: windowComplete
        ? new Map()
        : awaitingValueCount === "--"
          ? addDelivered(
              currentCount === undefined
                ? new Map()
                : (state?.delivered ?? new Map()),
              deliveredSub,
            )
          : (state?.delivered ?? new Map()),
    },
  };
};

/**
 * The instants of a subscription burst (a top-level init): every value is
 * keyed by its ROOT CAUSE — the provenance of the nearest enclosing init
 * reached without crossing an async wrapper. An async-wrapped subtree in a
 * burst is a derived-spawned UNIT: its whole subtree (however nested)
 * inherits the unit's instant. The same provenance reached at different
 * depths is the same instant (a shared cold subscribed twice), so batches
 * group across the whole tree, ordered by first appearance.
 */
const burstBatches = <A>(emit: InstInit<A>): A[][] => {
  const order: symbol[] = [];
  const byKey = new Map<symbol, A[]>();
  const push = (key: symbol, v: A): void => {
    const existing = byKey.get(key);
    if (existing === undefined) {
      byKey.set(key, [v]);
      order.push(key);
    } else {
      existing.push(v);
    }
  };
  const anchorOf = (e: InstAsync<A>): symbol =>
    e.child != null && e.child.type === "async"
      ? anchorOf(e.child)
      : e.provenance;
  const walk = (e: InstEmit<A>): void => {
    if (e.type === "async") {
      // a derived-spawned unit (or a routed close): one instant, all its
      // values keyed by the instant OWNER — the innermost async provenance
      // (outer layers are join routing)
      const anchor = anchorOf(e);
      for (const v of values(e)) {
        push(anchor, v);
      }
      return;
    }
    for (const child of e.children) {
      if (child.type === "value") {
        push(e.provenance, child.value);
      } else if (child.type !== "close") {
        walk(child);
      }
    }
  };
  walk(emit);
  return order
    .map((k) => byKey.get(k)!)
    .filter((batch) => batch.length > 0);
};

/**
 * Registration-only memory bookkeeping for a subscription burst: totalNum
 * ++/-- per init/close, async units register their subtrees (and their
 * unit-level closes decrement), but NO window operations — every value in
 * the burst was already batched by burstBatches, simultaneous by
 * construction, and awaits nothing.
 */
const registerBurst = <A>(
  emit: InstEmit<A>,
  memory: Record<symbol, ProvenanceState<A>>,
  parent?: NodeId,
  routing: readonly NodeId[] = [],
): Record<symbol, ProvenanceState<A>> => {
  if (emit.type === "init") {
    const base =
      parent !== undefined && sameId(emit.provenance, emit.sub, parent)
        ? memory
        : updateMemory(memory, emit.provenance, { totalNum: "++" });
    const selfId = { prov: emit.provenance, sub: emit.sub };
    return emit.children.reduce((acc, child) => {
      if (child.type === "value") {
        return acc;
      }
      if (child.type === "close") {
        return updateMemory(acc, emit.provenance, { totalNum: "--" });
      }
      return registerBurst(child, acc, selfId, [...routing, selfId]);
    }, base);
  }
  if (emit.child == null || emit.child.type === "value") {
    return memory;
  }
  if (emit.child.type === "close") {
    return updateMemory(memory, emit.provenance, { totalNum: "--" });
  }
  if (emit.child.type === "init") {
    // a unit: its anchor doesn't re-register; unit-level closes decrement;
    // nested subtrees (freshly subscribed inners) register
    const unit = emit.child;
    const selfId = { prov: emit.provenance, sub: emit.sub };
    const unitId = { prov: unit.provenance, sub: unit.sub };
    const afterCloses = unit.children.reduce(
      (acc, child) =>
        child.type === "close"
          ? updateMemory(acc, unit.provenance, { totalNum: "--" })
          : acc,
      memory,
    );
    return unit.children.reduce(
      (acc, child) =>
        child.type === "value" || child.type === "close"
          ? acc
          : registerSubtree(child, acc, [...routing, selfId, unitId]),
      afterCloses,
    );
  }
  return registerBurst(emit.child, memory, undefined, [
    ...routing,
    { prov: emit.provenance, sub: emit.sub },
  ]);
};

const groupInitSiblings = <A>(
  emit: InstInit<A>,
  memory: Record<symbol, ProvenanceState<A>>,
): InstEmit<A[]> | null => {
  const allVals = emit.children
    .filter((child) => child.type === "value")
    .map((v) => v.value);
  const consolidatedVal = allVals.length > 0 ? [val(allVals)] : [];
  const otherChildren = emit.children
    .filter((child) => child.type !== "value")
    .flatMap((child): (InstClose | InstEmit<A[]>)[] => {
      if (child.type === "close") return [child];
      const maybeNull = batchOrGroup(child, memory);
      return maybeNull == null ? [] : [maybeNull];
    });
  return init({
    provenance: emit.provenance,
    sub: emit.sub,
    children: [...otherChildren, ...consolidatedVal],
  });
};

/** every close in a unit's tree that ends a PRE-EXISTING registration OF
 * the unit's own provenance — literal children, nested same-provenance
 * init-internal closes (re-wrapped close markers), and bare async closes
 * — each identified by the SUB of the node it closes (the enclosing
 * init/async; undefined when the id is unknown, e.g. `cancelled`
 * annotations). Mirrors what the memory update decrements on that
 * provenance for this emission — EXCEPT closes inside an init that itself
 * REGISTERS within this unit (an off-spine lifecycle like take(0)(src)
 * arriving in a src-triggered flush, per registerSubtree's spine rule):
 * those pair with their own registration and end no outside
 * subscription. */
const unitProvenanceCloseSubs = <A>(
  unit: InstInit<A>,
  routing: readonly NodeId[] = [],
): (symbol | undefined)[] => {
  const prov = unit.provenance;
  const out: (symbol | undefined)[] = [];
  /** registrations of the unit's provenance BORN in this unit — a close
   * matching one of these subs is a self-contained lifecycle (e.g. a
   * graft re-subscribing an already-completed source: registration and
   * close arrive as siblings in one unit) and ends no outside
   * subscription */
  const born: symbol[] = [];
  const walk = (
    children: (InstEmit<A> | InstVal<A> | InstClose)[],
    enclosing: NodeId,
    ancestors: readonly NodeId[],
    enclosingRegistered: boolean,
  ): void => {
    for (const c of children) {
      if (c.type === "close") {
        if (enclosing.prov === prov && !enclosingRegistered) {
          out.push(enclosing.sub);
        }
      } else if (c.type === "value") {
        // no close
      } else if (c.type === "init") {
        // mirror registerSubtree's decision, enclosing-ancestors included
        const registered = registersHere(c, ancestors);
        const cId = { prov: c.provenance, sub: c.sub };
        if (registered && c.provenance === prov && c.sub !== undefined) {
          born.push(c.sub);
        }
        if (c.provenance === prov) {
          for (let i = 0; i < (c.cancelled ?? 0); i++) {
            out.push(undefined);
          }
        }
        walk(c.children, cId, [...ancestors, cId], registered);
      } else if (c.child?.type === "close") {
        if (c.provenance === prov) {
          out.push(c.sub);
        }
      } else if (c.child != null && c.child.type !== "value") {
        const cId = { prov: c.provenance, sub: c.sub };
        walk([c.child], cId, [...ancestors, cId], false);
      }
    }
  };
  const unitId = { prov, sub: unit.sub };
  walk(unit.children, unitId, [...routing, unitId], false);
  for (let i = 0; i < (unit.cancelled ?? 0); i++) {
    out.push(undefined);
  }
  // pair each born registration with its own close (exact sub match only —
  // identity-less closes keep the pre-identity counting semantics)
  for (const s of born) {
    const idx = out.indexOf(s);
    if (idx >= 0) {
      out.splice(idx, 1);
    }
  }
  return out;
};

/** the unit's closes that consume EXTRA window slots: one close pairs
 * with the unit's own delivery (preferring the unit's own sub), and each
 * remaining close is matched against the window's already-spent slots —
 * exact when identities are known (a close of a registration that
 * delivered this window eats nothing; one that never delivered eats a
 * slot), degrading to the pre-identity counting rule through undefined
 * subs (which match anything). Returns the UNMATCHED closes' subs — each
 * consumes one awaited slot. */
const unmatchedExtraCloses = <A>(
  unit: InstInit<A>,
  entry: ProvenanceState<A> | undefined,
  routing: readonly NodeId[] = [],
): (symbol | undefined)[] => {
  const subs = unitProvenanceCloseSubs(unit, routing);
  if (subs.length === 0) {
    return [];
  }
  // the unit's own close pairs with this unit's own delivery
  const ownIdx = subs.indexOf(unit.sub);
  const pairIdx =
    ownIdx >= 0 ? ownIdx : Math.max(subs.indexOf(undefined), 0);
  subs.splice(pairIdx, 1);
  const spent = new Map(entry?.delivered ?? []);
  const consume = (key: symbol | undefined): boolean => {
    const n = spent.get(key) ?? 0;
    if (n > 0) {
      spent.set(key, n - 1);
      return true;
    }
    return false;
  };
  return subs.filter((s) => {
    if (s !== undefined && consume(s)) {
      return false;
    }
    if (consume(undefined)) {
      return false;
    }
    if (s === undefined) {
      // an identity-less close matches any spent slot
      for (const [key, n] of spent) {
        if (n > 0) {
          spent.set(key, n - 1);
          return false;
        }
      }
    }
    return true;
  });
};

const batchAsync = <A>(
  emit: InstAsync<A>,
  memory: Record<symbol, ProvenanceState<A>>,
  routing: readonly NodeId[] = [],
): InstEmit<A[]> | null => {
  if (emit.child?.type === "close") {
    // every subscriber of a provenance delivers something at its close
    // instant — a value-carrying unit or a bare close — so a bare close
    // consumes one awaited delivery slot. If it's the last one, the
    // window flushes WITH the close (otherwise the buffered batch would
    // be stranded when the entry dies)
    const entry = memory[emit.provenance];
    if (
      entry !== undefined &&
      entry.awaitingValueCount === 1 &&
      entry.batch.length > 0
    ) {
      return async({
        provenance: emit.provenance,
        sub: emit.sub,
        child: init<A[]>({
          provenance: emit.provenance,
          sub: emit.sub,
          children: [val(entry.batch), close],
        }),
      });
    }
    return emit as InstEmit<A[]>;
  }
  if (emit.child?.type === "async") {
    // a wrapper level: this emission only routes a nested emission through,
    // so batching decisions belong to the nested provenance, not this one
    return async({
      provenance: emit.provenance,
      sub: emit.sub,
      child: batchAsync(emit.child, memory, [
        ...routing,
        { prov: emit.provenance, sub: emit.sub },
      ]),
    });
  }
  // the unit level: the child is null, a value, or an init caused by this
  // instant (a new inner subscription delivered through e.g. switchMap,
  // carrying its sync values). An async-wrapped init is one unit of its
  // provenance's instant, exactly like a value.
  const unitProvenance =
    emit.child?.type === "init" ? emit.child.provenance : emit.provenance;
  const unitEntry = memory[unitProvenance];
  const unitAwaiting = unitEntry?.awaitingValueCount;
  const unitBatch = unitEntry?.batch ?? [];
  // a unit's closes BEYOND the first (its own subscription's) end OTHER
  // subscriptions that will never deliver — e.g. a take cutting a diamond
  // closes every branch it passed, having swallowed their deliveries.
  // Each extra close consumes an awaited slot (mirror of the bare-close
  // rule), so the window mustn't hold out for them — EXCEPT closes of
  // registrations that ALREADY delivered this window (a take(n) cut whose
  // earlier branch values arrived before the cut): those slots are spent.
  const extraCloses =
    emit.child?.type === "init"
      ? unmatchedExtraCloses(emit.child, unitEntry, [
          ...routing,
          { prov: emit.provenance, sub: emit.sub },
        ]).length
      : 0;
  if (
    (unitEntry !== undefined &&
      unitAwaiting === undefined &&
      unitEntry.totalNum > 1 + extraCloses) ||
    (unitAwaiting !== undefined && unitAwaiting > 1 + extraCloses)
  ) {
    // more units of this instant still to come: buffer
    // (the unit's values are recorded in memory by updateMemoryFromEmit)
    return null;
  }
  const unitVals =
    emit.child == null
      ? []
      : emit.child.type === "value"
        ? [emit.child.value]
        : values(emit.child);
  if (
    emit.child?.type === "init" &&
    unitAwaiting === undefined &&
    (unitEntry === undefined || unitEntry.totalNum <= 1)
  ) {
    // no diamond on this provenance AND no window in flight (a sibling may
    // have closed mid-window, dropping totalNum to 1 while values wait) —
    // the delivery forms ONE batch: all its values inherit this instant
    if (unitVals.length === 0) {
      // a value-less delivery (registration / close bookkeeping): keep the
      // tree so the memory recursion below sees its structure
      return async({
        provenance: emit.provenance,
        sub: emit.sub,
        child: groupInitSiblings(emit.child, memory),
      });
    }
    return async({
      provenance: emit.provenance,
      sub: emit.sub,
      child: val(unitVals),
    });
  }
  const fullBatch = [...unitBatch, ...unitVals];
  if (fullBatch.length === 0) {
    return null;
  }
  return async({
    provenance: emit.provenance,
    sub: emit.sub,
    child: val(fullBatch),
  });
};

const batchOrGroup = <A>(
  emit: InstEmit<A>,
  memory: Record<symbol, ProvenanceState<A>>,
): InstEmit<A[]> | null => {
  if (emit.type === "init") {
    // a subscription burst: one emission, one batch per root cause
    return init({
      provenance: emit.provenance,
      sub: emit.sub,
      children: burstBatches(emit).map((batch) => val(batch)),
    });
  }
  return batchAsync(emit, memory);
};

/**
 * population-only bookkeeping for a unit's subtree: the window accounting
 * for the delivery happened once at the unit level, so nested asyncs here
 * are wrapping (not further deliveries — no count decrements, no value
 * appends), layers tagged with the unit's own provenance are
 * self-references (not new subscriptions), and only genuinely new
 * provenances register / close.
 */
const registerSubtree = <A>(
  emit: InstEmit<A>,
  memory: Record<symbol, ProvenanceState<A>>,
  ancestors: readonly NodeId[],
): Record<symbol, ProvenanceState<A>> => {
  if (emit.type === "init") {
    // EMPTY inits are registration LEAVES (a genuine new subscription,
    // even of the unit's own anchor — a concat advancing back onto the
    // source whose close advanced it); non-empty inits whose identity
    // matches ANY enclosing wrapper are routing re-statements and don't
    // re-register (a registration delivers once — its id enclosing this
    // node means it was already counted). A same-provenance init with a
    // fresh, unenclosed sub is a genuine lifecycle and registers (see
    // registersHere).
    const base = registersHere(emit, ancestors)
      ? updateMemory(memory, emit.provenance, { totalNum: "++" })
      : memory;
    const selfId = { prov: emit.provenance, sub: emit.sub };
    const childAncestors = [...ancestors, selfId];
    return emit.children.reduce((acc, child) => {
      if (child.type === "value") {
        return acc;
      }
      if (child.type === "close") {
        return updateMemory(acc, emit.provenance, { totalNum: "--" });
      }
      return registerSubtree(child, acc, childAncestors);
    }, base);
  }
  if (emit.child == null || emit.child.type === "value") {
    return memory;
  }
  if (emit.child.type === "close") {
    return updateMemory(memory, emit.provenance, { totalNum: "--" });
  }
  return registerSubtree(emit.child, memory, [
    ...ancestors,
    { prov: emit.provenance, sub: emit.sub },
  ]);
};

/**
 * The totalNum deltas an emission causes in the provenance memory — the
 * registration bookkeeping of updateMemoryFromEmit/registerSubtree, as
 * counts. Exported so joins can synthesize protocol closes for
 * provenances stranded when a live inner is UNSUBSCRIBED (switch-away):
 * downstream memory only learns of ended subscriptions through closes,
 * and an unsubscription emits none (precedent: take synthesizes closes).
 */
const walkDeltas = <A>(
  emit: InstEmit<A>,
  bump: (prov: symbol, sub: symbol | undefined, d: number) => void,
  parentProvenance?: symbol,
): void => {
  const subtree = (e: InstEmit<A>, ancestors: readonly NodeId[]): void => {
    if (e.type === "init") {
      // mirror registerSubtree: EMPTY inits are registration leaves and
      // always count; non-empty headers whose identity matches ANY
      // enclosing wrapper are re-statements
      if (registersHere(e, ancestors)) {
        bump(e.provenance, e.sub, 1);
      }
      const selfId = { prov: e.provenance, sub: e.sub };
      const childAncestors = [...ancestors, selfId];
      for (const child of e.children) {
        if (child.type === "close") {
          bump(e.provenance, e.sub, -1);
        } else if (child.type !== "value") {
          subtree(child, childAncestors);
        }
      }
      return;
    }
    if (e.child?.type === "close") {
      bump(e.provenance, e.sub, -1);
    } else if (e.child != null && e.child.type !== "value") {
      subtree(e.child, [...ancestors, { prov: e.provenance, sub: e.sub }]);
    }
  };
  // mirror of registerBurst for the init-headed walk
  const burst = (
    e: InstEmit<A>,
    parent?: NodeId,
    routing: readonly NodeId[] = [],
  ): void => {
    if (e.type === "init") {
      if (parent === undefined || !sameId(e.provenance, e.sub, parent)) {
        bump(e.provenance, e.sub, 1);
      }
      const selfId = { prov: e.provenance, sub: e.sub };
      for (const child of e.children) {
        if (child.type === "close") {
          bump(e.provenance, e.sub, -1);
        } else if (child.type !== "value") {
          burst(child, selfId, [...routing, selfId]);
        }
      }
      return;
    }
    if (e.child?.type === "close") {
      bump(e.provenance, e.sub, -1);
      return;
    }
    if (e.child == null || e.child.type === "value") {
      return;
    }
    if (e.child.type === "init") {
      // a unit init: only its subtree registers (mirror of
      // registerSubtree), and unit-level closes (a close traveling with a
      // value) decrement
      const unit = e.child;
      const selfId = { prov: e.provenance, sub: e.sub };
      const unitId = { prov: unit.provenance, sub: unit.sub };
      for (const child of unit.children) {
        if (child.type === "close") {
          bump(unit.provenance, unit.sub, -1);
        } else if (child.type !== "value") {
          subtree(child, [...routing, selfId, unitId]);
        }
      }
      return;
    }
    // routing wrapper
    burst(e.child, undefined, [
      ...routing,
      { prov: e.provenance, sub: e.sub },
    ]);
  };
  burst(
    emit,
    parentProvenance !== undefined
      ? { prov: parentProvenance, sub: undefined }
      : undefined,
  );
};

export const registrationDeltas = <A>(
  emit: InstEmit<A>,
  deltas: Map<symbol, number> = new Map(),
  parentProvenance?: symbol,
): Map<symbol, number> => {
  walkDeltas(
    emit,
    (prov, _sub, d) => deltas.set(prov, (deltas.get(prov) ?? 0) + d),
    parentProvenance,
  );
  return deltas;
};

/** per-registration balance: provenance → sub → live count. Registrations
 * whose ids are unknown accumulate under the undefined key. */
export type RegBalance = Map<symbol, Map<symbol | undefined, number>>;

export const registrationDeltasBySub = <A>(
  emit: InstEmit<A>,
  balance: RegBalance,
  parentProvenance?: symbol,
): RegBalance => {
  walkDeltas(
    emit,
    (prov, sub, d) => {
      const bySub =
        balance.get(prov) ?? new Map<symbol | undefined, number>();
      const next = (bySub.get(sub) ?? 0) + d;
      // a close whose id is unknown may end a KNOWN registration: soak
      // negative unknown balance into a positive identified one
      if (sub === undefined && next < 0) {
        for (const [k, n] of bySub) {
          if (k !== undefined && n > 0) {
            bySub.set(k, n - 1);
            balance.set(prov, bySub);
            return;
          }
        }
      }
      bySub.set(sub, next);
      balance.set(prov, bySub);
    },
    parentProvenance,
  );
  return balance;
};

const updateMemoryFromEmit = <A>(
  emit: InstEmit<A>,
  oldMemory: Record<symbol, ProvenanceState<A>>,
  parentProvenance?: symbol,
  routing: readonly NodeId[] = [],
): Record<symbol, ProvenanceState<A>> => {
  if (emit.type === "init") {
    // a subscription burst: registration only — its values were batched by
    // burstBatches and await nothing
    return registerBurst(
      emit,
      oldMemory,
      parentProvenance !== undefined
        ? { prov: parentProvenance, sub: undefined }
        : undefined,
    );
  }

  if (emit.child?.type === "close") {
    // a bare close consumes one awaited delivery slot of an in-flight
    // window (see batchAsync) before its registration ends
    const entry = oldMemory[emit.provenance];
    const afterWindow =
      entry?.awaitingValueCount !== undefined
        ? updateMemory(oldMemory, emit.provenance, {
            awaitingValueCount: "--",
            deliveredSub: emit.sub,
          })
        : oldMemory;
    return updateMemory(afterWindow, emit.provenance, { totalNum: "--" });
  }
  if (emit.child?.type === "value") {
    return updateMemory(oldMemory, emit.provenance, {
      awaitingValueCount: "--",
      batchAppend: [emit.child.value],
      deliveredSub: emit.sub,
    });
  }
  if (emit.child == null) {
    return updateMemory(oldMemory, emit.provenance, {
      awaitingValueCount: "--",
      deliveredSub: emit.sub,
    });
  }
  if (emit.child.type === "init") {
    // a unit init: one delivery of this instant through a join branch. It
    // does NOT register a new subscription of its own provenance — only its
    // subtree (the freshly subscribed inners) registers. Its values (however
    // deeply nested) join the provenance's batch window FIRST; then its
    // unit-level closes (a close traveling with the final value, e.g. take)
    // decrement — the value must land in the window before it shrinks.
    const unit = emit.child;
    // the extra closes are computed against the PRE-delivery window state
    // (mirrors batchAsync, which decided before this update ran)
    const extras = unmatchedExtraCloses(unit, oldMemory[unit.provenance], [
      ...routing,
      { prov: emit.provenance, sub: emit.sub },
    ]);
    const afterValues = updateMemory(oldMemory, unit.provenance, {
      awaitingValueCount: "--",
      batchAppend: values(unit),
      deliveredSub: unit.sub,
    });
    // the first close of the unit's provenance pairs with this unit's own
    // delivery (already counted above); each FURTHER one — literal or
    // re-wrapped deeper in the tree — ends another subscription that will
    // never deliver, so consume its awaited slot (see extraCloses in
    // batchAsync) — EXCEPT ones whose registration already delivered this
    // window (its slot was spent by its own delivery; sub identity makes
    // the match exact). totalNum decrements: literal closes here, nested
    // ones via registerSubtree.
    let afterSlots = afterValues;
    for (const closedSub of extras) {
      if (afterSlots[unit.provenance]?.awaitingValueCount === undefined) {
        break;
      }
      afterSlots = updateMemory(afterSlots, unit.provenance, {
        awaitingValueCount: "--",
        deliveredSub: closedSub,
      });
    }
    const afterCloses = unit.children.reduce(
      (acc, child) =>
        child.type === "close"
          ? updateMemory(acc, unit.provenance, { totalNum: "--" })
          : acc,
      afterSlots,
    );
    const unitId = { prov: unit.provenance, sub: unit.sub };
    const selfId = { prov: emit.provenance, sub: emit.sub };
    return unit.children.reduce(
      (acc, child) =>
        child.type === "value" || child.type === "close"
          ? acc
          : registerSubtree(child, acc, [...routing, selfId, unitId]),
      afterCloses,
    );
  }
  // an async child: this level is pure routing. It must NOT touch window
  // state — a provenance can be both a real source window and a routing
  // wrapper (a join anchored on it), and decrementing here opens phantom
  // windows that strand later values. All accounting happens at the unit
  // level.
  return updateMemoryFromEmit(emit.child, oldMemory, undefined, [
    ...routing,
    { prov: emit.provenance, sub: emit.sub },
  ]);
};

export const batchSimultaneous = <A>(
  inst: Instantaneous<A>,
): Instantaneous<A[]> => {
  return inst.pipe(
    r.scan(
      (
        { memory },
        currentEmit,
      ): {
        emit: InstEmit<A[]> | null;
        memory: Record<symbol, ProvenanceState<A>>;
      } => {
        const emit = batchOrGroup(currentEmit, memory);
        const newMemory = updateMemoryFromEmit(currentEmit, memory);
        return {
          emit,
          memory: newMemory,
        };
      },
      { emit: null, memory: {} } as {
        emit: InstEmit<A[]> | null;
        memory: Record<symbol, ProvenanceState<A>>;
      },
    ),
    r.mergeMap(({ emit }) => {
      return emit == null ? r.EMPTY : r.of(emit);
    }),
  );
};

/**
 * key:
 *
 * - async value with no provenance in memory:
 *   - means that its parent observable has closed
 *   - can safely ignore
 *   - example - the 'of' in 'of(a, a).pipe(mergeAll())'
 * - an async-wrapped init ("unit init"):
 *   - one delivery of an instant through a join branch: a new inner
 *     subscription caused by an event (switchMap/mergeMap), a take's
 *     final value traveling with its close, or a concat advancement
 *     grafted onto the closing emission
 *   - counts against the provenance's window like a value; its (possibly
 *     zero) values — however deeply nested — join the batch window
 *   - example - merge(a, a.pipe(switchMap(of)))
 * - a bare async close:
 *   - consumes one awaited delivery slot (every subscriber delivers
 *     something at a close instant); flushes the window if it was last
 * - a top-level init:
 *   - THE subscription burst: batches per root cause across the whole
 *     tree (burstBatches — async-wrapped subtrees inherit their unit's
 *     anchor; same provenance at any depth is the same instant), and
 *     registers provenances only (registerBurst — burst values await
 *     nothing)
 */
