import * as r from "rxjs";
import {
  Instantaneous,
  InstEmit,
  InstAsync,
  async,
  init,
  val,
  values,
  InstInit,
  InstClose,
} from "./types";

type ProvenanceState<A> = {
  awaitingValueCount: number | undefined;
  totalNum: number;
  batch: A[];
};

const deleteKey = <K extends string | number | symbol, A>(
  record: Record<K, A>,
  key: K,
): Record<K, A> => {
  const { [key]: _, ...rest } = record;
  return rest as Record<K, A>;
};

const updateMemory = <A>(
  memory: Record<symbol, ProvenanceState<A>>,
  provenance: symbol,
  {
    awaitingValueCount,
    totalNum,
    batchAppend,
  }: {
    awaitingValueCount?: "--";
    totalNum?: "++" | "--";
    batchAppend?: A[];
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
        : batchAppend !== undefined
          ? [...currentBatch, ...batchAppend]
          : currentBatch,
    },
  };
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
    children: [...otherChildren, ...consolidatedVal],
  });
};

const batchAsync = <A>(
  emit: InstAsync<A>,
  memory: Record<symbol, ProvenanceState<A>>,
): InstEmit<A[]> | null => {
  if (emit.child?.type === "close") {
    return emit as InstEmit<A[]>;
  }
  if (emit.child?.type === "async") {
    // a wrapper level: this emission only routes a nested emission through,
    // so batching decisions belong to the nested provenance, not this one
    return async({
      provenance: emit.provenance,
      child: batchOrGroup(emit.child, memory),
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
  if (
    (unitEntry !== undefined &&
      unitAwaiting === undefined &&
      unitEntry.totalNum > 1) ||
    (unitAwaiting !== undefined && unitAwaiting > 1)
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
        child: groupInitSiblings(emit.child, memory),
      });
    }
    return async({ provenance: emit.provenance, child: val(unitVals) });
  }
  const fullBatch = [...unitBatch, ...unitVals];
  if (fullBatch.length === 0) {
    return null;
  }
  return async({ provenance: emit.provenance, child: val(fullBatch) });
};

const batchOrGroup = <A>(
  emit: InstEmit<A>,
  memory: Record<symbol, ProvenanceState<A>>,
): InstEmit<A[]> | null => {
  return emit.type === "init"
    ? groupInitSiblings(emit, memory)
    : batchAsync(emit, memory);
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
  parentProvenance: symbol,
  unitProvenance: symbol,
): Record<symbol, ProvenanceState<A>> => {
  if (emit.type === "init") {
    const base =
      emit.provenance === parentProvenance || emit.provenance === unitProvenance
        ? memory
        : updateMemory(memory, emit.provenance, { totalNum: "++" });
    return emit.children.reduce((acc, child) => {
      if (child.type === "value") {
        return acc;
      }
      if (child.type === "close") {
        return updateMemory(acc, emit.provenance, { totalNum: "--" });
      }
      return registerSubtree(child, acc, emit.provenance, unitProvenance);
    }, base);
  }
  if (emit.child == null || emit.child.type === "value") {
    return memory;
  }
  if (emit.child.type === "close") {
    return updateMemory(memory, emit.provenance, { totalNum: "--" });
  }
  return registerSubtree(emit.child, memory, emit.provenance, unitProvenance);
};

const updateMemoryFromEmit = <A>(
  emit: InstEmit<A>,
  oldMemory: Record<symbol, ProvenanceState<A>>,
  parentProvenance?: symbol,
): Record<symbol, ProvenanceState<A>> => {
  if (emit.type === "init") {
    // an init nested directly inside an init of the same provenance is a
    // self-wrap artifact of flipInside, not a second subscription
    const newMemory =
      emit.provenance === parentProvenance
        ? oldMemory
        : updateMemory(oldMemory, emit.provenance, {
            totalNum: "++",
          });
    const withChildrensState = emit.children.reduce((acc, child) => {
      if (child.type === "close") {
        return updateMemory(acc, emit.provenance, { totalNum: "--" });
      }
      if (child.type === "value") {
        return updateMemory(acc, emit.provenance, {
          awaitingValueCount: "--",
          batchAppend: [child.value],
        });
      }
      return updateMemoryFromEmit(child, acc, emit.provenance);
    }, newMemory);

    return withChildrensState;
  }

  if (emit.child?.type === "close") {
    return updateMemory(oldMemory, emit.provenance, { totalNum: "--" });
  }
  if (emit.child?.type === "value") {
    return updateMemory(oldMemory, emit.provenance, {
      awaitingValueCount: "--",
      batchAppend: [emit.child.value],
    });
  }
  if (emit.child == null) {
    return updateMemory(oldMemory, emit.provenance, {
      awaitingValueCount: "--",
    });
  }
  if (emit.child.type === "init") {
    // a unit init: one delivery of this instant through a join branch. It
    // does NOT register a new subscription of its own provenance — only its
    // subtree (the freshly subscribed inners) registers. Its values (however
    // deeply nested) join the provenance's batch window.
    const unit = emit.child;
    const withSubtree = unit.children.reduce(
      (acc, child) =>
        child.type === "value" || child.type === "close"
          ? acc
          : registerSubtree(child, acc, unit.provenance, unit.provenance),
      oldMemory,
    );
    return updateMemory(withSubtree, unit.provenance, {
      awaitingValueCount: "--",
      batchAppend: values(unit),
    });
  }
  return updateMemoryFromEmit(
    emit.child,
    updateMemory(oldMemory, emit.provenance, { awaitingValueCount: "--" }),
  );
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
 *   - a new inner subscription caused by an event of the init's provenance
 *     (e.g. switchMap/mergeMap switching to a new inner), carrying that
 *     instant's sync values
 *   - counts as one delivery of the provenance's instant, like a value;
 *     its (possibly zero) values join the batch window
 *   - example - merge(a, a.pipe(switchMap(of)))
 * - a top-level init:
 *   - a subscription instant: registers its provenances in memory and emits
 *     its value groups directly (never awaited against a window)
 */
