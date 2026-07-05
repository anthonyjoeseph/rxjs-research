import { pipeWith } from "pipe-ts";
import { fromInstantaneous } from "../basic-primitives";
import { batchSimultaneous } from "../batch-simultaneous";
import { Instantaneous } from "../types";

/**
 * Subscribes to `inst.pipe(batchSimultaneous, fromInstantaneous)` and records
 * every batch it emits, so tests can drive subjects/timers and assert
 * synchronously.
 */
export const record = <A>(inst: Instantaneous<A>) => {
  const batches: A[][] = [];
  let completed = false;
  let error: unknown = undefined;
  pipeWith(inst, batchSimultaneous, fromInstantaneous).subscribe({
    next: (batch) => batches.push(batch),
    complete: () => {
      completed = true;
    },
    error: (err) => {
      error = err;
    },
  });
  return {
    batches,
    isCompleted: () => completed,
    getError: () => error,
  };
};
