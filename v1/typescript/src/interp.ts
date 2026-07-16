import { batchSimultaneous } from "./batch-simultaneous";
import {
  concatAll,
  empty,
  exhaustAll,
  InstantSubject,
  map,
  mergeAll,
  of,
  scan,
  share,
  switchAll,
  take,
} from "./primitives";
import { Instantaneous } from "./types";
import {
  applyFn,
  applyTemplate,
  DriverEvent,
  Exp,
  ExpS,
  scanStep,
} from "./model";

/** interpret a program over live streams, mirroring the Agda compiler:
 * `subjects` are the driver subjects (srcE : Fin n), `shares` is the de Bruijn
 * environment of letShare-bound shares (shareE : ℕ), extended at index 0. The
 * joins go through the PRIMITIVE stream-of-streams forms, mirroring ⟦_⟧S. */
const interpretS = (
  s: ExpS,
  subjects: Instantaneous<number>[],
  shares: Instantaneous<number>[],
): Instantaneous<Instantaneous<number>> =>
  s.k === "ofS"
    ? of(s.es.map((x) => interpret(x, subjects, shares)))
    : map((v: number) => interpret(applyTemplate(s.tmpl, v), subjects, shares))(
        interpret(s.e, subjects, shares),
      );

export const interpret = (
  e: Exp,
  subjects: Instantaneous<number>[],
  shares: Instantaneous<number>[],
): Instantaneous<number> => {
  switch (e.k) {
    case "empty":
      return empty();
    case "of":
      return of(e.vs);
    case "src": {
      const s = subjects[e.slot];
      if (s === undefined) throw new Error(`unbound subject ${e.slot}`);
      return s;
    }
    case "share": {
      const s = shares[e.slot];
      if (s === undefined) throw new Error(`unbound share ${e.slot}`);
      return s;
    }
    case "letShare": {
      const shared = share(interpret(e.src, subjects, shares));
      return interpret(e.body, subjects, [shared, ...shares]);
    }
    case "map":
      return map(applyFn(e.f))(interpret(e.e, subjects, shares));
    case "take":
      return take(e.n)(interpret(e.e, subjects, shares));
    case "scan":
      return scan(scanStep(e.f), 0)(interpret(e.e, subjects, shares));
    case "mergeAll":
      return mergeAll(interpretS(e.s, subjects, shares));
    case "concatAll":
      return concatAll(interpretS(e.s, subjects, shares));
    case "switchAll":
      return switchAll(interpretS(e.s, subjects, shares));
    case "exhaustAll":
      return exhaustAll(interpretS(e.s, subjects, shares));
  }
};

/** run a program through the real machinery: subscribe, collect batches,
 * fire the driver (one .next() per event), then complete the subjects in
 * slot order (each completion is its own instant) */
export const implBatches = (
  e: Exp,
  numSlots: number,
  d: DriverEvent[],
): number[][] => {
  const subjects = Array.from(
    { length: numSlots },
    () => new InstantSubject<number>(),
  );
  const out: number[][] = [];
  const sub = batchSimultaneous(
    interpret(
      e,
      subjects.map((s) => s.inst),
      [],
    ),
  ).subscribe((batch) => out.push(batch));
  for (const ev of d) subjects[ev.slot].next(ev.value);
  for (const s of subjects) s.end();
  sub.unsubscribe();
  return out;
};
