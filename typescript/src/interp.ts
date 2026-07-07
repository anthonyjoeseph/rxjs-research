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

/** interpret a deep-embedded program over live slot streams (slot i = the
 * i-th entry; letShare extends at index 0, De Bruijn style, exactly like
 * the model's extendEnv). The joins go through the PRIMITIVE stream-of-
 * streams forms, mirroring the Agda ⟦_⟧S. */
const interpretS = (
  s: ExpS,
  slots: Instantaneous<number>[],
): Instantaneous<Instantaneous<number>> =>
  s.k === "ofS"
    ? of(s.es.map((x) => interpret(x, slots)))
    : map((v: number) => interpret(applyTemplate(s.tmpl, v), slots))(
        interpret(s.e, slots),
      );

export const interpret = (
  e: Exp,
  slots: Instantaneous<number>[],
): Instantaneous<number> => {
  switch (e.k) {
    case "empty":
      return empty();
    case "of":
      return of(e.vs);
    case "shareRef": {
      const s = slots[e.slot];
      if (s === undefined) throw new Error(`unbound slot ${e.slot}`);
      return s;
    }
    case "letShare": {
      const shared = share(interpret(e.src, slots));
      return interpret(e.body, [shared, ...slots]);
    }
    case "map":
      return map(applyFn(e.f))(interpret(e.e, slots));
    case "take":
      return take(e.n)(interpret(e.e, slots));
    case "scan":
      return scan(scanStep(e.f), 0)(interpret(e.e, slots));
    case "mergeAll":
      return mergeAll(interpretS(e.s, slots));
    case "concatAll":
      return concatAll(interpretS(e.s, slots));
    case "switchAll":
      return switchAll(interpretS(e.s, slots));
    case "exhaustAll":
      return exhaustAll(interpretS(e.s, slots));
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
    ),
  ).subscribe((batch) => out.push(batch));
  for (const ev of d) subjects[ev.slot].next(ev.value);
  for (const s of subjects) s.end();
  sub.unsubscribe();
  return out;
};
