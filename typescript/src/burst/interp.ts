import {
  BurstSubject,
  concat,
  empty,
  exhaustStatic,
  map,
  merge,
  mergeMap,
  of,
  scan,
  share,
  switchStatic,
  take,
} from "./core";
import { batchSimultaneous } from "./machine";
import { Inst } from "./protocol";
import {
  applyFn,
  applyTemplate,
  DriverEvent,
  Exp,
  scanStep,
} from "./model";

/** interpret a deep-embedded program over live slot streams (slot i = the
 * i-th entry; letShare extends at index 0, De Bruijn style, exactly like
 * the model's extendEnv) */
export const interpret = (e: Exp, slots: Inst<number>[]): Inst<number> => {
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
    case "mergeAll": {
      if (e.s.k === "ofS")
        return merge(...e.s.es.map((x) => interpret(x, slots)));
      const tmpl = e.s.tmpl;
      return mergeMap((v: number) => interpret(applyTemplate(tmpl, v), slots))(
        interpret(e.s.e, slots),
      );
    }
    case "concatAll": {
      if (e.s.k === "ofS")
        return concat(...e.s.es.map((x) => interpret(x, slots)));
      throw new Error("concatAll over mapS: not implemented impl-side yet");
    }
    case "switchAll": {
      if (e.s.k === "ofS")
        return switchStatic(e.s.es.map((x) => interpret(x, slots)));
      throw new Error("switchAll over mapS: not implemented impl-side yet");
    }
    case "exhaustAll": {
      if (e.s.k === "ofS")
        return exhaustStatic(e.s.es.map((x) => interpret(x, slots)));
      throw new Error("exhaustAll over mapS: not implemented impl-side yet");
    }
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
    () => new BurstSubject<number>(),
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
