// THE ELABORATION: `SExp` -> `Exp`, mirroring Agda's `Rx.Elaborate`.
//
// This is the seam the whole Agda development turns on. `elaborate` is
// `mint . toPlain`, and every envelope a running program ever sees is
// put there by a clause of THIS function rather than by anything the
// author wrote. The author's palette (s-exp.ts) has no `mint` and no
// `batchSync`, so it is not that an author is discouraged from forging
// an envelope -- there is no term for it.
//
// WHAT IS WRITTEN HERE AND WHAT IS POSTULATED. Only `inputP` is
// transcribed, because it is the clause that matters: it is where a
// bare slot becomes a protocol-carrying source, and it is the exact
// term the Agda proof's `subs-shared` hole was found underneath. Every
// other wrapper -- `ofP`, `mapP`, `mergeAllP` and the rest -- is
// DECLARED and not defined, which is TypeScript's nearest thing to an
// Agda postulate: the recursion below is complete and typechecks, and
// the leaves are visibly unfilled.

import type { Observable } from "rxjs";
import type { Exp, Fn, Tm, Ty, Val } from "../exp.js";
import type { SExp, STm } from "./s-exp.js";

// ---------------------------------------------------------------
// The type translation (Agda: Rx.SExp.plainT / emitT).
// ---------------------------------------------------------------

const unitT: Ty = { type: "unit" };
const uniqT: Ty = { type: "uniq" };
const prod = (fst: Ty, snd: Ty): Ty => ({ type: "prod", fst, snd });
const sum = (left: Ty, right: Ty): Ty => ({ type: "sum", left, right });
const list = (elem: Ty): Ty => ({ type: "list", elem });
const obs = (elem: Ty): Ty => ({ type: "obs", elem });

// Agda: closeReasonT / emitKindT / instEventT / instEmitT.
const closeReasonT: Ty = sum(unitT, unitT);
const emitKindT: Ty = sum(unitT, sum(unitT, unitT));
const instEventT = (u: Ty, a: Ty): Ty =>
  sum(u, sum(a, sum(prod(u, closeReasonT), sum(u, unitT))));
const instEmitT = (u: Ty, a: Ty): Ty =>
  prod(list(instEventT(u, a)), prod(u, prod(u, emitKindT)));

// AN AUTHOR'S TYPE AND THE TYPE ITS ELABORATION STANDS AT DIFFER IN
// EXACTLY ONE PLACE, AND IT IS NOT THE OUTERMOST ONE. The wrapper at
// the top is applied by `elaborate`'s own signature; what this walk is
// for is the wrappers UNDERNEATH, since a nested observable is a value
// the author wrote at `obs t` and the elaborated program carries at
// `obs (machineEmitT (plainT t))`.
export const plainT = (t: Ty): Ty => {
  switch (t.type) {
    case "unit":
    case "bool":
    case "nat":
    case "uniq":
      return t;
    case "prod":
      return prod(plainT(t.fst), plainT(t.snd));
    case "sum":
      return sum(plainT(t.left), plainT(t.right));
    case "list":
      return list(plainT(t.elem));
    case "obs":
      return obs(machineEmitT(plainT(t.elem)));
  }
};

export const machineEmitT = (a: Ty): Ty => instEmitT(uniqT, a);
export const emitT = (t: Ty): Ty => machineEmitT(plainT(t));

// ---------------------------------------------------------------
// Envelope constructors (Agda: Rx.Envelope / Rx.Elaborate).
// ---------------------------------------------------------------

const varT = (ty: Ty, index: number): Tm => ({ type: "varT", ty, index });
const unitV: Tm = { type: "unitT", ty: unitT };
const inl = (ty: Ty, val: Tm): Tm => ({ type: "inlT", ty, val });
const inr = (ty: Ty, val: Tm): Tm => ({ type: "inrT", ty, val });
const pair = (ty: Ty, fst: Tm, snd: Tm): Tm => ({
  type: "pairT",
  ty,
  fst,
  snd,
});
const fst = (ty: Ty, p: Tm): Tm => ({ type: "fstT", ty, pair: p });
const snd = (ty: Ty, p: Tm): Tm => ({ type: "sndT", ty, pair: p });
const nil = (ty: Ty): Tm => ({ type: "nilT", ty });
const cons = (ty: Ty, head: Tm, tail: Tm): Tm => ({
  type: "consT",
  ty,
  head,
  tail,
});
const fold = (ty: Ty, l: Tm, init: Tm, step: Tm): Tm => ({
  type: "foldT",
  ty,
  list: l,
  init,
  step,
});
const strm = (ty: Ty, exp: Exp): Tm => ({ type: "strmT", ty, exp });

// `initV tok = inlT tok`; `valueV v = inrT (inlT v)`.
const initV = (a: Ty, tok: Tm): Tm => inl(instEventT(uniqT, a), tok);
const valueV = (a: Ty, v: Tm): Tm =>
  inr(
    instEventT(uniqT, a),
    inl(sum(a, sum(prod(uniqT, closeReasonT), sum(uniqT, unitT))), v),
  );

// the two kinds this clause uses. `subscribe` owes and pays nothing;
// `delivery` seeds the instant's owed from the source's live
// registration count and pays one against it -- which is why the tag an
// input's per-arrival emit carries is what makes the batcher's flush
// point reachable at all.
const subscribeV: Tm = inl(emitKindT, unitV);
const deliveryV: Tm = inr(emitKindT, inl(sum(unitT, unitT), unitV));

// `instEmitV evs inst src k = pairT evs (pairT inst (pairT src k))` --
// an envelope IS a nested pair at runtime, which is worth noticing:
// there is no envelope RECORD in the plain tree, only a product the
// decoder reads back.
const instEmitV = (a: Ty, evs: Tm, inst: Tm, src: Tm, kind: Tm): Tm =>
  pair(
    instEmitT(uniqT, a),
    evs,
    pair(
      prod(uniqT, prod(uniqT, emitKindT)),
      inst,
      pair(prod(uniqT, emitKindT), src, kind),
    ),
  );

// Agda: Rx.Exp.revT -- a left fold that conses, so it reverses.
const revT = (elem: Ty, l: Tm): Tm =>
  fold(
    list(elem),
    l,
    nil(list(elem)),
    cons(list(elem), varT(elem, 0), varT(list(elem), 1)),
  );

// ---------------------------------------------------------------
// THE CLAUSE THAT MATTERS.
// ---------------------------------------------------------------

// A SLOT REFERENCE BECOMES A REGISTRATION PLUS A DELIVERY STREAM.
//
// An author writes `input i` and means "the source at slot i". What the
// machine needs is (a) an announcement that the source EXISTS, so the
// protocol's live set has something to count against, and (b) every
// arrival stamped with an instant, a source and a kind. Neither is
// anything the author can say, so this clause says both.
//
//   mint (mergeAll (of [ strm announce, strm deliveries ]))
//
// THE TWO MINTS ARE TWO DIFFERENT ARITIES AND THE DIFFERENCE IS WHERE
// THE BINDER SITS. `mint` draws once per subscription of the node it
// stands at. The OUTER mint stands at this node, so it draws one SOURCE
// token per subscription of the input -- a source's own arity. The
// INNER mint stands at the head of a `mergeAll`'s inner, which is
// subscribed once per outer value, so it draws one INSTANT token per
// arrival.
//
// WITHOUT THE ANNOUNCE the source is absent from `live`, every delivery
// seeds owed at zero and underflows, and the automaton rejects the whole
// stream. It is tagged `subscribe` precisely so that it owes and pays
// nothing itself.
//
// WHAT IS DELIBERATELY ABSENT: the `close` at exhausted. The TypeScript
// mirror in primitive-operators.ts (`wrapCold`) DOES emit one; this term
// does not, because `batchSync` hands over no `isLast` bit. It costs
// nothing here because bracketing rejects a close with no init and never
// an init with no close -- so an unclosed registration at the end of a
// stream is accepted. It is the clearest divergence between the two
// mirrors and it is listed rather than hidden.
export const inputP = (i: number, a: Ty, frame: Tm): Exp => {
  const env = machineEmitT(a); // the type this whole clause stands at
  const group = prod(a, list(a)); // what batchSync hands over

  // --- under the SOURCE binder (Theta^1 = uniq :: Theta) ---
  const src = varT(uniqT, 0);
  // the frame was written under Theta, so it shifts by one binder
  const frameUp = shiftTm(frame, 1);

  const announce: Exp = {
    type: "of",
    ty: env,
    items: [
      instEmitV(
        a,
        cons(
          list(instEventT(uniqT, a)),
          initV(a, src),
          nil(list(instEventT(uniqT, a))),
        ),
        frameUp,
        src,
        subscribeV,
      ),
    ],
  };

  // --- under the INSTANT binder (Theta^2 = uniq :: group :: Theta^1) ---
  const inst = varT(uniqT, 0);
  const grp = varT(group, 1);
  const srcG = varT(uniqT, 2);

  // head first, then the tail in arrival order. The `revT` is what makes
  // a cons-fold rebuild the list rather than reverse it.
  const evs: Tm = cons(
    list(instEventT(uniqT, a)),
    valueV(a, fst(a, grp)),
    fold(
      list(instEventT(uniqT, a)),
      revT(a, snd(list(a), grp)),
      nil(list(instEventT(uniqT, a))),
      cons(
        list(instEventT(uniqT, a)),
        valueV(a, varT(a, 0)),
        varT(list(instEventT(uniqT, a)), 1),
      ),
    ),
  );

  // one arrival: mint its instant, emit its whole group under it
  const stamp: Fn = strm(obs(env), {
    type: "mint",
    ty: env,
    body: {
      type: "of",
      ty: env,
      items: [instEmitV(a, evs, inst, srcG, deliveryV)],
    },
  });

  const deliveries: Exp = {
    type: "mergeAll",
    ty: env,
    src: {
      type: "map",
      ty: obs(env),
      fn: stamp,
      src: {
        type: "batchSync",
        ty: group,
        src: { type: "input", ty: a, index: i },
      },
    },
  };

  return {
    type: "mint",
    ty: env,
    body: {
      type: "mergeAll",
      ty: env,
      src: {
        type: "of",
        ty: obs(env),
        items: [strm(obs(env), announce), strm(obs(env), deliveries)],
      },
    },
  };
};

// ---------------------------------------------------------------
// POSTULATED: the remaining wrappers.
// ---------------------------------------------------------------

// Each of these is a real definition in Agda's Rx.Elaborate and each
// does envelope work of its own -- `ofP` brackets a one-shot burst
// against the ambient frame, `mapP` rebuilds each emit under the
// incoming envelope's own instant/source/kind, `mergeAllP` is
// `mergeAll . map laneV`, and so on. They are left as leaves here
// because the point of this file is the shape of the recursion and the
// one clause above, not a second transcription of the elaboration.
export declare const ofP: (frame: Tm, items: Tm[], t: Ty) => Exp;
export declare const emptyP: (frame: Tm, t: Ty) => Exp;
export declare const takeP: (count: Tm, src: Exp, t: Ty) => Exp;
export declare const mapP: (fn: Fn, src: Exp, t: Ty) => Exp;
export declare const scanP: (fn: Fn, init: Tm, src: Exp, t: Ty) => Exp;
// ONE OUTER EMIT'S LANE, and the type is the one you would reach for
// by hand. `emitT (obs t)` unfolds through `plainT`'s observable clause,
// so the outer emit's PAYLOAD is an observable of envelopes -- the
// argument is an enveloped stream of enveloped streams, i.e. exactly
//
//   Observable<InstEmit<Observable<InstEmit<A>>>>
//
// `laneV` takes ONE of those outer envelopes and returns the lane it
// opens: the outer emit's own bookkeeping, re-stamped and payload-free,
// followed by the inner streams that emit carried. Nothing mints here,
// because BOTH layers arrive already stamped -- the inner's bookkeeping
// rides the inner's own emits, and only the outer's has to be placed.
//
//   Agda: Rx.Elaborate.laneV
//     Fn G Dg D Th (emitT (obs t)) (obs (emitT t))
//
// And `mergeAllP k e = mergeAll k (map laneV e)` -- which is why a
// forged inner reaches the wire untouched: `mergeAll` SUBSCRIBES the
// lane, and a lane's inners are whatever the payload held.
export declare const laneV: (outer: Val) => Observable<Val>;

export declare const mergeAllP: (
  limit: number | undefined,
  src: Exp,
  t: Ty,
) => Exp;
export declare const switchAllP: (src: Exp, t: Ty) => Exp;
export declare const exhaustAllP: (src: Exp, t: Ty) => Exp;
export declare const muP: (body: Exp, t: Ty) => Exp;
export declare const varP: (index: number, t: Ty) => Exp;
export declare const deferP: (body: Exp, t: Ty) => Exp;

// de Bruijn weakening (Agda: renTm). Postulated for the same reason.
export declare const shiftTm: (tm: Tm, by: number) => Tm;

// ---------------------------------------------------------------
// The walk.
// ---------------------------------------------------------------

// THE FRAME IS READ OUT OF THE TELESCOPE, WHICH IS WHY `depth` RIDES
// ALONG. Agda elaborates at term telescope `plainC Theta ++ [uniq]` --
// the ambient frame token sits at the END, so its de Bruijn index is
// exactly the number of binders the author's own term language has
// introduced. `elaborate` binds it with the outermost `mint`, where
// Theta is empty and the index is 0.
const frameV = (depth: number): Tm => varT(uniqT, depth);

export const toPlainTm = (tm: STm, depth: number): Tm => {
  const rec = (t: STm) => toPlainTm(t, depth);
  switch (tm.type) {
    case "varT":
    case "unitT":
    case "boolT":
    case "natT":
    case "nilT":
      return { ...tm, ty: plainT(tm.ty) } as Tm;
    case "pairT":
      return pair(plainT(tm.ty), rec(tm.fst), rec(tm.snd));
    case "fstT":
      return fst(plainT(tm.ty), rec(tm.pair));
    case "sndT":
      return snd(plainT(tm.ty), rec(tm.pair));
    case "inlT":
      return inl(plainT(tm.ty), rec(tm.val));
    case "inrT":
      return inr(plainT(tm.ty), rec(tm.val));
    case "caseT":
      // both branches bind one value, so they elaborate one binder deeper
      return {
        type: "caseT",
        ty: plainT(tm.ty),
        scrut: rec(tm.scrut),
        onInl: toPlainTm(tm.onInl, depth + 1),
        onInr: toPlainTm(tm.onInr, depth + 1),
      };
    case "ifT":
      return {
        type: "ifT",
        ty: plainT(tm.ty),
        cond: rec(tm.cond),
        then: rec(tm.then),
        else: rec(tm.else),
      };
    case "primT":
      return { type: "primT", ty: plainT(tm.ty), op: tm.op, arg: rec(tm.arg) };
    case "consT":
      return cons(plainT(tm.ty), rec(tm.head), rec(tm.tail));
    case "foldT":
      // the step binds the element AND the accumulator: two binders
      return fold(
        plainT(tm.ty),
        rec(tm.list),
        rec(tm.init),
        toPlainTm(tm.step, depth + 2),
      );
    case "strmT":
      // THE CLAUSE WHERE THE TWO TREES MEET. An author's stream-value
      // becomes the ELABORATION of the program it holds, which is why
      // `plainT (obs u) = obs (emitT u)` and not `obs (plainT u)`.
      return strm(plainT(tm.ty), toPlain(tm.exp, depth));
  }
};

export const toPlain = (exp: SExp, depth: number): Exp => {
  const rec = (e: SExp) => toPlain(e, depth);
  switch (exp.type) {
    case "input":
      // the only clause written out; everything else delegates
      return inputP(exp.index, plainT(exp.ty), frameV(depth));
    case "of":
      return ofP(
        frameV(depth),
        exp.items.map((t) => toPlainTm(t, depth)),
        emitT(exp.ty),
      );
    case "empty":
      return emptyP(frameV(depth), emitT(exp.ty));
    case "take":
      return takeP(toPlainTm(exp.count, depth), rec(exp.src), emitT(exp.ty));
    case "map":
      return mapP(toPlainTm(exp.fn, depth + 1), rec(exp.src), emitT(exp.ty));
    case "scan":
      return scanP(
        toPlainTm(exp.fn, depth + 1),
        toPlainTm(exp.init, depth),
        rec(exp.src),
        emitT(exp.ty),
      );
    case "mergeAll":
      return mergeAllP(exp.limit, rec(exp.src), emitT(exp.ty));
    case "switchAll":
      return switchAllP(rec(exp.src), emitT(exp.ty));
    case "exhaustAll":
      return exhaustAllP(rec(exp.src), emitT(exp.ty));
    case "mu":
      return muP(rec(exp.body), emitT(exp.ty));
    case "varE":
      return varP(exp.index, emitT(exp.ty));
    case "defer":
      return deferP(rec(exp.body), emitT(exp.ty));
  }
};

// A CLOSED SIMUL PROGRAM ELABORATES TO A CLOSED PLAIN ONE, and the
// outermost `mint` is what binds the ambient frame token every clause
// above reads with `frameV`. Agda: `elaborate e = mintE (toPlain e)`.
export const elaborate = (exp: SExp): Exp => ({
  type: "mint",
  ty: emitT(exp.ty),
  body: toPlain(exp, 0),
});
