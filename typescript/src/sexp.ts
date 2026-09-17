// The untyped runtime mirror of Agda's Rx.SExp -- the SIMUL tree, which
// is what an srxjs author writes, as opposed to `exp.ts`'s plain tree,
// which is the whole of what the evaluator runs.
//
// TWO TREES BECAUSE ONE OF THEM IS DELIBERATELY TOO BIG.  The plain
// tree can build an emit by hand, and once the envelope is an ordinary
// type of the object language it can build one of those too.  The
// theorem is not about that language: it is about programs made of the
// operators this development ships, so those operators get a syntax of
// their own and being outside it is a scope error rather than a side
// condition anything carries.
//
// WHAT KEEPS THE ENVELOPE HONEST IS THE PALETTE AND NOT A PREDICATE,
// and the one visible consequence is below: there is no `uniqT` in
// `STm`.  No former here reaches the term that makes a token, so no
// simul program can name an instant or a source, let alone forge one
// that collides.  The elaboration is the only thing that writes those
// fields.  Dropping that one constructor is the entire mechanism, which
// is why it is worth saying out loud -- it reads as an omission.
//
// Types are the AUTHOR's, with no envelope anywhere in them; the
// wrapper appears exactly once, at the boundary between the trees.
// Well-typedness and mu-guardedness are not tracked here, exactly as in
// `exp.ts`: the generator maintains them and the decoder re-checks them.

import { PrimOp, Ty } from "./exp.js";

// Agda: SFn Γ Δᵍ Δ Θ s t = STm with the argument bound as Θ-var 0.
export type SFn = STm;

export type SExp =
  // a slot reference.  share is NOT a former on either side: a shared
  // observable is a BINDING, so it lives in the slot telescope and is
  // named from here, exactly as a scripted input is.
  | { type: "input"; ty: Ty; index: number }
  | { type: "of"; ty: Ty; items: STm[] }
  | { type: "empty"; ty: Ty }
  | { type: "take"; ty: Ty; count: STm; src: SExp }
  // THE pure-function former, and the one the elaboration already has a
  // real body for.  A lift adds no event, mints nothing and cannot end
  // the stream, so everything it needs is in the emit it was handed --
  // which is why the instant is not missing here.  map and scan are
  // definitions over this on both sides rather than formers.
  | { type: "lift"; ty: Ty; fn: SFn; init: STm; src: SExp }
  | { type: "mergeAll"; ty: Ty; limit?: number; src: SExp }
  | { type: "switchAll"; ty: Ty; src: SExp }
  | { type: "exhaustAll"; ty: Ty; src: SExp }
  | { type: "mu"; ty: Ty; body: SExp }
  | { type: "varE"; ty: Ty; index: number }
  | { type: "defer"; ty: Ty; body: SExp };

// The author's TERM language is the plain one with its observable
// former re-pointed at this tree, and with the token literal REMOVED.
// Everything else is copied rather than shared because the two trees'
// observables are different objects: a `Tm`'s stream holds a program
// the evaluator runs, an author's holds one not yet elaborated.
export type STm =
  | { type: "varT"; ty: Ty; index: number } // into Θ
  | { type: "unitT"; ty: Ty }
  | { type: "boolT"; ty: Ty; val: boolean }
  | { type: "natT"; ty: Ty; val: number }
  | { type: "pairT"; ty: Ty; fst: STm; snd: STm }
  | { type: "fstT"; ty: Ty; pair: STm }
  | { type: "sndT"; ty: Ty; pair: STm }
  | { type: "nilT"; ty: Ty }
  | { type: "consT"; ty: Ty; head: STm; tail: STm }
  | { type: "inlT"; ty: Ty; val: STm }
  | { type: "inrT"; ty: Ty; val: STm }
  | { type: "caseT"; ty: Ty; scrut: STm; onInl: STm; onInr: STm }
  | { type: "foldT"; ty: Ty; list: STm; init: STm; step: STm }
  | { type: "ifT"; ty: Ty; cond: STm; then: STm; else: STm }
  | { type: "primT"; ty: Ty; op: PrimOp; arg: STm }
  | { type: "strmT"; ty: Ty; exp: SExp };
