// THE AUTHOR'S TREE: an untyped runtime mirror of Agda's `Rx.SExp`.
//
// WHAT MAKES IT A DIFFERENT TREE FROM `Exp` AND NOT A SUBSET OF IT.
// There are two syntax trees in this system and it is worth being blunt
// about why, because the whole difficulty on the Agda side lives in the
// gap between them:
//
//   * `Exp` (exp.ts) is PROTOCOL-BLIND. It is what the evaluator runs,
//     it has no idea what an envelope is, and `mint` / `batchSync` are
//     the two formers that let a program manufacture one.
//
//   * `SExp` (here) is the AUTHOR'S palette. It is what a person writes
//     with srxjs, and it is strictly SMALLER: there is no `mintS` and no
//     `batchSyncS`, because an author has no business minting an
//     identity token or reading the subscribe frame.
//
// The elaboration `toPlain` (to-plain.ts) is the translation, and every
// envelope in a running system is put there by IT rather than by
// anything the author wrote. That is the invariant the Agda proof is
// trying to state: an elaborated program cannot break the protocol
// BECAUSE the author could not reach the formers that would break it.
//
// TYPES ARE CARRIED BUT NOT ENFORCED, exactly as in exp.ts: the `ty`
// field on every node is there so a re-check is a local structural
// comparison rather than inference, and nothing here tracks
// well-typedness at the TypeScript level.

import type { Exp, Fn, PrimOp, Tm, Ty, Val } from "../exp.js";

// Agda: Rx.SExp.STm. The author's TERM language is the plain one with
// its observable former re-pointed at the simul tree.
//
// EVERYTHING ELSE IS COPIED RATHER THAN SHARED, and the reason is one
// line of Agda's own comment: "a `Tm`'s `strmT` holds a program the
// evaluator runs, and an author's holds a program that has not been
// elaborated yet." They are different objects at the same spelling.
export type STm =
  | { type: "varT"; ty: Ty; index: number }
  | { type: "unitT"; ty: Ty }
  | { type: "boolT"; ty: Ty; val: boolean }
  | { type: "natT"; ty: Ty; val: number }
  | { type: "pairT"; ty: Ty; fst: STm; snd: STm }
  | { type: "fstT"; ty: Ty; pair: STm }
  | { type: "sndT"; ty: Ty; pair: STm }
  | { type: "inlT"; ty: Ty; val: STm }
  | { type: "inrT"; ty: Ty; val: STm }
  | { type: "caseT"; ty: Ty; scrut: STm; onInl: STm; onInr: STm }
  | { type: "ifT"; ty: Ty; cond: STm; then: STm; else: STm }
  | { type: "primT"; ty: Ty; op: PrimOp; arg: STm }
  | { type: "nilT"; ty: Ty }
  | { type: "consT"; ty: Ty; head: STm; tail: STm }
  | { type: "foldT"; ty: Ty; list: STm; init: STm; step: STm }
  // THE ONE CLAUSE THAT DIFFERS: an author's stream-as-a-value holds an
  // SExp, so it is a program nothing has elaborated yet.
  | { type: "strmT"; ty: Ty; exp: SExp };

// Agda: SFn Γ Δᵍ Δ Θ s t = STm with the argument bound as Θ-var 0.
export type SFn = STm;

// Agda: Rx.SExp.SExp.
//
// NOTE WHAT IS ABSENT, since the absences are the point: no `mint`, no
// `batchSync`, and no `share` node — share identity is a BINDING and
// lives in the slot telescope, referenced by `input`, exactly as in the
// plain tree.
export type SExp =
  | { type: "input"; ty: Ty; index: number } // into Γ
  | { type: "of"; ty: Ty; items: STm[] }
  | { type: "empty"; ty: Ty }
  | { type: "map"; ty: Ty; fn: SFn; src: SExp }
  | { type: "scan"; ty: Ty; fn: SFn; init: STm; src: SExp }
  | { type: "take"; ty: Ty; count: STm; src: SExp }
  | { type: "mergeAll"; ty: Ty; limit?: number; src: SExp }
  | { type: "switchAll"; ty: Ty; src: SExp }
  | { type: "exhaustAll"; ty: Ty; src: SExp }
  | { type: "mu"; ty: Ty; body: SExp }
  | { type: "varE"; ty: Ty; index: number }
  | { type: "defer"; ty: Ty; body: SExp };

export type ClosedSExp = SExp;

// A SLOT TABLE IS THE PLAIN ONE, UNCHANGED, and that is deliberate
// rather than a shortcut. The Agda development runs `subscribeSExp`'s
// mirror against `Slots` at the PLAIN palette: scripted inputs carry
// bare payloads and a shared definition is a plain tree. Re-pointing
// the table at `SExp` is a separate question, and on the Agda side it
// is the one that took a palette parameter to answer.
export type { Exp, Fn, Tm, Ty, Val };
