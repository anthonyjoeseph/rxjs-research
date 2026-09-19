# old-evaluator — the last fully-defined Girard–Tait evaluator

A verbatim copy of the evaluator, the reducibility candidate and the `Exp`
tree they were built on, taken at **`d847bb4b`** ("Discharge red-thru: the
flattener's hop is a body over no new leaf"), which is the FIRST commit where
the four evaluator modules carry **zero postulates**. They stayed at zero
until `8c1b5750`, which rewrote `Exp`, `Evaluator` and `Reducible` together —
that commit is what this directory exists to undo the loss of.

## What is here

The import closure of `Rx.Evaluator.Builder`, `Rx.Evaluator.Reducible`,
`Rx.Evaluator`, `Rx.Evaluator.Domain`, `Rx.Exp` and `Rx.Exp.Guarded` at that
commit — 23 modules, self-contained apart from the standard library. Module
names are unchanged (`Rx.*`, `Decide`), so this is its own Agda library with
its own root; nothing in `agda/` reaches it and it reaches nothing in `agda/`.

## Why it was removed, and what that costs to undo

This tree is entangled with `InstEmit`: `Rx.Prim` still exports
`InstEmit`/`InstEvent`, and the evaluator hands a subscribe's whole output
back as a LIST — the bottom-up burst assembly. The current tree emits one
value at a time, which is what forced `batchSync-st` to hold a buffer rather
than one bit. That difference is the reason the two `Exp` trees cannot simply
be swapped, and it is what any resurrection has to answer.

## Status

**Not wired, not gated, not typechecked here.** It sits outside `agda/src`
and `agda/evidence`, so no claim root reaches it and no gate target reads it.
It is reference material for the resurrection question, not proof code —
which means the repo's own law applies: work no claim root reaches is exactly
what parks itself and gets re-derived, so this directory either becomes a
claimed tree or it goes.
