# Working methodology

This repo pairs an **Agda model** (`agda/`) with a **TypeScript implementation** (`typescript/`).
Agda's spec is gospel; TS conforms to it.

## The goal: nothing short of a proof

The ultimate and only goal is a **complete machine-checked proof** that the implementation
equals the spec — `Formal-Verification` fully discharged, **no postulates, everything
typechecks**, on *every* canonical program. Partial results, "passes almost all QuickCheck
seeds", "fixes the common case" — none of these are the finish line. They are waypoints.
A remaining counterexample (even 1 in 500, even a pathological nested program) means the
theorem is false and there is no proof. Keep going until it is airtight.

## Autonomy

You have standing approval to make any change that **does not alter the spec** — implementation
edits, protocol changes, new operators, refactors, experiments. Don't stop to ask permission
for these; just go. Finding the right implementation is inherently a throw-a-lot-at-the-wall
process: try approaches, keep what passes QuickCheck/oracle, revert what doesn't, commit the
wins. Only pause to ask when a change would touch the **spec** (`Spec/`, the root README's
semantics), or when the spec is genuinely ambiguous (then follow the ambiguity rule below).

## Agda: work from the outside in

Define and refine the **datatypes, primitives, and end goals first**, then link them
together with **postulates**. Before any serious proof work, all types should be settled
and the top-line results fully stated and typechecking _in terms of postulates_. Only then
start chipping the postulates away, one at a time, until everything is defined and there are
no gaps.

## Keep the repo lean — no fat

This repo always represents the **most present, up-to-date code**. Every definition must be
used somewhere — the only exceptions are the top-level, most-important exports. No
backwards-compatibility shims, nothing "stored for reference", no legacy, no deprecated.
**Do not be afraid to throw out code or documentation.** Git history is the archive.

## TypeScript implementation style

- The TS implementation should be as purely functional as possible: avoid manipulating mutable state and avoid calling .subscribe()
  directly. Delegate any form of IO/statefulness (e.g. accumulation) to rxjs operators like scan.
- Rationale is twofold: (1) aesthetic/cosmetic cleanliness, and (2) to keep the primitives and batchSimultaneous implementations in
  near-direct correspondence with the Agda, so translation between the two is straightforward.

## The change workflow

Follow these phases in order for any change to the implementation or spec:

1. **Agda first.** Make the change to the spec/impl in Agda before touching TypeScript.
2. **QuickCheck dev loop.** Use `npm run agda:qc` (the all-Agda QuickCheck comparing
   `impl-batchSimultaneous` vs `spec-batchSimultaneous`) to align the implementation and
   spec quickly. **The spec is gospel — do NOT touch it to resolve a mismatch.** When impl
   and spec disagree, the implementation is wrong by default; change the implementation.
   Only touch the spec under very special circumstances, and only after asking.

   **Resolving ambiguity.** When the spec seems ambiguous or you're unsure what the "right"
   answer is, defer to **naive plain rxjs** — the semantics should mirror ordinary rxjs
   wherever a case is underspecified. Actually run the example in rxjs and see. If that
   still doesn't resolve it, surface the question to the user with a clear TypeScript rxjs
   example that **avoids the `*All()` higher-order operators where possible** and follows
   the style of the README's edge-case examples.

3. **Ignore `Formal-Verification/` for now.** It may have errors during this phase — that's
   fine. Leave it until the end.
4. **Port to TypeScript** — but only once QuickCheck passes.
5. **Oracle.** Make the fast-check/Agda-alignment oracle (`npm run oracle`, TS-impl vs
   Agda-impl via the CLI) pass.
6. **Formal verification, last.** Now prove the implementation equals the spec. Do it in
   **phases** — leave middle steps as postulates and **commit in-between results**. Work
   until there are **no gaps**: no postulates, everything typechecks.

In some cases, however, it might make sense to adding a new "naive rx" operator to fix an Agda-impl bug.

This is allowed and encouraged when it's the best solution. But follow the port order:

- Develop the new operator in TypeScript first (as a proper rxjs-delegating, purely-functional operator).
