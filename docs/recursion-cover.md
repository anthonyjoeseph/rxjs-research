# `make recursion-cover` — every cycle in the evaluator is covered by a declared descent

`scripts/check-recursion-cover.py`, in the cheap block, seconds.

## What it is for

The evaluator terminates because a counter — `Gas` — is peeled at a few edges
and held fixed everywhere else, and every fixed-counter re-entry descends on an
argument it already carries: a queue, an emit list, an operator chain. That
reading is what the stratification rests on, because an order with one
constructor per peel edge covers the whole recursion **exactly when no other
cycle survives the peels**.

Nothing checked it. Agda's own termination checker is satisfied by the counter
and says nothing about *which* edges carry it, so a clause that routed a burst
walk back through `subscribeE` at fixed gas, or a share hop that re-entered a
frame, would open a cycle the order does not name and the tower would go on
compiling. That is the silent failure this exists for: the code stays correct,
and the argument written above it quietly stops being true.

## What it does

1. Build the call graph of the target module, over its own top-level names.
2. Cut every edge the source declares as a **peel**.
3. Every multi-member cycle still standing must be declared **structural**.

Both directions are held. A declared peel naming an edge that is no longer a
call is a finding, and so is a declared structural cycle that is no longer a
cycle — either means the declaration has aged past the code, which is what
makes a stale one worse than none at all.

## The declarations

They live in the source, one per line, anywhere in the file:

```
-- PEEL: subscribeInner -> subscribeE
-- STRUCTURAL SCC: subscribeE subscribeAll
```

A `PEEL` says the callee is entered at a strictly smaller counter, so the edge
cannot carry a cycle. A `STRUCTURAL SCC` says the members descend on an
argument of their own — the one thing here taken on the source's word, which is
why it has to be said out loud rather than by being left off a list.

## The reading it currently certifies

Cutting three edges collapses **both** of the evaluator's multi-member
recursions: the twelve-member subscribe component and the three-member share
component. Exactly one cycle survives, the pair that walks the expression.

Two consequences worth having in hand, because they are the questions the
stratification kept asking:

- **The merge join's drain needs no component of its own.** It is a singleton
  the moment the peels are cut — it rides its own queue, and its one outward
  call peels inside the callee.
- **The share hop does not join the triple.** Its counter is a plain `ℕ`
  bounding the slot telescope, it peels once per hop, and it reaches the frame
  walk one way only. It composes by being a separate component, not by sharing
  a measure.

## The call graph is over-approximated, deliberately

A name occurring anywhere in a body counts as a call — `where` blocks and type
annotations included. The error is one-sided: a spurious edge can only invent a
cycle, never hide one, so the check is conservative in the direction that
matters and cannot pass a recursion it has not seen. The cost is that a genuine
false positive is repaired by declaring the cycle, which is the right repair
anyway.

## Where it stops

A self-edge is invisible to a component check, so the third peel — `subscribeE`
at a `μᵉ` node, which unfolds its body rather than descending into it — is not
one this can cut or see. That edge is covered by `unfoldμ-shrinks` instead, and
the source says so where the declarations sit.
