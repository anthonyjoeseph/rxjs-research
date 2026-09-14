# `make recursion-cover` — every cycle in the evaluator is covered by a declared descent

`scripts/check-recursion-cover.py`, in the cheap block, seconds.

## What it is for

The evaluator's recursion has one genuine cycle, and what stops it is an
accessibility witness over `Rx.Strat-Order._≺_` threaded as an argument. The
stratification rests on that order having **one constructor per re-entry
edge**, which is a coverage claim: a re-entry site inhabiting none of the three
is a site the order does not cover.

Agda holds most of that itself. Because the witness is an argument rather than
a counter the machine reads, the termination checker verifies every member of
the cycle descends on something it carries — per call site, not on a
declaration's word. What it cannot see is a cycle re-entering the block from
**outside**: a new operator routing a burst walk back into the subscribe, or a
share hop reaching a frame, would compile quietly while the paragraph above the
order quietly stopped being true. That is the silent failure this exists for.

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

The target is `Rx/Evaluator/Builder.agda`, and it certifies one cycle: the
seven-member block the hop closes, declared structural because the `Acc`
argument is what each member descends on. No peel is declared at all, and that
is the doorless shape's whole point — a peel is what a counter the machine
reads needs, and there is no such counter.

Two members sit outside it and the reasons are worth having in hand:

- **The merge join's drain needs no component of its own.** It rides its own
  queue, and its one outward call descends inside the callee.
- **The share hop does not join the triple.** It reaches the frame walk one way
  only, so it composes by being a separate stratum rather than by sharing a
  measure.

## The call graph is over-approximated, deliberately

A name occurring anywhere in a body counts as a call — `where` blocks and type
annotations included. The error is one-sided: a spurious edge can only invent a
cycle, never hide one, so the check is conservative in the direction that
matters and cannot pass a recursion it has not seen. The cost is that a genuine
false positive is repaired by declaring the cycle, which is the right repair
anyway.

## Where it stops

A self-edge is invisible to a component check, so `subscribeE!` at a `μᵉ` node
— which unfolds its body rather than descending into it — is not an edge this
can cut or see. That one is covered by `unfoldμ-shrinks` and the `ltS`
constructor instead.

**And a name the tokeniser cannot spell is a name it cannot see.** The
builder's members all end in `!`, and while that character was outside the word
pattern the check read the module as having no recursion at all and reported a
tidy zero. Any future naming convention reaching outside `WORD` fails the same
way, silently — which is why the selftest fixtures pin the *firing*, not the
passing.
