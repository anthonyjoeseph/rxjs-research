# `make recursion-cover` — every cycle in the evaluator is covered by a declared descent

`scripts/check-recursion-cover.py`, in the cheap block, seconds.

## What it is for

What stops the evaluator's recursion is a descent threaded as an **argument**
— an accessibility, or the subject the clause is matching on. That rests on a
coverage claim: every cycle in the call graph is one some argument carries, and
a re-entry site nothing descends at is a site the reading does not cover.

Agda holds most of that itself. Because the witness is an argument rather than
a counter the machine reads, the termination checker verifies every member of
the cycle descends on something it carries — per call site, not on a
declaration's word. What it cannot see is a cycle re-entering the block from
**outside**: a new operator routing a burst walk back into the subscribe, or a
share hop reaching a frame, would compile quietly while the paragraph above the
order quietly stopped being true. That is the silent failure this exists for.

## What it does

1. Build the call graph of each module, over its own top-level names. The
   subject is **every module of the evaluator**, found by glob — `--file` takes
   one instead, and is repeatable.
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

## Why the subject is the whole evaluator

It was one module for as long as that module held the burst walk, and that is
exactly the shape this check cannot afford: a cycle is a property of the call
graph and **moves with the code**, so relocating a fold would have carried the
recursion out from under the check in silence — the one failure it exists to
stop, arriving through the check's own configuration. A glob is covered by
construction, and a module added to the evaluator is checked the day it
appears.

**No peel is declared anywhere in the tree, and that is the doorless shape's
whole point** — a peel is what a counter the machine reads needs, and there is
no such counter. Every cycle standing today is declared structural, and each
one names in its own header what its members descend on: the type at
`red-data`/`redDatas`, the derivation at the two thirteen-member Freshness
inductions.

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
can cut or see. Agda's own termination checker is what holds that one.

**And a name the tokeniser cannot spell is a name it cannot see.** The
builder's members all end in `!`, and while that character was outside the word
pattern the check read the module as having no recursion at all and reported a
tidy zero. Any future naming convention reaching outside `WORD` fails the same
way, silently — which is why the selftest fixtures pin the *firing*, not the
passing.
