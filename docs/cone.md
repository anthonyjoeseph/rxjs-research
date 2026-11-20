# `make cone` — the postulates one definition rests on

`make postulates` is the whole remaining-work ledger. `make cone` is the slice
of it under one name: every postulate a definition reaches through real
bodies, each with one chain of names from the root down to it.

```
make cone NAME=tree-bounded
    cc-bd  simultaneous/HorizonTree.agda:81    via cc-bd ← join-bd ← bd ← tree-bounded
    ...
    -- 14 postulate(s) under tree-bounded

make cone NAME=bounded FILE=simultaneous/Horizon.agda
    a name defined in several files: pick one
```

Reach for it whenever the question is "what does THIS proof still owe": before
claiming a theorem rests on nothing, before choosing which leaf to grind next,
and when a theorem's cone turns up a postulate nobody expected. A hand search
of the imports misses the leaves reached through a helper three modules down
(`after-ok` reaches a cold's `walk-past`).

## How it resolves a name

Nodes are `(name, file)`, not bare names. `scripts/check-wiring.py` merges
every `bounded` in the tree into one node — right for "is this used anywhere",
useless for "what does this use", where it drags in half the tree. An
occurrence of `n` in file F resolves only to a definition of `n` that F can
see: one in F itself, or in a module F imports whose `using` list names `n`,
imports with no list, or reaches qualified (`M.n`).

A postulate is a leaf: the walk does not continue into the names its type
mentions, since a type is not owed.

## What it cannot tell you

It is textual, so it **over-approximates and never under**:

- two definitions of one name in one file are both candidates;
- a record field resolves to every same-named definition in scope;
- a name anywhere in an owner's body counts, whichever clause it sits in.

So a listed postulate is a lead to check, and an **absent** postulate is
genuinely not reached. For the definitive answer, the typechecker is the
authority — but it has no command for this, which is why this exists.
