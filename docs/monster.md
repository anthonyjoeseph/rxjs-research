# `make monster-check` — the tier's monster, and what may be added

Every tier of PROOF-STATE.md names ONE declaration in a `### The monster`
section: the thing the session currently judges most likely to be FALSE,
chosen for BLAST RADIUS. The gate holds every line ADDED to `agda/src`,
against the lowest tier that names one, to that monster's own dependency
cone.

## The section

```
### The monster

`burst-drain-well-formed` — one paragraph saying why this is the thing most
worth killing and what goes with it when it falls.

also: `evaluate-deterministic` — a declared exception, and why.
```

One backticked name on the section's first prose line. `also:` lines add
further admitted roots; they are a ledger of exceptions and are FREE against
the section's 700-character prose budget, because charging a ledger buys
exceptions left undeclared rather than exceptions not taken.

## What the cone is, and why it is read off the edited tree

The cone is what the monster's statement and body REACH — not what reaches
them. That is the set whose truth decides the monster's, which is what makes
it the set worth adding to.

It is computed on the tree AS EDITED, and that is load-bearing rather than an
implementation detail. A monster that is a POSTULATE has a cone of its
statement's vocabulary only, so read against the old tree this check would
forbid the one move that kills a postulate — converting it into a real body
over smaller leaves. Read against the tree as it now stands, that body names
the new leaves, so they are inside and the commit passes. The same reading is
what lets a new lemma land: add it AND wire it into the monster in one commit,
which is the wiring law's own workflow, and nothing further is owed.

## Choosing one: the rule of thumb, and the floor under it

**As likely FALSE as possible, as far DOWN the tree as possible, and with as
big a BLAST RADIUS as possible** (Anthony). The three pull against each other
and the sweet spot is where they balance.

They are not three co-equal pressures, and knowing which one does the work is
what makes the rule usable. **Falsity and blast radius are both monotone UP
the tree**: a parent is false whenever any child is, and its blast radius
contains every child's. So maximising those two alone has exactly one answer —
the tier's top line — every time, for every tier, forever. **Depth is the only
pressure that can select anything else**, and it is therefore the one doing all
the selecting. Read the rule that way: among the nodes that could genuinely be
false, take the DEEPEST one that still takes its siblings and parents with it.

**THE FLOOR IS THE CONE, AND IT IS WHAT STOPS THE DESCENT.** The monster's cone
is the commit licence, so pushing the monster down narrows what may be worked
on — which is the point, right up until the work that would KILL the monster
falls outside its own cone. Then the gate forbids the only thing worth doing.
A leaf is usually past that floor: its cone is its statement's vocabulary, so
the assembly it serves and its own sibling are both off-tree. Measured on the
commit that introduced this check, naming a tier's drain leaf reported nine
offenders, six of them the assembly around it and its sibling; naming the
assembly reported three, all genuinely another tier's work.

**AND BOTH FAILURE DIRECTIONS HAVE A MECHANICAL SIGNAL, so neither is a matter
of taste.** TOO HIGH is the cone percentage this check prints: a monster whose
cone is very nearly the whole tree licenses everything, which is what naming a
top line always produces. TOO DEEP is the offender list: a monster below the
floor reports the same declarations every commit until they are `also:`-ed in,
and an `also:` ledger that keeps growing is the tier saying its monster is in
the wrong place.

A small tier bottoms out near its own top, and that is not the degenerate case
— it is a two-level tier having nowhere to descend to. Say so in the section,
so the choice reads as made under the rule rather than defaulted into.

## The trap this check was born with

The wiring graph gives a column-0 `...` continuation — a `with` arm, a
`rewrite` clause — its own node, seeded directly so a name used only inside
one still reads as reached. That exemption is right for reachability and
wrong here: it breaks the chain, so an assembly applying its leaves in a
`with` arm reaches none of them. `check-monster.py` splices every anonymous
node into the declaration it lexically continues. `make monster-selftest`
pins that, along with the lowest-tier rule and the `also:` budget exemption.

## Reading it

Without `--gate` the script is a report and exits 0, which is how to try a
candidate monster on for size before naming it. The report prints the cone's
size, so a monster whose cone is the whole tree is visible immediately.
