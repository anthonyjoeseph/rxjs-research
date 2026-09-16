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

## Choosing one: usually a definition, rarely a leaf

A leaf's cone is its vocabulary, so naming one puts the assembly it serves
OFF the monster's tree. Measured on the commit that introduced this check:
naming the tier's drain leaf reported nine offenders, of which six were the
assembly around it and its own sibling. Naming the assembly reported three,
and all three were genuinely another tier's work. The monster is the riskiest
node whose cone IS the work, and that is normally a definition — an assembly,
or a relation every leaf is stated in.

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
