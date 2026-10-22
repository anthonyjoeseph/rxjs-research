# `make split` — cut a long module into parts, consumers retargeted

A module over 1000 lines is too long (Anthony): every edit to it re-checks all
of it and invalidates the whole cone above it. `scripts/split-module.py` does
the mechanical part of a split in seconds. It is **textual and approximate by
design** — it gets the split most of the way, and the typechecker finishes it.

## The two commands

```
make split F=agda-impl/port/Content.agda
    lists every line the file may be cut at, with the gap since the last one

make split F=agda-impl/port/Content.agda \
     P='port.Content:Honesty port.Content.Hop:HonestHop@400'
    splits it; DRY=1 prints the plan and the problems without writing
```

Then `make imports-fix`, then a build (`make bg T=agda`).

## Choosing the cuts

A part is `MOD@LINE`, where LINE is the **original** file's line the part
begins at, its leading comment block included — take it straight from the
`--cuts` listing. The first part takes no `@LINE`. A part's MOD names its
file: `port.Content.Hop` is `agda-impl/port/Content/Hop.agda`,
and keeping the original name for one part (usually the first) spares the
consumers that only use that part.

- **Cut at the file's own section rules** (`------…` lines) where one falls
  near the size you want. A listed cut never splits a signature from its
  clauses, a mutual block, a record, or a nested module.
- **One nested module bigger than the limit** is cut IN PLACE first:
  `make split F=<file> SUB='Grown GrownHeaps@698'` closes `Grown` at line
  698 and opens a sibling `GrownHeaps` with the same telescope, which opens
  `Grown`. Consumers follow it: `using (module Grown)` gains `module
  GrownHeaps`, a `renaming (module Grown to W)` gains `W′`, an alias `module
  G = Grown τ` gains `G′ = GrownHeaps τ`, and every qualified use of a name
  that moved is renamed. Then cut the file between the two siblings.
- **A file that is ONE parametrised module** (`module Honesty (R : Set)
  where` wrapping everything — most of `port/`) is cut inside it. Give
  each part a wrapper name as well, `MOD:WRAPPER@LINE`; every part gets the
  wrapper's telescope and its leading `open` lines, and opens the earlier
  parts' wrappers with the same arguments.

## What it does

- Each part gets the original header's imports (imports-fix prunes them),
  its `OPTIONS` pragma, an `open import … using (…)` of the names it takes
  from earlier parts, and any bare `open R` of an earlier part's record. The
  header's prose stays with the part keeping the original name.
- Every consumer's `open import M using (…)` / `renaming (…)` is partitioned
  across the parts by who defines each name. For a wrapper: `open W args
  using (…)` the same way, a blanket `open W args` or `hiding (…)` becomes
  one per part, and a qualified `W.name` is renamed to its part's wrapper.
- An `import M as Q` becomes one import per part used, aliased `Q`, `Q′`,
  `Q″`…, and each `Q.name` follows its definer.

## What it leaves for you (reported as PROBLEM lines)

- a private name a later part uses — make it public or move it;
- a consumer's `module X = W args` alias — its `X.name` uses are untouched;
- anything it cannot parse;
- a name it cannot find a definer for: usually a field brought out by an
  `open R public` it missed, or a `syntax`/operator form.

`dup-check` can fire after a split on pairs it never reported in the
whole file — its `where`-block filter reads a fresh file differently. They
are real duplicates: move the fact down as usual.

It also over-approximates what a part uses (any token that matches an
earlier part's export, local binders included), so expect `imports-fix` to
delete some of what it wrote.
