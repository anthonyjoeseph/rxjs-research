# `make formers-check` — one correspondence, four surfaces

This repo carries the same object language twice: once as Agda datatypes and
once as TypeScript unions, with a JSON bridge between them. What tied the two
former sets together was a **tag string** — the Agda decoder matched one, the
TypeScript generator happened to emit one, and nothing anywhere said they were
the same list.

The failure that made a check necessary is not a crash. It is a **silence**: a
former only one tree has is never generated, so it is never decoded, so no run
of the oracle and no all-Agda sweep ever handles it — and both report green.
The coverage is missing exactly where nothing looks.

## The map

`scripts/formers.tsv` is the one declaration of the pairing. Tab-separated,
five fields, the last optional:

```
kind	agda	tag	gen	why-not
exp	liftᵉ	lift	yes
tm	caseᵗ	caseT	yes
```

- **`kind`** — `exp` or `tm`, naming which datatype and which union the row
  belongs to.
- **`agda`** — the constructor, spelled as the datatype spells it.
- **`tag`** — the JSON tag, spelled as both the decoder and the union spell it.
- **`gen`** — whether the TypeScript generator can produce one.
- **`why-not`** — required when `gen` is `no`, and printed on every green run.

A `gen=no` row is a **hole parked, not an exemption granted**: a former nothing
generates is a former nothing has covered, whatever the oracle says, and the
row is where that gets counted. The checker prints every such row even when it
exits 0, because a hole nobody is reminded of is the silence again.

## What is checked, and in which direction

| Surface | File | Direction |
| --- | --- | --- |
| the Agda datatypes | `agda/src/Rx/Exp.agda` | both |
| the Agda decoder | `agda/src/CLI/Decode.agda` | map → file |
| the TypeScript unions | `typescript/src/exp.ts` | both |
| the TypeScript generator | `typescript/src/generator.ts` | both, via `gen` |

The datatypes and the unions are **closed declarations**, so a former present
in one and absent from the map is a finding — that is what catches a former
added to one tree alone. The decoder and the generator are not: both files
also carry the tags of types, inputs and primitive operators, so "a tag here
that is not in the map" is their normal state and asserting otherwise would
report the whole grammar.

A new former is therefore **five edits**, and the fifth is the map row. Until
it exists the other four are each separately red, which is the property the
tag-string convention never had.

## Parsing, and the two things that rot silently

Constructors are read by **indentation** from `data <name> … where` to the
first line indented no further — which is what keeps a `mutual` block's
siblings (`Fn`, `Val`) out of the set. Several constructors may **share one
signature** (`switchAllᵉ exhaustAllᵉ : …`), and a reader taking the first name
only reports the rest as deleted; that is a real shape in this tree, and the
fixture reproduces it.

`make formers-selftest` perturbs one surface at a time against a copy of
`scripts/formers-selftest/`, whose base is deliberately **quiet**. Both of the
above are pinned by that quiet: the shared signature parses, and a `gen=no` row
is reported, on every run rather than only when one breaks.

## What it found on its first run

`caseᵗ` / `caseT` — the sum type's only eliminator. It was in both datatypes,
in both unions, and decoded correctly; the TypeScript generator had no lane for
it, so in the whole history of the bridge not one program containing a `case`
had ever been run on both sides. Writing the lane took nine lines, and roughly
two in five generated programs now carry one.
