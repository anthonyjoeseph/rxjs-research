# `make find` and `make dup-check` — the search tools

```
make find Q='≤ slotsSize'        every STATEMENT whose type mentions it
make find Q='1 ≤ sizeᵉ'          the phrase, matched against the type text
```

**Run it before you state a postulate, write a lemma, or commission a probe.** It
walks the whole of `agda/src` and prints the declared TYPE of every match, which is
the thing you need in order to answer "does this already exist?".

## It replaces a hand-rolled `grep`, and that is the point

The rule used to say "grep for the conclusion's shape", and it was FOLLOWED and
STILL FAILED. Three lemmas `1≤slotSize`, `n≤slotsSize` and `n≤sum-tab` were
rewritten from scratch and collided on the name with copies that had been sitting in
`.Caps-Face.Part1` for months. The search had been run, and run for the right shape —
it was scoped to two `grep` arguments instead of the tree. `make find` takes no
argument that narrows it, so that mistake is not available. **A rule you can satisfy
while still failing is a rule that needs a machine.**

## The judgement no command can do for you

- **Search for the CONCLUSION's shape, not the name you imagine.** Names here are
  idiosyncratic (`frameStep-chain-suc` is a path-length lemma) and a name-guess
  reliably misses. Feed `find` the operator and the relation.
- **A miss is weak evidence; two misses on different phrasings is strong.** If
  `≤ cSize` finds nothing, try the operator alone, or a neighbouring lemma and read
  what sits AROUND it — related facts cluster in one file.
- **Read the SIGNATURE, never the header prose.** A header saying a route is dead is
  a claim about an attempt; the signature is a fact.

## `make dup-check` — the after-the-fact net

Part of `make gate`. It fails the build when two declarations prove the same fact,
comparing declared types up to renaming of bound variables — `sizeᵉ-pos` and
`1≤sizeᵉ`, the same statement 170 lines apart in ONE file, unnoticed for months.
`make find` is how you avoid needing it.

### A finding is two SITES, not two names

The subtlety, and this repo's rules asserted the opposite for a while: the tempting
assumption is that Agda's `ClashingDefinition` already covers copies sharing a name,
so only DIFFERING names need a checker. That is FALSE. Agda says nothing when either
copy is `private`, or when the two modules are simply never in scope together:
`dbl-suc` and `2*suc≤2^suc` sat verbatim in `.Subscribe-Face` and in
`.Caps-Face/Part6`'s private block, invisible to the compiler and to the check.

Three ways one fact wears two types, all of which it matches through:

- **binder spelling** — `∀ X →` against `∀ (X : ℕ) →`, and explicit against
  implicit. Different types, but not different facts, and merging them costs only an
  eta-expansion at the call sites.
- **atomic type synonyms** — `Id = ℕ`, so `(id : Id)` and `(id : ℕ)` are one
  signature.
- **plain differing names.**

**`make dup-selftest`** — also in the gate — pins each of those rows against a
fixture outside `agda/src`, and pins the four shapes that must NOT fire (record
fields, `where`-locals, the mandated `-go` alias, and two lemmas differing only in
their operators). It earns its keep: three separate bugs shipped in this checker,
and every one was found by hand rather than by the check failing.

### When it fires, move the fact DOWN — do not pick a winner

The usual cause is structural rather than careless: two SIBLING modules both need a
fact and neither can import the other, so each grows its own copy (`reach-reset`'s
own header documents exactly this, and the ten primed pairs across `.Subscribe-Face`
and `.Caps-Face.Part6` are one missing home, not ten accidents). The repair is to put
the fact in the lowest module that reaches both and delete the copies. Deleting one
copy at random re-creates it later.

**And keep ONE naming convention per class of fact**, because two conventions are the
machine that generates duplicates: someone wanting "term size is positive" greps
`1≤`, finds nothing under that spelling, and writes a third copy. That is precisely
how `sizeᵉ-pos` and `1≤sizeᵉ` came to coexist.
