# fixture — a correctly sorted roadmap whose rows cover the whole ledger

## Tier 0 — anchor

- **`a-falsity`** — FALSITY: worst class goes first.
- **`b-shape`** — SHAPE: a restatement is owed.
- **`c-difficulty`** — DIFFICULTY: true, correctly stated, hard.
- **`d-grindable`** — GRINDABLE: the shape is already known.

## Tier 1 — parked

- **`e-difficulty`** — DIFFICULTY: mentions the word GRINDABLE later in its
  own prose, which must NOT be read as its class.
- **`fam-{alpha,beta}`** — DIFFICULTY: brace expansion counts as naming both.
- **`suf-nodry-loop` / `-nestRec`** — DIFFICULTY: a leading-dash suffix after a
  sibling in the same row counts as naming `suf-nodry-nestRec`.
- **`f-grindable`** — GRINDABLE: mechanical because the PROVEN twin
  `a-proven-citation` did the same thing at the same indices. A name CITED in a
  hook is not a name the row claims, so the staleness check must NOT fire on it
  — earning GRINDABLE requires naming a precedent, and a precedent is proven.
- **the `glob-*` family** — GRINDABLE: a glob covers the family it names.
- **`g-unclassified`** — carried, not counted.
- **`names-are-free-one` / `names-are-free-two` / `names-are-free-three` /
  `names-are-free-four` / `names-are-free-five` / `names-are-free-six` /
  `names-are-free-seven` / `names-are-free-eight` / `names-are-free-nine`** —
  GRINDABLE: nine names, well past the budget in raw characters, but the prose
  is a hook, so the length check must NOT fire. Shortening a row is never done
  by dropping a name.
- **`nonpostulate-parent`'s residue** — GRINDABLE: a head carrying prose names a
  PARENT, so a name declared in agda/src that is not a postulate must pass.
