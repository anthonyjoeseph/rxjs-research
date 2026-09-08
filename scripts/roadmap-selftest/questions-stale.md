# fixture — a correctly sorted roadmap, covering the whole ledger, whose OPEN
# QUESTIONS have gone stale.  This section is NOT required to move, so nothing
# else would notice it aging: the one thing held is that its relevant list is
# current.  Both ways a list rots are here — a name that left the ledger, and a
# name whose row is no longer FALSITY.

## Tier 0 — anchor

### Big picture tier roadmap

- **the anchor group** — the worst-class row and the two statements that share
  its currency; one unit of work because a restatement of any of them moves the
  other two.
- **the mechanical shelf** — every row whose shape is already known, ground in
  one pass off a single loaded context.
- **the parked remainder** — what is left once the two legs above land, kept
  here so the tier's plan is complete rather than open-ended.

### Open questions

- **THE-SETTLED-question.** Its list still names a row whose class has since
  come down, so the uncertainty this question is about has been settled there
  and the list is what moves.
  relevant: `a-falsity`, `b-shape`
- **THE-ANSWERED-question.** Its list names something that has left the
  postulate ledger, so the question is answered or the row was restated.
  relevant: `a-falsity`, `zz-off-the-ledger`

### The ledger

- **`a-falsity`** — FALSITY, `REFUTED, PROBED`: worst class goes first.
- **`b-shape`** — SHAPE, `NO EVIDENCE`: a restatement is owed.
- **`c-difficulty`** — DIFFICULTY, `PROBED`: true, correctly stated, hard.
- **`d-grindable`** — GRINDABLE, `TWIN`: the shape is already known.

## Tier 1 — parked

### Big picture tier roadmap

- **the anchor group** — the worst-class row and the two statements that share
  its currency; one unit of work because a restatement of any of them moves the
  other two.
- **the mechanical shelf** — every row whose shape is already known, ground in
  one pass off a single loaded context.
- **the parked remainder** — what is left once the two legs above land, kept
  here so the tier's plan is complete rather than open-ended.

### The ledger

- **`e-difficulty`** — DIFFICULTY, `REFUTED×2`: mentions the word GRINDABLE
  later in its own prose, which must NOT be read as its class.
- **`fam-{alpha,beta}`** — DIFFICULTY, `DEAD ROUTE`: brace expansion counts as
  naming both.
- **`suf-nodry-loop` / `-nestRec`** — DIFFICULTY, `PROBED`: a leading-dash
  suffix after a sibling in the same row counts as naming `suf-nodry-nestRec`.
- **`f-grindable`** — GRINDABLE, `TWIN`: mechanical because the PROVEN twin
  `a-proven-citation` did the same thing at the same indices. A name CITED in a
  hook is not a name the row claims, so the staleness check must NOT fire on it
  — earning GRINDABLE requires naming a precedent, and a precedent is proven.
- **the `glob-*` family** — GRINDABLE, `TWIN×2`: a glob covers the family it
  names.
- **`g-unclassified`** — carried, not counted.
- **`names-are-free-one` / `names-are-free-two` / `names-are-free-three` /
  `names-are-free-four` / `names-are-free-five` / `names-are-free-six` /
  `names-are-free-seven` / `names-are-free-eight` / `names-are-free-nine`** —
  GRINDABLE, `TWIN×9`: nine names, well past the budget in raw characters, but
  the prose is a hook, so the length check must NOT fire. Shortening a row is
  never done by dropping a name.
- **`nonpostulate-parent`'s residue** — GRINDABLE, `TWIN`: a head carrying
  prose names a PARENT, so a name declared in agda/src that is not a postulate
  must pass.
