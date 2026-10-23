# Spike: proving preservation without pairs

The marked engine (`operation.Marked`) is not the place the grid ends: its
order (`spike.MarkedFirst.Ord`) is not inductive, with or without `apart`
(`spike.MarkedApart`). This file is the plan for what to try instead, and
its findings.

## The diagnosis

The step picks the least key across the whole tree (`search`). Proving
that pick correct from per-node facts needs a fact about every OTHER node:
nobody else holds a key there. That fact is pairwise, and moving it into
fields does not remove it, which is why the grid keeps reappearing. Three
exits:

1. make the facts that justify the pick local;
2. never admit a configuration that needs justifying;
3. stop picking globally.

## Idea 1 — births no later than a cursor (exit 1; tested first)

Both configurations `spike.MarkedApart` refutes at hold a node born AFTER
the position, during an emission that has not happened. Every of and
joiner records where it was subscribed. Proposed fields:

- **born ≤ cursor** — a fold, compared against a cursor that only moves
  forward (the position itself regresses at an `after`-mark).
- **a node's keys lie under its own birth** — a per-node fact.

Together they confine a collision with an of's next key to a node born
at an ancestor of the of's birth: a parent/child fact, not a pairwise
one. Catches noted up front: the cursor must be ghost data or mirrored in
the TS, and siblings born at one position tie.

Kill test: find a configuration satisfying `Base`, `Ord` and the new
fields at which a step breaks `Ord`; if none exists after a real attempt,
prove `ord-next` over them.

## Idea 2 — the state computed from the meaning (exit 2)

`spike.MarkedGhost` and `adequacy.Content` read machine → meaning, which
needs an admission set (`Base`) to exclude unreachable configurations;
both refutations are configurations `Base` admits and no run reaches.
Reversed: define `conf P p`, the configuration a program is in at `p`,
by recursion on the program from the clairvoyant denotation. The
invariant becomes "in the image of `conf`", disjointness becomes a
theorem about the MonotonicList, and preservation the equation
`step (conf P p) ≡ conf P (next P p)`. Risk: `step` branches on moves,
so the grid returns unless `conf` of a composite is the plug of its
parts' `conf`s — the first thing to test.

## Idea 3 — a compositional step (exit 3)

Mathematical operational semantics (Turi–Plotkin) and up-to-context
bisimulation (the companion): when each former's step is a function of its
children's observations, operational and denotational semantics agree by
the framework, and every obligation is per former — no move × former
matrix. Concretely each node exposes `next : St → Maybe Key`, a parent
steps only through its children, and the global search becomes a min
fold: every comparison parent against children. Engine-internal only;
`Tree.agda` untouched. Open obstacles: feed is a broadcast to every live
joiner, connect shares its source (a graph, not a tree), ties under
batchSimultaneous.

## Order

Idea 1's kill test first. If it survives, a separate spike checks whether
moves still multiply with formers. If it dies, or that grid appears, idea
3, with idea 2's `conf`-of-composite lemma as its first test.

## Findings

### Idea 1 is dead (`spike.MarkedBorn`)

- **born ≤ cursor does exclude both `spike.MarkedApart` configurations**:
  each holds an of born after the position.
- **Two ofs born at one position refute it** (`born-next-false`):
  absorbed at `q ⊕ ix 0` with both ofs at index 1, births `q`, `Base`,
  `Ord` and `Born` all hold; the first runs value 1 at `q ⊕ ix 1`, where
  the second is keyed, and `Fresh` fails. The cursor is taken at the
  position, so every cursor at or past it admits the configuration.
  Excluding it is distinctness of births. Held per frame, that relates
  every birth under one child to every birth under another — the pairwise
  field again, indexed by the pair's least common frame.
- **"keys under own birth" is false of reachable configurations**, so the
  per-node half of the argument does not exist. A joiner shows its feed
  under its SOURCE's emission, tagged with its own birth
  (`operation.Marked.feed`); a cold's later frames sit in a cascade
  keyed by tick at the root (`operation.MarkedPure.rest`). Both zones are
  made by something other than the node.

### What the failure says about idea 3

Every surviving route to disjointness needs births DISTINCT BY
CONSTRUCTION rather than by invariant: a node's keys computable from its
place in the tree, so two places cannot share them. The two zones that
broke idea 1's per-node half are exactly what such a construction must
handle: a joiner's keys belong to its source's emissions (the connect's
broadcast), and a cold's to the clock (the cascade). Those are idea 3's
named obstacles, so the next spike starts there: can a joiner's and a
cold's keys be defined from their position in the tree, with the
connect's `next` the min over its body and its source's next
emissions, tagged?

### Idea 3, first test: the machine's next as the stepper's head

The compositional stepper already exists: `denotation.Unfold.step` is
structural recursion, and every decision it makes (`pick`, `raceˢ`,
`sourceˢ`, `aheadˢ`, `burstsˢ`, `unionˢ`) reads only its children's head
positions. Hypothesis H: per node, the engine's next key is the head of
`step (gh s)` (or at most it, for a silent step). H composes through min
and needs neither `Ord` nor births, provided every engine decision mirrors
the stepper's.

- **Tie rules alone do not diverge** (`passing-agree`): two lanes on one
  key take the older lane in both.
- **H is false of today's engine, per node** (`spike.MarkedGap`). The
  engine runs a step at its key; the stepper races steps by where their
  EVENT sits. A failing inclusive takeWhile runs at its source's key `k`
  and shows at `k ⊕ ix 0`. Two lanes on one key, the first under such a
  takeWhile: the engine shows the first lane's value, the stepper the
  second's (`engine-first`, `stepper-first`), and every node maps to its
  ghost. Agreement in such a gap holds only if no other node holds a key
  inside it — pairs again.
- **So the repair is in the engine, not the invariant**: a node's key
  must be the position of the event its next step makes, not the
  position it runs at. For takeWhile that means peeking at its source's
  next value; that is a function of the child's observation, so the step
  stays compositional, but the TS must mirror the peek.

Next: list every former whose run position and event position differ
(takeWhile failing, the connect's `q ⊕ ix 0` source comparison, a
joiner's feed, a cold's cascade), give the engine event-position keys for
each, port to TS and let the oracle judge; then K1 (of / map / empty /
merge) preservation of H.
