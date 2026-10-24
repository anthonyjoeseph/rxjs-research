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
  stays compositional.

## Plan: event-position keys (current)

1. **Census.** Every former whose run position and event position
   differ. Candidates: a failing takeWhile, the connect's `q ⊕ ix 0`
   source comparison, a joiner's feed, a cold's cascade.
2. **Engine.** Give `operation.Marked` event-position keys for each.
   The TS side is rxjs itself; the oracle's `marks` and `marks io`
   columns judge the Agda engine against it in CI.
3. **K1.** Prove H preserved for of / map / empty / merge; then K2
   (connect, feed) and K3 (colds).

Kill criterion unchanged: a needed field that is neither a fold over
nodes nor a comparison of keys against the position, or clauses needing
bespoke arguments.

## Findings: the census (step 1)

Where `denotation.Unfold.step`'s head differs from the key the engine
runs at, by kind.

**Tie-only shifts, to `k ⊕ ix 0`.** A connect's source event
(`sourceˢ`, `endedˢ`), a flatMap's outer value (`outerˢ`), a lane ending
with a value queued (`laneˢ`), a defer (`step`), an inclusive takeWhile's
failing value (`taking`). Nothing lies strictly between `k` and
`k ⊕ ix 0` (`adequacy.Stepper.shy-order`), so these diverge only when
another node is keyed at exactly `k`: a tie-break. The stepper's
tie-break reads the EVENT, not just its position: its kind (out, skip or
end) at the outer, the source and a lane, and its value at a takeWhile
(`spike.MarkedGap`). Every event the engine searches for carries that
information on reachable nodes: an of's list, a joiner's inbox, a pure
cold's tape. IO's colds are never searched
(`operation.MarkedObservable`: what a cold makes is pushed). So tie-breaks
that mirror the stepper fit the shared engine, given a `due` that also
says what the cold's next event is.

**Real gaps: the run's own region.** A non-inclusive takeWhile ends at
`k ⊕ last`. Each synchronous subscribe cascade reaches its events under
the run position: empty's end, a closed joiner's end, a connect's body
under `ix 0` and its source under `ix 1` (`bodyM`), a lane started under
`ix 1`. The engine runs through the region under `k` in one go, while
the stepper races any foreign head inside it. The engine agrees only if
nothing else is keyed under `k`, which is the pairwise fact again. Exact
keys would need the engine to compute each pending subscription's first
head from its `Obs` (pure; a cold's first frame from `timelineAt`), and
in IO a cold's first frame is unknown.

**What sits in a gap is never a value.** A subscribe cascade shows only
completions (`operation.Marked.begin`: of waits, cold starts, the rest
descend), and only a takeWhile moves a position on the way up
(`operation.Marked.rise`); its value moves only into a tie-only gap.
Values always show at their own keys (of, joiner, cold). So in a real gap
the engine and stepper differ only in the order of SILENT steps:
completions and skips.

**Joiners and colds are not obstacles.** A joiner runs at its inbox
head, which is where it shows (`joinˢ`). A pure cold's `due` is its
frame's head (`burstˢ`), except the done case: it ends at its
subscription's `last`, which is K3's question.

### What this leaves for step 2

- **Ties:** mechanical. Change `kids`/`better` to the stepper's rules;
  the extra input is the next event's kind and value.
- **Real gaps:** exact keys alone do not close them. The second event of
  a cascade needs a later position than the first, which opens a gap no
  choice of positions closes, so the denotation cannot be moved to fix
  it either. Two routes:
  - (d) **One event per search.** Every synchronous continuation becomes
    a mark at its event position, as a takeWhile's completion already is
    (`cpAt`). Lane starts and a connect's subscriptions become marks
    keyed at their first head, computed from the `Obs`: a defer stops
    at its skip, so this terminates, and a pure cold uses `timelineAt`.
    The engine then interleaves as the stepper does on every
    configuration. It matches rxjs's sequential cascades only where
    positions are causal, which the oracle checks, not a proof. IO keys
    a cold's subscription at its lower bound, `u ⊕ ix 0`.
  - (b) **Weaken H** to agreement up to reordering silent steps inside
    a run's region. This is no longer a per-node head equation, so it
    gives up idea 3.
- **Recommendation: (d), after a cheap fit test.** Re-key the ties, mark
  the lane start, and run the oracle, before touching the connect.

## Findings: one event per search (step 2, route d)

`operation.Marked` now keys each candidate where its event sits as its
parent sees it (`seek`), and breaks every tie as the stepper does.

- **The cold needs one more parameter**: `peek`, what a leaf shows when
  due (a value, its end, or nothing). Pure: its tape's head
  (`operation.MarkedPure.peek`). IO: never, since its colds push.
- **Subscribe cascades are silent.** Empty's end and a closed joiner's
  end are an of with nothing left, owed at their `last`; a non-inclusive
  takeWhile's end is a `cpAt` mark. A subscribe itself shows nothing.
- **The tie that refuted H per node now agrees** (`spike.MarkedGap`:
  `failing-agree`, `passing-agree`).
- **Still not the stepper's rule, to watch in K1/K2:** a silent candidate
  is shifted only at the outer and the source; a dead lane races as a
  lane, where the stepper pools dead lanes and takes them only strictly
  ahead; a node's own mark wins a tie against its children.
- **Lane starts and a connect's subscriptions are not yet marks keyed at
  their first head.** The fit test comes first: the oracle's `marks` and
  `marks io` columns judge this engine against rxjs in CI.
