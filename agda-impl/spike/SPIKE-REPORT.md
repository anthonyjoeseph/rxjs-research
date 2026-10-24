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
- **A merge races raw heads, as the stepper does** (`Unfold.goˢ`): the
  outer and the earliest lane each by its own head, the winner's event
  then read as the merge's (`raceT` over `outerT`/`laneT`). A silent
  outer step stays where it is.
- **Lane starts and a connect's subscriptions are not yet marks keyed at
  their first head.**
- **The oracle agrees** with this engine (1000/1000 random seeds,
  100/100 named).

## Findings: K1 — the fragment of / empty / map / switches / merge

**H holds of every state of the fragment, by recursion on the state**
(`spike.MarkedHead.head-agrees`). No step-preservation argument at all:
H is per node (`Agrees`: the engine's candidate is the stepper's next
event, or a silent mark no later; under a closed observer, `Quiet`).

- **The fragment's invariant (`Frag`) passes the kill criterion.** Its
  fields: a lane count equal to the live lanes (a fold), "outer done →
  `Done`" (a shape predicate), each lane a switch on or off, the queue
  empty. No order between nodes, no births.
- **The merge is the only real work, and it is generic.** The engine's
  lanes fold oldest-first, ties to the left; the stepper's `earliest`
  runs newest-first, ties to the right. They meet through one exchange
  lemma (`swap`) over two `Pos` facts already in `Events`, and a snoc
  lemma (`win-snoc`). The race then splits four ways (engine and stepper
  each take outer or lane); every disagreeing branch is either
  impossible or the engine's pick is silent and no later.
- **What was cheap:** dead lanes, a silent outer, an attach's own mark
  winning a tie — all one lemma: a silent candidate first is harmless
  (`silent-first`, `quiet-wa`).
- **Left as leaves:** five order facts about keys (`<ᴷ-trans`,
  `<ᴷ-irrefl`, `≮ᴷ-trans`, `at-<ᵖ`, `ext-≮`), each a statement about
  `operation.Key`'s lexicographic order, none about the engine.
- **Two engine bugs found by writing the merge clause**, both fixed and
  oracle-confirmed: lanes were transformed before racing, and a silent
  outer step was shifted.

## Findings: K2 — connect and feed

**H holds of every connect and joiner state, still by recursion on the
state, with no order invariant** (`spike.MarkedHead.Agrees.conn-at`,
`join-head`). The kill criterion is not hit.

- **The invariant grows by shape only.** `Conn` records which phase a
  connect is in: pending source with the body's own mark at `r = p ++
  [ix 1]`, or subscribed. `NoConn` (no connect inside) appears wherever
  the stepper's rest must be hush: under a cut-off switch, in dead
  lanes, in a done outer, in an over connect's source and body, in an
  ended connect's source. Still no order between nodes, no births.
- **The phases split cleanly.** Pending: the body's mark is silent and
  no later than the stepper's head. Live: every step of the source is
  either the body's step or a skip just past the source's key, so a
  disagreement is a silent mark no later, or a contradiction. Ended:
  the stepper shuts. Over: the stepper hushes or shows the source's
  head. Closed: everything is quiet.
- **Left as leaves: two stepper facts about a fresh subscription**
  (`sub-head`, `sub-bursts`): what `denotation.Unfold.subscribe`'s first
  step and its bursts are. Statements about the denotation only.
- **Two engine bugs found by writing the clauses**, both fixed: a joiner
  under a closed observer showed its event, and an over connect still
  shifted its source's keys.
- **Coverage boundary:** a connect under a rest (cut off, a dead lane, a
  done outer, an over connect's parts) is excluded by `NoConn`. The real
  case behind it is the pool's race with rest skips, which K3's colds
  and a later pass must cover.

## Findings: K3 — colds

**H holds of every cold state, with no new invariant and no leaves**
(`spike.MarkedHead.cold-head`). A cold's ghost is its tape read as a
node (`spike.MarkedGhost.tape`), so each clause is one evaluation: a
playing cold shows its frame's next event where the stepper's burst
does; an unsubscribed one is a silent mark against a stepper with no
head; a cold owing its end shows it at the same key. A cold under a rest
hushes, so `NoConn` needs no cold case.

- **One engine mismatch found and fixed:** a cold owing its end showed
  it even under a closed observer; it is now silent there, as an of's
  end is. The runner still delivers that end, into an observer that has
  closed.
- **What K3 did not test:** that the tape a subscription opens IS the
  stepper's node for that subscription (`operation.MarkedPure.opening`
  against `denotation.Unfold.subscribe`), including the end owed at the
  subscription's `last`. That is the ghost's correspondence, a statement
  about subscribing, not about H; it is the same kind of fact as K2's
  `sub-head`.

## Findings: the pick from H (`spike.MarkedPick`)

`spike.MarkedInv` and `spike.MarkedKept` now carry `Order` in place of
the global key order `Ord` (refuted as non-inductive by
`spike.MarkedApart`). `Order` has two fields: `shape`, which is `Frag`
of the whole tree, and `lead`, which is `Clear` at a rising
configuration. `Clear` holds, at each flatMap frame a rising lane sits
in, the `First` facts `lanes-first` consumes, read off the meaning.
Both modules typecheck: `lanes-first` is now one projection.

**The grid is gone from the pick half.** `won-clear` builds `Clear` at
the step that finds a node. It walks up the found node's frames and,
at each flatMap, reads:

- the engine's race there (`search-won`: the found node's lane beat each
  older lane strictly and each newer lane and the outer weakly);
- `head-agrees` at each sibling, turning candidate order into
  step-head order (`after-step`, `not-before-step`, `race-steps`);
- `sides-link`, which turns step heads into the meaning's heads and
  tails.

No comparison between two nodes not related by a frame appears: each
sibling is compared with the winner only through the one race they
both entered.

**Leaves, by kind.**

- *Shape only:* `frag-flat` (a subtree of a `Frag` tree is `Frag`),
  `shape-next` (`Frag` survives a step). The new `Frag` clauses (scan,
  takeWhile, bounded merge, switch and exhaust as flatMaps, a pending
  subscription) cost five per-former H leaves (`scanS-head`,
  `takeS-head`, `limit-head`, `switch-head`, `exhaust-head`), each the
  same kind of clause K1–K3 proved.
- *Engine only:* `search-won`, `run-lead` (a run rises, if at all, the
  event it showed at its own key). `sub-lead` and `rise-lead` are proven.
- *Meaning link:* `sides-link`, which needs the stepper's step of each
  part to be the meaning's head. That is the ghost correspondence,
  possibly with `Base` for a joiner's buffer.

**`rise-lead` is a body, after a restatement.** As first stated, the
lead was one position for every frame, and it is false. An inclusive
takeWhile failing at `p` sends its value up at `p ⊕ [ ix 0 ]`. An older
lane headed exactly there is after `p`, but not after where the value
arrives. The repair moved an index; no new mathematics was needed.
`Clear` now follows the value up as `rise` carries it: each frame at the
position the value has there, ending where `rise` absorbs it. `Won`
follows the winner's candidate up as `seek` retags it, and `seek` shifts
the key at the same frames by the same `shift`. So `won-clear` reads each
frame's race at the position the value will reach it, and `rise-lead` is
one clause per frame.

**Risks, riskiest first.**

1. `limited-sides`: for a bounded merge, switch or exhaust, the queue
   and the one-lane rule sit outside the race `race-steps` reads, so the
   merge clause's route does not carry over as written.
2. `rise-src-nx` / `rise-body-nx` in `spike.MarkedKept`: settled below.
   What remains is the source's race at `inSrc` as a `Won` clause, and
   `_≅_` closed under a node gaining skips.
3. `sides-link`: the stepper's head of each part is the meaning's. It may
   need `Base` for a joiner's buffer.

## Findings: the connect's feed

The engine fed every live joiner by inserting in position order. The
meaning appends, and only to joiners that joined before the feed; any
other joiner gets a skip. The two agreed only if (A) every live joiner
joined before the feed position `p`, and (B) every inbox entry lies
before the new one.

**(A) is the grid as the engine stood.** A joiner with an empty inbox
has no key, so neither the race nor `Won` can bound its join position
against `p`. Its join is in the past and the feed is in the present, and
relating the two is the births-against-a-cursor route. `spike.MarkedBorn`
already found that route needs births to be distinct, which is a
pairwise fact. The engine's own `shift` tie-break at a connect admits a
body key equal to the source's key. Only distinctness of births rules
that tie out.

The regression of the position at `after`-marks is not the obstacle. All
four `after`-marks only unsubscribe and land `absorbed`, and the next
search runs at a node's own position.

**The engine change.** The engine now makes the meaning's choice itself
(`operation.Marked.queued`). It appends instead of inserting. It queues
a value only for a joiner joined before `p`. It queues an end at
`p ⊕ [sub j]`, or at `j ⊕ [last]` for a joiner joined at or after `p`.
This is an engine-internals change. In reachable runs the guard should
always hold, so the oracle should not move; CI will confirm. With it, (A)
and (B) are no longer obligations: on every live joiner, both sides
compute the same thing.

**What remains for `rise-src-nx`.** The meaning also feeds what the
engine has not started:

- a flatMap's later lanes, because `feed` composes into its `g`;
- a source not yet subscribed (`subOr`).

Each of these joins at or under a position of the connect's body. Every
key of the body is past `shift p` once the source wins its race, so the
meaning feeds each of them only skips. The later lanes start at the
outer's emissions, which are at or past its head key (`head-agrees`)
and monotone in the meaning.

Two things are owed:

- the source's race at `inSrc`, as a `Won` clause like `LaneWon`. This
  compares keys with the position.
- `_≅_` closed under a node gaining skips. This is compositionality of
  the meaning.

Neither is a fact about a pair of nodes. `rise-body-nx` needs the same
race the other way, at `inBody` (the source not strictly before).

**Verdict: firm ground.** No pairwise fact returns.

### `rise-src-nx` as a body

`rise-src-nx` is now a body (`spike.MarkedKept`). It chains three steps:

1. **`src-leads`.** The source's value shows at the top as a skip at
   `p ⊕ [ix 0]`. What follows is the body as `denotation.Unfold.feed`
   feeds it. This is the stepper's own `fed-first`, restated for the
   ghost. Its race is now a field. `Won` at `inSrc` carries the
   engine's `sourceT` comparison: the body's candidate is strictly after
   the source's shifted key. `won-clear` turns that comparison into
   `Clear` at `inSrc`, an `After` on the body's step head (`frag-body`
   is the shape leaf it reads).
2. **`fed-ghost`.** The meaning's feed and the engine's differ only in
   skips. Each skip goes to a joiner joined at or after `p`, or to a
   lane or subscription not yet started. Each such start is past the
   source's position, by the race just carried.
3. **`src-plug`** (proven). This returns to the after-configuration.

`lift-skip` drops the top skip. Every leaf reads one connect and its
own subtree, and none relates two nodes.

**Measured.** `quickcheck.MarkedOrder`'s `kept` checks the whole
preservation statement, `Kept`, for every step. The check covers the
first 600 steps of each of 300 seeds, on the first 60 events each side
shows, with skips erased. CI's `order` job: no failure.

## Where the spike stands

H is a body for of, empty, map, the switches, merge without a queue,
connect, the joiner and colds. It is a leaf per former for scan,
takeWhile, a bounded merge, and switch and exhaust as flatMaps. The order
the preservation half consumes is local: `Order` is a shape fact plus
per-frame race facts. The pick discharges the race facts from H, and a
rise carries them by definition. The connect's feed needs no pairwise
fact once the engine makes the meaning's choice. `rise-src-nx` is a body
over grid-free leaves, and `Kept` holds on every measured step. Next:
`limited-sides`.
