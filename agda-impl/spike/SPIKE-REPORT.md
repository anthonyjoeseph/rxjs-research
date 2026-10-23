# Spike: a pointer-free engine and a frame-wise adequacy invariant

Question: is the step × field grid intrinsic to adequacy, or an artifact of
how the engine stores its state?

## Step 1 — inventory: what carries a reference

The engine's configuration (`operation.AbstractObservable.Conf`) and the
pure driver (`operation.PureObservable.Mach`) hold six kinds of
cross-reference, each of which names one part of the state from another:

| Reference | Where | Names | Read by |
| --- | --- | --- | --- |
| job stack `rets` | Conf | a node by path, plus a tag and a resume position | `stepAt absorbed` (`downs q`) |
| joiner list `CS.subs` | connect node | joiners by path relative to the binder | `feedOn` (`downs q`) |
| feed stack `CS.feeds` + `feeding js` jobs | connect node + stack | the value being fed, paired by POSITION IN TWO STACKS with the joiners still to feed | `fedUp` (joiner reads its binder) |
| timers | Mach | a cold leaf by path | `fire` |
| turns | Mach | a cold leaf by path, plus a stack DEPTH | `turned` compares `depthOf t` with `length rets` |
| cursor `pos` | Conf | the global position | everything that places an event |

The adequacy carrier (`adequacy.Strong.Carried`, 16 fields) splits the same
way:

| Class | Fields | Why each step must re-prove it |
| --- | --- | --- |
| content core | kernels, meets, ctlAs | — (these are the semantics) |
| denotation-only | sane, placed | — |
| node-local | ended, flags (all but `ns`), lingers | fold once over the tree (the Keep walks already do this) |
| cursor | behind, told, `queue.ahead`, sorted | every step that moves `pos` |
| stack pointers | owned, meaning (owing / feedsAt), `books.ticked`, sorted | every step that pushes, pops or reshapes the tree under a pointer |
| driver pointers | `queue.timed`, `books.turned`, CtlAs depth | every step that changes the depth or a leaf |
| joiner paths | `queue.joined`, meaning | every step that grows a body |

**The grid is (stack pointers + driver pointers + joiner paths + cursor) ×
(steps that change the shape).** Every fold so far has worked only on the
node-local row. The pointer rows cannot be folded, because a pointer
field's obligation at a step depends on two places at once: the node the
step rewrote, and the entry that names it.

Mapping today's Tier 1 risk groups onto those classes:

- **Pointer- or cursor-driven, removed by construction:**
  - THE JOB STACK and THE WALK (stack order and `WellMach`).
  - THE PLANTED END'S CARRIER (owned, queue, books at a take's end).
  - THE CUT AND THE FIRE (cut-owned, cut-meaning, cut-queue).
  - Most of THE PLANTED CLIMBS and THE LANDING CLIMBS: the cells that
    re-establish `owned`/`queue`/`books` after a push or a growth.
- **Pointer-free content, which remains in any design:**
  - THE TAKE'S JUMP: the cursor jump at a take. Its cursor half stays.
  - THE FLATMAP UNDER A SHUT.
  - THE LEFTOVER ACROSS A PLANT.
  - THE FLATMAP DRAINED.
  - THE SUBSCRIBE.
  - STEP PARTS.

Kill criterion ("the risk is mostly local"): **not met.** The two
top-ranked groups and the largest groups are pointer groups. The content
groups are real, but each is ONE obligation per operator, not a cell per
field.

## Step 2 — the pointer-free state, on paper

### The finding that makes it possible

Positions are execution order. That is `Events`' header: a position is a
path in the run's call tree, read in pre-order. A deleted spike
(`spike.StateTree3Order`, `git show c24a177e`) proved that the job stack
is a CHAIN of nested scopes. Each job's resume position encloses the scope
above it, and is ready from wherever the scopes above leave the run.

So the job on top of the stack is always the pending continuation whose
next event has the LEAST position. **The stack order is recoverable
structurally:** it is the position order the denotation already uses.
`Unfold`'s stepper picks its next event the same way (`sourceˢ`,
`unionˢ`, `beforeˢ`). That clears step 2's kill criterion.

### The design: marks on nodes, a least-key scheduler

Every continuation the stack holds today becomes a MARK stored on the node
that owns it. Each mark has a KEY: the position of the event it will make,
or `after p` (later than everything under `p`) for a silent one.

| Today (tag on the stack) | Mark on the node | Key |
| --- | --- | --- |
| `next i` at p | `ofS` keeps `(i , p)` | `p ++ [ix i]` (`p ++ [last]` when empty) |
| `att` at p | `cutS` keeps `p` until attached | `after p` |
| `attBody` at p | `connS` keeps `p` until the source is subscribed | `p ++ [ix 1]` |
| `att` (source) at p ++ [ix 1] | `connS` keeps it until the source is attached | `after (p ++ [ix 1])` |
| `owed` at p | `connS` keeps `p` | `after p` |
| `owedCp` / `owedCut` at p | `takeS` keeps the owed stage and `p` | `p ++ [last]` / `after p` |
| `feeding js` + `CS.feeds` + `CS.subs` + `fedUp` | each joiner keeps its OWN inbox of `(position, Ev)`, sorted; a feed walks the body once, as `Unfold.feed` does | the inbox head's position |
| timers | the cold leaf keeps its next frame's due time and creation position | `[ix due , sub from , ix 0]` |
| turns (play / finish, with depth) | the cold leaf keeps the frame it is playing: `u`, `i` | `u ++ [ix i]`, or the completion's position |

What disappears:

- the job stack;
- `CS.subs` and `CS.feeds`;
- `fedUp`, `rooted` and `downs` on a stored path;
- timers and turns;
- every depth comparison;
- every path stored in the state.

**The scheduler.** When the run is calm, find the node holding the
least-keyed mark, focus it, and resume it. This is a structural search,
and ties are broken by the first one found in pre-order. The only tie the
stack can produce is two nested connects whose bodies complete at the same
position. Both of their `owed` marks are silent teardowns, so the tie is
unobservable.

**The pure driver collapses to the engine.** Timers and turns are leaf
marks, so "play the jobs owed above the frame first" and "fire the next
timer when nothing is running" are both "run the least key". The clock is
the tick of the key being run.

**IO.** IO does not know positions today: it delivers at `[]` and uses the
stack depth to freeze the jobs owed before a cold's subscription.
Under the design, the IO driver, which is unproven and checked by the
oracle, manufactures positions:

- a cold delivering during its own subscription at `u` delivers at
  `u ++ [ix i]`;
- an asynchronous delivery starts a fresh cascade with nothing pending.

The depth freeze becomes "settle while the least key is below
`after u`". Every one of these is a list of labels compared
lexicographically, so all of it is portable to TypeScript.

### What adequacy becomes

The ghost is a FUNCTION of the configuration, read node by node, with no
lookup. `ofS (i , p) xs` reads as `ofᶜ p i xs`, a joiner's inbox as
`joinᶜ`'s list, and so on. The deleted spike's `spike.StateTree3Ghost`
computed the same thing, but through `jobsAt π rets` lookups. Here those
lookups are gone.

The invariant is frame-wise:

- **Head** (static, by structural recursion; no step involved): Unfold's
  next event position of `gh s` is the least event key in `s`.
- **Kept** (one obligation per step clause): stepping the focused node
  changes the ghost exactly as Unfold's step does at that node, up to
  skips. A `plug` congruence then lifts it through the context.

Neither statement names a second location. That is the pass condition
step 4 has to show in Agda.

## Step 3 — the engine, built beside today's

`operation.Marked` (with `operation.Key`, `operation.MarkedPure`,
`operation.MarkedObservable`) is the Step 2 design in Agda. The
configuration is `⟨ ctx , focus , mode , pos ⟩` over a typed zipper. Every
continuation the old engine kept elsewhere is a mark on the node that owns
it: the job stack, joiner paths, feed stacks, timers and depths. `search`
finds the least-keyed mark in the tree. Nothing in the state names any
other place in it.

- **Agreement with the old engine.** `quickcheck.MarkedDiff` compares the
  two pure engines on 400 seeds, the whole bug cache and the adversary
  cases. The comparison runs at typecheck time and is green.
- **Oracle.** The oracle has gained `marks` and `marks-io` columns. Their
  CI run on PR #334 is still in progress as I write this.
- **Not done: the TypeScript mirror.** Keys are lists of labels compared
  lexicographically and the search is a tree fold, so nothing in it needs
  Agda-only machinery. But it has not been ported. CLAUDE.md requires that
  port before the main tree builds on this engine.

## Step 4 — the invariant, assembled (`spike/MarkedGhost`, `spike/MarkedKept`, `spike/MarkedRace`)

**Shape of the top line.** `adequate o` gives both directions for every
program:

- **Soundness (`sound`):** whatever the machine shows, `meaning (subscribe
  o root)` shows. It is a real body. It walks the run and uses `kept` at
  each step.
- **Completeness:** the converse is one leaf, `shows-all`.

`kept` says that each step keeps what its configuration means, up to what
a run shows. It is a real body, dispatched three ways:

- by **mode**;
- then by the **one frame** a rise passes, the **one node** whose mark
  runs, or the **one former** a subscribe begins.

No case of it mentions a second location.

### Proven exactly, with no postulate under it

- **`lift-plug`.** A configuration focused anywhere means what the whole
  tree means, for all ten context formers. This is the frame
  decomposition the old development never had. There, each field had to
  be transported across each move by hand. Here it is one structural
  recursion over the context.
- **Every unary frame's rise:** map, scan and the takeWhile frame.
- **takeWhile's three outcomes** (`took-nx`: true, inclusive-false,
  exclusive-false). This is the acid test Step 2 named. The take's jump
  costs no postulate at all here, whereas it was a whole group in the
  old ledger.
- **Every subscribe:** of, cold, empty, map/scan/take/flatMap/connect
  begin, and a connect's source subscribed (`conn-src`).
- **Marks:** the cp and cut marks, the cut tear (`cut-rest`), and a
  leaf's emit, stall and close.
- **A flatMap lane's rise.** `rise-lanes-nx` is a body over
  `spike.MarkedRace.go-rise`. That is a per-frame denotation lemma, fully
  proven: a lane first among a merge's parts is the merge's next.

### Hidden invariants the bodies surfaced

All of them are now fields of `Inv`, not hypotheses.

- **Settled:** the focus of an absorbed configuration is never a pending
  node.
- **TakeFree:** a take frame above the focus is still free.
- **Opened** (inside `Wf`): a connect whose body is subscribed has not
  closed its source. Without it, the source frame's plug lemma is false.

Each one is a predicate on ONE node, or on one node and its two children.
None of them relates two distant places in the tree. That is the
qualitative change from the old `Carried` record, whose fields were
mostly cross-references.

### The order, done (`spike/MarkedFirst`, checked by `quickcheck/MarkedOrder` in CI)

The one global fact soundness needs, `lanes-first`, is now a **real
body**. It sits over an order invariant `Ord` that is a field of `Inv`
(`Inv = Base & Ord`). `Ord` names no frame and no pointer. It is a
predicate on the whole tree's keys and joiners at the configuration's
position `p`:

| Mode | `Ord` | CI (300 seeds, every configuration reached) |
| --- | --- | --- |
| subscribing, rising at `p` | **beyond**: no key earlier than `after p`; **live**: an untold joiner whose source's run is `end c` has `p < c` | green |
| absorbed at `r` | **past**: every key later than `at r`; **live** as above | green |

From `Ord`, `ahead` proves that every node's next event, and every
tail it would leave running, lies strictly after `p`:

- It is **one row per `St` constructor** (12 constructors), recursing
  into the children.
- The lanes, the outer and the pool are walked by `liveL-ahead`,
  `deadOne-ahead` and `pool-after`.
- A connect's source feeds its body's environment through
  `src-ahead` and `conn-ahead`.
- `first-lanes` then assembles a `First` for the rising lane against
  every sibling in its flatMap.

**It is not a grid.** Its leaves are one fact per stream function and
one about key order:

- `beyond-after`: a key not before `after p` is a position after `p`.
- `ahead-cold`, `take-head`, `go-ahead`, `beside-ahead`,
  `rejoin-after`, `sub-after`: each says that the stream function
  keeps "the head is after `p`".

All seven are statements about the denotation (`MonotonicList` and
`Unfold`) and the key order. **None mentions a step or a configuration.**

Two design facts the CI run settled:

- **`live` must depend on the position.** The first, position-free
  version ("an untold joiner's source has not ended") was refuted on
  many seeds. A live source about to complete already has the meaning
  `end c`.
- **Distinctness is not needed and is false.** Every `distinct`
  failure is a tie between two emission-free `after` keys: att/att,
  srcAtt/att, or owed/owed from nested connects or switches torn down
  at one position. Those keys make no event, so they cannot reorder an
  emission, and nothing in `lanes-first` reads distinctness.

### Postulates left on the soundness and adequacy path (25)

| Leaf | Module | Kind |
| --- | --- | --- |
| `beyond-after`, `ahead-cold`, `take-head`, `go-ahead`, `beside-ahead`, `rejoin-after`, `sub-after` | MarkedFirst | one per stream function / key order; no step |
| `rise-outer-nx/cp`, `rise-src-nx/cp`, `rise-body-nx/cp`, `rise-lanes-cp` | MarkedKept | one per frame with siblings; same shape as the proven `rise-lanes-nx` over `go-rise` |
| `unsub-rest`, `conn-unsub` | MarkedKept | one node's teardown vs `restᶜ` |
| `lift-skip` | MarkedKept | non-expansiveness through `up`, the kind already proven as `lift-≅` |
| `join-nx`, `joined-closed`, `defer-kept` | MarkedKept | one node's step each |
| `search-hit`, `quiet-empty` | MarkedInv / MarkedKept | `search` as a tree fold; static |
| `env-ne` | MarkedGhost | the ghost's environment |
| **`ord-next`** | MarkedInv | the order's preservation (see below) |
| **`shows-all`** | MarkedKept | completeness / progress |

`Base`'s preservation (`base-next`) is a **real body**, dispatched by
mode, then by the frame, node or former. Every clause is local. The
grid did not come back there.

### The kill test: `ord-next`, `rise-src-nx`, `unsub-rest`

The criterion: the test fails if any of the three needs an `Inv` field
that is neither a fold over nodes nor a comparison of keys against `p`,
or if any `ord-next` clause needs an argument of its own.

**It fails, at `ord-next`, before the clauses.** `spike/MarkedApart.agda`
refutes both candidate statements by evaluation (typechecks), at
configurations `Base` admits:

- `ord-next-false`: `ord-next` as postulated, over `Ord`.
- `apart-next-false`: `Ord` with `apart` added, the strengthening CI
  measured true on 300 seeds. CI measured it on reachable states. The
  proof needs it inductive over every state the invariant admits, and
  it is not.

The configuration is two lanes. One holds an `of` subscribed at `q`; the
other holds an `of` subscribed at `q ⊕ ix 1`. The first of's *next* key
is a **sibling** of its current one (`ix i` to `ix (suc i)`), not a
child, so running it lands on territory the second lane already holds.
Three node kinds key their future outside their current key's subtree:

- an `of` (its next index);
- a cold (its next frame, on a root-level timer cascade);
- a joiner (its next inbox entry, a key nobody can see yet).

What excludes these configurations in a real run is **provenance**: a
key under `q ⊕ ix 1` is made only by an event there, and only the first
of emits there. As an invariant, that is a zone per node (every key it
will ever make), with zones **pairwise disjoint**. A pairwise field is
what the criterion forbids. It is the grid's shape, read node × node.

Two things make it worse than a single extra field:

- **The zones are not intervals.** An of at index `i` owns
  `[at (q ⊕ ix i), after q)`. A cold owns a cascade *column* (every tick,
  under `sub` of its frame's end). A feed needs every joiner's join
  position distinct, and no zone covers that.
- **"Everything so far was made at or before `p`" is not a fact about
  the Conf's `p`.** That would be the key-vs-position form of
  provenance. But an `after`-mark (`attM`, `srcAttM`, `owedM`, `cutM`)
  moves the position *back* to the mark's own `p`. The fact needs a
  cursor key the engine does not carry. That is an engine change, which
  is free, but it is not this engine.

The leaves, analysed but not proven:

- **`unsub-rest` forces no `Inv` field.** Before an unsubscribe, a
  connect's source burst inside `srcAt` survives as tail pins
  (`burstOn`). After it, a torn-down cold is idle. Tails show only
  skips, so the leaf is "a hole showing nothing swaps for another
  showing nothing": a `≅`-congruence column, one fact per frame.
  - **Caveat:** that is false for a Zeno frame (infinitely many stalls
    inside `r`), whose skips starve a merge's siblings. Either frames
    carry a finiteness fact (a node fold), or it is a semantics
    question.
- **`rise-src-nx` forces two facts.** It needs `gh` of `Marked.feed` to
  match `Unfold.feed` of `gh`. `Marked.feed` feeds every live joiner by
  sorted insert; `Unfold.feed` feeds only joiners joined before the
  feed, by append. So:
  - **Every live joiner joined before `p`.** This compares joiner
    positions against `p`, but needs a mode split, because `p` moves
    back at `after`-marks.
  - **At a feed, every inbox entry is before the new one.** Insert is
    then append. Only scoping guarantees this: a body cannot reach its
    own source, so a source never emits under its own last emission.
    Scoping is invisible to `Ord`, so this is provenance again, between
    a source's zone and its joiners' inboxes.

### Coverage caveats

- `quickcheck.MarkedDiff` (old-engine vs marked-engine agreement) runs
  at typecheck time, but is not in Main's coverage. CI's `make agda` does
  not check it, so its last green is the one from Step 3.
- The spike modules are deliberately outside Main. `wiring-gate`
  reports them as unreachable, which is expected for a spike.
- The TypeScript mirror of the marked engine is still owed.

## Go / no-go

**NO-GO on this engine as the place the grid ends.** `kept` and `Base`
stay per frame and per node, and that half holds: the table's first five
rows below are unchanged. But the order half reintroduces a pairwise
invariant (zone disjointness), and its preservation is exactly where a
grid would grow: every clause's new zones, against every other node
kind's zones.

| Question | Answer | Evidence |
| --- | --- | --- |
| Is "keeps its meaning" (`kept`) per frame and per node? | **Yes.** It is a real body; no clause reads a second place | typechecks |
| Is the frame decomposition (`lift-plug`) provable? | **Yes**, outright, over all ten context formers | typechecks |
| Is takeWhile's jump (the acid test) cheap? | **Yes**, with no postulate | typechecks |
| Does the invariant's preservation rebuild the grid? | **No** for `Base`: `base-next` is a real body, every clause one node's fold | typechecks |
| Can the one global fact (`lanes-first`) be had without pointers? | **Yes.** It is a real body over `Ord`, through a 12-row `ahead` over 7 stream-function leaves | typechecks |
| Is `Ord` true? | **Yes**, at every reachable configuration | CI, 300 seeds |
| Is `Ord` (or `Ord` with `apart`) inductive? | **No.** Both are refuted at `Base`-admitted configurations; the missing fact is pairwise provenance | `spike.MarkedApart`, typechecks |

The open question is no longer the proof. It is whether provenance can
be made **local**: whether the engine can carry, per node, the territory
it owns, so that disjointness holds by construction rather than as an
invariant. Two candidates:

- **Keys relative to a node's own subscription position, never
  absolute.** The cascades are the obstacle, because a cold's later
  frames are rooted at the root.
- **A cursor key in the Conf**, with every node's next key derived from
  its current key and the cursor.

Neither is designed.

### What is left, ranked by risk

1. **Local provenance.** `ord-next` is false over the present `Inv`.
   The missing fact is pairwise zone disjointness. Either an engine
   change makes it local, or the order half carries a pairwise
   invariant.
2. **`shows-all` (completeness).** It has not been attempted. It needs
   a progress measure. The old tower had the same obligation, so this
   is not new risk, but it is unmeasured.
3. **The TypeScript mirror of `operation.Marked`.** It is owed before
   the main tree builds on this engine (CLAUDE.md). It is mechanical,
   because keys are label lists and the search is a tree fold.
4. **The 23 other leaves.** Each is one stream function, one frame
   with siblings (the proven `rise-lanes-nx` is the template), one
   node's step, or a static fact about `search`.

### What committing means

- Adequacy moves to `operation.Marked`.
- The Carried / Restage / Climbs tower and its 197-postulate PROOF-STATE
  (dominated by THE JOB STACK, THE PLANTED END'S CARRIER, THE CUT AND
  THE FIRE) is deleted.
- A new PROOF-STATE is written with the four groups above, ranked in
  that order.
- **Main and `Tree.agda` are untouched until you approve the Main
  rewiring.** The new top line would be `spike.MarkedKept.adequate`,
  renamed out of `spike/`.
