# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

#### THE WORLD INVARIANT

Open for the operators that place rows of their own: a timeline's ticks,
a joiner's lanes, takeWhile's failing value, a rejoined hot. Settled by
bodies, or a program whose reading leaves its world.

Members: `flatMap-inv`, `takeWhile-inv`, `cold-inv`, `lawful-hot`.

#### THE JOINERS WITHIN THE BOUND

Untried: a lane subscribed at a world position is admissible, and its
bound is at least the outer's, uniformly in the lane. Settled by bodies.

Members: `flatMap-ne`.

## Tier 0 — the emission set carries the theorems

**Port:** Main restated over the emission set; `adequacy/` and `simultaneous/` ported to it; no old-denotation use left.

### Ledger

#### THE PORTED THEOREM

Untried: what the engine's run shows is what a reader of the emission set
meets. Settled by porting `adequacy/` onto the emission set under
`make port-check` until `make old-denotation` reads zero; what is left
is Tier 1.

Members: `adequacyᵀ`.

#### THE PORTED SPEC

Untried: the simultaneous spec read off the emission set's rows. Settled
by porting `simultaneous/` the same way.

Members: `left-to-rightᵀ`, `coherentᵀ`, `batchableᵀ`, `positionedᵀ`.

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### THE FLIGHT KEPT

Untried: a connect's body keyed under its source's environment entry, past
skips the source drops (`adequacy.Engine.Passed`); and where only the tail
is read, past the tail a dequeue grows. An outer's value, a subscribe
beginning a former, and a mark run each leave the hole's run in shape and
every frame above keyed against it (`adequacy.Engine.Above.Flight`). Settled
by the per-frame keys past a dropped skip.

Members: `body-keyed-drops`, `lane-begin-tail`, `outer-begin-tail`,
`begin-flight`, `run-flight`, `flight-load`.

#### THE KEYS KEPT

Untried: a node rewritten by a rise, a connect's begin, a mark run or an
unsubscribe keeps every node's positional facts (`adequacy.Engine.Keys`),
reading the event in flight from the flight; a joiner of a subject over
runs as an empty `of`: the subject ended before the joiner's position. Probed in kept-depth,
except a merge's mark. Settled by bodies, or a probe refuting a clause.

Members: `unsub-take-here`, `unsub-flat-here`, `unsub-conn-here`, `unsub-body-keyed`,
`rise-admit-keys`, `rise-outer-end-keys`, `rise-lane-end-keys`,
`rise-src-keys`, `rise-body-end-keys`, `begin-conn-keys`, `joined-over`,
`run-keys`.

#### THE ENDLESS SUBSCRIPTION

A subscription's cut trails its run and keeps any rules its run keeps,
finite or not: a limit over the finite case, once a truncation's cut
agrees as its run does. Settled when bodies, or refuted.

Members: `trailing-sub`, `reach-cut`.

#### THE FED MERGE

Refuted over any node: a merge interleaves its parts' relations, and a
lane it subscribes is related as its outer's value. Probed at every node by
`quickcheck.KeptDepth`. Settled when a body, or refuted.

Members: `fed-flat`.

#### THE FED TAILS

Probed at every node by `quickcheck.KeptDepth`: a run read through its tail,
fed the rest. An erased skip erases tail pins too, so the tails' heads need
not match; the configuration must keep erased pins out of a rested node.
Settled when bodies, or refuted.

Members: `fed-cut`, `fed-taken`, `fed-done`, `fed-ended`, `fed-shut`.

#### THE FED POSITIONS

Probed by `quickcheck.KeptDepth`: the body fed the rest, and each inner
source, come after each position asked of, and a hushed inner source leaves
nothing running. Settled when bodies, or refuted.

Members: `src-body-on`, `fed-body-on`, `fed-src-next`.

#### THE FRESH FEED

Probed by `quickcheck.KeptDepth`: a source subscribed fresh, a joiner, and a
defer's fresh source, fed the rest, relate as the fed source does; an inner
source fed the run is subscribed where its connect is. Settled when bodies,
or refuted.

Members: `fed-fresh`, `fed-join`, `defer-links`, `fed-sourced`.

#### THE SORTED TAILS

Probed: a lane's tail, at its flatMap's environment, is in position order;
a tape mid-play, an of part-way, an ended source and a run read through its
tail keep their shape. Proven only for a finite program's subscription
(`trailing-subᶠ`); nothing ties a state to a residual of its own
subscription. Settled when these are bodies or refuted.

Members: `lanes-sorted`.

#### THE SWITCH'S KILL

Untried: a lane a switch kills, switched off, leaves in the pool the tail the
live lane's meaning cuts to, and the pool's union is blind to the order the
kill reads the lanes in. Settled when `kill-pool` is a body or refuted.

Members: `kill-pool`.

#### THE STILL'S SUBTREE

One stored causality invariant (`Causal`), over every key to come; every
rise keying something new keeps it but a source's event feeding its
joiners. Open: a mark run's node already shy of what it plants where it
rises (an of's, a takeWhile's completion, a joiner's, a cold's); a
connect's source subscribed once its body is; a subscription headed and
alien to its environment; a begun lane's flatMap's other parts. Settled
when these are bodies, or refuted.

Members: `feed-causal`, `of-proper`, `take-shy`, `join-shy`, `cold-end`,
`cold-shy`, `src-fresh`, `sub-fresh`, `outer-begins-links`,
`outer-queues-links`, `outer-ignores-links`, `lane-begin-links`,
`outer-begun-sides`, `switch-begun-sides`, `lane-begun-sides`.

#### THE TAIL'S SKIP

Probed (`quickcheck.KeptDepth`'s closed-cut programs): a defer begun under a
frame reading only its tail still drops a skip at the root, through the pin
the connect's burst leaves. Whether every such skip is pinned, and a lift
carrying each skip with its pin. Settled when the lift is a body, or a
skipped step there is refuted.

Members: `defer-tail`, `outer-tail`, `lane-tail`, `stall-tail`, `close-tail`.

#### THE KEPT DEPTH

Probed: Kept is set-level; these keep the meaning at every depth: a silent
step drops leading skips or means the same (`quickcheck.KeptDepth`: a defer
begun drops several), a value step's leftover reaches all after it. Settled
when a depth-aware Kept dispatch proves both, or refuted.

Members: `silent-exact`, `value-ahead`.

#### THE VALUE'S PLACE

Untried: a value the engine shows is the ghost's least, unique at its
position, and both what the engine leaves and what the ghost leaves lie
strictly after it. Settled when the three are bodies or refuted.

Members: `value-past`, `ghost-out`, `ghost-end`.

#### THE ROOT STEP

Whether a step, its sources clear of it, keeps its parts placed: a flatMap's
admitted lanes; a defer's program, subscribed or fed. Settled when
`flat-within` is a body or refuted.

Members: `flat-within`, `defer-within`, `defer-fed`, `under-shown-connect`.

#### THE KEPT FRAMES

Each frame's or node's step keeps what the configuration means, up to what
it shows: the rises through an outer, lanes, a connect's source and body, a
joiner, a defer, an unsubscribe. Probed on the spike engine. Settled when
each is a body.

Members: `quiet-empty`, `lift-skip`, `unsub-rest`, `conn-unsub`,
`rise-outer-nx`, `rise-outer-cp`, `rise-lanes-cp`, `src-leads`, `fed-ghost`,
`rise-src-cp`, `rise-body-nx`, `rise-body-cp`, `join-nx`,
`defer-kept`, `env-ne`.

#### THE PICK

The search's found node leads every race above it, and shows out of no body
whose connect is over; a step keeps the tree in the fragment. Probed on the
spike engine. Settled when each is a body.

Members: `search-hit`, `search-won`, `found-own`, `frag-next`, `run-lead`.

#### THE HEADS

Each operator's state, read through the shuts that told it, heads no
earlier than its subscription, and a subscription's burst leaves nothing
earlier. Settled when each is a body.

Members: `sub-head`, `sub-bursts`, `scanS-head`, `takeS-head`, `limit-head`,
`switch-head`, `exhaust-head`, `fresh-src`, `src-next`, `src-atop`,
`body-src-atop`.

#### THE KEY ORDER

Keys are a strict order agreeing with positions. Believed unfoldings.
Settled when each is a body.

Members: `<ᴷ-trans`, `<ᴷ-irrefl`, `≮ᴷ-trans`, `at-<ᵖ`, `ext-≮`, `under-after`,
`deep-after`, `deep-nb`, `lost-at`.

#### THE LINK

An ascending record alike a program's events as a set is placed against
them, and the meaning's ticks never fall. Settled when both are bodies.

Members: `placing`, `ticks-up`.

#### STEP PARTS

Each node's step, alone, is its meaning's next event: the generators,
map/scan/take, a flatMap, an ended connect, a node fed or a body shut its
source's step, and the rest-likes. Untried; believed unfoldings. Settled when each is
a body.

Members: `after-map`, `after-scan`, `after-take`, `clear-take`,
`frames-after`, `burst-after`, `of-after`, `flat-skips`, `ended-skips`,
`feed-alikeⁱ`, `shut-alikeⁱ`, `defer-skips`, `rest-skips`, `union-skips`,
`bursting-skips`, `under-skips`, `first-defer`, `first-rest`, `first-union`,
`first-bursting`, `first-under`.

#### THE FLIGHT, READ

Untried, mechanical: what the frames above keep, and a run's shape, is read
alike off runs alike, and off the ghost as the whole tree's keys, a dead
lane's read only through what it leaves running. Settled by bodies.

Members: `rise-dead-keys`, `keyed-same`, `laneKeys-lanes`, `flatAt-rest`,
`cue-≈`, `ub-transport`.

#### A CANDIDATE IS A NODE'S KEY

Untried, mechanical: `seek` passes a node's own key up as it is or
shifted, so whatever every key shift-closed has its candidate has. Settled
by a body over `seek`'s mutual recursion.

Members: `cand-keys`.

## Tier 2 — the simultaneous spec

**The statement:** the simultaneous spec, stated over the denotation.

### Ledger

#### THE INSTANTS

Whether every position the fold builds lies under the subscribe frame or a
timer cascade, as `instantOf` reads it. Settled when `positioned` is a body
by induction over the fold.

Members: `positioned`.

## Tier 3 — the simultaneous spec, proven

**The proof:** Tier 2's statements, discharged over `adequacy`.

### Ledger

#### THE SPEC

Suspect fact: false of the placeholder elaboration, one name and no
protocol. Batches joined are the plain values, batches are the spec's
grouping, at every site and related environment. Settled when both are
bodies over the real operators.

Members: `left-to-rightˢ`, `batchableˢ`.

#### SOUND NAMES

Suspect fact: `Sound` (names lie in their instant, one name per instant)
is false of the placeholder's one name. Whether each real operator keeps it
and it survives limits. Settled when the per-operator facts are bodies.

Members: `coldˢ-sound`, `emptyˢ-sound`, `ofˢ-sound`, `mapˢ-sound`,
`scanˢ-sound`, `takeWhileˢ-sound`, `flatMapˢ-sound`, `connectˢ-sound`,
`defer-sound`, `sound-admissible`, `batched-sound`.
