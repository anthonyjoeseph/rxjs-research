# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### THE ERASURE

Refuted for a skip or a pin erased out of order (`adequacy.Engine.Erase`'s
`Erase`, `Eraseᵀ`); restated: each erased one comes no later than the other's
next. A merge so fed runs so erased (`adequacy.Engine.Merge`). Refuted at a
connect fed any source; restated over a source subscribed where the connect
is (`Sourced`). Open: whether that suffices. The burst pins the source's
events inside the subscription, then its tail; an erased one must lead the
other's next pin, and a tail may sit before a skip that marks it. Settled
when `body-⊒` is a body, or refuted again.

Members: `body-⊒`.

#### THE SILENT RUN

Refuted as one dropped skip (`quickcheck.KeptDepth`: a lane joined after its
source's skip sees a later skip erased); restated: a skipped step drops its
hole's leading skips and erases none or more past them. Open: each live
source's link, its body fed the source's skips dropping and erasing its own,
and a defer's fresh source among them. Settled when these are bodies, or
refuted again.

Members: `src-fed`, `src-body-on`, `defer-links`.

#### THE CLOSED LANE

Untried: a lane completing under a closed frame. The race that picked it
still ran, but a closed frame's candidates need not be its parts' heads, so
the lane's end may not lead them. Settled when `lane-begins-shut` is a body,
or refuted (then `lane-begins` reads the open frame `lane-drop` reaches).

Members: `lane-begins-shut`.

#### THE SORTED TAILS

Probed: a lane's tail, at its flatMap's environment, is in position order;
a connect's source runs in order, its tail trailing it. Both are proven only
for a finite program's subscription (`trailing-subᶠ`); nothing ties a lane's
or a source's state to a residual of its own subscription. Settled when
these are bodies or refuted.

Members: `lanes-sorted`, `src-trails`, `body-src-trails`.

#### THE SWITCH'S KILL

Untried: a lane a switch kills, switched off, leaves in the pool the tail the
live lane's meaning cuts to, and the pool's union is blind to the order the
kill reads the lanes in. Settled when `kill-pool` is a body or refuted.

Members: `kill-pool`.

#### THE STILL'S SUBTREE

Untried: a still skip leads every race above it past each live source's
skips: nothing above is due under the skip's position. Both what the search
finds (`Apart`; `quickcheck.KeptDepth` checks every absorbed configuration)
and the skip a value or a lane's end leaves just past itself, where the race
`Won` records only the shifted key, and the lane a value or an end begins,
whose frames above must pass every skip under its position. Settled when
these are bodies, or refuted.

Members: `apart-next`, `won-src`, `outer-begins-links`, `outer-queues-links`,
`outer-ignores-links`, `lane-begins-links`, `outer-begun`, `switch-begun`,
`lane-begun`.

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

#### THE WALK

Untried: the old well-configuration invariant was a well heap over the CPS
machine's states, so a state-tree `WellMach` is unwritten. Settled when it is
a definition and `preserve` a body or refuted.

Members: `WellMach`, `preserve`, `begin-well`.

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
`rise-src-cp`, `rise-body-nx`, `rise-body-cp`, `join-nx`, `joined-closed`,
`defer-kept`, `env-ne`.

#### THE PICK

The search's found node leads every race above it, and a step keeps the tree
in the fragment. Probed on the spike engine. Settled when each is a body.

Members: `search-hit`, `search-won`, `found-own`, `shape-next`, `run-lead`,
`frag-flat`, `frag-body`, `sides-link`, `limited-sides`, `outer-link`,
`body-link`.

#### THE HEADS

Each operator's state heads no earlier than its subscription, and a
subscription's burst leaves nothing earlier. Settled when each is a body.

Members: `sub-head`, `sub-bursts`, `scanS-head`, `takeS-head`, `limit-head`,
`switch-head`, `exhaust-head`, `fresh-src`, `src-next`, `src-atop`,
`body-src-atop`.

#### THE KEY ORDER

Keys are a strict order agreeing with positions. Believed unfoldings.
Settled when each is a body.

Members: `<ᴷ-trans`, `<ᴷ-irrefl`, `≮ᴷ-trans`, `at-<ᵖ`, `ext-≮`, `under-after`.

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
