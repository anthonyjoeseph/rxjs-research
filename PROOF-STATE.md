# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### THE SILENT RUN

Each skipped step (an outer value, a lane's completion under a queue, a defer
begun, a frame's stall or close) drops a leading skip at its hole; whether the
frames above pass it up: an outer frame, a connect's source (joiners' images
drop too), and every frame's `Pass` condition at a real configuration (a
hushed connect source leaves nothing running). Settled when these are
bodies, or refuted.

Members: `outer-begins`, `outer-queues`, `outer-ignores`, `outer-begins-pass`,
`outer-queues-pass`, `outer-ignores-pass`, `lane-begins`, `lane-begins-pass`,
`stall-pass`, `close-pass`, `defer-hole`, `defer-pass`, `outer-drops`,
`src-drops`.

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

Members: `search-hit`, `search-won`, `shape-next`, `run-lead`, `frag-flat`,
`frag-body`, `sides-link`, `limited-sides`.

#### THE HEADS

Each operator's state heads no earlier than its subscription, and a
subscription's burst leaves nothing earlier. Settled when each is a body.

Members: `sub-head`, `sub-bursts`, `scanS-head`, `takeS-head`, `limit-head`,
`switch-head`, `exhaust-head`.

#### THE KEY ORDER

Keys are a strict order agreeing with positions. Believed unfoldings.
Settled when each is a body.

Members: `<ᴷ-trans`, `<ᴷ-irrefl`, `≮ᴷ-trans`, `at-<ᵖ`, `ext-≮`.

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
