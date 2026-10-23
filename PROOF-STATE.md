# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 0 — the port

**Port:** the old `adequacy/` tower carried to the state tree in `port/`, old names only (`make port-check`).

### Ledger

#### THE STRONG CARRIER

Untried: whether the heap machine's re-entry invariant has a reading on the
state tree, whose nodes are addressed by path, not by heap cell. Settled
when `Strong` is a ported body that `strong-hop` and `measure` go through,
or the old body is shown not to port.

Members: `Strong`, `strong-begin`, `strong-sane`, `strong-hop`, `measure`.

#### THE WALK

Untried: whether the old well-configuration walk carries to the state tree's
step. Settled when `WellMach` is a ported body and `preserve` goes through.

Members: `WellMach`, `preserve`, `begin-well`.

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

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
