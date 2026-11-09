# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

## Tier 1 — the instant is a datum

**The instant is a datum:** the subscribe frame, or one async emission (`cascade t e l`), carried in the position; everything green over it.

### Ledger

## Tier 2 — the elaboration

**The elaboration:** `elaborate` makes `make spec-check` green: no seed refutes the batches joined, the grouping by name, or names agreeing with instants.

### Ledger

## Tier 3 — the simultaneous spec

**The spec:** the batched run, each batch stamped by its instant, is the spec's grouping of the plain run, each value stamped by its instant.

### Ledger

#### THE ERASURE

Probed, unproven: the elaborated run, marks dropped, is the plain run
stamp for stamp — the elaboration adds no instant, and both count the
subscribe frame — with an instant over on one side over on the other,
and completing together. Switch, exhaust and the bounded queue are the
real cases. Settled when each is a body by operator.

Members: `erases`.

#### THE PROTOCOL

Untried: every emit is named for its own instant, one begin and one
value name per instant — the elaboration mints both per async value,
which is per instant; the subscribe mark sits once before every begin
with every value past it async; every value precedes the completion.
Settled when each is a body over the elaboration's layers.

Members: `named`, `one-name`, `one-value-name`, `sub-first`, `sub-one`, `sub-async`, `done-last`.

#### THE HELD STREAMS

Untried: every elaborated stream names its begins for their instants,
counts a route of its own instant under every row outside the bursts it
is exempt for, and keeps dead instants dead. Hardest: flatMap's scan
counters (`lanes-current`, `parked-current`): each is the `idle` of
what holds the routes, the lanes' and the connects' in scope, read at a
row of the scan's source; that needs a run of the source projected onto
each branch's run. Then `m-rows`, a reader's joins and the defer limit.
The cold's runs (`cold-covered`) need its rows' order, not their shape.
Settled when each former's leaf is a body.

Members: `outer-current`, `lanes-current`, `held-current`,
`parked-current`, `value-open`, `over-open`, `end-open`, `comb-shut`,
`walk`, `step-local`, `m-rows`, `lane-ends`, `close-ends`, `lane-named`,
`lane-early`, `lane-late`, `close-marks`, `scan-idle`, `comb-run`,
`held-connected`, `held-lim`, `held-top`, `held-next`, `held-⊥`,
`held-takeWhile`, `cold-rows`, `cold-covered`, `cold-shut`,
`cold-idle`, `held-of`, `held-empty`.

#### THE RELEASE

Untried in this vocabulary: the batcher holds nothing exactly where the
run's last instant is over — no value of it left past its last value, by
position, and the run leaving it. The bridge from the batcher's routes
to `Over` is open both ways. Settled when both are bodies over `shut`
and the protocol.

Members: `flush-closes`, `releases`.

#### THE BATCH RANK

Untried: a batch leaves within its own instant, at the rank its values
carry. Needs the layers' positions to keep instants, and the release
mark to sit in the instant it releases. Settled when `batch-rank` is a
body over the layers and the release protocol.

Members: `batch-rank`.

#### THE RANKS

Untried: a met run has its ranks, and rows of one instant share a rank
while rows of two do not. A rank cannot be computed from `Few`: its
cover may hold positions with no row. Settled when these are bodies over
`rooted`, the instant interval and a way to list a run's instants.

Members: `ranks-x`, `ranks-b`, `instant-rank`, `rank-instant`.
