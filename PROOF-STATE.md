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

#### THE HEARD PIN

Probed: a hot row past a reader's subscription carried into its
instant (`PB`) has its annotated carrier past the elaborated
subscription. No field orders a `PB` carrier against the map, and one
read negatively is kept by `carry-grow` only given where grown points
lie. Settled by `PB` placed against the map, or a carrier past the
subscription by instant.

Members: `pb-order`.

#### THE ERASURE

Probed, unproven: at each approximant, each former's elaborated run
carries its plain one (`Carry`), extending an order embedding of
positions over its own worlds; the meaning is reached through
`never-lies`, never carried. Riskiest: the embedding past a former's
children, then a concat's queued lane. Settled when each former's leaf
is a body.

Members: `carry-connect`, `carry-flatMap`, `carry-cold`, `wrap-merge`, `wrap-concat`.

#### THE PROTOCOL

Untried: every emit is named for its own instant, one begin and one
value name per instant — the elaboration mints both per async value,
which is per instant; the subscribe mark sits once before every begin
with every value past it async; every value precedes the completion.
Settled when each is a body over the elaboration's layers.

Members: `named`, `one-name`, `one-value-name`, `sub-first`, `sub-one`, `sub-async`, `done-last`.

#### THE HELD STREAMS

Probed, unproven: every elaborated stream names its begins for their
instants, counts a route of its own instant under every row outside the
bursts it is exempt for, and keeps dead instants dead. Hardest:
flatMap's scan counters, true on every row probed, hand-offs and parks
included: each is the `idle` of what holds the routes, read on the
scan's run split onto that branch (`lane-run`, `lane-next`; a tracker's
split is owed). Then what each branch sent, a reader's joins and the
defer limit. The cold's runs (`cold-covered`) need its rows' order, not
their shape. Settled when each former's leaf is a body.

Members: `outer-current`, `lane-run`, `lane-next`, `lane-idle`,
`lanes-count`, `held-current`, `parked-live`, `live-current`,
`value-open`, `over-open`, `end-open`, `comb-shut`, `walk`,
`step-local`, `outer-sent`, `lane-sent`, `close-sent`, `m-ends`,
`lane-ends`, `close-ends`, `lane-named`, `lane-early`, `lane-late`,
`close-marks`, `scan-idle`, `comb-run`, `held-connected`, `held-lim`,
`held-top`, `held-next`, `held-⊥`, `held-takeWhile`, `cold-rows`,
`cold-covered`, `cold-shut`, `cold-idle`, `held-of`, `held-empty`.

#### THE NEXT ROW

Untried: past finitely many rows of a value's instant, the program
reaches another instant or its end, or makes no row — constructively.
Nothing decides the row after a position; `listed` decides those before
one. Settled when the next row past a position is decided by operator,
each timeline forcing to its next frame, `done` or `quiet`.

Members: `exits-bounded`.

#### THE FINITE REST

Untried: past a zero count only finitely many rows of the instant last
begun remain — a route is held while its instant can still make a row.
Settled when each is a body: connect's rows beyond its body's (bursts,
echoes), the combinator scan's, a cold's.

Members: `cold-rest`, `scan-rest`, `conn-rest`.

#### THE RELEASE

Untried: the batcher releases exactly at the protocol's marks — past
the last value with nothing held, a mark past it released it, of one of
four kinds; a held batch is released by marks before the run leaves its
instant. Settled when each is a body over `Walk`'s tally and the
protocol.

Members: `release-at`, `release-on`, `done-end`, `sub-rest`.

#### THE PASS

Untried: a run meets on to every visible row up to one with finitely
many rows before it. `listed`, `Reaching.reach` and `run-det` are each
proven; open is the row at the bound itself, which a listing before it
omits. Settled when it is a body over them.

Members: `pass`.

#### THE BATCH RANK

Untried: a batch leaves within its own instant, at the rank its values
carry. Needs the layers' positions to keep instants, and the release
mark to sit in the instant it releases. Settled when `batch-rank` is a
body over the layers and the release protocol.

Members: `batch-rank`.
