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

#### THE NEXT ROW

Scouted, unproven: past a value whose instant has finitely many rows
left, decide whether a proper row of another instant follows. Classically
trivial; constructively nothing decides it: `listed` decides only the rows
before a position, the simulation only the visible ones. Settled by a
computable next row (the machine, through a simulation of every row), or
by `Over` asking only that the instant's proper rows past the value be
finitely many, classically the same (Anthony's question).

Members: `exits-bounded`.

#### THE DEAD PIN

Untried: a takeWhile keeps a source pin past its failure, while its
source's rows there are hidden, so the source is never listed up to the
pin. Needs the source's early-connect pins listed over a region (an
early cover). Settled when the leaf is a body.

Members: `take-pin-past`.

#### THE CONNECT'S CARRY

Probed, unproven: the connect's rows carried from its body's carry and
its annotated source's. Each subterm is listed before the other's image
by `cover`; open: the same before a LATE carrier, and a pin, alive or
dead, carried from whichever subterm made it. Settled when each leaf is
a body.

Members: `conn-img¬¬`, `conn-shown`, `conn-place`, `conn-whole`, `conn-pinned`, `conn-σ-late`, `conn-σ-ended`, `conn-β-late`, `conn-echo-row`, `conn-src-carrier`, `conn-heard-home`, `conn-src-home`.

#### THE COVER

Untried: a carry lists its elaborated run before a point its carriers
follow, from its plain run listed and alive before the matching point.
Spins, defers and scans carry it through; open per producer: the told
run, the take, a read, a reader, the connect. Settled when each is a
body.

Members: `told-cover`, `take-cover`, `read-cover`, `reader-cover`, `conn-cover`.

#### THE ERASURE

Probed, unproven: each other former's elaborated run carries its plain
one (`Carry`) along an order embedding; the take moves the end under the
completion mark. Settled when each former's leaf is a body.

Members: `carry-flatMap`, `carry-cold`, `wrap-take`.

#### THE BATCH RANK

Untried: a batch leaves within its own instant, at the rank its values
carry. Needs the layers' positions to keep instants, and the release
mark to sit in the instant it releases. Settled when `batch-rank` is a
body over the layers and the release protocol.

Members: `batch-rank`.

#### THE RELEASE

Untried: the batcher releases exactly at the protocol's marks — past
the last value with nothing held, a mark past it released it, of one of
four kinds; a held batch is released by marks before the run leaves its
instant. Settled when each is a body over `Walk`'s tally and the
protocol.

Members: `release-at`, `release-on`, `done-end`, `sub-rest`.

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

#### THE FINITE REST

Untried: past a zero count only finitely many rows of the instant last
begun remain — a route is held while its instant can still make a row.
Settled when each is a body: connect's rows beyond its body's (bursts,
echoes), the combinator scan's, a cold's.

Members: `cold-rest`, `scan-rest`, `conn-rest`.

#### THE PROTOCOL

Untried: every emit is named for its own instant, one begin and one
value name per instant — the elaboration mints both per async value,
which is per instant; the subscribe mark sits once before every begin
with every value past it async; every value precedes the completion.
Settled when each is a body over the elaboration's layers.

Members: `named`, `one-name`, `one-value-name`, `sub-first`, `sub-one`, `sub-async`, `done-last`.

#### THE PASS

Untried: a run meets on to every visible row up to one with finitely
many rows before it. `listed`, `Reaching.reach` and `run-det` are each
proven; open is the row at the bound itself, which a listing before it
omits. Settled when it is a body over them.

Members: `pass`.
