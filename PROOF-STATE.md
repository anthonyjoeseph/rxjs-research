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

#### CONNECT: THE ELABORATED SOURCE ROWS

Untried: the source positions behind the elaborated connect's source
rows under a bound's image are listed. Risk: past the body's end the
source may hide infinitely many rows before a kept pin, and may pin
past its own end, so its raw rows are listed only up to the body's end
and its pins past it only as late pins, lifted through the annotation's
owners. Settled when `src-rows` is a body over the source's raw
simulation up to the body's end, its late pins, and the owners.

Members: `src-rows`.

#### THE LATE PINS

Untried: a run lists its elaborated pins of subscriptions before a bound
wherever the plain such pins and rows are. Risk: the reader's and the
annotation's pins trace to plain rows only through joins and owners,
and the connect's through the source's late pins, recursively. Settled
when each is a body over its run's own carriers.

Members: `ann-late`, `conn-late`, `reader-late`, `late-f`.

#### CONNECT: THE MAPS

Untried: the source's map, the three pairs and the body's map are one
embedding, fresh at each pair; each lies in its own pair's worlds, none
under the other's rows, none under a source row. Settled when each is
a body over the simulations' locality and freshness.

Members: `joins-σ`, `joins-sub`, `emb-s`, `fresh-s`, `nh-s`, `joins-b`,
`emb-b`, `fresh-b`, `apart-b`, `nh-b`, `below-b`, `below-b′`, `below-s`,
`below-s′`, `body-s`, `src-b`, `pairs-none`.

#### FLATMAP: THE RELAY'S LISTING

Probed: `lane-row→` is a body, bounded; the lane's rows before its
carrier are listed by its simulation up to the row (`lane-at`). Open:
the relay's input listed the same way — the outer's, every lane's and the
trackers' rows before it — and each scan's forward step a body over
`foldᵈ`. Risk: the trackers read hots, listed only by their own runs.
Settled when `relay-at` is a body over the sims up to the row.

Members: `relay-at`, `few₂`, `relay-fwd`, `lane-fwd`.

#### FLATMAP: THE DECISIONS

Probed: read back, every elaborated lane value is a plain running lane's,
uncut; read forward, each decision is taken up to the bound. Open: an
exhaust's run and a switch's cut, read forward, and a lane's end, read
both ways. Risk: each moves along other values' carriers, simulated only
up to the bound. Settled when each is a body over `run←` and the outer's
simulation up to the row.

Members: `ex-run→`, `cut-sw→`, `lane-end←`, `lane-end→`.

#### FLATMAP: THE LANE BOUND

Untried: a running lane's rows and hots are listed up to the flatMap's
bound, or a switch's next value. Risk: a switched-out lane may run on
unlisted past its cut. Settled when each is a body over the cut and the
flatMap's listing.

Members: `lane-env`, `lane-listed`.

#### FLATMAP: THE BOUNDED MERGE

Untried: a bounded merge's lanes start at its schedule's starts, read
off the same ends on both sides. Settled when `sim-bounded` is a body
over the unbounded joiners' lanes.

Members: `sim-bounded`.

#### FLATMAP: THE MAPS

Untried: the outer's and every lane's subscription pair lie alone in
their worlds, admissible, the lanes' hots lawful; the joined map is an
embedding, local, under no plain row, keeping the joins, one carrier a
row. Settled when each is a body over the pieces' locality.

Members: `ok-o`, `fresh-o`, `emb-l`, `fresh-l`, `joins-l`, `good-l`,
`ok-l`, `ok-l′`, `nh-l`, `flat-img`, `local-f`, `emb-f`, `none-f`,
`flat-joins`.

#### FLATMAP: ENDS, REACH AND LISTING

Untried: the ends correspond; a relayed lane value is reached; the
outer's rows, and the elaborated rows, up to a bound are listed; a
lane value is anchored. Settled when each is a body.

Members: `flat-end→`, `flat-end←`, `lane-reach`, `outer-listed`, `u-upto`,
`anchor-v`.

#### THE SIMULATION: DECISIONS

Untried: a take's failure, a scan's state and a map's values transfer
both ways along the map; the closed run beside its marks, restamped,
simulates the program from the root. Settled when each is a body.

Members: `sim-takeWhile`, `sim-scan`, `restamp-sim`.

#### THE SIMULATION: SOURCES

Untried: a cold's, an of's and an empty's elaborated rows carry their
plain rows; a defer's guard and bottom carry theirs. Settled when each
is a body.

Members: `sim-cold`, `sim-of`, `sim-empty`, `sim-⊥`, `sim-next`.

#### THE CONSUMPTION

Untried: a table image of a plain row agreed with is the approximant's,
with few rows before it; a late placement too; and agreement crosses
back from the elaborated side. Settled when each member is a body over
`sim-root`'s simulation and the tables.

Members: `img-row`, `img-few`, `put-row`, `causal←`.

#### THE TABLES

Untried: the plain and elaborated tables of one cut correspond along one
position map and one late placement. Settled when `tables` is a body
over per-operator simulations.

Members: `tables`.

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
`cold-covered`, `cold-shut`, `cold-idle`, `held-of`, `held-empty`,
`held-trigger`.

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
