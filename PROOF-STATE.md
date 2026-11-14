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

#### THE JOINER'S DECISIONS

Untried: the elaborated joiner decides as the plain one. Each running
value is paired with the value its carrier reads, and back; its end is
joined and handed off where its partner's is, and the outer's end where
its partner's is. Open: exhaust's run reads the outer against lane ends
across the two maps; bounded's run read forward needs the environment
listed, which its statement lacks; its hand-off reads the queue; every
op's done reads all lanes' ends. Settled when each holds, or a
refutation names the op.

Members: `exhaust-runs`, `exhaust-runs⁻`, `bounded-runs`, `bounded-hand`, `bounded-hand-to`, `bounded-hand¬¬`, `pair-done`, `pair-done¬¬`, `end-done`, `end-done¬¬`, `outer-ends`, `ends⁻`.

#### THE JOINED LANES

Untried: a joiner over lanes carried into another's, its decisions
agreeing, carries its lane rows (`Joined`); a row is imaged through its
lane's carry from the lane's own listing. Open: whether the lanes' maps
embed jointly with the outer's (`joined-maps`), rows of two lanes, a
hand-off and the outer's end lying apart, a lane listed under its
environment's listing, and the fields read lane by lane. Settled when
each is a body.

Members: `joined-maps`, `joined-nest`, `lanes-apart`, `lanes-pb-apart`, `lane-listing`, `hand-apart`, `end-apart`, `hand-ext`, `end-ext`,
`join-pb-few`, `join-pb-past`, `join-img¬¬`, `join-place`, `join-live`, `join-whole`, `join-cover`, `join-bk`, `join-pinned`,
`img-reach`, `back-reach`, `end-reach⁻`, `join-from`, `into-lift`.

#### THE ERASURE

Probed, unproven: a flatMap's lanes and a cold's elaborated runs carry
their plain ones (`Carry`) along an order embedding. A lane ends under
its plain end's image, so a queued lane and the end keep the plain order
past dead pins; open: a lane through its frame (`lane-framed`), the
routing scan's reading, the two connects' bodies. Settled when every
member is a body.

Members: `lane-framed`, `lanes-routed`, `lanes-inner`, `lanes-closer`, `carry-cold`.

#### THE LATE WINDOW

Untried: a live pin has an in-order carrier, at or before the carrier
of every later live row, so it is listed as the plain row is (`cover`).
The take moves one under its failure, the told run by `δ`; open: the
connect's source pin, whose own carrier is late, and, in the told run,
a skip's carrier with no row, which the source's order does not reach.
Settled when each is a body.

Members: `conn-first`, `flat-first`, `told-skip`.

#### THE CONNECT'S CARRY

Probed, unproven: the connect's rows carried from its body's carry and
its annotated source's. Each subterm is listed before the other's image
by `cover`; open: the same before a LATE carrier, and a pin, alive or
dead, carried from its connect's own past by whichever subterm made it.
Settled when each leaf is a body.

Members: `conn-img¬¬`, `conn-shown`, `conn-shown-end`, `conn-place`, `conn-whole`, `conn-pinned↓`, `conn-σ-late`, `conn-σ-ended`, `conn-β-late`, `conn-echo-row`, `conn-src-carrier`, `conn-heard-home`, `conn-src-home`.

#### THE FLATMAP'S CARRY

Untried: the flatMap's rows carried from its lanes' carry and its
outer's echoes, as the connect's are from its body's and source's; a
lane row never shows where an outer row does. Open: each field past
that, an outer row's late carrier included. Settled when each is a body.

Members: `flat-src-live`, `flat-pb-past`, `flat-img`, `flat-img¬¬`, `flat-shown`, `flat-shown-end`, `flat-place`, `flat-whole`, `flat-pinned↓`.

#### THE COVER

Untried: a carry lists its elaborated run before a point its carriers
follow, from its plain run listed and alive before the matching point.
Spins, defers and scans carry it through; open per producer: the told
run, the take, a read, a reader, the connect. Settled when each is a
body.

Members: `told-cover`, `take-cover`, `read-cover`, `reader-cover`, `conn-cover`, `flat-cover`.

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
