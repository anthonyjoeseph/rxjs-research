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

#### THE COMBINED SCAN

The combined scan's record is written: a lanes' row re-emitted at the
lane branch's reader, the flatMap's end at the `nothing` past the last
of the three branches' ends (probed, kind `whole`). Untried: its fields,
the scan emitting nothing but marks besides. Settled by bodies.

Members: `cb-corr`, `cb-φ-agree`, `cb-back`,
`cb-back-put`, `cb-elab-causal`, `cb-stable←`,
`cb-stable-put`, `cb-stable-lead`, `cb-elab-all`, `cb-func*`,
`cb-flat*`, `cb-cons*`,
`cb-pin-after*`, `cb-pin-stable`.

#### THE FLATMAP'S ORDER FACTS

Untried: the whole flatMap's rows carry the order facts, each row a
source or lane row imaged along its stream's map through the layers.
Settled by its body.

Members: `flatmap-order`.

#### THE SWITCH

The switch's record is the merge's map over every value's lane. Untried:
a cut lane's rows unshown alike, its pins kept alike, its end shown at
the same `done`. Settled by bodies, or a lane cut at one side's row only.

Members: `sw-corr`, `sw-φ-agree`, `sw-in-bk`, `sw-pb-few`, `sw-back`,
`sw-put-up`, `sw-back-put`, `sw-elab-causal`, `sw-stable←`,
`sw-stable-put`, `sw-stable-lead`, `sw-elab-all`, `sw-func`, `sw-func*`,
`sw-flat`, `sw-flat*`, `sw-cons`, `sw-cons*`,
`sw-after-φ`,
`sw-pin-after*`, `sw-pin-stable`.

#### THE EXHAUST

The exhaust's record is the merge's map over the lanes the plain
exhaust runs. Untried: the elaborated exhaust runs the same lanes,
though its lanes end at their end images. Settled by bodies, or a value
run on one side only.

Members: `ex-corr`, `ex-φ-agree`, `ex-in-bk`, `ex-pb-few`, `ex-back`,
`ex-put-up`, `ex-back-put`, `ex-elab-causal`, `ex-stable←`,
`ex-stable-put`, `ex-stable-lead`, `ex-elab-all`, `ex-func`, `ex-func*`,
`ex-flat`, `ex-flat*`, `ex-cons`, `ex-cons*`,
`ex-after-φ`,
`ex-pin-after*`, `ex-pin-stable`.

#### THE BOUNDED MERGE

The bounded merge's record is written: lanes enumerated level by level,
a queued lane's record had from the lane it waited on, at its end, and
subscribed under that end's image (probed, kind `lane-sub`). Untried:
its fields, the queue's state a run's. Settled by bodies.

Members: `cc-corr`, `cc-φ-agree`, `cc-in-bk`, `cc-pb-few`, `cc-back`,
`cc-put-up`, `cc-back-put`, `cc-elab-causal`, `cc-stable←`,
`cc-stable-put`, `cc-stable-lead`, `cc-elab-all`, `cc-func`, `cc-func*`,
`cc-flat`, `cc-flat*`, `cc-cons`, `cc-cons*`,
`cc-after-φ`,
`cc-pin-after*`, `cc-pin-stable`.

#### THE PLAIN MERGE

The merge's record is written: lane rows through `laneˢ`'s reader and
`counted`'s emit, a value's marker at its elaborated value's, the
source's end at the later of its own and the trigger's. Visible images
probed (`make table-check`, kind `core`); skip images and puts untried.
Settled by bodies.

Members: `mg-corr`, `mg-φ-agree`, `mg-in-bk`, `mg-pb-few`, `mg-back`,
`mg-put-up`, `mg-back-put`, `mg-elab-causal`, `mg-stable←`,
`mg-stable-put`, `mg-stable-lead`, `mg-elab-all`, `mg-func`, `mg-func*`,
`mg-flat`, `mg-flat*`, `mg-cons`, `mg-cons*`,
`mg-after-φ`,
`mg-pin-after*`, `mg-pin-stable`.

#### THE CLOSER AND THE SHARE

Each record is its body's, the connect showing its body's rows as they
are and its source's only as pins and skips. Untried: the fields.
Settled by bodies.

Members: `cz-corr`, `cz-back`,
`cz-back-put`, `cz-elab-causal`, `cz-stable←`,
`cz-stable-put`, `cz-stable-lead`, `cz-elab-all`, `cz-func*`,
`cz-flat*`, `cz-cons*`,
`cz-after-φ`,
`cz-pin-after*`, `cz-pin-stable`.

Members: `sr-corr`, `sr-back`,
`sr-back-put`, `sr-elab-causal`, `sr-stable←`,
`sr-stable-put`, `sr-stable-lead`, `sr-elab-all`, `sr-func*`,
`sr-flat*`, `sr-cons*`,
`sr-after-φ`,
`sr-pin-after*`, `sr-pin-stable`.

#### THE BACK FACT

A cut whose elaborated table agrees up to a row's image agrees up to the
row, and a put moves between cuts agreeing up to its row or its place:
what lets the erasure read preimages at the cut settling an image.
Probed at the root (`make table-check`, kind `back`); proven for of,
spin, map, scan, defer. Settled by bodies, or a cut holding an image
but not its row.

Members: `walk-back`, `take-back`, `take-put-up`, `take-back-put`.

#### THE CONNECT

The connect's record is written: body rows along the body's map, source
rows one label down at their annotated image. Untried: its field leaves,
the source's hot (`conn-hot`), an old hot cutting the new alike
(`conn-old-cut`); the first former making pins, so `ct-pin-stable`.
Settled by bodies.

Members: `conn-hot`, `conn-old-cut`, `conn-order`, `ct-corr`, `ct-φ-agree`,
`ct-in-bk`, `ct-pb-few`, `ct-back`, `ct-put-up`, `ct-back-put`, `ct-elab-causal`, `ct-stable←`, `ct-stable-put`,
`ct-stable-lead`, `ct-elab-all`, `ct-func`, `ct-func*`, `ct-flat`,
`ct-flat*`, `ct-cons`, `ct-cons*`,
`ct-after-φ`, `ct-pin-after*`,
`ct-pin-stable`.

#### THE ORDER FACTS

Probed (`make table-check`, every uncut subterm), unproven: each
former's rows carry the record's order facts (`Rest`): linked to their
images, cutting every hot in scope alike up each creator chain. A leaf former's rows lie at steps of timers it created
at its subscription; a one-to-one former's are its child's. Settled by
bodies, or a row whose creator chain is cut unlike its image's.

Members: `cold-order`, `of-order`, `spin-order`, `map-order`,
`scan-order`, `take-order`, `defer-order`.

#### THE FINITE REST

Untried: past a zero count only finitely many rows of the instant last
begun remain. A cold needs no run: one step makes finitely many rows.
Connect and the combinator scan can loop synchronously, so theirs need
the count: a route is held while its instant can still make a row.

Members: `cold-step-few`, `scan-rest`, `conn-rest`.

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

#### THE BATCH RANK

Untried: the batcher keeps the elaborated run's instants, an `each`
over a `scan` adding rows only within an instant of its source, and a
batch leaves in an instant holding a value of its name.

Members: `batch-home`, `batch-instant`, `elab-instant`.

#### THE RELEASE

Untried: the batcher releases exactly at the protocol's marks. Past the
last value with nothing held, a mark released it: a begin of another
instant, over or last stop (batcher state is `cnt` once subscribed), the
completion, or the subscribe mark, whose values lie in the frame. A held
batch is released before the run leaves its instant.

Members: `release-at`, `release-on`, `done-end`, `sub-rest`.

#### THE PROTOCOL

Untried: carried emits are named for their instant (a run reaching the
row stamps it with the count's name, `Held.covered`, once `stamps-of`
sits below this); one value name per instant; the subscribe mark sits
once, before every begin, every value past it async, and every value
precedes the completion.

Members: `named-carried`, `named-sub`, `named-done`, `one-value-name`, `sub-first`, `sub-one`, `sub-async`, `done-last`.

#### THE TOP

Untried: the program carried through the told run, the merge and take
with the completion mark, and the restamp. The closed run owes that
the program never emits a completion mark. Settled by bodies.

Members: `told-rel`, `closed-rel`, `stamped-rel`.

#### THE COLD'S ROWS

The rewrite: the elaborated cold's table is its rows written out
(`CRow`); the top merge, the scan, its merge, the concat's schedule and
each render are matched. Untried: the
rows are functional, flat, causal across cuts. Settled by bodies, or a
listed row `CRow` lacks.

Members: `rows-func`, `rows-flat`, `rows-causal`, `rows-cons`.

#### THE COLD'S WALK

The rewrite: the plain cold's cuts, renamed onto the elaborated
cold's, keep order, instants and kinds. Untried; each is about one
walk of one timeline. Settled by bodies.

Members: `walk-past`, `walk-under`, `walk-end`, `walk-before`,
`walk-apart`, `walk-ren→`,
`walk-ren←`, `walk-kind`, `walk-func`, `walk-flat`, `walk-agree`, `walk-cons`,
`walk-all`, `walk-alone`, `φ-mono`, `φ-inst`, `φ-home`, `φ-after`,
`φ-back`.

#### THE CUT ARITHMETIC

Untried, order arithmetic: the body's subscription cuts the source's
alike up the link, and a cut survives a label under a row not over it.

Members: `cut-body`, `lvl-sub`, `past-src`.
