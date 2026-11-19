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

#### THE ROOT'S CROSSINGS

A row exists only if no hang came first. One cut's pair orders only
that cut's rows, so neither crossing follows from it. `root-lead` is
suspected false at a hang inside a subscribe burst, which moves the
fault to `Erase.place`'s leading-row arm; `root-back` needs a pair
across cuts, a deeper row clear where its image is. Settled by a
leading row whose image a cut hangs before while a pin of its instant
is clear, or a cross-cut pair in `Rel`.

Members: `root-back`, `root-lead`, `root-real`, `root-real*`,
`root-φ-agree`, `root-late-agree`, `root-put-up`, `root-back-put`.

#### THE JOINS' HANGS

Untried: a join's boundaries are its outer's and each running lane's
before the lane's cut, bounded, and paired over its parts' pairs (a
pair over cross-part leaves is recoverable, see the merge's leaves).
Settled by bodies, or a lane hang the join does not keep.

Members: `mg-bd`, `mg-bd*`, `mg-bounded`, `mg-bounded*`, `mg-bcorr`,
`cc-bd`, `cc-bd*`, `cc-bounded`, `cc-bounded*`, `cc-bcorr`,
`sw-bd`, `sw-bd*`, `sw-bounded`, `sw-bounded*`, `sw-bcorr`,
`ex-bd`, `ex-bd*`, `ex-bounded`, `ex-bounded*`, `ex-bcorr`.

#### THE CONNECT'S HANGS

The connect's bounded is `Horizon.ConnB`'s and its pair `HorizonConn.ConnPair`'s,
each table read as `Connecting.ConnT` of its parts, the elaborated over
the annotated source. The body's pair cuts its source alike through
`Rest.bcorr-env`. Riskiest: a pinned or late source row is placed at its
image (`ct-src-img`), which the body's placements need; then the
annotated source's pair and the cross-part leaves. Settled by bodies,
or a late source row placed off its image.

Members: `ct-src-img`, `ct-src-hot`, `ct-src-bcorr`, `ct-conn→`, `ct-conn←`,
`ct-conn*→`, `ct-conn*←`, `ct-src-after`, `ct-src-held`, `ct-ann-bd*`,
`ct-ann-bounded*`, `ct-ann-after*`, `ct-ann-held*`,
`ct-φc-body`, `ct-φc-echo`, `ct-late-body`, `ct-late-echo`,
`ct-put-split`, `ct-img`, `ct-put-row`, `ct-gap-src`, `ct-gap-src*`,
`ct-held-src`, `ct-held-src*`, `ct-held-body`, `ct-held-body*`,
`ct-body-src`, `ct-body-src-put`, `ct-home→`, `ct-home←`, `ct-end→`,
`ct-end←`, `ct-rows-after`, `ct-rows-after*`, `gap-c`.

#### THE HOT READER'S HANGS

A reader is bounded by its hot's boundaries through `Horizon.RejoinB`,
its table read as `Rejoin` at the subscription. Untried: that reading,
the elaborated reader's boundaries and their pair. Settled by bodies,
or a reader row the rejoined hot lacks.

Members: `rd-rejoin→`, `rd-rejoin←`, `rd-apart`, `rd-bd*`,
`rd-bounded*`, `rd-bcorr-env`.

#### THE LAYERS' HANGS

Each wrapping layer's pair is `HorizonCorr.Wrap` over its body's; the
combined scan, closer and share owe which rows they keep, which they
move and where, and their own boundaries bounded. Untried. Settled by
bodies, or a kept row whose hang the layer drops.

Members: `cb-bd*`, `cb-bounded*`, `cb-keeps`, `cb-only`, `cb-moved`,
`cb-moved-q`, `cb-putw`, `cz-bd*`, `cz-bounded*`, `cz-keeps`, `cz-only`,
`sr-bd*`, `sr-bounded`, `sr-bounded*`, `sr-bcorr`.

#### THE ONE-CHILD HANGS

A scan, map or defer keeps its child's boundaries, a take its
`TakeB`'s, a cold has its own. Untried: bounded across the row
isomorphism, the take's pair where a placement leaves its row, the
defer's pair, the cold's. Settled by bodies.

Members: `scan-bounded`, `scan-bounded*`, `ev-bounded`, `ev-bounded*`,
`defer-bounded`, `defer-bounded*`, `defer-bcorr`, `take-bcorr`,
`cold-bd`, `cold-bd*`, `cold-bounded`, `cold-bounded*`, `cold-bcorr`.

#### THE COMBINED SCAN

The combined scan's record is written: a lanes' row re-emitted at the
lane branch's reader, the flatMap's end at the `nothing` past the last
of the three branches' ends (probed). Untried: its fields,
the scan emitting nothing but marks besides. Settled by bodies.

Members: `cb-corr`.

#### THE FLATMAP'S ORDER FACTS

Untried: the whole flatMap's rows carry the order facts, each row a
source or lane row imaged along its stream's map through the layers.
Settled by its body.

Members: `flatmap-order`.

#### THE SWITCH

The switch's record is the merge's map over every value's lane. Untried:
a cut lane's rows unshown alike, its pins kept alike, its end shown at
the same `done`. Settled by bodies, or a lane cut at one side's row only.

Members: `sw-corr`, `sw-in-bk`, `sw-after-φ`.

#### THE EXHAUST

The exhaust's record is the merge's map over the lanes the plain
exhaust runs. Untried: the elaborated exhaust runs the same lanes,
though its lanes end at their end images. Settled by bodies, or a value
run on one side only.

Members: `ex-corr`, `ex-in-bk`, `ex-after-φ`.

#### THE BOUNDED MERGE

The bounded merge's record is written: lanes enumerated level by level,
a queued lane's record had from the lane it waited on, at its end, and
subscribed under that end's image (probed). Untried:
its fields, the queue's state a run's. Settled by bodies.

Members: `cc-corr`, `cc-in-bk`, `cc-after-φ`.

#### THE PLAIN MERGE

The merge's record is written: lane rows through `laneˢ`'s reader and
`counted`'s emit, a value's marker at its elaborated value's, the
source's end at the later of its own and the trigger's. Visible images
probed; skip images and puts untried.
Settled by bodies.

Members: `mg-corr`, `mg-in-bk`, `mg-after-φ`.

#### THE CLOSER AND THE SHARE

Each record is its body's, the connect showing its body's rows as they
are and its source's only as pins and skips; the share puts the
source's pins where its connect shows them, the layers inside relating
the plain flatMap without them. Untried: the fields. Settled by bodies.

Members: `cz-corr`, `sr-corr`.

#### THE CONNECT'S HOT

A reader of the connect's hot is related wherever it is subscribed:
its rows are the source's hot rows one label down, its images the
source's carried under the annotation's reader and its own. Riskiest:
a shown row cuts the hot and the reader's own rows of other cuts alike,
off the source's `Rest.self`. Then the elaborated reader's rows read
back to the source's. Settled by bodies.

Members: `rd-corr`, `rd-linked`, `rd-cuts`, `rd-self`, `rd-self-at`, `rd-seen`.

#### THE CONNECT

The connect's record is written: body rows along the body's map, source
rows one label down at their annotated image. Untried: its field leaves,
an old hot's reader cutting the new alike, rows and partners
(`conn-old-cut`, `conn-old-bcorr`). Settled by bodies.

Members: `conn-old-cut`, `conn-old-bcorr`, `conn-order`, `ct-corr`, `ct-in-bk`, `ct-after-φ`.

#### THE ORDER FACTS

Probed at every uncut subterm, unproven: each
former's rows carry the record's order facts (`Rest`): linked to their
images, each shown row cutting every hot in scope and the stream's own
rows of every cut alike up each creator chain. A leaf former's rows lie at steps of timers it created
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

Members: `rows-func`, `rows-flat`.

#### THE COLD'S WALK

The rewrite: the plain cold's cuts, renamed onto the elaborated
cold's, keep order, instants and kinds. Untried; each is about one
walk of one timeline. Settled by bodies.

Members: `walk-past`, `walk-under`, `walk-end`, `walk-before`, `walk-apart`,
`walk-ren→`, `walk-ren←`, `walk-kind`, `walk-func`, `walk-flat`, `walk-alone`,
`φ-mono`, `φ-inst`, `φ-home`, `φ-after`, `φ-back`.

#### THE CUT ARITHMETIC

Untried, order arithmetic: the body's subscription cuts the source's
alike up the link, and what is past the source is not over the body.

Members: `cut-body`, `past-src`.
