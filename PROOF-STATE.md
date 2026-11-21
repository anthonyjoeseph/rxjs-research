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

#### THE PARTS AT THE TREE'S BOUNDARIES

A late row put past a tree boundary (`mg-o-pb`); then the lanes under
`laneˢ`, whose `Rel.Bd` is not yet pinned to the lane tree's `bd`.
Untried. Settled by bodies over the parts' fields, or a late row whose
placement crosses a boundary its image does not.

Members: `mg-o-pb`, `mg-lane-bcorr`,
`mg-outer-back`, `mg-lane-back`, `mg-outer-put`, `mg-lane-put`,
`mg-outer-lead`, `mg-lane-lead`.

#### THE MERGE'S CROSS-PART FACTS

`JoinPair` asks the merge what no part knows alone: each part's rows
cut the other parts' marks alike, a merge row's map is its outer's (`φo`) or its lane's, and every
image row is a row's. Untried. Settled by bodies over the listing, or
a lane row ordered against an outer mark unlike its image.

Members: `mg-is-val`, `mg-not-val`, `mg-late-src`, `mg-φ-src`, `mg-val←`, `mg-φ-val`, `mg-nl-out`, `mg-put-split`,
`mg-img`, `mg-outer-lane`, `mg-outer-lane-put`,
`mg-lane-outer`, `mg-lane-outer-put`, `mg-lane-lane`, `mg-lane-lane-put`.

#### THE PLACEMENTS ORDERED BACK

`Inter.BCorr.to` orders placements both ways: a late row whose
placement lies before an elaborated hang lies before its plain partner
(`Inter.PutAfter`), as `from` orders them forward. With it a row clear
where its placement is (`Across.put-clear`) is derived. Riskiest: the
merge places a late or pinned outer row at its own image, which the
source's `Corr` does not constrain (`mg-o-pa`, and `mg-o-pb` forward).
Then the cross-part mirrors. Settled by bodies, or a put row past a
plain hang whose placement lies before the partner.

Members: `mg-o-pa`, `mg-outer-lane-put←`, `mg-lane-outer-put←`,
`mg-lane-lane-put←`, `ct-body-src-put←`.

#### THE HANGS ACROSS CUTS

Each `Rel` owes `TableCorr.Across`; `TableCorr.across-of` builds it from
one cut's `bcorr` and `TableCorr.Stable`: an own row whose image lies
before a shallower cut's elaborated hangs is in that cut, on the same
image; a late row whose placement does is in that cut, placed there.
Untried. Settled by bodies, or a deeper row before the elaborated hangs
whose shallower image or placement moved. Leading rows stay per former.

Members: `cc-stable`, `sw-stable`, `ex-stable`, `cold-pull`, `defer-stable`, `rd-stable`,
`cb-stable`, `sr-stable`, `ct-stable`, `cc-lead`, `sw-lead`, `ex-lead`,
`cold-lead`, `defer-lead`, `rd-lead`, `cb-lead`, `sr-lead`, `ct-lead`,
`cz-lead-clear`.

#### THE ROOT'S LEAVES

The crossings are the `Rel`'s. Left: a closed program's boundaries are
real and over none of its rows (false of an open one), and the map and
placements are read alike by cuts agreeing up to them. Untried. Settled
by bodies over the tree, or a placement that moves between agreeing cuts.

Members: `root-real`, `root-real*`, `root-off`, `root-off*`,
`root-φ-agree`, `root-late-agree`, `root-put-up`, `root-put-down`.

#### THE SOURCE PAST ITS SUBSCRIPTION

`Horizon.ConnB` keeps a source boundary before the connect as an echo,
so it asks only that none lies inside the connect's own window and that
a burst's held pin is past the subscription; the plain side's are bodies
over the placement. Left: the elaborated side's. Untried. Settled by a proof over the
tree, or a source boundary between the connect and its source's
subscription.

Members: `ct-src-out`, `ct-src-held`.

#### THE JOINS' HANGS

Each core's pair with the plain flatMap's: the merge's is
`JoinPair`'s over its parts' and cross-part leaves; the others copy it,
over `cc-bd`, `sw-bd`, `ex-bd`. Settled by bodies.

Members: `cc-bcorr`, `sw-bcorr`, `ex-bcorr`, `share-bd→`, `share-bd←`.

#### THE CONNECT'S HANGS

The connect's bounded is `Horizon.ConnB`'s and its pair `HorizonConn.ConnPair`'s,
the elaborated over the annotated source. The body's pair cuts its source alike through
`Rest.bcorr-env`. Riskiest: a pinned or late source row is placed at its
image (`ct-src-img`), which the body's placements need; then the
annotated source's pair and the cross-part leaves. Settled by bodies,
or a late source row placed off its image.

Members: `ct-src-img`, `ct-src-hot`, `ct-src-bcorr`, `ct-φc-body`,
`ct-φc-echo`, `ct-late-body`, `ct-late-echo`, `ct-put-split`, `ct-img`,
`ct-put-row`, `ct-gap-sb`, `ct-gap-bs`, `ct-gap-sb*`, `ct-gap-bs*`, `ct-gap-src`, `ct-gap-src*`, `ct-held-src`, `ct-held-src*`,
`ct-held-body`, `ct-held-body*`, `ct-body-src`, `ct-body-src-put`, `ct-home→`,
`ct-home←`, `ct-end→`, `ct-end←`, `ct-rows-after`, `ct-rows-after*`.

#### THE HOT READER'S HANGS

A reader is bounded by its hot's boundaries through `Horizon.RejoinB`,
its table read as `Rejoin` at the subscription. Untried: that reading
and the readers' pair. Settled by bodies,
or a reader row the rejoined hot lacks.

Members: `rd-rejoin→`, `rd-rejoin←`, `rd-apart`, `rd-bcorr-env`.

#### THE LAYERS' HANGS

Each wrapping layer's pair is `HorizonCorr.Wrap` over its body's; the
combined scan, closer and share owe which rows they keep, which they
move and where. Untried. Settled by
bodies, or a kept row whose hang the layer drops.

Members: `cb-keeps`, `cb-only`, `cb-moved`,
`cb-moved-q`, `cb-putw`, `cz-keeps`, `cz-only`, `sr-bcorr`.

#### THE ONE-CHILD HANGS

Untried: the defer's bound across its marker row, the take's pair
where a placement leaves its row, the defer's pair, the cold's pair. Settled by bodies.

Members: `defer-bounded`, `defer-bounded*`, `defer-bcorr`, `take-bcorr`,
`cold-bcorr`.

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

Members: `sw-corr`, `sw-in-bk`, `sw-after-φ`, `sw-img`.

#### THE EXHAUST

The exhaust's record is the merge's map over the lanes the plain
exhaust runs. Untried: the elaborated exhaust runs the same lanes,
though its lanes end at their end images. Settled by bodies, or a value
run on one side only.

Members: `ex-corr`, `ex-in-bk`, `ex-after-φ`, `ex-img`.

#### THE BOUNDED MERGE

The bounded merge's record is written: lanes enumerated level by level,
a queued lane's record had from the lane it waited on, at its end, and
subscribed under that end's image (probed). Untried:
its fields, the queue's state a run's. Settled by bodies.

Members: `cc-corr`, `cc-in-bk`, `cc-after-φ`, `cc-img`.

#### THE PLAIN MERGE

The merge's record is written: lane rows through `laneˢ`'s reader and
`counted`'s emit, a value's marker at its elaborated value's, the
source's end at the later of its own and the trigger's. Visible images
probed; skip images and puts untried.
Settled by bodies.

Members: `mg-row→`, `mg-late-put`, `mg-pin→`, `mg-put-before`, `mg-pin-before`,
`mg-shown←`, `mg-place`, `mg-mono`, `mg-inst`, `mg-home`, `mg-in-bk`, `mg-after-φ`.

#### THE CLOSER AND THE SHARE

Each record is its body's, the connect showing its body's rows as they
are and its source's only as pins and skips; the share puts the
source's pins where its connect shows them, the layers inside relating
the plain flatMap without them. Untried: the fields. Settled by bodies.

Members: `cz-corr`, `sr-corr`, `sr-img`.

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
The combinator scan loops synchronously, so its rest needs the count.
A connect's echoes are its source's rows: where its body empties, its
source must be done with the instant (`Tracks`), true of an elaborated
body because each flatMap parks what it cuts while a connect in scope
holds a route. Settled by bodies, or a body emptied under a looping source.

Members: `cold-step-few`, `scan-rest`, `connect-tracks`, `tracks-trig`,
`tracks-closer`, `tracks-real`.

#### THE HELD STREAMS

Probed, unproven: every elaborated stream names its begins for their
instants, counts a route of its own instant under every row outside the
bursts it is exempt for, and keeps dead instants dead. Hardest:
flatMap's scan counters, each the `idle` of what holds the routes, read
on the scan's run split onto that branch; read on the scan's lanes
counter, not the lanes' own count, which a carried route outlives; the outer's
lanes ended at an idle `outerDone`. Then a reader's joins, the
defer limit's rest (no one approximant bounds it), and the cold's rows'
order. Settled when each former's leaf is a body.

Members: `lanes-ended`, `closer-ends`, `src-ends`, `lane-end-shut`, `lane-idle`, `held-current`,
`live-current`, `value-open`, `over-open`, `end-open`, `comb-shut`,
`scan-idle`, `held-connected`, `lim-rest`, `cold-rows`, `cold-covered`,
`cold-shut`, `cold-idle`.

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

Members: `walk-under`, `walk-end`, `walk-before`, `walk-apart`,
`walk-ren→`, `walk-ren←`, `walk-kind`, `walk-func`, `walk-flat`, `walk-alone`,
`φ-mono`, `φ-inst`, `φ-home`, `φ-after`, `φ-back`.

#### THE CUT ARITHMETIC

Untried, order arithmetic: the body's subscription cuts the source's
alike up the link, and what is past the source is not over the body.

Members: `cut-body`, `past-src`.
