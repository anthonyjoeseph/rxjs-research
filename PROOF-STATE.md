# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

#### A RISEN OUTER VALUE'S ENTRY

Riskiest: `Inv` holds a rising outer value past the joiner's other parts,
but not in its outer's frozen entry nor where its binders are hot; the
begun lane's `Rooted` and `Subs` need both. Open: a lead field reading each
frame through the risen row, not an entry on every node of `Good`. Settled
by that field, or a value risen outside its entry.

Members: `begin-good`, `begin-ok`.

#### A CONNECT ENDED BEFORE ITS SOURCE

Riskiest: `Inv` asks a rising end's node to be `Empty`, but a body ending
before its source's burst leaves that burst owed as silent pins. Open:
`Ends cp` over visible rows only, which a lane's end then reads. Settled
when `≈` carries silent rows past `p` with `Truncate`'s reach intact.

Members: `rise-body-cp`.

#### A DONE JOINER RISEN AGAIN

Refuted against `Inv` as it stands: a joiner done with no lane live and
none waiting has risen its end, yet nothing stops its outer rising one.
Open: an invariant tying a done joiner to a closed or spent frame above.
Settled by that invariant, or a program whose done joiner's outer ends.

Members: `rise-joiner-cp-spent`.

#### THE CONNECT'S SEARCH

Riskiest: how a connect's source rows and its body's sit against each
other. Open: whether a body's find lies under no row its source still owes,
an invariant `Good` does not yet state. Settled by a body, or a program whose
body finds at or under a source row not yet fed.

Members: `body-apart`.

#### THE COLD STEPPED

A cold entered at its timeline read where it subscribes, and each turn of
its tape, keep `Inv`, and a burst's rows lie from its frame on. Open:
whether a stall or a frame's close, a skip in its rows, moves nothing owed.
Settled when each is a body.

Members: `sub-cold`, `abs-leaf`, `burst-from`.

#### THE JOINERS STEPPED

Untried: a bounded merge, a switch or an exhaust part way through reads
its begun lanes over off its live count, not off each lane's rows, and
each entry, outer value and outer end keeps `Inv`; a lane's end, value and
begin are each one step over the policy, a switch's begin excepted. Open: whether `Rows.BoundedF`'s schedule
from begun lanes tracks the machine's queue, with a lane gone or handed
on. Settled when each is a body, or a bounded merge whose freed slot the
schedule reads wrong.

Members: `bounded-ends-at`, `bounded-val-at`, `bounded-outer-at`,
`rise-bounded-lane-hand`, `rise-switch-nx`, `rise-exhaust-drop`,
`bounded-begin-at`, `exhaust-begin-at`, `rise-bounded-wait`.

#### THE CONNECT STEPPED

A connect entered, a joiner joined, a source's or body's rise, a
connect's own mark run and a joiner's next, each one step keeping `Inv`.
Open: whether `G`'s connect node (source held until subscribed, a
completed source owing nothing) is enough for each; a source's end must
leave its rows `Empty`. Settled when each is a body.

Members: `sub-connect`, `sub-join`, `sub-joined`, `rise-src-nx`, `rise-src-cp`,
`abs-con`, `abs-join`.

#### THE BINDER READ

Believed: a good tree's connect source reads lawfully, its rows and its
end one event a position, none under another. Open: a connect under a
switched-off cut, whose `G` asks nothing of its source. Settled by a body,
or a good tree whose dead connect's source rows clash.

Members: `src-lawful`.

#### A SKIP UNDER A CONNECT

Untried: a skip at a source past its lead is unseen above its connect,
the connect showing it a skip or a pin and each joiner a skip where it
joined. Settled by a body, or a source skip that changes what the
connect shows.

Members: `src-vis`.

#### AN OF IN A COMPLETED SOURCE

Untried: an of or an outer value in a source its connect has seen
complete runs out silently, its rows reaching no row above. Settled by a
body, or such a run that shows.

Members: `shut-of`, `shut-begin`.

#### ONE EVENT A POSITION

Untried: a good node's rows hold one event at a position, its binders'
doing so: a merge's parts apart by `Rooted`, a connect's body and source
echoes by world, a binder's rejoins by its source's. Settled by a body by
former, or a good tree with two rows at a position.

Members: `rows-single`, `bind-single`.

#### THE SCAN STEPPED

Untried: a scan's rising value is its source's least, so the fold of it
leads the scanned rows and the rest fold from it; an end rises unfolded.
Settled when each is a body over `denotation.EmissionSet`'s `Scan.Acc`.

Members: `rise-scan-nx`, `rise-scan-cp`.

#### THE TAKE STEPPED

Untried: a take's search leads its rows; a value passing or failing,
its end, its stop and its cut keep `Inv`. Settled when each is a body.

Members: `take-leadᶜ`, `rise-take-nx`, `rise-take-fail`,
`rise-take-cp`, `rise-take-owed`, `abs-stop`, `abs-cut`.

#### THE SILENT RUN, FINITE

Short of a row a reader meets next, a run is fuelled by the rows at or
before it strictly past its clock. Open: whether the clock (the least mark
due once absorbed, else the run's position) never runs back, and whether
steps passing no such row are few. Settled by bodies, or a program whose
engine stalls silently forever before a row its emission set holds.

Members: `clock-mono`, `still-finite`.

#### THE GOOD TREE KEPT

Untried: a mark run at an of, and a lane's end leaving its list and its
merge's count, keep `Good`. Apartness is derived, not carried: `Rooted`
reads it off Tier −1's invariant at the outer's entry. Owed: each outer
still inside its entry, a lane begun rooted at a value of its own, its
rows in its subscription's world, and every frame above a merge good
over rows that may now end where the lane did. Settled by bodies, or a
program whose of run leaves two parts sharing a position.

Members: `good-of`, `good-done`, `good-lane-end`, `good-outer-end`.

#### THE MARK FOUND

Untried: a good tree's search finds an of's next, an attach, a
connect's own mark or a joiner's next; an attach moves nothing owed, and
an outer's end shows only with no lane running (`adequacy.Sim`). Settled when each is a body.

Members: `found-mark`, `abs-att`.

#### THE SUBSCRIPTIONS ENTERED

Believed: subscribing to `empty` or `of` enters exactly the rows its
emission set begins with, those rows placed behind every ancestor's parts
so its merges stay apart and end last; a `defer` entered at an admissible
subscription reads as its body one level down. Settled when each is a
body.

Members: `sub-empty`, `sub-of`, `sub-defer`.

## Tier 1 — the simultaneous spec

**The spec:** batchSimultaneous groups what plain rxjs delivers by instant, in order, read off the emission set.

### Ledger

#### THE SPEC

Untried: batches joined are the plain values, each batch is one instant,
and it leaves the moment its instant is over. Settled when each is a body
over the emission set.

Members: `left-to-right`, `coherent`, `batchable`.

#### THE INSTANTS

Whether every position the emission set gives lies under the subscribe
frame or a timer cascade, as `instantOf` reads it. Settled when
`positioned` is a body by induction over the tree.

Members: `positioned`.
