# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

#### THE COLD STEPPED

A cold entered at its timeline read where it subscribes, and each turn of
its tape, keep `Inv`; its due mark keys and leads its rows. Open: whether
a stall or a frame's close, a skip in its rows, moves nothing owed. Settled
when each is a body.

Members: `sub-cold`, `abs-leaf`, `cold-ok`, `cold-lead`.

#### THE JOINERS STEPPED

Untried: a bounded merge, a switch or an exhaust part way through reads
its begun lanes over off its live count, not off each lane's rows, and
each entry, outer value, outer end, lane value and lane end keeps `Inv`.
Open: whether the count and `Rows.BoundedF`'s schedule from begun lanes
track the machine's queue and kills. Settled when each is a body, or a
joiner whose lane end in flight the count reads wrong.

Members: `enter-bounded`, `enter-switch`, `enter-exhaust`,
`rise-bounded-nx`, `rise-bounded-cp`, `rise-bounded-lane-nx`,
`rise-bounded-lane-cp`, `rise-switch-nx`, `rise-switch-cp`,
`rise-switch-lane-nx`, `rise-switch-lane-cp`, `rise-exhaust-run`,
`rise-exhaust-drop`, `rise-exhaust-cp`, `rise-exhaust-lane-nx`,
`rise-exhaust-lane-cp`.

#### THE QUEUED SEARCH

A bounded merge's search with values waiting keys and leads its rows: a
lane's end hands off to the queue's first just past it. Settled by
bodies over the bounded schedule's `Queued` and `Starts`.

Members: `bounded-wait-ok`, `bounded-wait-lead`.

#### THE CONNECT'S SEARCH

Riskiest: a connect's search is stated whole, over the connect node, at
an empty environment only, because its body's joiners read the binder.
Open: whether the whole-node statement holds with the source winning
only strictly before the body, or the search's key needs a cap carried
from the binder (`From`/`OK` keyed by a bound). Settled by bodies, or a
connect whose body's joiner keys a row before its source's find.

Members: `conn-ok`, `conn-lead`.

#### THE CONNECT STEPPED

A connect entered, a joiner joined, a source's or body's rise, a
connect's own mark run and a joiner's next, each one step keeping `Inv`.
Open: whether `G`'s connect node (source held until subscribed, a
completed source owing nothing) is enough for each; a source's end must
leave its rows `Empty`. Settled when each is a body.

Members: `sub-connect`, `sub-join`, `sub-joined`, `rise-src-nx`,
`rise-src-cp`, `rise-body-nx`, `rise-body-cp`, `abs-con`, `abs-join`.

#### THE BINDER READ

Believed: a body reads its binder only through the binder's rows, and a
good tree's connect source reads lawfully. Settled by bodies, or a body
whose rows or goodness differ under equal binder rows.

Members: `rows-hot`, `good-hot`, `src-lawful`.

#### A SKIP UNDER A CONNECT

Untried: a skip at a source past its lead is unseen above its connect,
the connect showing it a skip or a pin and each joiner a skip where it
joined. Settled by a body, or a source skip that changes what the
connect shows.

Members: `src-vis`.

#### AN OF IN A COMPLETED SOURCE

Untried: an of in a source its connect has seen complete runs out
silently, its rows reaching no row above. Settled by a body, or such an
of whose run shows.

Members: `shut-of`.

#### ONE EVENT A POSITION

Untried: a good node's rows hold one event at a position: a merge's
parts apart by `Rooted`, a connect's body and source echoes by world.
Settled by a body by former, or a good tree with two rows at a position.

Members: `rows-single`.

#### THE SCAN STEPPED

Untried: a scan's rising value is its source's least, so the fold of it
leads the scanned rows and the rest fold from it; an end rises unfolded.
Settled when each is a body over `denotation.EmissionSet`'s `Scan.Acc`.

Members: `rise-scan-nx`, `rise-scan-cp`.

#### THE TAKE STEPPED

Untried: a take's search leads its rows; a value passing or failing,
its end, its stop and its cut keep `Inv`. Settled when each is a body.

Members: `take-lead`, `rise-take-nx`, `rise-take-fail`,
`rise-take-cp`, `rise-take-owed`, `abs-stop`, `abs-cut`.

#### THE COMPLETE HALF

Untried: every row met, some run shows. Route: a machine-only progress
lemma, a measure on `Conf` (pending program, marks, context depth) bounding
silent steps while a visible row is owed; a mark keyed `after` shows nothing
and removes itself. Soundness then names what shows. The one row fact
needed is that owing nothing is `Empty`. Settled by a body, or a program
whose emission set holds a row no run reaches.

Members: `complete`.

#### THE SKIPS BETWEEN

Untried: the engine's shown rows, each the least visible one left, are
the shown rows of a reader's run, which meets every skip in order. Rows
before each are finitely many, but which of a listing's positions are rows
is undecided, and the oracle's listing is cut at a fixed horizon. Settled
by a body, or a program showing a value past its end.

Members: `met-of-shown`.

#### THE GOOD TREE KEPT

Untried: a mark run at an of, and a lane's end leaving its list and its
merge's count, keep `Good`. Apartness is derived, not carried: `Rooted`
reads it off Tier −1's invariant at the outer's entry. Owed: each outer
still inside its entry, a lane begun rooted at a value of its own, its
rows in its subscription's world, and every frame above a merge good
over rows that may now end where the lane did. Settled by bodies, or a
program whose of run leaves two parts sharing a position.

Members: `good-of`, `good-done`, `good-lane-end`.

#### THE MARK FOUND

Untried: a good tree's search finds an of's next, an attach, a
connect's own mark or a joiner's next; an attach moves nothing owed, an outer's value begins its lane, its end shows only
with no lane running, and a lane's value passes unless the lane is over
(`adequacy.Sim`). Settled when each is a body.

Members: `found-mark`, `abs-att`, `rise-outer-nx`, `rise-outer-cp`,
`rise-lane-nx`.

#### THE SUBSCRIPTIONS ENTERED

Believed: subscribing to `empty` or `of` enters exactly the rows its
emission set begins with, those rows placed behind every ancestor's parts
so its merges stay apart and end last; a `defer` entered at an admissible
subscription reads as its body one level down. Settled when each is a
body.

Members: `sub-empty`, `sub-of`, `sub-defer`.

#### THE KEYS

Believed: keys order as positions do, strictly and transitively, and a
position just past another stays before the mark the other is before.
Settled by bodies over `denotation.Events`' label comparisons.

Members: `shift-after`, `<ᴷ-trans`, `<ᴷ-irrefl`, `≮ᴷ-trans`, `at-<ᵖ`.

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
