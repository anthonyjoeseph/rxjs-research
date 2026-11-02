# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

#### THE DEAD PART'S TAIL

A part that stops (take's failure, a source's end) has finitely many rows
past the cursor. Suspected false: a stop inside a connect's body keeps its
source's pins, an infinite burst when the source is `ones`. Settled by
restating as `Tail` against the state still running, or a body.

Members: `took-fin`, `shut-fin`.

#### THE JOINER'S PAST

A joiner subscribed at `q`: every row of its meaning lies past `q`.
Settled by a body over `pend-past` and each lane's subscription key.

Members: `join-past`.

#### THE CONNECT STEPPED

A connect entered, a joiner joined, a source's or body's rise, its own
marks, a joiner's next and a take's failure, each keeping `Inv`. Open:
whether every entry lands a region apart from its siblings' and clear of
its scope's hots, so the rest moves past `p`. Settled when each is a body.

Members: `sub-join`, `sub-joined`, `run-con`, `run-join-nx`,
`run-join-cp`, `rise-take-failᵢ`, `feed-up`, `conn-parts`, `flat-sound`,
`flat-within`.

#### THE JOINER STEPPED

An outer's value or end and a lane's, each rising into `Joined`/`Begun`
by its policy: a switch's kill, an exhaust's drop, a bounded queue.
Open: whether begun lanes stay ascending (`Asc`), and whether `Begun`'s
live count makes a freed slot the queue head's `Starts.queued`. Settled
when each is a body.

Members: `rise-outer-nx`, `rise-outer-cp`, `rise-lane-nx`, `rise-lane-cp`.

#### THE GUARD ROWS

A step that begins work a level down — a lane, a defer's body, a
source's feed — leaves a row first, so is never still. Open: that the
denotation has that row, at or before the one met next. Settled by
bodies over the joiner's and connect's rows.

Members: `lane-guard`, `echo-guard`, `defer-guard`.

#### THE MARK AT ITS ROW

Open: that an open cold's tick is an ancestor of a row at or before the
row met next, so it is listed. Settled by a body over the cursor `Inv`.

Members: `tick-row`.

#### THE COLD STEPPED

A cold entered at its timeline, and each turn of its tape, keep `Inv`.
Open: whether a stall or a frame's close moves nothing owed. Settled when
each is a body.

Members: `sub-cold`, `abs-leaf`.

#### THE FOLD AND THE TAKE

A scan or take entered: its fold or test over no value passed. Settled
when each is a body.

Members: `sub-scan`, `sub-take`.

#### THE ENTRIES

Believed: a subscription's entry is its program's meaning there, and an
of's next delivers its next row. Settled when each is a body.

Members: `sub-empty`, `sub-of`, `sub-map`, `sub-defer`, `run-of-nx`, `run-of-end`,
`flat-jinv`, `flat-joined`, `conn-flags`, `conn-ok`.

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
