# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

## Tier 1 — the elaboration

**The elaboration:** `elaborate` makes `make spec-check` green: no seed refutes the batches joined, the grouping by name, or names agreeing with instants.

### Ledger

## Tier 2 — the simultaneous spec

**The spec:** the batched run, each batch stamped by its instant, is the spec's grouping of the plain run, each value stamped by its instant.

### Ledger

#### THE RELEASE

Untried in this vocabulary: the batcher holds nothing exactly where the
run's last instant is over — no value of it left past its last value, by
position, and the run leaving it. The bridge from the batcher's routes
to `Over` is open both ways. Settled when both are bodies over `shut`
and the protocol.

Members: `flush-closes`, `releases`.

#### THE BATCH RANK

Untried: a batch leaves within its own instant, at the rank its values
carry. Needs the layers' positions to keep instants, and the release
mark to sit in the instant it releases. Settled when `batch-rank` is a
body over the layers and the release protocol.

Members: `batch-rank`.

#### THE RANKS

Untried: a met run has its ranks, and rows of one instant share a rank
while rows of two do not. A rank cannot be computed from `Few`: its
cover may hold positions with no row. Settled when these are bodies over
`rooted`, the instant interval and a way to list a run's instants.

Members: `ranks-x`, `ranks-b`, `instant-rank`, `rank-instant`.

#### THE ROUTES

Proven on a closed branch over the held-route tower: a dead instant
stays dead, and an instant's values precede its overs. Settled when the
tower is ported and these are its bodies.

Members: `shut`, `over-last`.

#### THE PROTOCOL

Untried: every emit is named for its instant, the begins and values of
one instant carry one name, the subscribe mark sits once before every
begin with every value past it async, and every value precedes the
completion. Settled when each is a body over the elaboration's layers.

Members: `named`, `one-name`, `one-value-name`, `sub-first`, `sub-one`, `sub-async`, `done-last`.

#### THE ERASURE

Untried: the elaborated run, marks dropped, is the plain run stamp for
stamp — the elaboration adds no instant, so the ranks agree — with an
instant over on one side over on the other, and completing together.
Switch, exhaust and the bounded queue are the real cases. Settled when
each is a body by operator.

Members: `erases`.

#### THE INSTANTS

Whether every position a program reaches lies under the subscribe frame
or a timer cascade, as `instantOf` reads it. The world invariant says
where a row lies, not yet that none sits at a timer's root. Settled when
the invariant carries that, and `positioned` and `rooted` read it off.

Members: `positioned`, `rooted`.
