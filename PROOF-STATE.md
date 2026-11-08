# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

## Tier 1 — the elaboration

**The elaboration:** `elaborate` makes `make spec-check` green: no seed refutes `left-to-right`, `coherent` or `batchable`.

### Ledger

## Tier 2 — the simultaneous spec

**The spec:** batchSimultaneous groups what plain rxjs delivers by instant, in order, read off the emission set.

### Ledger

#### THE HANG SHOWS

Untried: past a position, a reader reaching few rows before it finds few
rows there. Suspect under nested truncation: an infinite chain of pins,
each cut for the next one down, read past by a later row. Settled by a
body by operator over `Reach`, or a program refuting it.

Members: `shows-ev`.

#### THE HELD STREAMS

Untried: every elaborated stream names its begins for their instants,
counts a route of its own instant under every row outside the bursts it
is exempt for, and keeps dead instants dead. Hardest: flatMap's scan
source (`start-current`): its counters must track each branch's open
routes of the current instant, which needs a branch's routes closed
before a later instant's first row; then which rows the source meets
(`m-rows`), a reader's joins and the defer limit. Settled when each
former's leaf is a body.

Members: `start-current`, `value-open`, `over-open`, `end-open`,
`comb-shut`, `walk`, `step-local`, `m-rows`, `lane-ends`,
`close-ends`, `lane-named`, `lane-early`, `lane-late`,
`close-marks`, `scan-idle`, `comb-run`, `held-connected`, `held-lim`,
`held-top`, `held-next`, `held-⊥`, `held-takeWhile`, `held-cold`,
`held-of`, `held-empty`.

#### THE ROUTES

Untried: the run leaves an
instant once nothing of it is held; a closed instant's batch meets a
releasing mark before any value. Hardest: the liveness `releases` asks
for.

Members: `flush-closes`, `releases`.

#### THE BURST

Untried: the subscribe mark sits once, before every begin, and every
row past it is async; every value precedes the completion. Needs where
`merge` and `concatˢ` place the top-level marks.

Members: `sub-first`, `sub-one`, `sub-async`, `done-last`.

#### THE ERASURE

Untried: the elaborated run, marks dropped, is the plain run, values and
completion, and its instants are finite when the plain run's are.
Switch, exhaust and the bounded queue are the real cases. Settled when
each is a body by operator.

Members: `erases`, `settles`.

#### THE NAMES

Untried: each async cold step mints one name and its whole cascade
carries it, so every emit is named for its instant and one instant's
begins alike. Settled when `named` and `one-name` are bodies over a
restamp invariant, and `coherent` a body over them.

Members: `coherent`, `named`, `one-name`.
