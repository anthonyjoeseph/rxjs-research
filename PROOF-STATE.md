# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

#### THE COMPLETE HALF

Untried: every row a reader of the emission set meets, some run of the
pure semantics shows. Settled by a body, or a program whose emission set
holds a row no run reaches.

Members: `complete`.

#### BEYOND THE FRAGMENT

Untried: the sound half for `cold`, `scan`, `takeWhile`, `connect`,
`defer`, switch, exhaust and a bounded merge. The split is excluded
middle: `Frag` is not decidable over a merge's lanes. Settled once the
sound half covers every program, which retires the split.

Members: `sound-beyond`, `frag?`.

#### THE GOOD TREE KEPT

Untried: a mark run at an of keeps `Good`, its merges' parts still apart,
and a closed of dropped changes nothing owed (`adequacy.AbsOf`). Settled by
bodies, or a program whose of run leaves two parts sharing a position.

Members: `good-of`, `good-done`, `owes-closed`.

#### THE MARK FOUND

Untried: a good tree's search finds an of's next or an attach, an attach
moves nothing owed, an outer's value begins its lane, its end shows only
with no lane running, and a lane's value passes unless the lane is over
(`adequacy.Sim`). Settled when each is a body.

Members: `found-mark`, `abs-att`, `rise-outer-nx`, `rise-outer-cp`,
`rise-lane-nx`.

#### THE SUBSCRIPTIONS ENTERED

Believed: subscribing to `empty`, `of`, `map` or a merge enters exactly
the rows its emission set begins with. Settled when each is a body.

Members: `sub-empty`, `sub-of`, `sub-map`, `sub-merge`.

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
