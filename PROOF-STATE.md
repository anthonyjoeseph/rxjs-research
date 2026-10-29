# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

#### THE CONNECT GROWN

Riskiest, grown first: subscribing to a connect is its own leaf until a
good tree can hold one. Open: what a connect node owes in
`adequacy.Bound.G`; equal binder rows giving equal body rows; a skip
lifting past no binder, as a connect shows its source's skip one level
down and a joiner its own at the binder's. Settled when `reach` links a
connect a step at a time.

Members: `beyond-connect`, `rows-hot`.

#### THE FORMERS NOT GROWN

Each former still handed to its own leaf in `reach` owes a node in
`adequacy.Bound.G`, its rows and what it owes, and the step arms of the
nodes it builds. A cold that hushes meets THE OWED; `defer` unfolds only
at admissible subscriptions. Settled former by former, as each leaf
becomes arms.

Members: `beyond-cold`, `beyond-scan`, `beyond-take`, `beyond-bounded`,
`beyond-switch`, `beyond-exhaust`, `beyond-defer`.

#### OWING AS ENTERED

Believed: a merge of good parts owing a row owes one with finitely many
before it. The goal is a negation, so a finitary case split is free:
finitely many parts lie before any row, each truncation-closed. Settled
by a body, or a good merge whose every row has infinitely many before.

Members: `owing-row`.

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

Untried: a mark run at an of keeps `Good`. Apartness is derived, not
carried: `Rooted` reads it off Tier −1's invariant at the outer's entry.
Owed: each outer still inside its entry, and a lane begun rooted at a
value of its own, its rows in its subscription's world. Settled by
bodies, or a program whose of run leaves two parts sharing a position.

Members: `good-of`, `good-done`.

#### THE OWED

Suspect once cold is grown: `Owes` reads a live node as owing a row, false
for a cold that hushes (live, no rows, never ends). Restate as a live node
owing no end, equivalent on the grown formers and all `¬ Done` needs. Then a
closed of dropped changes nothing owed (`adequacy.AbsOf`). Settled by the
restatement and a body.

Members: `owes-closed`.

#### THE MARK FOUND

Untried: a good tree's search finds an of's next or an attach, an attach
moves nothing owed, an outer's value begins its lane, its end shows only
with no lane running, and a lane's value passes unless the lane is over
(`adequacy.Sim`). Settled when each is a body.

Members: `found-mark`, `abs-att`, `rise-outer-nx`, `rise-outer-cp`,
`rise-lane-nx`.

#### THE SUBSCRIPTIONS ENTERED

Believed: subscribing to `empty` or `of` enters exactly the rows its
emission set begins with, those rows placed behind every ancestor's parts
so its merges stay apart and end last. Settled when each is a body.

Members: `sub-empty`, `sub-of`.

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
