# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier −1 — the emission set is compositional

**Compositional:** every former but `defer` means its operator; `defer` unfolds to its body at admissible subscriptions.

### Ledger

## Tier 0 — adequacy

**Adequacy:** what the pure semantics shows is what a reader of the emission set meets, row by row.

### Ledger

#### BEYOND THE FRAGMENT

Untried, riskiest under a connect: `rows` reads only the state, so
`pendRows` owes nothing under a binder, yet a joiner owes its inbox, the
source's remaining rows rekeyed under it, and a late end. `rows` needs an
environment per binder (the source's remaining rows, closed or not), and a
body's rows past a position shown blind to earlier hot rows but the end.
This can change `rows`'s type, so it comes before any other former. The
split is excluded middle. Settled once the sound half covers every program.

Members: `sound-beyond`, `frag?`.

#### THE COMPLETE HALF

Untried: every row met, some run shows. Route: a machine-only progress
lemma, a measure on `Conf` (pending program, marks, context depth) bounding
silent steps while a visible row is owed; a mark keyed `after` shows nothing
and removes itself. Soundness then names what shows. The one row fact
needed is that owing nothing is `Empty`. Settled by a body, or a program
whose emission set holds a row no run reaches.

Members: `complete`.

#### THE GOOD TREE KEPT

Untried: a mark run at an of keeps `Good`, its merges' parts still apart.
A lane begun at a value's second child stays apart by Tier −1's `world`,
`flat` and `under`, given `Ok` there: owed first, a lemma that the
machine's subscription positions are `Real`. Settled by bodies, or a
program whose of run leaves two parts sharing a position.

Members: `good-of`, `good-done`.

#### THE OWED

Suspect past the fragment: `Owes` reads a live node as owing a row, false
for a cold that hushes (live, no rows, never ends). Restate as a live node
owing no end, equivalent in the fragment and all `¬ Done` needs. Then a
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
