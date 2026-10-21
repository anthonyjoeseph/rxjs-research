# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### THE FED LEFTOVER

Suspect fact: a retag keeps the body's leftover. A nested connect whose source
holds a joiner of the fed one reads that joiner's part, so its burst and pins
move. Settled by a witness, then restating what `Refed`'s lingering owes as
the fed rest, or by `re-leftover` as a body.

Members: `re-leftover`.

#### THE REST'S TIES

An ended part's rest stays twinned with what the heap keeps. Open: whether
what a closed sub leaves running heads past the run, as hidden runs may not,
and whether a pool's untold sources follow, though `Lifts` leaves the closed
node free and only its rest is tied. Settled when
`closed-rest-heads` and `settle-told` are bodies, or one is refuted.

Members: `closed-rest-heads`, `rest-sourced`, `close-told`, `settle-told`,
`take-leftover`, `body-leftover`.

#### JOIN ORDER

Whether a source's call finds every subscriber of its connect's subject joined
before the run's position: a field `Carried` owes, every join framing it, or
a consequence of the agenda's placement. Settled when `joined-before` is a
body, or the field is added and framed.

Members: `joined-before`.

#### THE ROOT STEP

A sane, placed root ghost's meaning is what its step shows, then the stepped
node's, and the step leaves its parts placed; no connect's body shows under a
source step. Refuted four times as stated. Settled when `step-skips` and
`within-step` are bodies over the per-node facts.

Members: `step-skips`, `within-step`, `under-shown-connect`.

#### DEEP ORDER

Whether `Deep`, order to every depth, is the invariant a launch, a step and a
gap keep, so that the order lemmas `Placed` stands on reach every depth.
Settled when `step-deep` and `gapped-deep` are bodies, or the field is
restated.

Members: `deep-subscribe`, `step-deep`, `gapped-deep`, `gapped-past`,
`gapped-sane`, `gapped-placed`.

#### HIDDEN RUNS

Suspect fact: nothing but the `of` heads under the run, while
`Carried.behind` bounds only at its `p`. Every pin and landing for a hidden
`of` under a pool, an ended source or a take rides on it. Settled when
`pooled-pin` and `left-pin` are bodies, or a missing `Carried` field is
found.

Members: `pooled-pin`, `left-pin`, `pool-off`, `pool-land`, `rest-body`,
`rest-land`, `spread-held`, `void-site`, `shut-late`, `step-late`,
`emit-shut`, `emit-run`, `note-least`, `turn-dry`.

#### UP-ENDED

Whether `tells-past` is a field `Carried` owes, every producer framing it, or
follows from `Owned`'s finishes and the agenda's placement; the shut nodes'
steps heading past the shutting end ride on the answer. Settled by deriving
`tells-past`, or by adding the field and framing it.

Members: `tells-past`, `ended-past`, `union-down`, `source-down`,
`ended-down`, `bursts-down`, `flat-down`.

#### THE LANE START

The code's own naturality: a compiled subscription and a leaf's continuation
read alike along a growth, so a lane's start is a splice in one world.
Settled when `compile-grow` and `kont-grow` are bodies by operator over the
`-wk` toolkit and the `bg-` facts follow over `ghost-lift`.

Members: `compile-grow`, `kont-grow`, `walk-kont-sub`, `flat-wk-here`,
`bg-owns`, `bg-heads`, `bg-lingered`, `bg-ghosted`, `bg-apart`, `begin-path`,
`lanes-counted`, `calling-open`, `live-parted`, `outer-switch`,
`outer-queued`, `outer-drop`.

#### THE CONNECT REFED

A connect refed: its body retagged keeps each tree field and a part, and that
part is the body's fed the value. `part-retag` wants `Steady`, held only at
the call site. Settled when the retag keeps a part as a body.

Members: `re-revive`, `re-told`, `re-root`, `re-just`, `re-heads`,
`re-lingers`, `retag-parted`, `retag-fed`, `src-idle`.

#### PLANT MOVES

An agenda's calls, a source call and what is owed survive a plant and a store
outside the tree's names, call kind by kind. Settled when one call kind moves
as a body and the rest mirror it.

Members: `rehome-src`, `run-{ofs,begun,bodies,cuts,ends,feeds,fins,fires,plays,placed}`,
`connect-owned`, `connect-behind`, `of-owned`, `store-owned`, `store-queue`.

#### COMPLETIONS

A completion begun, held or hidden, for a takeWhile, a spent `of`, a
connect's feed and a take: begun at the right frame, the ghost past it, every
part heading past the take's own position. Settled when one held and one
hidden completion are bodies.

Members: `take1-enter`, `take1-void`, `last-enter`, `last-void`, `fin-enter`,
`end-ghost`, `out-deeper`, `take-pooled`, `body-pooled`, `turn-told`,
`turn-ended`.

#### AGENDA CALLS

Each agenda call does what the code says: a cold, joiner or defer begun, a
feed or source or continuation onward, a burst polled and played, the run's
position headed by a tick. Settled when one call is a body by unfolding the
code.

Members: `sub-cold`, `sub-joined`, `sub-defer`, `feed-onward`, `src-onward`,
`kont-onward`, `burst-poll`, `burst-play`, `pos-headed`.

#### SCAN WRITES

A write at a scan's accumulator moves no definedness and no seen path.
Settled when `scan-apart` is a body.

Members: `defined-alike`, `seen-gates`, `gates-apart`, `scan-apart`.

#### THE LINK

An ascending record alike a program's events as a set is placed against
them, and the meaning's ticks never fall. Settled when both are bodies.

Members: `placing`, `ticks-up`.

## Tier 2 — the simultaneous spec

**The statement:** the simultaneous spec, stated over the denotation.

### Ledger

#### THE ELABORATION

The statements are about srxjs only once srxjs is a program: each
primitive rebuilt over InstEmits with `fresh` names, and the batcher built
from primitives. `elaborate` must pass Agda's productivity check through
`defer`, so each clause is constructors around the elaborated child.
Settled when each equation holds by `refl`, oracle-checked.

Members: `elaborate`, `elaborate-cold`, `elaborate-empty`, `elaborate-of`,
`elaborate-map`, `elaborate-scan`, `elaborate-takeWhile`,
`elaborate-flatMap`, `elaborate-connect`, `elaborate-connected`,
`elaborate-defer`, `coldˢ`, `emptyˢ`, `ofˢ`, `mapˢ`, `scanˢ`, `takeWhileˢ`,
`flatMapˢ`, `connectˢ`, `batchSimultaneous`.

#### THE INSTANTS

Whether every position the fold builds lies under the subscribe frame or a
timer cascade, as `instantOf` reads it. Settled when `positioned` is a body
by induction over the fold.

Members: `positioned`.

## Tier 3 — the simultaneous spec, proven

**The proof:** Tier 2's statements, discharged over `adequacy`.

### Ledger

#### THE SPEC

Untried, and the batcher's liveness half waits on the elaboration: batches
joined are the plain values, batches are the spec's grouping, at every site
and related environment. Settled when both are bodies.

Members: `left-to-rightˢ`, `batchableˢ`.

#### SOUND NAMES

Whether `Sound` (names lie in their instant, one name per instant) is kept
by each elaborated primitive and survives limits. Settled when the
per-operator facts are bodies over the elaborations.

Members: `coldˢ-sound`, `emptyˢ-sound`, `ofˢ-sound`, `mapˢ-sound`,
`scanˢ-sound`, `takeWhileˢ-sound`, `flatMapˢ-sound`, `connectˢ-sound`,
`defer-sound`, `sound-admissible`, `batched-sound`.
