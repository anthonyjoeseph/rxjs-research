# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 1 — the adequacy theorem

**THE LINK.** `adequacy`: the pure run's limit is the fold's meaning observed
at the root, positions forgotten down to ticks. SAFETY, every prefix placed
against the meaning's events, is a body: SORTED (`adequacy.Sorted`, the
machine alone) and ALIKE as sets (`content`) is placed (`placing`). LIVENESS
is by an item's depth, then the witness's `measure` (`adequacy.Progress`).
Sortedness rides SCOPED positions: `under l m k` runs `m` at
`pos ++ [l]` and puts `pos` back, so the run's positions are a tree's
pre-order; each kernel is well-positioned (`Well`, unary) given its
observer is; `preserve` is the tree walk, the timers and the loop's turn,
a body: a turn opens an epoch at its timer's cascade, and setting a timer
moves the last to where it was set, so same-tick timers pop in order.
Content rides a GHOST, the meaning's own configuration, which the machine's
runs; at the launch its residual is the events (`begun`, by `subscribed`).
Only re-entry configurations are related to the ghost; the rest reach one
by their own silent steps (`Mirror`).

### Progress

- `Leaves` ties a ghost's free node to the heap's leftover in meaning and in
  order (`Deep`), both ways; `Leaving.rests` makes the held rest `Restful`.
- An end keeps every tie: `lefts-off` is proven, over `Stays.left`.
- A source's end is a lift: `fin-ghost` is a body over `ghost-lift`, owing
  only `fin-shut`.
- Open: whether a plant and a growth keep the ties (`lefts-planted`,
  `lefts-grow`), and whether a repooled rest ties as a left-over one does.

### Ledger

#### THE REST'S TIES

An ended part's rest, left over (`Leaving`, `Lefts`) or repooled
(`Lingers`), stays tied to what the heap keeps, through every move. The
repool cells carry the most dead routes in the tree. Settled when a plant, a
growth and one repool move keep the tie as bodies, or one is refuted and the
tie restated.

Members: `*-leaving`, `leaving`, `lefts-planted`, `lefts-grow`, `bg-left`,
`fin-shut`, `rest-sourced`, `idle-tied`, `close-heads`, `close-tied`,
`close-told`, `settle-heads`, `settle-lingering`, `settle-told`, `next-heads`,
`next-lingering`, `take-leftover`, `body-leftover`, `re-leftover`.

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

**THE STATEMENT.** Define the new "simultaneous" spec over the denotation,
adapted from the old `agda/` tree's statement modules (reference only). No
groups until the statements exist; each lands as a postulate here.

## Tier 3 — the simultaneous spec, proven

**THE PROOF.** Discharge Tier 2's statements using the denotation and
`adequacy`. No groups until Tier 2 states them.
