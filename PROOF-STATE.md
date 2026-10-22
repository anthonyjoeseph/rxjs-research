# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### UP-ENDED

Whether every step keeps `Untold` and `Ended`, now fields of `Carried` and
`Calling`, and whether the shut nodes' steps head past the shutting end.
Settled when each step's framing leaf and `bursts-down` are bodies.

Members: `back-told`, `bg-ended`, `bg-told`, `connect-ended`, `connect-told`,
`fed-ended`, `fed-told`, `fin-ended`, `fin-told`, `fire-ended`, `fire-told`,
`fr-ended`, `grow-ended`, `grow-told`, `of-ended`, `of-told`, `out-told`,
`rf-ended`, `rf-told`, `rm-ended`, `rm-told`, `rs-ended`, `rs-told`, `rt-ended`,
`rt-told`, `scan-ended`, `scan-told`, `shift-ended`, `shift-told`, `torn-ended`,
`torn-told`, `wr-ended`, `wr-told`, `bursts-down`, `flat-down`.

#### THE REST'S TIES

Undecided invariant: an ended outer's or lane's last ghost tells its joiners
past the run at each bound binder's end, though no part holds it and its tie
is meaning only. No untold measure is kept over the ghost. Open too: the
siblings' rests at a settle, which the pool reached only while the flatMap held
a part. Settled when
`outer-ghost-told` is a body over such a measure, and `others-heads` is a body.

Members: `outer-ghost-told`, `lane-ghost-told`, `others-heads`,
`outer-ended-heads`, `lanes-rest-heads`, `body-burst-heads`, `rest-sourced`,
`take-leftover`, `body-leftover`.

#### SOURCE-CALL POSITIONS

Which position facts a source's call finds, a field `Carried` owes or the
agenda's placement gives: every subscriber of its subject joined before the
run, and no connect's burst in its body open at the run. Untried; a source
re-entering itself would refute both. Settled when `joined-before` and
`fed-calm` are bodies, or the field is added and framed.

Members: `joined-before`, `fed-calm`, `fin-calm`.

#### THE FED LEFTOVER

Whether a connect's leftover is kept, as a twin, when a feed or a finish
restages it with no burst in its body open (`Shut`): a fed joiner differs
only inside a nested connect's burst. Settled when `fed-calm-tw` is a body
by the leftover's clauses, or a witness under `Shut`.

Members: `fed-calm-tw`, `fin-calm-tw`.

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
`end-ghost`, `out-deeper`, `take-pooled`, `body-pooled`.

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

#### STEP PARTS

Each node's step, alone, is its meaning's next event: the generators,
map/scan/take, a flatMap, an ended connect, a node fed or a body shut its
source's step, and the rest-likes. Untried; believed unfoldings. Settled when each is
a body.

Members: `after-map`, `after-scan`, `after-take`, `clear-take`,
`frames-after`, `burst-after`, `of-after`, `flat-skips`, `ended-skips`,
`feed-alikeⁱ`, `shut-alikeⁱ`, `defer-skips`, `rest-skips`, `union-skips`,
`bursting-skips`, `under-skips`, `first-defer`, `first-rest`, `first-union`,
`first-bursting`, `first-under`.

## Tier 2 — the simultaneous spec

**The statement:** the simultaneous spec, stated over the denotation.

### Ledger

#### THE INSTANTS

Whether every position the fold builds lies under the subscribe frame or a
timer cascade, as `instantOf` reads it. Settled when `positioned` is a body
by induction over the fold.

Members: `positioned`.

## Tier 3 — the simultaneous spec, proven

**The proof:** Tier 2's statements, discharged over `adequacy`.

### Ledger

#### THE SPEC

Suspect fact: false of the placeholder elaboration, one name and no
protocol. Batches joined are the plain values, batches are the spec's
grouping, at every site and related environment. Settled when both are
bodies over the real operators.

Members: `left-to-rightˢ`, `batchableˢ`.

#### SOUND NAMES

Suspect fact: `Sound` (names lie in their instant, one name per instant)
is false of the placeholder's one name. Whether each real operator keeps it
and it survives limits. Settled when the per-operator facts are bodies.

Members: `coldˢ-sound`, `emptyˢ-sound`, `ofˢ-sound`, `mapˢ-sound`,
`scanˢ-sound`, `takeWhileˢ-sound`, `flatMapˢ-sound`, `connectˢ-sound`,
`defer-sound`, `sound-admissible`, `batched-sound`.
