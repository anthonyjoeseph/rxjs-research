# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### THE CALM CARRIED

Untried: whether every step keeps each burst source's rest, wherever a shut
could fall back on it, heading no sooner than the run's position — the
`Calm` half of `Carried.behind`. A rest early yet unreached is what
refuted the unconditional shut. Settled when `take-end-calm` is a body
or a reachable configuration refutes it.

Members: `take-out-calm`, `take-end-calm`, `lanes-end-calm`,
`outer-end-calm`, `cut-calm`, `pop-calm`.

#### THE FLATMAP UNDER A SHUT

Untried: whether a flatMap's step stays twinned or past `q` when its outer,
lanes and pool do. Settled when `flat-down` is a body or refuted.

Members: `flat-down`.

#### THE JOB STACK

Suspect: `Meaning`'s `owing` zips a subject's feeds with its feeding jobs,
which `Owned` does not yet align. Whether a job pushed, popped, dropped or
left idle keeps the carrier. Settled when `owned-popped` and `meaning-pop`
are bodies or refuted.

Members: `owned-idle`, `meaning-idle`, `sorted-idle`, `owned-popped`,
`meaning-pop`, `sorted-pop`, `pop-queue`, `pop-told`, `pop-heads`,
`owned-dropped`, `meaning-drop`, `sorted-drop`, `meaning-note`,
`sorted-note`, `note-least`, `turn-dry`, `downs-plug`, `kont-onward`,
`feed-onward`, `src-onward`, `join-onward`, `src-cut-onward`,
`body-cut-onward`, `body-meaning`, `body-books`.

#### THE PLANTED CLIMBS

Untried: the climb carries no take's stage, so whether every take on a
value's route is `taking`; and whether an `of`'s emission, a dropped turn
and a body's owed completion keep the carrier. Settled when `take-pass` is
a body or refuted.

Members: `gone-take`, `take-pass`, `body-rest-heads`, `owned-body`,
`emit-void`, `emit-open`, `burst-spent`.

#### THE LEFTOVER ACROSS A PLANT

A plant moves the part a connect above it reads into its leftover, so
`Lefts` does not follow `lifts-planted` for free: open whether the
leftovers twin along a live route, as `Keep.route-lingers` twins the
pools. Every planted climb's `lefts` needs it. Settled when `scan-lefts`
is a body or refuted.

Members: `scan-lefts`, `take-out-lefts`, `take-end-lefts`,
`lanes-end-lefts`, `outer-end-lefts`.

#### THE LANDING CLIMBS

A climb that lands plants a node and stops: a `Hopped` needs `Carried`'s
`meets` and a `Gain`, which want the lift of a skip through the plant —
no lemma gives it. Open which skip each lands on: a queued value begun,
an admitted lane, a connect's feed. Settled when `outer-admit` is a body
or refuted.

Members: `outer-admit`, `outer-settle`, `lanes-dequeue`, `call-source`.

#### THE FLATMAP DRAINED

Suspect: nothing in the carrier ties a flatMap's count to its running
lanes or its done flag to its outer's part, so its last end may not
leave both gone. A missing invariant goes in the record. Settled when
`lanes-drained` is a body or refuted.

Members: `lanes-drained`, `outer-drained`.

#### THE PLANTED END'S CARRIER

A climb planting its node anew — a take's next stage, a dead take, a
flatMap done — has every part of `Calling` but the carrier's: open
whether the jobs, meaning, queue, books, told, load and heads survive the
plant and the step past it, and whether the staged connects are ended,
tied and flagged. Settled when `take-end-owned` is a body or refuted.

Members: `take-out-owned`, `take-out-queue`, `take-out-books`,
`take-out-told`, `take-out-load`, `take-out-heads`,
`take-end-rest-heads`, `take-end-ended`, `take-end-lingers`,
`take-end-flags`, `take-end-owned`, `take-end-meaning`,
`take-end-queue`, `take-end-books`, `take-end-told`,
`take-end-load`, `take-end-heads`, `lanes-end-rest-heads`, `lanes-end-ended`,
`lanes-end-lingers`, `lanes-end-flags`, `lanes-end-owned`,
`lanes-end-meaning`, `lanes-end-queue`, `lanes-end-books`,
`lanes-end-told`, `lanes-end-load`, `lanes-end-heads`,
`outer-end-rest-heads`, `outer-end-ended`, `outer-end-lingers`,
`outer-end-flags`, `outer-end-owned`, `outer-end-meaning`,
`outer-end-queue`, `outer-end-books`,
`outer-end-told`, `outer-end-load`, `outer-end-heads`.

#### THE CUT AND THE FIRE

Untried: whether a cut node's step and a timer's fire keep each carrier part
on the state tree. The cut node has no old counterpart. Settled when
`cut-owned` and `fire-owned` are bodies.

Members: `call-cut`, `cut-torn`, `cut-owned`, `cut-meaning`, `cut-queue`,
`cut-turned`, `cut-sorted`, `cut-lingers`, `cut-told`,
`cut-ended`, `cut-flags`, `cut-load`, `cut-heads`, `fire-kernels`, `fire-part`,
`fire-load`, `fire-owned`, `fire-meaning`, `fire-timed`, `fire-joined`,
`fire-sorted`, `burst-poll`,
`burst-play`, `burst-finish`.

#### THE WALK

Untried: the old well-configuration invariant was a well heap over the CPS
machine's states, so a state-tree `WellMach` is unwritten. Settled when it is
a definition and `preserve` a body or refuted.

Members: `WellMach`, `preserve`, `begin-well`.

#### THE ROOT STEP

Whether a step, its sources clear of it, keeps its parts placed: a flatMap's
admitted lanes; a defer's program, subscribed or fed. Settled when
`flat-within` is a body or refuted.

Members: `flat-within`, `defer-within`, `defer-fed`, `under-shown-connect`.

#### THE SUBSCRIBE

Untried: whether subscribing each operator keeps the carrier. Settled when
`sub-flat` and `sub-connect` are bodies.

Members: `sub-cold`, `sub-empty`, `sub-of`, `sub-map`, `sub-scan`,
`sub-take`, `sub-flat`, `sub-connect`, `sub-joined`, `sub-defer`.

#### THE CLIMB FRAMES

Believed unfoldings: the climbs with no old body. Settled when each is a body.

Members: `scan-books`, `scan-load`, `call-lane`, `emit-shut`, `last-void`,
`last-enter`, `take1-void`, `take1-enter`.

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
