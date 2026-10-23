# PROOF-STATE — the risk ledger

Rules: CLAUDE.md, "PROOF-STATE.md — the risk ledger" and "Two phases".

## Tier 0 — the port

**Port:** the old `adequacy/` tower carried to the state tree in `port/`, old names only (`make port-check`, deleted with this tier).

### Ledger

#### THE SHUT'S HEADS

Suspected false: `Heads` reads a node's step alone, and a burst skipping
inside its range falls back, once shut out of it, to a rest no premise
bounds. Settled by a machine counterexample, or a component-wise heads
invariant carried by `Each` that bounds every rest.

Members: `shut-heads`.

## Tier 1 — the adequacy theorem

**Adequacy:** the denotation matches the operational semantics.

### Ledger

#### THE JOB STACK

Suspect: `Meaning`'s `owing` zips a subject's feeds with its feeding jobs,
which `Owned` does not yet align. Whether a job pushed, popped, dropped or
left idle keeps the carrier. Settled when `owned-popped` and `meaning-pop`
are bodies or refuted.

Members: `owned-idle`, `meaning-idle`, `sorted-idle`, `owned-popped`,
`meaning-pop`, `sorted-pop`, `pop-queue`, `pop-behind`, `pop-told`,
`owned-dropped`, `meaning-drop`, `sorted-drop`, `meaning-note`,
`sorted-note`, `note-least`, `turn-dry`, `downs-plug`, `kont-onward`,
`feed-onward`, `src-onward`, `join-onward`, `src-cut-onward`,
`body-cut-onward`, `body-meaning`, `body-books`.

#### THE PLANTED CLIMBS

Untried, and every old body a dead route: whether a climb's write, read as a
`plant` (a scan's accumulator, a take's stage) or a job (`admit`, `dequeue`,
`feeds`, `rets`), keeps each carrier part. Settled when `scan-owned` and
`take-out` are bodies or refuted.

Members: `scan-kernels`, `scan-lifts`, `scan-lefts`, `scan-owned`,
`scan-meaning`, `scan-queue`, `scan-behind`, `scan-lingers`, `scan-flags`,
`gone-take`, `take-pass`, `take-out`, `take-end`, `call-outer`,
`call-lanes`, `call-source`, `body-rest-heads`, `owned-body`, `emit-void`,
`emit-open`, `burst-spent`.

#### THE CUT AND THE FIRE

Untried: whether a cut node's step and a timer's fire keep each carrier part
on the state tree. The cut node has no old counterpart. Settled when
`cut-owned` and `fire-owned` are bodies.

Members: `call-cut`, `cut-torn`, `cut-owned`, `cut-meaning`, `cut-queue`,
`cut-turned`, `cut-sorted`, `cut-behind`, `cut-lingers`, `cut-told`,
`cut-ended`, `cut-flags`, `cut-load`, `fire-kernels`, `fire-part`,
`fire-load`, `fire-owned`, `fire-meaning`, `fire-timed`, `fire-joined`,
`fire-sorted`, `fire-flags`, `fire-told`, `fire-ended`, `burst-poll`,
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

Believed unfoldings: a context climbing one frame, and the climbs with no old
body. Settled when each is a body.

Members: `of-path`, `map-at`, `scan-at`, `take-at`, `take-path`, `body-at`,
`scan-books`, `scan-load`, `scan-told`, `scan-ended`, `call-lane`, `emit-shut`, `last-void`,
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
